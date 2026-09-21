#!/usr/bin/env python3
"""Mirror an arXiv paper's TeX source into ``references/<key>-paper/``.

Downloads ``https://arxiv.org/e-print/<id>``, keeps only the text of the paper
(``.tex .bib .bbl .sty .cls .bst`` plus the figures the text actually includes)
and writes ``SOURCE.md`` recording what was fetched, when, from where, with the
archive's sha256 and the licence.  Nothing is flattened, rewritten or
reformatted: the bytes are the mathematical ground truth, and
``scripts/split_reference_paper.py`` later splits them with a byte-identity
check.  A PDF-only submission is a hard stop — the kit needs TeX source.

Usage:
    python3 scripts/fetch_arxiv_source.py 1234.56789 --dest references/demo-paper
    python3 scripts/fetch_arxiv_source.py https://arxiv.org/abs/1234.56789v2 \\
        --dest references/demo-paper --title "A demonstration paper"
    python3 scripts/fetch_arxiv_source.py 1234.56789 --dest DIR --from-archive FILE
"""

from __future__ import annotations

import argparse
import datetime
import gzip
import hashlib
import io
import re
import shutil
import sys
import tarfile
import time
import urllib.error
import urllib.request
from pathlib import Path

#: A descriptive User-Agent is not optional: arXiv answers the default Python
#: one with 403.
USER_AGENT = "formalization-kit/1 (arXiv e-print mirror; one polite retry)"

EPRINT_URL = "https://arxiv.org/e-print/{id}"
ABS_URL = "https://arxiv.org/abs/{id}"

#: What a mathematical source mirror is made of.
KEEP_SUFFIXES = {".tex", ".bib", ".bbl", ".sty", ".cls", ".bst"}
FIGURE_SUFFIXES = (".pdf", ".png", ".jpg", ".jpeg", ".eps", ".ps", ".svg",
                   ".gif", ".tif", ".tiff")

#: The verbatim download lives beside the split, not in it: the splitter
#: deletes `.tex` files in its output directory when it is asked to overwrite.
SOURCE_SUBDIR = "arxiv-source"

UNKNOWN_LICENCE = "UNKNOWN - check before redistributing"

MAX_MEMBER_BYTES = 64 * 1024 * 1024
MAX_TOTAL_BYTES = 512 * 1024 * 1024

#: New style `1234.56789v2`, old style `math-ph/0000001`, with or without a
#: version, bare or inside an abs/pdf/e-print URL or an `arXiv:` prefix.
NEW_ID = r"\d{4}\.\d{4,5}(?:v\d+)?"
OLD_ID = r"[a-z][a-z-]*(?:\.[A-Z]{2})?/\d{7}(?:v\d+)?"
ID_RE = re.compile(rf"^(?:{NEW_ID}|{OLD_ID})$")
URL_RE = re.compile(
    rf"arxiv\.org/(?:abs|pdf|e-print|format)/({NEW_ID}|{OLD_ID})", re.IGNORECASE)

INCLUDEGRAPHICS_RE = re.compile(r"\\includegraphics\*?\s*(?:\[[^\]]*\])?\s*\{([^}]*)\}")
DOCUMENTCLASS_RE = re.compile(r"^[^%\n]*\\documentclass", re.MULTILINE)
BEGIN_DOCUMENT_RE = re.compile(r"^[^%\n]*\\begin\{document\}", re.MULTILINE)


class FetchError(Exception):
    """Anything that stops the mirror; the message is shown to the operator."""


# ── identifiers ─────────────────────────────────────────────────────────────


def parse_arxiv_id(text: str) -> str:
    """``https://arxiv.org/pdf/1234.56789v2.pdf`` -> ``1234.56789v2``."""
    raw = text.strip()
    match = URL_RE.search(raw)
    if match:
        return match.group(1)
    raw = re.sub(r"^arxiv:", "", raw, flags=re.IGNORECASE)
    raw = re.sub(r"\.pdf$", "", raw, flags=re.IGNORECASE)
    if ID_RE.match(raw):
        return raw
    raise FetchError(
        f"{text!r} is not an arXiv identifier or URL. Give the id (1234.56789, "
        "with or without a version) or any arxiv.org abs/pdf/e-print link."
    )


def split_version(arxiv_id: str) -> tuple[str, str]:
    """``1234.56789v2`` -> ``("1234.56789", "v2")``; no version -> ``("…", "")``."""
    match = re.search(r"(v\d+)$", arxiv_id)
    if match:
        return arxiv_id[: -len(match.group(1))], match.group(1)
    return arxiv_id, ""


# ── download ────────────────────────────────────────────────────────────────


def http_get(url: str, timeout: float = 90.0, retries: int = 1,
             pause: float = 5.0) -> bytes:
    """GET with a real User-Agent and one polite retry."""
    last = ""
    for attempt in range(retries + 1):
        request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
        try:
            with urllib.request.urlopen(request, timeout=timeout) as response:
                return response.read()
        except urllib.error.HTTPError as exc:
            last = f"HTTP {exc.code} {exc.reason}"
            if exc.code in (400, 403, 404):
                break  # a wrong id does not get better by asking twice
        except (urllib.error.URLError, OSError, ValueError) as exc:
            last = str(exc)
        if attempt < retries:
            time.sleep(pause)
    raise FetchError(f"could not download {url}: {last}")


def fetch_licence_and_version(arxiv_id: str) -> tuple[str, str]:
    """Best effort read of the abs page: (licence line, version such as ``v3``)."""
    base, version = split_version(arxiv_id)
    try:
        page = http_get(ABS_URL.format(id=arxiv_id), timeout=45, retries=0).decode(
            "utf-8", "replace")
    except FetchError:
        return UNKNOWN_LICENCE, version
    licence = UNKNOWN_LICENCE
    match = re.search(r"https?://(?:arxiv\.org/licenses|creativecommons\.org/"
                      r"(?:licenses|publicdomain))/[^\s\"'<>]+", page)
    if match:
        licence = match.group(0).rstrip("/") + "/"
    if not version:
        seen = re.search(re.escape(base) + r"v(\d+)", page)
        if seen:
            version = "v" + seen.group(1)
    return licence, version


# ── unpacking ───────────────────────────────────────────────────────────────


def _safe_members(tar: tarfile.TarFile):
    total = 0
    for member in tar.getmembers():
        name = member.name.replace("\\", "/")
        while name.startswith("./"):
            name = name[2:]
        if not member.isfile():
            continue  # directories are recreated; links and devices are dropped
        if name.startswith("/") or ".." in Path(name).parts:
            continue
        if member.size > MAX_MEMBER_BYTES:
            continue
        total += member.size
        if total > MAX_TOTAL_BYTES:
            raise FetchError("the archive is implausibly large; refusing to unpack it")
        member.name = name
        yield member


def unpack(blob: bytes, workdir: Path) -> None:
    """Unpack an arXiv e-print into *workdir*, or explain why it cannot be."""
    if blob[:4] == b"%PDF":
        raise FetchError(
            "this submission is a PDF, not TeX source. The kit needs the TeX source: "
            "tell the meta session to ask the owner to obtain it from the authors "
            "(and to record where it came from in SOURCE.md)."
        )
    if not blob:
        raise FetchError("the download was empty")

    payload = blob
    if blob[:2] == b"\x1f\x8b":
        try:
            with tarfile.open(fileobj=io.BytesIO(blob), mode="r:gz") as tar:
                tar.extractall(workdir, members=list(_safe_members(tar)))
            return
        except tarfile.TarError:
            pass
        try:
            payload = gzip.decompress(blob)
        except OSError as exc:
            raise FetchError(f"the download is gzip but unreadable: {exc}") from exc
        if payload[:4] == b"%PDF":
            raise FetchError(
                "this submission is a single gzipped PDF, not TeX source. The kit "
                "needs the TeX source: tell the meta session to ask the owner to "
                "obtain it from the authors."
            )
    else:
        try:
            with tarfile.open(fileobj=io.BytesIO(blob), mode="r:*") as tar:
                tar.extractall(workdir, members=list(_safe_members(tar)))
            return
        except tarfile.TarError:
            pass

    text = payload.decode("utf-8", "replace")
    if not (DOCUMENTCLASS_RE.search(text) or BEGIN_DOCUMENT_RE.search(text)):
        raise FetchError(
            "the download is neither a tar archive nor a single TeX file "
            "(no \\documentclass and no \\begin{document} in it)."
        )
    (workdir / "main.tex").write_bytes(payload)


# ── selection ───────────────────────────────────────────────────────────────


def graphics_candidates(name: str) -> list[str]:
    name = name.strip().replace("\\", "/")
    if not name:
        return []
    if Path(name).suffix.lower() in FIGURE_SUFFIXES:
        return [name]
    return [name + suffix for suffix in FIGURE_SUFFIXES]


def select_files(workdir: Path) -> tuple[list[Path], list[Path]]:
    """(text files, figure files) as paths relative to *workdir*."""
    every = sorted(p for p in workdir.rglob("*") if p.is_file())
    text = [p for p in every if p.suffix.lower() in KEEP_SUFFIXES]

    wanted: set[str] = set()
    for path in text:
        if path.suffix.lower() != ".tex":
            continue
        body = path.read_text(encoding="utf-8", errors="replace")
        for raw in INCLUDEGRAPHICS_RE.findall(body):
            for piece in raw.split(","):
                wanted.update(graphics_candidates(piece))

    by_relative = {p.relative_to(workdir).as_posix(): p for p in every}
    by_name: dict[str, list[Path]] = {}
    for p in every:
        by_name.setdefault(p.name, []).append(p)

    figures: list[Path] = []
    for candidate in sorted(wanted):
        hit = by_relative.get(candidate) or by_relative.get(candidate.lstrip("./"))
        if hit is None:
            same = by_name.get(Path(candidate).name, [])
            hit = same[0] if len(same) == 1 else None
        if hit is not None and hit not in figures and hit not in text:
            figures.append(hit)
    return text, figures


def find_main(text_files: list[Path], workdir: Path) -> Path | None:
    """The file with both ``\\documentclass`` and ``\\begin{document}``."""
    candidates = []
    for path in text_files:
        if path.suffix.lower() != ".tex":
            continue
        body = path.read_text(encoding="utf-8", errors="replace")
        if DOCUMENTCLASS_RE.search(body) and BEGIN_DOCUMENT_RE.search(body):
            candidates.append(path)
    if not candidates:
        return None
    preferred = ("main.tex", "ms.tex", "paper.tex", "article.tex")
    for name in preferred:
        for path in candidates:
            if path.name.lower() == name:
                return path
    return max(candidates, key=lambda p: p.stat().st_size)


# ── writing the mirror ──────────────────────────────────────────────────────


def copy_into(dest_dir: Path, workdir: Path, files: list[Path]) -> list[str]:
    written: list[str] = []
    for path in files:
        relative = path.relative_to(workdir)
        target = dest_dir / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, target)
        written.append(relative.as_posix())
    return written


def rename_main_bbl(dest_dir: Path, main: str | None, names: list[str]) -> str:
    """Move ``<main>.bbl`` aside so a stray bibtex run cannot overwrite it.

    arXiv submissions ship a precompiled `.bbl` and often no `.bib` at all;
    that file is the bibliography, and losing it loses every citation.
    """
    if not main:
        return ""
    stem = Path(main).with_suffix(".bbl").as_posix()
    if stem not in names:
        return ""
    target = Path(stem).with_name(Path(stem).stem + "-arxiv.bbl").as_posix()
    (dest_dir / stem).rename(dest_dir / target)
    names[names.index(stem)] = target
    return f"{stem} -> {target}"


def write_source_md(dest: Path, *, arxiv_id: str, version: str, url: str,
                    sha256: str, size: int, licence: str, title: str,
                    names: list[str], main: str | None, bbl_note: str,
                    offline: bool) -> None:
    now = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    base, _ = split_version(arxiv_id)
    lines = [
        f"# Source mirror: {title or 'arXiv:' + base}",
        "",
        f"- arXiv id: `{base}`",
        f"- Version: `{version or 'unknown (the unversioned e-print was requested)'}`",
        f"- Fetched from: {url}",
        f"- Fetched (UTC): {now}",
        f"- Archive sha256: `{sha256}`",
        f"- Archive size: {size} bytes",
        f"- Licence: {licence}",
        "",
        "Only `.tex`, `.bib`, `.bbl`, `.sty`, `.cls` and `.bst` files and the figures",
        f"referenced by `\\includegraphics` are kept, under `{SOURCE_SUBDIR}/`; nothing is",
        "flattened, reformatted or edited, so the bytes below are the ones arXiv served.",
        "Copyright remains with the authors.",
        "",
    ]
    if offline:
        lines += ["This mirror was unpacked from a local archive (`--from-archive`), so the",
                  "licence could not be read from the abstract page.", ""]
    if main:
        lines += [f"Main file: `{SOURCE_SUBDIR}/{main}`", ""]
    if bbl_note:
        lines += [f"Renamed so a bibtex run cannot clobber it: `{bbl_note}`", ""]
    lines += ["| File | Bytes |", "|------|-------|"]
    for name in names:
        try:
            size_b = (dest / SOURCE_SUBDIR / name).stat().st_size
        except OSError:
            size_b = 0
        lines.append(f"| `{SOURCE_SUBDIR}/{name}` | {size_b} |")
    lines.append("")
    (dest / "SOURCE.md").write_text("\n".join(lines), encoding="utf-8")


def mirror(args: argparse.Namespace) -> int:
    arxiv_id = parse_arxiv_id(args.arxiv)
    base, version = split_version(arxiv_id)
    dest: Path = args.dest
    source_dir = dest / SOURCE_SUBDIR
    if source_dir.exists() and any(source_dir.iterdir()) and not args.force:
        raise FetchError(f"{source_dir} already holds files; pass --force to replace them")

    offline = args.from_archive is not None
    if offline:
        blob = Path(args.from_archive).read_bytes()
        url = f"(local archive {Path(args.from_archive).name})"
        licence = args.licence or UNKNOWN_LICENCE
    else:
        url = EPRINT_URL.format(id=arxiv_id)
        blob = http_get(url)
        licence, version = fetch_licence_and_version(arxiv_id)
        licence = args.licence or licence
    sha256 = hashlib.sha256(blob).hexdigest()

    workdir = dest / ".unpack.tmp"
    if workdir.exists():
        shutil.rmtree(workdir)
    workdir.mkdir(parents=True)
    try:
        unpack(blob, workdir)
        text_files, figures = select_files(workdir)
        if not text_files:
            raise FetchError("the archive holds no .tex file; nothing to mirror")
        main_path = find_main(text_files, workdir)
        if source_dir.exists():
            shutil.rmtree(source_dir)
        source_dir.mkdir(parents=True)
        names = copy_into(source_dir, workdir, text_files + figures)
        main = main_path.relative_to(workdir).as_posix() if main_path else None
        bbl_note = rename_main_bbl(source_dir, main, names)
    finally:
        shutil.rmtree(workdir, ignore_errors=True)

    write_source_md(dest, arxiv_id=arxiv_id, version=version, url=url, sha256=sha256,
                    size=len(blob), licence=licence, title=args.title or "",
                    names=sorted(names), main=main, bbl_note=bbl_note, offline=offline)

    print(f"mirrored arXiv:{base}{version} -> {source_dir} "
          f"({len(text_files)} text files, {len(figures)} figures)")
    if main is None:
        print("warning: no file carries both \\documentclass and \\begin{document}; "
              "pick the main file by hand before splitting.")
        return 0
    title = args.title or f"arXiv:{base}"
    print("next, split it into one file per section:")
    print(f'  python3 scripts/split_reference_paper.py {source_dir / main} {dest} '
          f'--arxiv {base} --title "{title}"')
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("arxiv", help="arXiv id or any arxiv.org abs/pdf/e-print URL")
    parser.add_argument("--dest", type=Path, required=True,
                        metavar="references/<key>-paper",
                        help="mirror directory; the download lands in its "
                             f"{SOURCE_SUBDIR}/ subdirectory")
    parser.add_argument("--title", default="", help="paper title, for SOURCE.md")
    parser.add_argument("--licence", default="",
                        help="licence line to record when the abstract page cannot be read")
    parser.add_argument("--from-archive", metavar="FILE",
                        help="unpack this local e-print archive instead of downloading")
    parser.add_argument("--force", action="store_true",
                        help="replace an existing mirror")
    args = parser.parse_args(sys.argv[1:] if argv is None else argv)
    try:
        return mirror(args)
    except FetchError as exc:
        sys.stderr.write(f"fetch_arxiv_source.py: {exc}\n")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
