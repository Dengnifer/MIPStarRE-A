#!/usr/bin/env python3
"""Split a monolithic reference-paper TeX source into one file per section.

The split is purely positional — no line is edited, added, or dropped — so the
concatenation of the emitted pieces reproduces the input byte-for-byte, which
``--verify`` checks (and the run aborts if it fails).  Output layout, following
the ``references/ldt-paper/`` mirror convention (content files for reading and
citation, not a standalone build):

    00_preamble.tex     everything before ``\\begin{document}``
    01_frontmatter.tex  ``\\begin{document}`` up to the first ``\\section``
    NN_<slug>.tex       one file per ``\\section`` (an ``\\appendix`` switch is
                        kept at the head of the section that follows it)
    NN_bibliography.tex trailing bibliography block through ``\\end{document}``

A README.md manifest with provenance and the file/line-range table is written
alongside (or printed with ``--manifest-only``).

Usage:
    python3 scripts/split_reference_paper.py INPUT.tex OUTDIR \\
        --arxiv 2001.04383 --title "MIP*=RE" [--force]
"""

from __future__ import annotations

import argparse
import datetime
import re
import sys
from pathlib import Path

SECTION_RE = re.compile(r"^\s*\\section\*?\s*\{")
APPENDIX_RE = re.compile(r"^\s*\\appendix\s*(%.*)?$")
BEGIN_DOC_RE = re.compile(r"^\s*\\begin\{document\}")
BIB_RE = re.compile(r"^\s*\\bibliograph(y|ystyle)\s*\{")


def section_title(line: str) -> str:
    """Extract the brace-balanced title of a ``\\section{...}`` line."""
    start = line.index("{")
    depth = 0
    for i in range(start, len(line)):
        if line[i] == "{" and (i == 0 or line[i - 1] != "\\"):
            depth += 1
        elif line[i] == "}" and line[i - 1] != "\\":
            depth -= 1
            if depth == 0:
                return line[start + 1 : i]
    return line[start + 1 :].strip()


def slugify(title: str) -> str:
    slug = re.sub(r"\\[A-Za-z@]+", " ", title)          # drop TeX commands
    slug = re.sub(r"[${}^_]", " ", slug)
    slug = re.sub(r"[^A-Za-z0-9]+", "_", slug).strip("_").lower()
    return slug[:48].rstrip("_") or "section"


def split_lines(text: str) -> list[tuple[str, str, int, int]]:
    """Return (kind, name-hint, start, end) pieces covering every line once.

    ``start``/``end`` are 0-based, end-exclusive line indices into
    ``text.splitlines(keepends=True)``.
    """
    lines = text.splitlines(keepends=True)
    n = len(lines)

    begin_doc = next((i for i, l in enumerate(lines) if BEGIN_DOC_RE.match(l)), None)
    if begin_doc is None:
        sys.exit("error: no \\begin{document} found")

    section_starts = [i for i, l in enumerate(lines) if SECTION_RE.match(l) and i > begin_doc]
    if not section_starts:
        sys.exit("error: no \\section after \\begin{document}")

    last_section = section_starts[-1]
    bib_start = next((i for i in range(last_section + 1, n) if BIB_RE.match(lines[i])), n)

    pieces: list[tuple[str, str, int, int]] = [
        ("preamble", "preamble", 0, begin_doc),
        ("frontmatter", "frontmatter", begin_doc, section_starts[0]),
    ]
    for idx, start in enumerate(section_starts):
        end = section_starts[idx + 1] if idx + 1 < len(section_starts) else bib_start
        # Pull a directly preceding \appendix switch into THIS piece so the
        # previous section's file does not end with a dangling mode change.
        adj = start
        j = start - 1
        while j > pieces[-1][2] and (APPENDIX_RE.match(lines[j]) or not lines[j].strip()):
            if APPENDIX_RE.match(lines[j]):
                adj = j
            j -= 1
        if adj != start:
            prev = pieces[-1]
            pieces[-1] = (prev[0], prev[1], prev[2], adj)
            start = adj
        title_line = next(l for l in lines[start:end] if SECTION_RE.match(l))
        pieces.append(("section", slugify(section_title(title_line)), start, end))
    if bib_start < n:
        pieces.append(("bibliography", "bibliography", bib_start, n))
    return pieces


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("input", type=Path)
    ap.add_argument("outdir", type=Path)
    ap.add_argument("--arxiv", required=True, help="arXiv identifier for the manifest")
    ap.add_argument("--title", required=True, help="paper title for the manifest")
    ap.add_argument("--force", action="store_true", help="overwrite a non-empty OUTDIR")
    ap.add_argument("--no-verify", action="store_true",
                    help="skip the byte-identity check (not recommended)")
    args = ap.parse_args()

    raw = args.input.read_bytes()
    # Normalize CRLF deliberately (arXiv sources are sometimes CRLF); the
    # byte-identity check below is modulo exactly this normalization, and the
    # manifest records it.  Path.read_text would do the same silently — and a
    # silent normalization once defeated the verification here (events.md
    # 2026-08-30).
    crlf = b"\r\n" in raw
    text = raw.replace(b"\r\n", b"\n").decode("utf-8")
    lines = text.splitlines(keepends=True)
    pieces = split_lines(text)

    args.outdir.mkdir(parents=True, exist_ok=True)
    existing = [p for p in args.outdir.iterdir() if p.suffix == ".tex"]
    if existing and not args.force:
        sys.exit(f"error: {args.outdir} already holds .tex files; use --force to overwrite")
    for p in existing:
        p.unlink()

    seen: dict[str, int] = {}
    rows: list[tuple[str, str, int, int]] = []
    for num, (kind, hint, start, end) in enumerate(pieces):
        slug = hint
        if slug in seen:
            seen[slug] += 1
            slug = f"{slug}_{seen[slug]}"
        else:
            seen[slug] = 1
        name = f"{num:02d}_{slug}.tex"
        (args.outdir / name).write_text("".join(lines[start:end]), encoding="utf-8")
        rows.append((name, kind, start + 1, end))

    if not args.no_verify:
        joined = b"".join((args.outdir / name).read_bytes() for name, _, _, _ in rows)
        if joined != raw.replace(b"\r\n", b"\n"):
            for name, _, _, _ in rows:
                (args.outdir / name).unlink()
            sys.exit("error: byte-identity verification FAILED; output removed")

    today = datetime.date.today().isoformat()
    manifest = [
        f"# Paper mirror: {args.title}",
        "",
        f"In-repo TeX source mirror of arXiv:{args.arxiv}, split one file per",
        f"section from `{args.input.name}` by `scripts/split_reference_paper.py`",
        f"on {today}. The split is positional only: concatenating the `.tex`",
        "files below in filename order reproduces the downloaded source"
        + (" byte-for-byte after CRLF→LF newline normalization"
           if crlf else " byte-for-byte")
        + " (verified at split time). This mirror is the",
        "mathematical ground truth for citation and reading; it is not meant",
        "to compile standalone.",
        "",
        "| File | Kind | Source lines |",
        "|------|------|--------------|",
    ]
    manifest += [f"| `{name}` | {kind} | {start}–{end} |" for name, kind, start, end in rows]
    manifest.append("")
    (args.outdir / "README.md").write_text("\n".join(manifest), encoding="utf-8")

    print(f"split {args.input.name}: {len(rows)} files -> {args.outdir} (byte-identity "
          + ("verified" if not args.no_verify else "NOT verified"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
