#!/usr/bin/env python3
"""Turn this kit checkout into the repository of one specific paper.

Renames the placeholder Lean root ``PaperLib`` to the name you choose, points
the repository slugs at your GitHub repository, writes ``local/project.json``,
retitles the blueprint and the paper-gap configuration, writes a project
README (the kit's own README moves to ``docs/KIT.md``) and — unless
``--keep-git`` — starts a fresh git history with one mechanical first commit.
It never creates the GitHub repository and never pushes: those need the
owner's word once, and the two commands are printed at the end.

Usage:
    python3 scripts/bootstrap_project.py --lean-root MyPaper \\
        --github-slug owner/my-paper --arxiv https://arxiv.org/abs/1234.56789 \\
        --title "The title of the paper" [--dry-run]

Exit codes: 0 done, 2 refused (bad name, already bootstrapped, git failure),
5 the project is instantiated but the paper mirror step did not finish.
"""

from __future__ import annotations

import argparse
import datetime
import json
import os
import re
import shutil
import subprocess
import sys
from collections import Counter
from pathlib import Path

#: The kit's placeholders.  The two SLUGS are spelled in pieces on purpose: this
#: script rewrites the literal strings across the whole tree, and a constant that
#: means "no repository has been approved yet" has to survive its own rewrite, or
#: the instantiated project would read its real slug as a placeholder.  The Lean
#: root is the name of the library itself and is renamed with everything else, so
#: it stays a plain literal.  Same reasoning, same spelling, as
#: `scripts/project_config.py`.
PLACEHOLDER_ROOT = "PaperLib"
PLACEHOLDER_SLUG = "OWNER" + "/" + "REPO"
PLACEHOLDER_COMPARATOR = PLACEHOLDER_SLUG + "-comparator"

#: Never rewritten: the origin project's frozen ledger, and the kit's own
#: extraction record.  Both are history, not this project's files.
EXCLUDED_PREFIXES = ("docs/origin/", "local/kit/")

#: Directories the walk never enters when there is no git index to ask.
SKIP_DIRS = {".git", ".lake", "__pycache__", ".worktrees", "node_modules", ".mypy_cache"}

#: Tokens that must come through the rename untouched: the environment prefix
#: and the cache-directory name are deliberately kept as they are (they are
#: per-machine, not per-project; projects are separated by paths.cache_root).
INVARIANT_TOKENS = (b"MIPSTARRE_", b"mipstarre")

#: Only the capitalized token is renamed.  The lower-case `paperlib` appears
#: exclusively as the built-in fallback for `paths.cache_root` and
#: `session.tmux` (and in the tests that pin those fallbacks); the values this
#: script writes into local/project.json override every one of them, so
#: renaming the fallback would change nothing except break those tests.

LEAN_IDENT_RE = re.compile(r"^[A-Z][A-Za-z0-9_']*$")
SLUG_RE = re.compile(r"^[A-Za-z0-9](?:[A-Za-z0-9-]{0,38})/[A-Za-z0-9._-]{1,100}$")
KEY_RE = re.compile(r"^[a-z0-9][a-z0-9-]*$")
TRACK_RE = re.compile(r"^[a-z][a-z0-9-]*$")

#: Names a Lean library must not take: Lean core, the packages this repository
#: builds against, and the most common Mathlib root namespaces.  The list is
#: deliberately blunt — the fix is always "pick another name".
RESERVED_ROOTS = {
    "Lean", "Init", "Std", "Batteries", "Mathlib", "Aesop", "Qq", "ProofWidgets",
    "Plausible", "Cli", "ImportGraph", "LeanSearchClient", "Verso", "Lake",
    "Main", "Basic", "Tactic", "Meta", "Elab", "Parser", "Term", "IO", "System",
    "Nat", "Int", "Rat", "Real", "Complex", "Bool", "Char", "String", "Array",
    "List", "Option", "Prod", "Sum", "Set", "Finset", "Function", "Classical",
    "Quot", "Matrix", "Polynomial", "Data", "Logic", "Order", "Topology",
    "Algebra", "Analysis", "Geometry", "Combinatorics", "NumberTheory",
    "MeasureTheory", "Probability", "RingTheory", "LinearAlgebra", "GroupTheory",
    "FieldTheory", "Dynamics", "Computability", "SetTheory", "CategoryTheory",
    PLACEHOLDER_ROOT,
}

README_TEMPLATE = """# {name}

A machine-checked formalization in Lean 4 of {paper}.

| | |
|---|---|
| Source paper | {source_row} |
| Lean library | `{name}` |
| Toolchain | {toolchain} |
| Blueprint | `blueprint/src/` (chapters are written during the blueprint stage) |
| Status | **bootstrapped — no mathematics is formalized yet** |

## Layout

- `{name}/` — the Lean library; `{name}.lean` is its root module.
- `blueprint/src/` — the blueprint: the informal proof, chapter by chapter, with
  `\\lean{{...}}` links to the Lean declarations that discharge each node.
- `references/` — the source paper's TeX, mirrored and split one file per section.
  This mirror is the mathematical ground truth for every statement.
- `docs/` — conventions, the completion criteria, the comparator note, and
  `docs/KIT.md`, the kit this repository was created from.
- `scripts/`, `local/`, `.githooks/` — the checks, the protocols and the
  automation that keep the two in step.

## Working on this

Read `AGENTS.md` first: it states the faithfulness rules that every change obeys.
`local/README.md` explains the workflow layer, `local/protocols/` holds the
protocols it follows, and `local/protocols/completion.md` defines what "done"
means for this project. Machine setup: `python3 scripts/preflight.py`.

## Honesty

Nothing in this repository claims a result it has not checked. Proof debt is
tracked in the blueprint and in the paper-gap notes under `docs/paper-gaps/`;
the completion gate (`python3 scripts/completion_gate.py check --track {track}`)
is the only thing that may declare the project finished.
"""


class Refused(Exception):
    """A precondition the operator has to fix; the message says how."""


# ── helpers ─────────────────────────────────────────────────────────────────


def run(cmd: list[str], cwd: Path, env: dict | None = None,
        timeout: float = 1800.0) -> tuple[int, str, str]:
    try:
        proc = subprocess.run(cmd, cwd=str(cwd), capture_output=True, text=True,
                              timeout=timeout, env={**os.environ, **(env or {})})
    except FileNotFoundError:
        return 127, "", f"{cmd[0]}: not found"
    except subprocess.TimeoutExpired:
        return 124, "", f"{cmd[0]}: timed out"
    return proc.returncode, proc.stdout, proc.stderr


def utc_now() -> str:
    return datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def is_excluded(relative: str) -> bool:
    return any(relative.startswith(prefix) for prefix in EXCLUDED_PREFIXES)


def repo_files(root: Path) -> list[Path]:
    """Every file the rename may touch — the git index when there is one."""
    git = shutil.which("git")
    if git and (root / ".git").exists():
        rc, out, _ = run([git, "-C", str(root), "ls-files", "-z"], cwd=root, timeout=120)
        if rc == 0:
            found = [root / name for name in out.split("\0") if name]
            return [p for p in found if p.is_file() and not p.is_symlink()]
    found = []
    for path in sorted(root.rglob("*")):
        if any(part in SKIP_DIRS for part in path.relative_to(root).parts):
            continue
        if path.is_file() and not path.is_symlink():
            found.append(path)
    return found


def is_binary(data: bytes) -> bool:
    return b"\x00" in data[:8192]


def camel(token: str) -> str:
    return "".join(part[:1].upper() + part[1:] for part in re.split(r"[-_]", token) if part)


# ── validation ──────────────────────────────────────────────────────────────


def validate(args: argparse.Namespace) -> None:
    name = args.lean_root
    if not LEAN_IDENT_RE.match(name):
        raise Refused(
            f"--lean-root {name!r} is not usable as a Lean library root. Use one "
            "capitalized identifier: letters, digits, _ and ' only, no dots "
            "(for example: MyPaper, LowDegree, FourierBound)."
        )
    if name in RESERVED_ROOTS:
        raise Refused(
            f"--lean-root {name!r} is a Lean, Mathlib or kit name; a library with "
            "that root would shadow it. Pick a name that belongs to this paper."
        )
    if "mipstarre" in name.lower():
        raise Refused(
            f"--lean-root {name!r} contains the environment-variable prefix used "
            "throughout the tooling; pick another name."
        )
    if not SLUG_RE.match(args.github_slug):
        raise Refused(
            f"--github-slug {args.github_slug!r} is not owner/repo (for example: "
            "someone/my-paper)."
        )
    if not KEY_RE.match(args.key):
        raise Refused(
            f"--key {args.key!r} must be lower-case letters, digits and hyphens; "
            "it names the paper mirror references/<key>-paper."
        )
    if not TRACK_RE.match(args.track):
        raise Refused(f"--track {args.track!r} must be lower-case letters, digits and hyphens.")


def already_bootstrapped(config: dict) -> str:
    """The marker: a project.json whose Lean root is no longer the placeholder."""
    project = config.get("project") or {}
    root = project.get("lean_root") or project.get("name") or ""
    return root if root and root != PLACEHOLDER_ROOT else ""


# ── the token rewrite ───────────────────────────────────────────────────────


def replacement_pairs(name: str, slug: str, comparator: str) -> list[tuple[bytes, bytes]]:
    """Longest first: the comparator slug contains the repository slug."""
    return [
        (PLACEHOLDER_COMPARATOR.encode(), comparator.encode()),
        (PLACEHOLDER_SLUG.encode(), slug.encode()),
        (PLACEHOLDER_ROOT.encode(), name.encode()),
    ]


def rewrite_contents(root: Path, pairs: list[tuple[bytes, bytes]],
                     dry_run: bool) -> tuple[int, Counter]:
    """Replace the placeholders in every eligible file.  Returns (files, counts)."""
    counts: Counter = Counter()
    touched = 0
    for path in repo_files(root):
        relative = path.relative_to(root).as_posix()
        if is_excluded(relative):
            continue
        try:
            data = path.read_bytes()
        except OSError:
            continue
        if is_binary(data):
            continue
        before = {token: data.count(token) for token in INVARIANT_TOKENS}
        new = data
        hits = 0
        for old, replacement in pairs:
            found = new.count(old)
            if found:
                new = new.replace(old, replacement)
                counts[old.decode()] += found
                hits += found
        if not hits:
            continue
        for token in INVARIANT_TOKENS:
            if new.count(token) != before[token]:  # pragma: no cover - guarded by validate()
                raise Refused(
                    f"the rename would have changed {token.decode()!r} in {relative}; "
                    "that token is deliberately kept. Nothing was written."
                )
        touched += 1
        if not dry_run:
            path.write_bytes(new)
    return touched, counts


def rename_paths(root: Path, name: str, dry_run: bool) -> list[str]:
    """Rename `PaperLib.lean` and `PaperLib/` (and anything else so named)."""
    moves: list[str] = []
    if name == PLACEHOLDER_ROOT:
        return moves
    candidates = sorted(
        (p for p in root.rglob(f"*{PLACEHOLDER_ROOT}*")
         if not any(part in SKIP_DIRS for part in p.relative_to(root).parts)
         and not is_excluded(p.relative_to(root).as_posix())),
        key=lambda p: len(p.relative_to(root).parts), reverse=True,
    )
    for path in candidates:
        if not path.exists():
            continue
        target = path.with_name(path.name.replace(PLACEHOLDER_ROOT, name))
        moves.append(f"{path.relative_to(root).as_posix()} -> "
                     f"{target.relative_to(root).as_posix()}")
        if not dry_run:
            if target.exists():
                raise Refused(f"{target.relative_to(root)} already exists; "
                              "move it aside and run this again.")
            path.rename(target)
    return moves


# ── local/project.json ──────────────────────────────────────────────────────


def default_config() -> dict:
    """The schema of local/project.json, used when the file is not there yet.

    `scripts/project_config.py` (`DEFAULTS`) is the schema of record; keep the
    two in step — the loader validates what this writes.
    """
    return {
        "schema": 1,
        "project": {"name": PLACEHOLDER_ROOT, "lean_root": PLACEHOLDER_ROOT,
                    "track": "main", "title": "", "arxiv": [],
                    "github_slug": PLACEHOLDER_SLUG,
                    "comparator_slug": PLACEHOLDER_COMPARATOR},
        "paths": {"cache_root": "~/.cache/paperlib-dev",
                  "full_build_lock": "~/.cache/lean-full-build.lock"},
        "issues": {"progress": None, "owner_inbox": None, "tracker_root": None},
        "session": {"tmux": "paperlib", "turn_max_minutes": 25,
                    "main": {"model": "", "effort": "", "key": "default",
                             "native_delegates": 1},
                    "workers": {"model": "", "hard_model": "", "effort": "",
                                "lanes": 0, "models_allowed": []}},
        "keys": {"default": {"codex_home": "~/.codex", "limit": 2}},
        "paper_mirrors": [],
        "tracks": {},
    }


def load_config(root: Path) -> dict:
    path = root / "local" / "project.json"
    if path.is_file():
        try:
            return json.loads(path.read_text(encoding="utf-8"))
        except ValueError as exc:
            raise Refused(f"local/project.json is not valid JSON ({exc}); fix it first.")
    return default_config()


def track_entry(name: str, track: str) -> dict:
    """One track, with the conventional paths; the mathematics is filled later.

    The fields are exactly those of the `Track` record the completion gate
    reads.  `headline` and `blueprint_chapters` stay empty until the blueprint
    stage knows what the headline theorems and the chapters are; the gate says
    so rather than guessing.
    """
    sub = camel(track)
    lean_root = name if track == "main" else f"{name}/{sub}"
    challenge = "Challenge.lean.expected" if track == "main" else f"Challenge{sub}.lean.expected"
    return {
        "name": track,
        "lean_root": lean_root,
        "headline": [],
        "gap_register": f"docs/paper-gaps/{track}-gap-register.md",
        "axiom_audit": f"{lean_root}/Test/AxiomAudit.lean",
        "blueprint_chapters": [],
        "leanok_exemptions": f"docs/completion/{track}-leanok-exemptions.md",
        "comparator_doc": "docs/comparator.md",
        "expected_challenge": f"scripts/comparator/expected/{challenge}",
        "truthful_docs": ["README.md"],
        "artifact_files": ["README.md", "docs/ARTIFACT.md", "LICENSE"],
        "artifact_script": "scripts/make_artifact.sh",
    }


def build_config(base: dict, args: argparse.Namespace, arxiv_id: str) -> dict:
    config = json.loads(json.dumps(base))  # a copy, key order preserved
    config.setdefault("schema", 1)
    project = config.setdefault("project", {})
    project["name"] = args.lean_root
    project["lean_root"] = args.lean_root
    project["track"] = args.track
    project["title"] = args.title
    project["arxiv"] = [arxiv_id] if arxiv_id else []
    project["github_slug"] = args.github_slug
    project["comparator_slug"] = args.comparator_slug
    paths = config.setdefault("paths", {})
    paths["cache_root"] = args.cache_root
    paths.setdefault("full_build_lock", "~/.cache/lean-full-build.lock")
    config.setdefault("issues", {"progress": None, "owner_inbox": None, "tracker_root": None})
    session = config.setdefault("session", {})
    session["tmux"] = args.tmux
    session.setdefault("turn_max_minutes", 25)
    session.setdefault("main", {"model": "", "effort": "", "key": "default",
                                "native_delegates": 1})
    session.setdefault("workers", {"model": "", "hard_model": "", "effort": "",
                                   "lanes": 0, "models_allowed": []})
    config.setdefault("keys", {"default": {"codex_home": "~/.codex", "limit": 2}})
    #: One entry per source-paper mirror: the KEY, whose directory is
    #: references/<key>-paper.  The tools that used to enumerate mirror names
    #: in a regex read this list instead.
    mirrors = [m for m in config.get("paper_mirrors") or [] if m != args.key]
    config["paper_mirrors"] = mirrors + [args.key]
    tracks = config.setdefault("tracks", {})
    tracks[args.track] = track_entry(args.lean_root, args.track)
    return config


def write_config(root: Path, config: dict) -> None:
    path = root / "local" / "project.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(config, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


# ── blueprint and paper-gap identity ────────────────────────────────────────


def replace_macro(text: str, macro: str, body: str) -> str:
    """Replace ``\\macro{...}`` with brace balancing, across lines."""
    needle = "\\" + macro + "{"
    start = text.find(needle)
    if start < 0:
        return text
    depth = 0
    index = start + len(needle) - 1
    while index < len(text):
        char = text[index]
        if char == "{" and text[index - 1] != "\\":
            depth += 1
        elif char == "}" and text[index - 1] != "\\":
            depth -= 1
            if depth == 0:
                return text[:start] + "\\" + macro + "{" + body + "}" + text[index + 1:]
        index += 1
    return text


def blueprint_identity(root: Path, name: str, slug: str, title: str,
                       arxiv_id: str, dry_run: bool) -> list[str]:
    owner, repo = slug.split("/", 1)
    home = f"https://{owner}.github.io/{repo}"
    if arxiv_id and title:
        heading = f"Blueprint for arXiv:{arxiv_id}\\\\\n\\textit{{{title}}}"
    elif arxiv_id:
        heading = f"Blueprint for arXiv:{arxiv_id}"
    elif title:
        heading = f"Blueprint for \\textit{{{title}}}"
    else:
        heading = f"Blueprint for {name}"
    changed = []
    for relative in ("blueprint/src/web.tex", "blueprint/src/print.tex"):
        path = root / relative
        if not path.is_file():
            continue
        text = original = path.read_text(encoding="utf-8")
        text = replace_macro(text, "home", home)
        text = replace_macro(text, "github", f"https://github.com/{slug}")
        text = replace_macro(text, "dochome", f"{home}/docs")
        text = replace_macro(text, "title", heading)
        text = replace_macro(text, "author", f"The {name} contributors")
        if text != original:
            changed.append(relative)
            if not dry_run:
                path.write_text(text, encoding="utf-8")
    return changed


def site_identity(root: Path, name: str, slug: str, title: str,
                  dry_run: bool) -> list[str]:
    """Point `home_page/_config.yml` at this project's GitHub Pages site.

    The kit ships placeholders (`OWNER`, `REPO`, `PaperLib`); jekyll-github-metadata
    reads `repository` and `url`, and `local/bin/site.sh` passes the same
    `--baseurl` on the command line, so the two must agree.
    """
    path = root / "home_page" / "_config.yml"
    if not path.is_file():
        return []
    owner, repo = slug.split("/", 1)
    values = {
        "title": f'"{title or name}"',
        "baseurl": f'"/{repo}"',
        "url": f'"https://{owner}.github.io"',
        "github_username": owner,
        "repository": slug,
    }
    out, changed = [], False
    for line in path.read_text(encoding="utf-8").splitlines():
        for key, value in values.items():
            if re.match(rf"^{re.escape(key)}\s*:", line):
                replacement = f"{key}: {value}"
                changed = changed or replacement != line
                out.append(replacement)
                break
        else:
            out.append(line)
    if not changed:
        return []
    if not dry_run:
        path.write_text("\n".join(out).rstrip("\n") + "\n", encoding="utf-8")
    return ["home_page/_config.yml"]


def _toml_scalar(line: str, key: str, value: str) -> str | None:
    if re.match(rf"^\s*{re.escape(key)}\s*=", line):
        return f"{key:<11} = {value}"
    return None


def paper_gap_identity(root: Path, name: str, slug: str, key: str, title: str,
                       arxiv_id: str, dry_run: bool) -> bool:
    """Retitle texra-blueprint.toml and reduce its source registry to this paper.

    A source key survives only when a note whose stem starts with it still
    exists under docs/paper-gaps/, so the registry never describes notes that
    are not there.
    """
    path = root / "texra-blueprint.toml"
    if not path.is_file():
        return False
    owner, repo = slug.split("/", 1)
    notes = {p.stem for p in (root / "docs" / "paper-gaps").glob("*.tex")} \
        if (root / "docs" / "paper-gaps").is_dir() else set()
    scalars = {
        "site_base": f'"https://{owner}.github.io/{repo}"',
        "blob_base": f'"https://github.com/{slug}/blob/main/docs/paper-gaps"',
        "bib_author": f'"The {{{name}}} contributors"',
        "institution": f'"{name}"',
        "title": f'"{name} paper-gap notes"',
        "scan_roots": f'["{name}", "blueprint/src", "docs"]',
    }
    source = f'arXiv:{arxiv_id}' if arxiv_id else (title or "the source paper")
    if arxiv_id and title:
        source = f"arXiv:{arxiv_id} ({title})"

    out: list[str] = []
    section = ""
    pending_comments: list[str] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        header = re.match(r"^\s*\[([^\]]+)\]\s*$", line)
        if header:
            section = header.group(1)
            if section in ("paper_gaps.sources", "paper_gaps.aliases"):
                pending_comments = []  # the old commentary described the old paper
            out.extend(pending_comments)
            pending_comments = []
            out.append(line)
            if section == "paper_gaps.sources":
                out.append("# One line per source key: a note named <key>-<topic>.tex audits")
                out.append("# the source recorded here. Written by scripts/bootstrap_project.py")
                out.append("# and extended by hand when a second source enters the project.")
                out.append(f'{key} = "{source}"')
            continue
        if line.lstrip().startswith("#"):
            pending_comments.append(line)
            continue
        if section in ("paper_gaps.sources", "paper_gaps.aliases"):
            entry = re.match(r"^\s*([A-Za-z0-9_.-]+)\s*=", line)
            if entry:
                stem_key = entry.group(1)
                if stem_key != key and any(n == stem_key or n.startswith(stem_key + "-")
                                           or n.startswith(stem_key + "_") for n in notes):
                    out.extend(pending_comments)
                    out.append(line)
                pending_comments = []
                continue
        if section == "paper_gaps" or not section:
            for scalar_key, value in scalars.items():
                replaced = _toml_scalar(line, scalar_key, value)
                if replaced is not None:
                    out.extend(pending_comments)
                    pending_comments = []
                    out.append(replaced)
                    break
            else:
                out.extend(pending_comments)
                pending_comments = []
                out.append(line)
            continue
        out.extend(pending_comments)
        pending_comments = []
        out.append(line)
    out.extend(pending_comments)
    text = "\n".join(out).rstrip("\n") + "\n"
    if not dry_run:
        path.write_text(text, encoding="utf-8")
    return True


def write_readme(root: Path, name: str, track: str, title: str, key: str,
                 arxiv_id: str, dry_run: bool) -> list[str]:
    """Project README; the kit's own README becomes docs/KIT.md."""
    steps: list[str] = []
    readme = root / "README.md"
    kit_doc = root / "docs" / "KIT.md"
    if readme.is_file() and not kit_doc.exists():
        steps.append("README.md -> docs/KIT.md")
        if not dry_run:
            kit_doc.parent.mkdir(parents=True, exist_ok=True)
            readme.rename(kit_doc)
    toolchain = "Lean 4"
    toolchain_file = root / "lean-toolchain"
    if toolchain_file.is_file():
        toolchain = toolchain_file.read_text(encoding="utf-8").strip() or toolchain
    if arxiv_id:
        source_row = (f"[arXiv:{arxiv_id}](https://arxiv.org/abs/{arxiv_id}) — mirrored under "
                      f"`references/{key}-paper/`")
        paper = f"{title or 'the paper'} ([arXiv:{arxiv_id}](https://arxiv.org/abs/{arxiv_id}))"
    else:
        source_row = f"to be mirrored under `references/{key}-paper/`"
        paper = title or "one research paper"
    text = README_TEMPLATE.format(name=name, paper=paper, source_row=source_row,
                                  toolchain=toolchain, track=track)
    steps.append("README.md (new)")
    if not dry_run:
        readme.write_text(text, encoding="utf-8")
    return steps


# ── the paper mirror ────────────────────────────────────────────────────────


def fetch_and_split(root: Path, arxiv: str, key: str, title: str) -> None:
    """Mirror the paper and split it; raises Refused with the retry command."""
    sys.path.insert(0, str(root / "scripts"))
    import fetch_arxiv_source as fetcher  # noqa: PLC0415

    dest = root / "references" / f"{key}-paper"
    rc = fetcher.main([arxiv, "--dest", str(dest), "--title", title, "--force"])
    if rc != 0:
        raise Refused(
            "the paper mirror could not be fetched. Run it again when the machine "
            f'is online:\n  python3 scripts/fetch_arxiv_source.py {arxiv} '
            f'--dest references/{key}-paper --title "{title}"'
        )
    source_dir = dest / fetcher.SOURCE_SUBDIR
    text_files, _ = fetcher.select_files(source_dir)
    main_file = fetcher.find_main(text_files, source_dir)
    if main_file is None:
        raise Refused(
            f"the mirror in references/{key}-paper has no obvious main .tex file; "
            "pick it by hand and run scripts/split_reference_paper.py on it."
        )
    arxiv_id, _ = fetcher.split_version(fetcher.parse_arxiv_id(arxiv))
    rc, out, err = run([sys.executable, "scripts/split_reference_paper.py",
                        str(main_file.relative_to(root)), f"references/{key}-paper",
                        "--arxiv", arxiv_id, "--title", title or f"arXiv:{arxiv_id}",
                        "--force"], cwd=root, timeout=600)
    sys.stdout.write(out)
    if rc != 0:
        raise Refused("splitting the paper failed:\n" + (err.strip() or f"exit {rc}"))


# ── fresh git history ───────────────────────────────────────────────────────


def record_bootstrap(root: Path, name: str, slug: str) -> None:
    """Explain the override in the incident log and open the bootstrap stage."""
    bullet = (
        f"Project bootstrapped from the formalization kit: scripts/bootstrap_project.py "
        f"renamed the Lean root to {name}, pointed the repository at {slug}, wrote "
        "local/project.json and committed the whole tree as the first commit of a fresh "
        "history with MIPSTARRE_INFRA_OVERRIDE=1. Diagnosis: the workflow-layer line "
        "budget exists to stop unbounded scaffolding inside a running project; a "
        "scripted, mechanical, owner-side instantiation is the one thing it is not "
        "aimed at, and it cannot be split into budget-sized commits. Fix: the override "
        "is set by this script only, for this one commit. Lesson: if you find yourself "
        "reaching for the override a second time, that is scaffolding, and it needs a "
        "recorded decision instead."
    )
    note = f"instantiated from the kit as {name} ({slug})"
    telemetry = root / "local" / "bin" / "telemetry.py"
    ok = False
    if telemetry.is_file():
        rc_a, _, _ = run([sys.executable, str(telemetry), "--repo-root", str(root),
                          "event", "--text", bullet], cwd=root, timeout=120)
        rc_b, _, _ = run([sys.executable, str(telemetry), "--repo-root", str(root),
                          "stage", "--stage", "0-bootstrap", "--event", "start",
                          "--note", note], cwd=root, timeout=120)
        ok = rc_a == 0 and rc_b == 0
    if ok:
        return
    # Fallback: the records matter more than the writer.
    events = root / "results" / "telemetry" / "events.md"
    events.parent.mkdir(parents=True, exist_ok=True)
    today = datetime.date.today().isoformat()
    text = events.read_text(encoding="utf-8") if events.is_file() else "# Incident log\n"
    if f"## {today}" not in text:
        text = text.rstrip("\n") + f"\n\n## {today}\n"
    events.write_text(text.rstrip("\n") + f"\n\n- {bullet}\n", encoding="utf-8")
    stages = root / "results" / "telemetry" / "stages.jsonl"
    with stages.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps({"ts": utc_now(), "stage": "0-bootstrap",
                                 "event": "start", "note": note}) + "\n")


def fresh_git_history(root: Path, name: str, slug: str) -> None:
    git = shutil.which("git")
    if not git:
        raise Refused("git is not on PATH; install git, then run this again.")
    identity_missing = [
        flag for flag in ("user.name", "user.email")
        if not run([git, "config", "--get", flag], cwd=root, timeout=30)[1].strip()
    ]
    if identity_missing:
        raise Refused(
            "git has no commit identity, so the first commit would fail. Run:\n"
            '  git config --global user.name "Your Name"\n'
            '  git config --global user.email "you@example.com"'
        )
    shutil.rmtree(root / ".git", ignore_errors=True)
    rc, _, err = run([git, "init", "-b", "main"], cwd=root, timeout=120)
    if rc != 0:
        rc, _, err = run([git, "init"], cwd=root, timeout=120)
        if rc == 0:
            run([git, "symbolic-ref", "HEAD", "refs/heads/main"], cwd=root, timeout=60)
    if rc != 0:
        raise Refused(f"git init failed: {err.strip()}")
    hooks = root / "scripts" / "install_git_hooks.sh"
    if hooks.is_file():
        rc, out, err = run(["/bin/sh", str(hooks), "--install"], cwd=root, timeout=120)
        if rc != 0:
            raise Refused(f"installing the git hooks failed: {(err or out).strip()}")
    record_bootstrap(root, name, slug)
    rc, _, err = run([git, "add", "-A"], cwd=root, timeout=600)
    if rc != 0:
        raise Refused(f"git add failed: {err.strip()}")
    message = (
        f"chore: instantiate {name} from the formalization kit\n\n"
        f"Lean root {name}, repository {slug}. Fresh history: this commit is the\n"
        "whole tree, written by scripts/bootstrap_project.py. The workflow-layer\n"
        "line budget is overridden once, mechanically, and the reason is recorded\n"
        "in results/telemetry/events.md.\n"
    )
    print("running the repository hooks on the first commit "
          "(they run the script test suite; this takes a few minutes) …")
    rc, out, err = run([git, "commit", "-m", message], cwd=root,
                       env={"MIPSTARRE_INFRA_OVERRIDE": "1"}, timeout=3600)
    if rc != 0:
        raise Refused(
            "the first commit did not pass the repository hooks. Nothing is lost: the "
            "tree is instantiated and everything is staged.\n"
            "Two things fail on a FIRST commit for structural reasons, and the hook "
            "output below says which one you hit:\n"
            "  * the whitespace gate treats every line as new, so one stray trailing "
            "space anywhere in the tree stops it (`git diff --cached --check "
            "-- \':(exclude)references/\'` lists them);\n"
            "  * parts of the script test suite need a repository that already has a "
            "commit, and this one has none yet.\n"
            "Fix what the output names and run:\n"
            "  MIPSTARRE_INFRA_OVERRIDE=1 git commit -m 'chore: instantiate the project'\n"
            "If the failure is only the second kind, this one commit may skip the hooks "
            "-- it is a mechanical rename of an already-reviewed tree, and every commit "
            "after it runs the full gate:\n"
            "  MIPSTARRE_INFRA_OVERRIDE=1 MIPSTARRE_SKIP_HOOKS=1 git commit -m "
            "'chore: instantiate the project'\n\n"
            + (out or "") + (err or "")
        )


# ── the plan ────────────────────────────────────────────────────────────────


def describe(args: argparse.Namespace, arxiv_id: str, touched: int,
             counts: Counter, moves: list[str]) -> str:
    lines = [
        "plan:",
        f"  Lean root        {PLACEHOLDER_ROOT} -> {args.lean_root}",
        f"  repository       {PLACEHOLDER_SLUG} -> {args.github_slug}",
        f"  comparator       {PLACEHOLDER_COMPARATOR} -> {args.comparator_slug}",
        f"  track            {args.track}",
        f"  paper mirror     references/{args.key}-paper"
        + (f" (arXiv:{arxiv_id})" if arxiv_id else " (no --arxiv given)"),
        f"  cache root       {args.cache_root}",
        f"  tmux session     {args.tmux}",
        f"  files rewritten  {touched}",
    ]
    for token in (PLACEHOLDER_ROOT, PLACEHOLDER_SLUG, PLACEHOLDER_COMPARATOR):
        lines.append(f"  occurrences      {counts.get(token, 0):>5}  {token}")
    for move in moves:
        lines.append(f"  rename           {move}")
    lines.append("  git              " + ("kept (--keep-git)" if args.keep_git
                                          else "fresh history, one first commit"))
    return "\n".join(lines)


def bootstrap(args: argparse.Namespace) -> int:
    root: Path = args.root.resolve()
    if not (root / "local").is_dir() or not (root / "scripts").is_dir():
        raise Refused(f"{root} does not look like the kit checkout "
                      "(no local/ and scripts/ directories). Pass --root.")
    validate(args)
    config = load_config(root)
    done = already_bootstrapped(config)
    if done and not args.force:
        raise Refused(
            f"this checkout is already the project '{done}' "
            "(local/project.json). Bootstrapping twice would rename a name that is "
            "no longer there. Use --force only if you know the first run did not finish."
        )

    arxiv_id = ""
    if args.arxiv:
        sys.path.insert(0, str(root / "scripts"))
        import fetch_arxiv_source as fetcher  # noqa: PLC0415
        try:
            arxiv_id, _ = fetcher.split_version(fetcher.parse_arxiv_id(args.arxiv))
        except fetcher.FetchError as exc:
            raise Refused(str(exc))

    pairs = replacement_pairs(args.lean_root, args.github_slug, args.comparator_slug)
    touched, counts = rewrite_contents(root, pairs, dry_run=args.dry_run)
    moves = rename_paths(root, args.lean_root, dry_run=args.dry_run)
    print(describe(args, arxiv_id, touched, counts, moves))
    if args.dry_run:
        print("dry run: nothing was written.")
        return 0

    write_config(root, build_config(config, args, arxiv_id))
    blueprint_identity(root, args.lean_root, args.github_slug, args.title,
                       arxiv_id, dry_run=False)
    paper_gap_identity(root, args.lean_root, args.github_slug, args.key, args.title,
                       arxiv_id, dry_run=False)
    site_identity(root, args.lean_root, args.github_slug, args.title, dry_run=False)
    write_readme(root, args.lean_root, args.track, args.title, args.key,
                 arxiv_id, dry_run=False)

    mirror_failed = ""
    if args.arxiv:
        try:
            fetch_and_split(root, args.arxiv, args.key, args.title)
        except Refused as exc:
            mirror_failed = str(exc)

    if not args.keep_git:
        fresh_git_history(root, args.lean_root, args.github_slug)

    print("")
    print(f"{args.lean_root} is instantiated.")
    if mirror_failed:
        print("")
        print("the paper mirror is MISSING:")
        print(mirror_failed)
    print("")
    print("Nothing was created on GitHub and nothing was pushed. When the owner has")
    print("said yes to creating the repository, these two commands do it:")
    print(f"  gh repo create {args.github_slug} --private --source . --remote github")
    print("  git push -u github main")
    return 5 if mirror_failed else 0


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--lean-root", required=True, metavar="Name",
                        help="the Lean library root, one capitalized identifier")
    parser.add_argument("--github-slug", required=True, metavar="owner/repo",
                        help="the GitHub repository this project will live in")
    parser.add_argument("--arxiv", metavar="URL",
                        help="arXiv id or URL; the paper is mirrored and split")
    parser.add_argument("--key", metavar="short",
                        help="paper-mirror key (references/<key>-paper); "
                             "default: the Lean root in lower case")
    parser.add_argument("--title", default="", help="the paper's title")
    parser.add_argument("--track", default="main",
                        help="the track name registered in local/project.json (default: main)")
    parser.add_argument("--comparator-slug", metavar="owner/repo",
                        help="the comparator challenge repository "
                             "(default: <repo>-comparator beside it)")
    parser.add_argument("--cache-root", metavar="PATH",
                        help="runtime cache and state root (default: ~/.cache/<name>-dev)")
    parser.add_argument("--tmux", metavar="NAME",
                        help="tmux session name (default: the Lean root in lower case)")
    parser.add_argument("--keep-git", action="store_true",
                        help="keep the current git history and make no commit")
    parser.add_argument("--dry-run", action="store_true",
                        help="print the plan and the counts, change nothing")
    parser.add_argument("--force", action="store_true",
                        help="run again on a checkout that is already instantiated")
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1],
                        help="the kit checkout (default: the one this script lives in)")
    args = parser.parse_args(argv)
    lower = args.lean_root.lower()
    args.key = args.key or lower
    args.cache_root = args.cache_root or f"~/.cache/{lower}-dev"
    args.tmux = args.tmux or lower
    if not args.comparator_slug and SLUG_RE.match(args.github_slug):
        args.comparator_slug = f"{args.github_slug}-comparator"
    return args


def main(argv: list[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    try:
        return bootstrap(args)
    except Refused as exc:
        sys.stderr.write(f"bootstrap_project.py: {exc}\n")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
