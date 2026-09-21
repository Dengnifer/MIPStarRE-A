#!/usr/bin/env python3
"""Total Lean **code** lines of this project, for the completion-estimate comment.

"Code lines" means exactly what the merge-title Lean delta means: the rule of
``local/bin/pr_merge.py`` ``lean_code_line_mask``, where blank lines and lines lying
wholly inside a line, block, doc or module-doc comment do not count.  The rule is
*imported*, never copied, so the two figures can never drift apart.

Scope: every ``*.lean`` file under the project's Lean root (``project.lean_root`` in
``local/project.json``, or ``--lean-root``), plus ``<root>.lean`` itself.

Modes (each prints one line on stdout):

``--rev REV``
    Count the tree at that git revision (default ``github/main``); prints
    ``files code_lines all_lines``.
``--paths FILE...``
    Count the given files on disk instead of a git revision, same output.  Offline.
``--format-clause FILES CODE_LINES [--name NAME]``
    Print the one clause ``estimate.sh`` appends to the comment it posts, e.g.
    ``PaperLib Lean code: 75,906 lines in 311 files``.

The figure is cosmetic by contract, like the merge-title delta: on **any** failure this
prints nothing on stdout and exits non-zero, and the caller carries on without it.

Provenance: the origin's owner-tools/lean-loc.py, which hard-coded the library path and
the project's name in the clause.
"""

from __future__ import annotations

import argparse
import os
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[3]


def _project(field: str, default: str) -> str:
    """One ``project.*`` field: environment override, then local/project.json."""
    env = {"lean_root": "KIT_LEAN_ROOT", "name": "KIT_NAME"}.get(field)
    if env and os.environ.get(env):
        return os.environ[env]
    try:
        sys.path.insert(0, str(REPO_ROOT / "scripts"))
        import project_config  # noqa: PLC0415 - optional and deliberately late

        value = (project_config.load(REPO_ROOT).get("project") or {}).get(field)
        if value:
            return str(value)
    except Exception:
        pass
    return default


def pathspecs(lean_root: str) -> list[str]:
    return [lean_root, f"{lean_root}.lean"]


def _load_mask():
    """Return ``pr_merge.lean_code_line_mask`` (imported, never re-implemented)."""
    local_bin = str(REPO_ROOT / "local" / "bin")
    if local_bin not in sys.path:
        sys.path.insert(0, local_bin)
    import pr_merge  # noqa: PLC0415 — deliberately late, keeps the CLI cheap

    return pr_merge.lean_code_line_mask


def count_texts(texts) -> tuple[int, int, int]:
    """``(files, code_lines, all_lines)`` over the given Lean sources."""
    mask = _load_mask()
    files = code = total = 0
    for text in texts:
        bits = mask(text)
        files += 1
        code += sum(bits)
        total += len(bits)
    return files, code, total


def count_paths(paths) -> tuple[int, int, int]:
    """Count Lean files on disk (offline; used by the unit test)."""
    return count_texts(Path(p).read_text(encoding="utf-8") for p in paths)


def _git(args: list[str]) -> str:
    proc = subprocess.run(["git", "-C", str(REPO_ROOT), *args],
                          capture_output=True, text=True, check=True)
    return proc.stdout


def count_revision(rev: str, lean_root: str) -> tuple[int, int, int]:
    """Count the library tree at *rev* without touching the working tree."""
    listing = _git(["ls-tree", "-r", "--name-only", rev, "--", *pathspecs(lean_root)])
    names = [n for n in listing.splitlines() if n.endswith(".lean")]
    return count_texts(_git(["show", f"{rev}:{name}"]) for name in names)


def format_clause(files: int, code_lines: int, name: str) -> str:
    """The short clause appended to the tracker-issue comment.

    Tracker updates are one-liners, so this is a clause and never a line of its own.
    """
    noun = "file" if files == 1 else "files"
    return f"{name} Lean code: {code_lines:,} lines in {files:,} {noun}"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--rev", help="git revision to count (default github/main)")
    group.add_argument("--paths", nargs="+", help="count these Lean files instead")
    group.add_argument("--format-clause", nargs=2, metavar=("FILES", "CODE_LINES"),
                       help="print the tracker-issue clause for an already-measured figure")
    parser.add_argument("--name", help="project name for the clause (default: project.name)")
    parser.add_argument("--lean-root", help="library directory (default: project.lean_root)")
    args = parser.parse_args(argv)

    try:
        if args.format_clause:
            files, code_lines = (int(v) for v in args.format_clause)
            print(format_clause(files, code_lines, args.name or _project("name", "PaperLib")))
            return 0
        if args.paths:
            files, code, total = count_paths(args.paths)
        else:
            root = args.lean_root or _project("lean_root", "PaperLib")
            files, code, total = count_revision(args.rev or "github/main", root)
        if not files:
            raise RuntimeError("no Lean files found")
        print(f"{files} {code} {total}")
        return 0
    except Exception as exc:  # cosmetic by contract: never break the caller
        print(f"lean-loc: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
