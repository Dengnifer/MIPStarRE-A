#!/usr/bin/env python3
"""Total Lean **code** lines of the QPBT project (owner request, issue #168).

The owner asked for the size of the QPBT development to ride along with every
completion-estimate update on the tracker issue.  "Code lines" here means
exactly what the merge-title Lean delta means: the rule of
``local/bin/pr_merge.py`` ``lean_code_line_mask`` (issue #574), where blank
lines and lines lying wholly inside a line, block, doc or module-doc comment do
not count.  The rule is *imported*, never copied, so the two figures can never
drift apart.

Scope: every ``*.lean`` file under ``MIPStarRE/QPBT`` plus ``MIPStarRE/QPBT.lean``
at the requested revision.

Modes (all of them print one line on stdout):

``--rev REV``
    Count the tree at that git revision (default ``github/main``) and print
    ``files code_lines all_lines``.
``--paths FILE...``
    Count the given files on disk instead of a git revision, same output.
    Offline: used by ``scripts/tests/test_estimate_lean_loc.py``.
``--format-clause FILES CODE_LINES``
    Print the one-clause wording that ``estimate.sh`` appends to the comment it
    posts on the tracker issue, e.g.
    ``QPBT Lean code: 75,906 lines in 311 files``.

The figure is cosmetic by contract, like the merge-title delta: on **any**
failure this prints nothing on stdout and exits non-zero, and the caller is
expected to carry on without it.
"""

from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[3]
QPBT_PATHSPECS = ["MIPStarRE/QPBT", "MIPStarRE/QPBT.lean"]


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
    proc = subprocess.run(
        ["git", "-C", str(REPO_ROOT), *args],
        capture_output=True,
        text=True,
        check=True,
    )
    return proc.stdout


def count_revision(rev: str) -> tuple[int, int, int]:
    """Count the QPBT tree at *rev* without touching the working tree."""
    listing = _git(["ls-tree", "-r", "--name-only", rev, "--", *QPBT_PATHSPECS])
    names = [n for n in listing.splitlines() if n.endswith(".lean")]
    return count_texts(_git(["show", f"{rev}:{name}"]) for name in names)


def format_clause(files: int, code_lines: int) -> str:
    """The short clause appended to the tracker-issue comment.

    #168 updates are one-liners by the owner's rule, so this is a clause and
    never a line of its own.
    """
    noun = "file" if files == 1 else "files"
    return f"QPBT Lean code: {code_lines:,} lines in {files:,} {noun}"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--rev", help="git revision to count (default github/main)")
    group.add_argument("--paths", nargs="+", help="count these Lean files instead")
    group.add_argument(
        "--format-clause",
        nargs=2,
        metavar=("FILES", "CODE_LINES"),
        help="print the tracker-issue clause for an already-measured figure",
    )
    args = parser.parse_args(argv)

    try:
        if args.format_clause:
            files, code_lines = (int(v) for v in args.format_clause)
            print(format_clause(files, code_lines))
            return 0
        if args.paths:
            files, code, total = count_paths(args.paths)
        else:
            files, code, total = count_revision(args.rev or "github/main")
        if not files:
            raise RuntimeError("no Lean files found")
        print(f"{files} {code} {total}")
        return 0
    except Exception as exc:  # cosmetic by contract: never break the caller
        print(f"lean-loc: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
