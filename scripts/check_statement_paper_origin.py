#!/usr/bin/env python3
"""Check that every statement-like declaration under the project's Lean roots
carries a paper-origin citation in its def-site docstring.

Scope: the roots come from ``local/project.json`` — the Lean root of every
registered track, or the library root when no track is registered yet (see
``scan_targets``).  A root that does not exist is reported and skipped, so a
freshly bootstrapped repository can commit.  For every ``structure``, ``def``, or ``abbrev`` whose
identifier ends in ``Statement`` (and similar proof-obligation suffixes
``Witness``, ``Hypotheses``, ``Conclusion``, ``Output``, ``Input``,
``Assumptions``, ``Hypothesis``, ``Assumption``, ``Bridge``, ``Producer``,
``Package``, ``Bundle``, ``Conditional``, ``Residual``, ``Repair``,
``Obligation``, ``Obligations``, ``Wrapper``, ``Slackness``, ``Dominance``, and
``CompletionTransport``), we look at the
*immediately preceding docstring or comment block* (after skipping blank lines)
for one of three citation forms:

1. A paper line reference of the form ``references/<mirror>-paper/.../*.tex``
   optionally followed by a colon and line range.  The accepted mirror names
   are ``paper_mirrors`` of ``local/project.json``; with none configured any
   ``references/<name>-paper/`` directory counts.
2. A LaTeX cross-reference ``\\label{<kind>:...}`` where ``<kind>`` is one of
   ``lem``, ``thm``, ``prop``, ``cor``, ``def``, ``eq``, ``sec``.
3. A paper-gap reference ``docs/paper-gaps/.../*.tex``.

Restricting the search to the immediately preceding comment block (rather than
a fixed line window over arbitrary code/comments) prevents a citation in an
earlier nearby declaration's docstring from spuriously satisfying the
linter for a later declaration.

The repository workflow runs this as a blocking guard.  During a future
backfill or local exploratory audit, pass ``--warn-only`` to print violations
without failing the command.

Suggested CI wiring::

    name: Statement paper-origin guard
    on:
      pull_request:
        types: [opened, synchronize, reopened]
    permissions:
      contents: read
    jobs:
      guard:
        runs-on: ubuntu-latest
        steps:
          - uses: actions/checkout@v6
          - uses: actions/setup-python@v6
            with:
              python-version: '3.12'
          - run: python3 scripts/check_statement_paper_origin.py --root .
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path
from typing import Sequence

sys.path.insert(0, str(Path(__file__).resolve().parent))

import project_config  # noqa: E402
from check_oversized_lean_files import _is_excluded  # noqa: E402

# Suffixes treated as "statement-like" and thus subject to the paper-origin rule.
SUFFIXES: tuple[str, ...] = (
    "Statement",
    "Witness",
    "Hypotheses",
    "Hypothesis",
    "Conclusion",
    "Output",
    "Input",
    "Assumptions",
    "Assumption",
    "Bridge",
    "Producer",
    "Package",
    "Bundle",
    "Conditional",
    "Residual",
    "Repair",
    "Obligation",
    "Obligations",
    "Wrapper",
    "Slackness",
    "Dominance",
    "CompletionTransport",
)

DECL_KEYWORDS: tuple[str, ...] = ("structure", "def", "abbrev")

# Lean 4 declaration modifiers that may appear before the keyword.  Allow
# them in any order and any combination so that, e.g., `private noncomputable
# def FooStatement` is still detected.
DECL_MODIFIERS: tuple[str, ...] = (
    "private",
    "protected",
    "noncomputable",
    "partial",
    "unsafe",
)

DECL_RE = re.compile(
    r"^\s*(?:(?:" + "|".join(DECL_MODIFIERS) + r")\s+)*"
    r"(?:" + "|".join(DECL_KEYWORDS) + r")\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_']*)"
)

def paper_path_re(mirrors: Sequence[str] = ()) -> re.Pattern[str]:
    """Regex for ``references/<mirror>-paper/<file>.tex`` citations.

    With no mirror configured any ``<name>-paper`` directory counts: before the
    paper is split into its mirror the rule would otherwise reject every
    citation.  Once ``paper_mirrors`` names the project's mirrors, only those
    are accepted, which is what keeps a citation from pointing at a paper this
    project does not carry.
    """

    alternatives = "|".join(re.escape(m) for m in mirrors) if mirrors else r"[A-Za-z0-9._-]+"
    return re.compile(rf"references/(?:{alternatives})-paper/[^\s`]+\.tex")


PAPER_PATH_RE = paper_path_re()
PAPER_GAP_RE = re.compile(r"docs/paper-gaps/[^\s`]+\.tex")
LATEX_LABEL_RE = re.compile(r"\\label\{(?:lem|thm|prop|cor|def|eq|sec):[^}]+\}")


def _has_origin(window: str, paper_re: re.Pattern[str] | None = None) -> bool:
    """Return True if *window* contains any of the three accepted citation forms."""
    paper_re = paper_re or PAPER_PATH_RE
    return bool(
        paper_re.search(window)
        or PAPER_GAP_RE.search(window)
        or LATEX_LABEL_RE.search(window)
    )


def _matches_suffix(name: str) -> bool:
    return any(name.endswith(suffix) for suffix in SUFFIXES)


def _preceding_docstring(lines: list[str], decl_idx: int) -> str:
    """Return the text of the docstring/comment block immediately preceding
    ``decl_idx``, or the empty string if no such block exists.

    The walk skips blank lines, then collects exactly one preceding comment
    block:

    - a ``/- ... -/`` or ``/-- ... -/`` block that may span multiple lines, or
    - a contiguous run of ``--`` single-line comments.

    Anything beyond that one block (further comment blocks, or arbitrary code)
    is *not* included.  This prevents an earlier declaration's docstring from
    spuriously satisfying the linter for a later declaration that happens to
    sit within ``CONTEXT_LINES`` lines.
    """
    i = decl_idx - 1
    # Skip blank lines.
    while i >= 0 and not lines[i].strip():
        i -= 1
    if i < 0:
        return ""

    stripped = lines[i].strip()
    # Single-line comments first, since a `--` line with `... -/` text would
    # otherwise be misclassified as a closing `/-...-/` block.
    if stripped.startswith("--"):
        end = i
        while i >= 0 and lines[i].strip().startswith("--"):
            i -= 1
        start = i + 1
        return "\n".join(lines[start:end + 1])

    if stripped.endswith("-/"):
        end = i
        # Walk back until the first non-whitespace characters are a block-comment
        # opener (`/-`, `/--`, or `/-!`).  Literal mentions of `/-` inside the
        # body of the docstring should not truncate the collected block.
        while i >= 0 and not lines[i].lstrip().startswith("/-"):
            i -= 1
        if i < 0:
            return ""
        return "\n".join(lines[i:end + 1])

    return ""


def _scan_file(path: Path, paper_re: re.Pattern[str] | None = None) -> list[tuple[int, str]]:
    """Return a list of (line, name) for declarations in *path* missing a citation."""
    missing: list[tuple[int, str]] = []
    text = path.read_text(encoding="utf-8", errors="replace")
    lines = text.splitlines()

    for idx, line in enumerate(lines):
        m = DECL_RE.match(line)
        if not m:
            continue
        name = m.group("name")
        if not _matches_suffix(name):
            continue

        window = _preceding_docstring(lines, idx)
        if not _has_origin(window, paper_re):
            missing.append((idx + 1, name))

    return missing


class TargetMissingError(RuntimeError):
    """Raised when a configured scan target does not exist."""


def scan_targets(root: Path, cfg: dict | None = None) -> list[str]:
    """The subtrees that carry statements, relative to *root*.

    The Lean root of every registered track, or — before any track exists —
    ``<lean_root>/<track>`` when that directory is there and ``<lean_root>``
    otherwise.  "Which subtree carries statements" is a project decision, so it
    is read, never guessed.
    """

    return project_config.lean_scan_targets(root, cfg)


def _scan_root(
    root: Path,
    targets: Sequence[str] | None = None,
    paper_re: re.Pattern[str] | None = None,
) -> dict[str, list[tuple[int, str]]]:
    """Scan each target under *root* and return ``rel-path -> missing``.

    Raises :class:`TargetMissingError` when no target exists at all; `main`
    reports that and exits 0, because a repository whose Lean tree is not
    written yet has nothing to check and must still be able to commit.
    """
    targets = list(targets) if targets is not None else scan_targets(root)
    present = [root / rel for rel in targets if (root / rel).is_dir()]
    if not present:
        raise TargetMissingError(
            "no scan target exists: "
            + (", ".join(targets) if targets else "no Lean root is configured")
            + f" (under {root})"
        )
    results: dict[str, list[tuple[int, str]]] = {}
    for target in present:
        for path in sorted(target.rglob("*.lean")):
            if _is_excluded(path, root):
                continue
            missing = _scan_file(path, paper_re)
            if missing:
                rel = path.relative_to(root).as_posix()
                results[rel] = missing
    return results


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Check that statement-like structures and definitions under the "
            "project's Lean roots carry a paper-origin citation in their "
            "def-site docstring."
        )
    )
    parser.add_argument(
        "--root",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="Repository root (default: parent of scripts/).",
    )
    parser.add_argument(
        "--warn-only",
        action="store_true",
        help="Report violations but exit 0.  Use during a backfill.",
    )
    args = parser.parse_args(argv)

    try:
        cfg = project_config.load(args.root)
    except project_config.ConfigError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    targets = scan_targets(args.root, cfg)
    paper_re = paper_path_re(project_config.get(cfg, "paper_mirrors", []))

    try:
        results = _scan_root(args.root, targets, paper_re)
    except TargetMissingError as exc:
        # Nothing to scan is not a violation: a repository whose Lean tree is
        # not written yet must still be able to commit.  A misspelled --root
        # lands here too, so the note names what was looked for.
        print(f"note: {exc}; nothing to check", file=sys.stderr)
        return 0

    if not results:
        print("OK: every statement-like declaration under "
              + ", ".join(targets)
              + " carries a paper-origin citation.")
        return 0

    total = sum(len(items) for items in results.values())
    label = "warning" if args.warn_only else "error"
    print(
        f"{label}: {total} statement-like declaration(s) missing a paper-origin "
        "citation in the immediately preceding docstring/comment block:",
        file=sys.stderr,
    )
    for rel, items in results.items():
        for line, name in items:
            print(f"  {rel}:{line}: {name}", file=sys.stderr)
    print(
        "\nAccepted citation forms (any one of these in the immediately "
        "preceding docstring/comment block):",
        file=sys.stderr,
    )
    print("  - references/<mirror>-paper/<file>.tex  (optionally with :line-range)",
          file=sys.stderr)
    print(r"  - \label{lem:...} / \label{thm:...} / \label{prop:...} /"
          r" \label{cor:...} / \label{def:...} / \label{eq:...} /"
          r" \label{sec:...}", file=sys.stderr)
    print("  - docs/paper-gaps/<file>.tex", file=sys.stderr)
    return 0 if args.warn_only else 1


if __name__ == "__main__":
    raise SystemExit(main())
