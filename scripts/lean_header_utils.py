#!/usr/bin/env python3
"""Small scanner primitives for Lean declaration headers."""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import project_config  # noqa: E402


OPEN_TO_CLOSE = {"(": ")", "{": "}", "[": "]", "⦃": "⦄"}
CLOSE_TO_OPEN = {value: key for key, value in OPEN_TO_CLOSE.items()}


def line_number(text: str, offset: int) -> int:
    """Return the one-based line number of ``offset`` in ``text``."""

    return text.count("\n", 0, offset) + 1


def project_lean_files(root: Path) -> list[Path]:
    """Return the Lean files of this project's own tree.

    The subtrees come from `local/project.json` (`project_config.lean_scan_targets`),
    so an audit that used to be pinned to one directory name now follows whatever
    library root and track the project registered.  A target that is not there
    contributes nothing, which is what a repository whose Lean tree is not
    written yet needs.
    """

    files: list[Path] = []
    for target in project_config.lean_scan_targets(root):
        base = root / target
        if not base.is_dir():
            continue
        files.extend(path for path in base.rglob("*.lean") if path.is_file())
    return sorted(set(files))


def advance_depth(ch: str, stack: list[str]) -> None:
    """Update a delimiter stack with one Lean header character."""

    if ch in OPEN_TO_CLOSE:
        stack.append(ch)
    elif ch in CLOSE_TO_OPEN and stack and stack[-1] == CLOSE_TO_OPEN[ch]:
        stack.pop()


def identifier_char(ch: str) -> bool:
    """Return whether ``ch`` can continue a Lean identifier-like token."""

    return ch.isalnum() or ch in "_?'"


def starts_keyword(text: str, pos: int, keyword: str) -> bool:
    """Return whether ``keyword`` starts at ``pos`` as a standalone token."""

    if not text.startswith(keyword, pos):
        return False
    before_ok = pos == 0 or not identifier_char(text[pos - 1])
    after = pos + len(keyword)
    after_ok = after >= len(text) or not identifier_char(text[after])
    return before_ok and after_ok
