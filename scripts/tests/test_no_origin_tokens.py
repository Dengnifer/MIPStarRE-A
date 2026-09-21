#!/usr/bin/env python3
"""The kit carries no trace of the project it was extracted from.

The kit was cut out of one finished formalization.  Anything that still named
that project — its GitHub account and repositories, its Lean library token, its
papers, the machine it ran on, the names of its API keys, the model ids it used —
would be a lie in a repository a stranger clones, and in the worst case would
point a new project's tools at somebody else's repository.

This guard scans every text file the repository ships and fails on any of those
names.  Three things are deliberately NOT scanned:

* ``docs/origin/`` and ``local/kit/`` — the two places that describe the origin on
  purpose: the origin's protocol ledger (history is evidence, not law) and the
  one-time script that produced this tree.  ``scripts/bootstrap_project.py``
  excludes exactly these two prefixes from its rename for the same reason.
* ``references/`` — third-party paper sources a project fetches for itself.
* Markdown — the documents have their own review, and a word in prose is a
  different kind of defect from a name baked into a tool.

Three tokens are kept ON PURPOSE and are therefore not forbidden: the
``MIPSTARRE_`` environment prefix, the ``mipstarre-dev`` cache-directory name and
the ``mipstarre-review`` comment markers.  They are per-machine names that never
collide with a project's own; projects are separated by ``paths.cache_root``.
``PaperLib`` and ``OWNER/REPO`` are the kit's placeholders and are expected.
"""

from __future__ import annotations

import re
import subprocess
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]

#: Prefixes whose contents are origin material on purpose (see the docstring).
SKIPPED_PREFIXES = ("docs/origin/", "local/kit/", "references/")

#: Directories that are never part of the shipped tree.
SKIPPED_DIRS = {".git", ".lake", "__pycache__", ".worktrees", "node_modules"}

#: Files that must carry one of these strings to do their job: this module and
#: the service-layer guard carry the list itself, and the artifact test needs a
#: personal-looking home path to prove that the packaging script rewrites one.
SKIPPED_FILES = {
    "scripts/tests/test_no_origin_tokens.py",
    "scripts/tests/test_service_tools.py",
    "scripts/tests/test_make_artifact.py",
}

#: Plain substrings that may not appear anywhere else.
FORBIDDEN = (
    "MIPStarRE",            # the origin's Lean library token (MIPSTARRE_ is kept)
    "QPBT", "qpbt",         # the origin's track
    "Dengnifer", "dengnifer",
    "gpt-6-astra", "gpt-5.6-sol",
    "codex-home-space", "codex-home-yxy",
    "sirui-lu.com",
    "PaperLib/LDT", "PaperLib.LDT",
    "2009.12982", "2001.04383", "1904.05870",   # the origin's papers
)

#: Names that need a word boundary: they are short enough to occur inside an
#: ordinary word (a frequency in GHz, a relay of something else).
FORBIDDEN_WORDS = (
    "ghz", "space-3", "space-d", "relay-1", "relay-3", "erkki", "virvm",
)

#: A personal home directory, in any of its spellings.
HOME_PATH_RE = re.compile(r"(?<![\w$])/(?:home|Users)/[a-z]")

WORD_RE = re.compile(r"(?<![\w-])(?:%s)(?![\w-])" % "|".join(FORBIDDEN_WORDS))


def shipped_text_files() -> list[Path]:
    """Every text file of the tree that this guard covers."""

    try:
        listed = subprocess.run(
            ["git", "-C", str(ROOT), "ls-files", "-z"],
            capture_output=True, text=True, timeout=120, check=True).stdout
        paths = [ROOT / name for name in listed.split("\0") if name]
    except (OSError, subprocess.SubprocessError):
        paths = [p for p in ROOT.rglob("*")
                 if not SKIPPED_DIRS & set(p.relative_to(ROOT).parts)]

    out = []
    for path in paths:
        if not path.is_file() or path.is_symlink():
            continue
        relative = path.relative_to(ROOT).as_posix()
        if relative in SKIPPED_FILES:
            continue
        if any(relative.startswith(prefix) for prefix in SKIPPED_PREFIXES):
            continue
        if SKIPPED_DIRS & set(Path(relative).parts):
            continue
        try:
            data = path.read_bytes()
        except OSError:
            continue
        if b"\x00" in data[:8192]:          # binary
            continue
        out.append(path)
    return sorted(out)


class NoOriginTokenTests(unittest.TestCase):
    def setUp(self) -> None:
        self.files = shipped_text_files()
        self.assertGreater(len(self.files), 100, "the file walk found almost nothing")

    def test_no_origin_name_survives(self) -> None:
        for path in self.files:
            text = path.read_text(encoding="utf-8", errors="replace")
            # Links to the ANCESTOR project (cited precedent issues and PRs) are kept on purpose;
            # local/kit/extract.sh shields them from the rename. They are not origin leftovers.
            for ancestor in ("LionSR/MIPStarRE", "sirui-lu.com/MIPStarRE"):
                text = text.replace(ancestor, "")
            relative = path.relative_to(ROOT).as_posix()
            for token in FORBIDDEN:
                with self.subTest(file=relative, token=token):
                    # assertFalse, not assertNotIn: a failure should name the file
                    # and the token, not print the whole file.
                    self.assertFalse(token in text, f"{relative} still names {token!r}")

    def test_no_origin_host_or_key_name_survives(self) -> None:
        for path in self.files:
            text = path.read_text(encoding="utf-8", errors="replace")
            relative = path.relative_to(ROOT).as_posix()
            with self.subTest(file=relative):
                found = WORD_RE.search(text)
                self.assertIsNone(found, f"{relative} still names {found.group(0) if found else ''}")

    def test_no_personal_home_directory_is_hard_coded(self) -> None:
        for path in self.files:
            text = path.read_text(encoding="utf-8", errors="replace")
            relative = path.relative_to(ROOT).as_posix()
            with self.subTest(file=relative):
                found = HOME_PATH_RE.search(text)
                self.assertIsNone(
                    found, f"{relative} hard-codes {found.group(0) if found else ''}...")


if __name__ == "__main__":
    unittest.main()
