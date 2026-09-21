#!/usr/bin/env python3
"""Unit tests for ``results/telemetry/owner-tools/lean-loc.py``.

Every completion-estimate update carries the total Lean code-line count of the
project, counted with the same rule as the merge-title Lean delta: blank lines
and comment-only lines do not count.  These tests pin that behaviour on a tiny
fixture tree and pin the wording of the clause ``estimate.sh`` appends to the
posted comment — including that the project name in it comes from the
configuration rather than from a constant in the helper.

They are offline: the helper is driven through its ``--paths`` and
``--format-clause`` entry points, which never touch git, gh, or the telemetry
log.
"""

from __future__ import annotations

import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LEAN_LOC = ROOT / "results" / "telemetry" / "owner-tools" / "lean-loc.py"
ESTIMATE_SH = ROOT / "results" / "telemetry" / "owner-tools" / "estimate.sh"

# Code, a blank line, a line comment, a multi-line block comment, a docstring,
# and code trailed by a comment: 3 code lines out of 9.
FIXTURE = """import Mathlib

-- a line comment
/- a block
   comment spanning two lines -/
/-- A doc comment on one line. -/
theorem a : True := trivial  -- trailing comment

theorem b : True := trivial
"""

# A doc comment spanning several lines, then one line of code: 1 of 5.
FIXTURE_DOCSTRING = """/-- A doc comment
that runs over
three lines. -/
theorem c : True := trivial
"""


def run(*args: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        ["python3", str(LEAN_LOC), *args], capture_output=True, text=True
    )


class LeanLocCountTests(unittest.TestCase):
    def count(self, *sources: str) -> tuple[int, int, int]:
        with tempfile.TemporaryDirectory() as tmp:
            paths = []
            for i, src in enumerate(sources):
                p = Path(tmp) / f"Fixture{i}.lean"
                p.write_text(src)
                paths.append(str(p))
            proc = run("--paths", *paths)
            self.assertEqual(proc.returncode, 0, proc.stderr)
            files, code, total = (int(v) for v in proc.stdout.split())
            return files, code, total

    def test_blank_and_comment_only_lines_are_not_code(self):
        self.assertEqual(self.count(FIXTURE), (1, 3, 9))

    def test_multi_line_doc_comment_is_not_code(self):
        self.assertEqual(self.count(FIXTURE_DOCSTRING), (1, 1, 4))

    def test_counts_are_summed_across_files(self):
        self.assertEqual(self.count(FIXTURE, FIXTURE_DOCSTRING), (2, 4, 13))


class LeanLocFailureTests(unittest.TestCase):
    def test_a_missing_file_prints_no_figure(self):
        """Cosmetic by contract: a failure yields no figure, never bad output."""
        proc = run("--paths", "/nonexistent/Fixture.lean")
        self.assertNotEqual(proc.returncode, 0)
        self.assertEqual(proc.stdout, "")


class ClauseFormattingTests(unittest.TestCase):
    def clause(self, files: int, code_lines: int, name: str = "Demo") -> str:
        proc = run("--format-clause", str(files), str(code_lines), "--name", name)
        self.assertEqual(proc.returncode, 0, proc.stderr)
        return proc.stdout.strip()

    def test_thousands_separators(self):
        self.assertEqual(
            self.clause(311, 75906), "Demo Lean code: 75,906 lines in 311 files"
        )

    def test_one_file_is_singular(self):
        self.assertEqual(self.clause(1, 7), "Demo Lean code: 7 lines in 1 file")

    def test_the_project_name_comes_from_the_configuration(self):
        """No project name is baked into the helper: it reads project.name."""
        import json

        proc = run("--format-clause", "1", "7")
        self.assertEqual(proc.returncode, 0, proc.stderr)
        configured = json.loads((ROOT / "local" / "project.json").read_text())["project"]["name"]
        self.assertEqual(proc.stdout.strip(), f"{configured} Lean code: 7 lines in 1 file")


class EstimateWiringTests(unittest.TestCase):
    """The figure is useless unless ``estimate.sh`` actually carries it."""

    def test_estimate_uses_the_helper_and_records_the_fields(self):
        text = ESTIMATE_SH.read_text()
        self.assertIn("lean-loc.py", text)
        self.assertIn("lean_code_lines", text)
        self.assertIn("lean_files", text)


if __name__ == "__main__":
    unittest.main()
