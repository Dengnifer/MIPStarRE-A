#!/usr/bin/env python3
"""Unit tests for the sorry-site counter of ``results/telemetry/owner-tools/estimate.sh``.

Issue #168 tracks the open proof obligations, and the estimate comment posted on
it used to be produced by an unanchored ``grep -c 'sorry'``.  That also matched
prose mentions inside docstrings, so the owner-facing progress tracker
over-reported the number of open sites.

These tests are offline: they drive the script's ``--count-sorry-sites`` entry
point, which never touches git, gh, or the telemetry log.
"""

from __future__ import annotations

import subprocess
import tempfile
import unittest
from pathlib import Path

ESTIMATE_SH = (
    Path(__file__).resolve().parents[2]
    / "results"
    / "telemetry"
    / "owner-tools"
    / "estimate.sh"
)

# One prose mention inside a docstring plus one real ``sorry`` tactic.  The
# prose line is copied from the shape used in PaperLib/Sample/Games/
# StrategyClasses.lean, which is what the unanchored counter mis-counted.
FIXTURE = """import Mathlib

/-- A statement kept faithful to the source.

**Unfaithful:** The `sorry` is the source's unattested attainment step:
the `sorry` records the gap and must not be removed silently. -/
theorem example_gap (n : Nat) : n = n := by
  sorry
"""


class SorryCountTests(unittest.TestCase):
    def count(self, *sources: str) -> int:
        with tempfile.TemporaryDirectory() as tmp:
            paths = []
            for i, src in enumerate(sources):
                p = Path(tmp) / f"Fixture{i}.lean"
                p.write_text(src)
                paths.append(str(p))
            proc = subprocess.run(
                ["bash", str(ESTIMATE_SH), "--count-sorry-sites", *paths],
                capture_output=True,
                text=True,
            )
            self.assertEqual(proc.returncode, 0, proc.stderr)
            return int(proc.stdout.strip())

    def test_docstring_prose_is_not_a_site(self):
        """Two backticked prose mentions and one real tactic count as one."""
        self.assertEqual(self.count(FIXTURE), 1)

    def test_bare_sorry_forms_are_counted(self):
        self.assertEqual(
            self.count(
                "theorem a : True := by\n  sorry\n"
                "theorem b : True := sorry\n"
                "theorem c : True := by sorry\n"
                "example : True := (sorry)\n"
                "theorem d : True := by\n  · sorry\n"
            ),
            5,
        )

    def test_prose_and_commented_out_sorry_are_not_counted(self):
        self.assertEqual(
            self.count(
                "/-- Its `sorry` records the gap. -/\n"
                "-- sorry\n"
                "  -- sorry\n"
                "/-- The sorryAx marker is reported by the kernel. -/\n"
                "theorem e : True := trivial\n"
            ),
            0,
        )

    def test_counts_are_summed_across_files(self):
        self.assertEqual(self.count(FIXTURE, FIXTURE), 2)


if __name__ == "__main__":
    unittest.main()
