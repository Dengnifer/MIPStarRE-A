#!/usr/bin/env python3
"""Unit tests for ``local/bin/claim.sh`` — the atomic worker-claim list (issue #576).

The claim file is redirected with ``MIPSTARRE_CLAIM_FILE`` so the tests never
touch the operator's live list; the recorded format is asserted against the
format the meta session's copy writes.
"""

from __future__ import annotations

import re
import subprocess
import tempfile
import unittest
from pathlib import Path

CLAIM_SH = Path(__file__).resolve().parents[2] / "local" / "bin" / "claim.sh"

_CLAIM_LINE = re.compile(
    r"^(main|opus)-[a-z]+ \d+ claimed \d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z(?: .*)?$"
)
_RELEASE_LINE = re.compile(
    r"^(main|opus)-[a-z]+ \d+ released .*\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z$"
)


class ClaimScriptTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.file = Path(self.tmp.name) / "watchdog" / "meta-dispatched.txt"
        self.addCleanup(self.tmp.cleanup)

    def run_claim(self, *argv: str) -> subprocess.CompletedProcess:
        return subprocess.run(
            ["bash", str(CLAIM_SH), *argv], capture_output=True, text=True,
            env={"PATH": "/usr/bin:/bin:/usr/local/bin", "HOME": self.tmp.name,
                 "MIPSTARRE_CLAIM_FILE": str(self.file)},
        )

    def lines(self) -> list[str]:
        return [line for line in self.file.read_text().splitlines() if line.strip()]

    def test_script_is_executable_and_self_documenting(self):
        self.assertTrue(CLAIM_SH.exists(), f"{CLAIM_SH} is missing")
        head = CLAIM_SH.read_text()
        self.assertIn("meta-dispatched.txt", head)
        self.assertIn("MIPSTARRE_CLAIM_FILE", head)

    def test_check_of_an_unclaimed_number_is_free(self):
        result = self.run_claim("check", "576")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.strip(), "free")

    def test_claim_records_the_documented_line_format(self):
        result = self.run_claim("claim", "opus", "feature", "576", "issue 576 build")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.strip(), "claimed")
        line = self.lines()[0]
        self.assertRegex(line, _CLAIM_LINE)
        self.assertTrue(line.startswith("opus-feature 576 claimed "))
        self.assertTrue(line.endswith("issue 576 build"))

    def test_second_claim_is_refused_while_the_first_is_open(self):
        self.run_claim("claim", "opus", "feature", "576", "first")
        result = self.run_claim("claim", "main", "fix", "576", "second")
        self.assertEqual(result.returncode, 3)
        self.assertIn("HELD:", result.stdout)
        self.assertIn("opus-feature 576 claimed", result.stdout)
        self.assertEqual(len(self.lines()), 1, "a refused claim must not be recorded")

    def test_a_different_number_is_not_blocked(self):
        self.run_claim("claim", "opus", "feature", "576", "first")
        self.assertEqual(self.run_claim("claim", "main", "fix", "577", "other")
                         .returncode, 0)

    def test_check_reports_the_holder_and_exits_three(self):
        self.run_claim("claim", "opus", "review", "576", "note")
        result = self.run_claim("check", "576")
        self.assertEqual(result.returncode, 3)
        self.assertIn("opus-review 576 claimed", result.stdout)

    def test_release_frees_the_number_and_records_its_line(self):
        self.run_claim("claim", "opus", "feature", "576", "first")
        result = self.run_claim("release", "opus", "feature", "576", "done ok")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.strip(), "released")
        self.assertRegex(self.lines()[1], _RELEASE_LINE)
        self.assertEqual(self.run_claim("check", "576").stdout.strip(), "free")
        self.assertEqual(
            self.run_claim("claim", "main", "fix", "576", "next").returncode, 0)

    def test_release_of_one_kind_does_not_free_another_kinds_claim(self):
        self.run_claim("claim", "opus", "feature", "576", "a")
        self.run_claim("release", "main", "fix", "576", "not mine")
        result = self.run_claim("check", "576")
        self.assertEqual(result.returncode, 3)
        self.assertIn("opus-feature", result.stdout)

    def test_the_file_is_append_only(self):
        self.run_claim("claim", "opus", "feature", "576", "a")
        self.run_claim("release", "opus", "feature", "576", "b")
        self.run_claim("claim", "main", "fix", "576", "c")
        self.assertEqual(len(self.lines()), 3)

    def test_bad_party_and_non_numeric_number_are_usage_errors(self):
        self.assertEqual(self.run_claim("claim", "bot", "fix", "576", "x").returncode, 2)
        self.assertEqual(self.run_claim("claim", "opus", "fix", "PR576", "x").returncode, 2)
        self.assertEqual(self.run_claim("frobnicate", "576").returncode, 2)


if __name__ == "__main__":
    unittest.main()
