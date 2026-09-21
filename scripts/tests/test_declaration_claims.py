#!/usr/bin/env python3
"""Unit tests for the declaration-claims registry of ``dup_check.py`` (issue #576)."""

from __future__ import annotations

import io
import json
import subprocess
import sys
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "local" / "bin"))
sys.path.insert(0, str(REPO_ROOT / "scripts"))

import dup_check  # noqa: E402
import dup_scan  # noqa: E402

LEMMA = """\
import Mathlib

namespace PaperLib.Sample

theorem already_on_main (n : Nat) : n = n := rfl

end PaperLib.Sample
"""


def git(repo: Path, *args: str) -> str:
    return subprocess.run(["git", "-C", str(repo), *args],
                          capture_output=True, text=True, check=True).stdout


def run_cli(*argv: str) -> tuple[int, str]:
    buffer = io.StringIO()
    with redirect_stdout(buffer):
        code = dup_check.main(list(argv))
    return code, buffer.getvalue()


class RegistryUnitTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.path = Path(self.tmp.name) / "claims.jsonl"
        self.addCleanup(self.tmp.cleanup)

    def test_release_closes_the_open_claim(self):
        dup_check.append_claim(self.path, dup_check.ClaimRow(
            ts="2026-09-17T10:00:00Z", action="claim", issue=1, names=("A.b",)))
        self.assertIn(1, dup_check.open_claims(dup_check.read_claims(self.path)))
        dup_check.append_claim(self.path, dup_check.ClaimRow(
            ts="2026-09-17T11:00:00Z", action="release", issue=1))
        self.assertEqual(dup_check.open_claims(dup_check.read_claims(self.path)), {})

    def test_reclaim_after_release_reopens(self):
        for index, action in enumerate(("claim", "release", "claim")):
            dup_check.append_claim(self.path, dup_check.ClaimRow(
                ts=f"2026-09-17T1{index}:00:00Z", action=action, issue=7,
                names=("A.b",) if action == "claim" else ()))
        self.assertIn(7, dup_check.open_claims(dup_check.read_claims(self.path)))

    def test_conflict_detection_uses_short_names_too(self):
        dup_check.append_claim(self.path, dup_check.ClaimRow(
            ts="2026-09-17T10:00:00Z", action="claim", issue=100,
            names=("PaperLib.Sample.shared_name",)))
        rows = dup_check.read_claims(self.path)
        conflicts = dup_check.claim_conflicts(
            rows, 200, ["PaperLib.Games.shared_name"])
        self.assertEqual([issue.issue for _, issue in conflicts], [100])
        self.assertEqual(dup_check.claim_conflicts(rows, 200, ["Other.name"]), [])

    def test_an_issue_does_not_conflict_with_itself(self):
        dup_check.append_claim(self.path, dup_check.ClaimRow(
            ts="2026-09-17T10:00:00Z", action="claim", issue=100, names=("A.b",)))
        self.assertEqual(
            dup_check.claim_conflicts(dup_check.read_claims(self.path), 100, ["A.b"]),
            [])

    def test_malformed_row_is_reported_with_its_line(self):
        self.path.write_text('{"ts": "t", "action": "claim"}\n')
        with self.assertRaises(dup_scan.DupScanError) as caught:
            dup_check.read_claims(self.path)
        self.assertIn(":1:", str(caught.exception))


class RegistryCliTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.repo = Path(self.tmp.name) / "repo"
        self.repo.mkdir(parents=True)
        git(self.repo, "init", "-q", "-b", "main")
        git(self.repo, "config", "user.email", "test@example.invalid")
        git(self.repo, "config", "user.name", "claims test")
        git(self.repo, "config", "commit.gpgsign", "false")
        target = self.repo / "PaperLib" / "Sample" / "A.lean"
        target.parent.mkdir(parents=True)
        target.write_text(LEMMA)
        git(self.repo, "add", "-A")
        git(self.repo, "commit", "-q", "-m", "main")
        git(self.repo, "branch", "-f", "github/main", "main")
        self.registry = str(Path(self.tmp.name) / "claims.jsonl")
        self.addCleanup(self.tmp.cleanup)

    def _claim(self, *extra: str) -> tuple[int, str]:
        return run_cli("claim", "--repo", str(self.repo),
                       "--registry", self.registry, *extra)

    def test_first_claim_of_a_new_name_is_recorded(self):
        code, out = self._claim("--issue", "601", "--name",
                                "PaperLib.Sample.brand_new", "--by", "meta")
        self.assertEqual(code, 0, out)
        rows = dup_check.read_claims(Path(self.registry))
        self.assertEqual(rows[0].issue, 601)
        self.assertEqual(rows[0].by, "meta")

    def test_claim_of_a_name_main_already_has_is_refused(self):
        code, out = self._claim("--issue", "602", "--name",
                                "PaperLib.Sample.already_on_main")
        self.assertEqual(code, 3)
        self.assertIn("DUPLICATE", out)
        self.assertIn("refusing", out)
        self.assertFalse(Path(self.registry).exists())

    def test_force_records_the_refused_claim_but_still_exits_three(self):
        code, _ = self._claim("--issue", "602", "--name",
                              "PaperLib.Sample.already_on_main", "--force")
        self.assertEqual(code, 3)
        self.assertEqual(len(dup_check.read_claims(Path(self.registry))), 1)

    def test_second_issue_claiming_the_same_name_is_refused(self):
        self.assertEqual(
            self._claim("--issue", "603", "--name", "PaperLib.Sample.shared")[0], 0)
        code, out = self._claim("--issue", "604", "--name", "PaperLib.Sample.shared")
        self.assertEqual(code, 3)
        self.assertIn("CONFLICT", out)
        self.assertIn("#603", out)

    def test_claims_check_is_read_only(self):
        self._claim("--issue", "605", "--name", "PaperLib.Sample.taken")
        before = Path(self.registry).read_text()
        code, out = run_cli("claims-check", "--repo", str(self.repo),
                            "--registry", self.registry, "--json",
                            "--issue", "606", "--name", "PaperLib.Sample.taken")
        self.assertEqual(code, 3)
        self.assertEqual(json.loads(out)["claim_conflicts"][0]["issue"], 605)
        self.assertEqual(Path(self.registry).read_text(), before)

    def test_claim_against_an_absent_ref_is_advisory_not_clean(self):
        code, out = self._claim("--issue", "610", "--ref", "github/nope",
                                "--name", "PaperLib.Sample.already_on_main")
        self.assertEqual(code, 4)
        self.assertIn("duplicate check skipped", out)
        self.assertNotIn("DUPLICATE", out)
        self.assertEqual(len(dup_check.read_claims(Path(self.registry))), 1)

    def test_claims_check_against_an_absent_ref_is_advisory_not_clean(self):
        code, out = run_cli("claims-check", "--repo", str(self.repo),
                            "--registry", self.registry, "--ref", "github/nope",
                            "--issue", "611", "--name",
                            "PaperLib.Sample.already_on_main")
        self.assertEqual(code, 4)
        self.assertIn("duplicate check skipped", out)
        self.assertNotIn("no duplicate", out)

    def test_claims_check_absent_ref_still_reports_a_registry_conflict(self):
        self._claim("--issue", "612", "--name", "PaperLib.Sample.contested")
        code, out = run_cli("claims-check", "--repo", str(self.repo),
                            "--registry", self.registry, "--ref", "github/nope",
                            "--json", "--issue", "613", "--name",
                            "PaperLib.Sample.contested")
        self.assertEqual(code, 3)
        payload = json.loads(out)
        self.assertEqual(payload["claim_conflicts"][0]["issue"], 612)
        self.assertIn("skipped", payload)

    def test_predispatch_without_a_claim_is_advisory(self):
        code, out = run_cli("predispatch", "--repo", str(self.repo),
                            "--registry", self.registry, "--issue", "607")
        self.assertEqual(code, 4)
        self.assertIn("no declaration claim registered", out)

    def test_predispatch_flags_a_claim_main_already_satisfies(self):
        self._claim("--issue", "608", "--name",
                    "PaperLib.Sample.already_on_main", "--force")
        code, out = run_cli("predispatch", "--repo", str(self.repo),
                            "--registry", self.registry, "--issue", "608")
        self.assertEqual(code, 3)
        self.assertIn("PaperLib/Sample/A.lean:5", out)

    def test_predispatch_on_a_clean_claim_exits_zero(self):
        self._claim("--issue", "609", "--name", "PaperLib.Sample.not_yet")
        code, out = run_cli("predispatch", "--repo", str(self.repo),
                            "--registry", self.registry, "--issue", "609")
        self.assertEqual(code, 0, out)

    def test_release_then_reclaim_by_another_issue(self):
        self._claim("--issue", "610", "--name", "PaperLib.Sample.handover")
        code, _ = run_cli("claims-release", "--repo", str(self.repo),
                          "--registry", self.registry, "--issue", "610")
        self.assertEqual(code, 0)
        self.assertEqual(
            self._claim("--issue", "611", "--name", "PaperLib.Sample.handover")[0], 0)

    def test_claims_list_shows_open_claims_only(self):
        self._claim("--issue", "612", "--name", "PaperLib.Sample.one")
        self._claim("--issue", "613", "--name", "PaperLib.Sample.two")
        run_cli("claims-release", "--repo", str(self.repo),
                "--registry", self.registry, "--issue", "612")
        code, out = run_cli("claims-list", "--repo", str(self.repo),
                            "--registry", self.registry, "--json")
        self.assertEqual(code, 0)
        self.assertEqual([row["issue"] for row in json.loads(out)], [613])


if __name__ == "__main__":
    unittest.main()
