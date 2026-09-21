#!/usr/bin/env python3
"""Unit tests for ``local/bin/dup_check.py`` (issue #576).

Everything runs against synthetic git repositories built in a temp directory:
no network, no model call, and no read of the real checkout's history.
"""

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


LEMMA_A = """\
import Mathlib

namespace PaperLib.Sample

/-- A doc comment that must not reach the normal form. -/
theorem foo_bar (n : Nat) (hn : 0 < n) : n + 0 = n := by
  simp

end PaperLib.Sample
"""

# Same statement as `foo_bar`, different name, different binder names and
# spacing, and a different proof.
LEMMA_A_RENAMED = """\
import Mathlib

namespace PaperLib.Sample

theorem foo_bar_alt   (m : Nat)   (hm : 0 < m) :
    m + 0 = m := by
  omega

end PaperLib.Sample
"""

LEMMA_B = """\
import Mathlib

namespace PaperLib.Sample

theorem unrelated (n : Nat) : n * 1 = n := by
  simp

end PaperLib.Sample
"""

# Same short name as `foo_bar`, different namespace, still inside PaperLib.
LEMMA_SHORT = """\
import Mathlib

namespace PaperLib.Games

theorem foo_bar (s : String) : s = s := rfl

end PaperLib.Games
"""


def git(repo: Path, *args: str) -> str:
    proc = subprocess.run(
        ["git", "-C", str(repo), *args], capture_output=True, text=True, check=True,
    )
    return proc.stdout


def init_repo(root: Path) -> Path:
    root.mkdir(parents=True, exist_ok=True)
    git(root, "init", "-q", "-b", "main")
    git(root, "config", "user.email", "test@example.invalid")
    git(root, "config", "user.name", "dup-check test")
    git(root, "config", "commit.gpgsign", "false")
    return root


def write(repo: Path, rel: str, text: str) -> None:
    path = repo / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def commit(repo: Path, message: str) -> str:
    git(repo, "add", "-A")
    git(repo, "commit", "-q", "-m", message)
    return git(repo, "rev-parse", "HEAD").strip()


def run_cli(*argv: str) -> tuple[int, str]:
    buffer = io.StringIO()
    with redirect_stdout(buffer):
        code = dup_check.main(list(argv))
    return code, buffer.getvalue()


class NormalizationTests(unittest.TestCase):
    def test_binder_renaming_makes_alpha_variants_equal(self):
        first = dup_scan.normalize_statement(
            "theorem foo_bar (n : Nat) (hn : 0 < n) : n + 0 = n := by simp"
        )
        second = dup_scan.normalize_statement(
            "theorem other   (m : Nat)  (hm : 0 < m) :\n    m + 0 = m := by omega"
        )
        self.assertNotEqual(first, "")
        self.assertEqual(first, second)

    def test_different_statements_do_not_collapse(self):
        first = dup_scan.normalize_statement("theorem a (n : Nat) : n + 0 = n := rfl")
        second = dup_scan.normalize_statement("theorem a (n : Nat) : n * 1 = n := rfl")
        self.assertNotEqual(first, second)

    def test_proof_is_cut_off(self):
        normal = dup_scan.normalize_statement(
            "theorem a (n : Nat) : n = n := by\n  induction n <;> simp"
        )
        self.assertNotIn("induction", normal)

    def test_top_level_by_ends_the_signature_but_nested_by_does_not(self):
        self.assertEqual(dup_scan.cut_at_proof("(h : P) : Q by tac").strip(),
                         "(h : P) : Q")
        kept = dup_scan.cut_at_proof("(h : P := by tac2) : Q")
        self.assertIn("Q", kept)


class ParsingTests(unittest.TestCase):
    def test_namespace_is_applied_and_doc_comments_dropped(self):
        records = dup_scan.decls_from_text(LEMMA_A, "PaperLib/Sample/A.lean")
        self.assertEqual([r.fqn for r in records], ["PaperLib.Sample.foo_bar"])
        record = records[0]
        self.assertEqual(record.short_name, "foo_bar")
        self.assertEqual(record.file, "PaperLib/Sample/A.lean")
        self.assertNotIn("doc comment", record.normalized)


class RefSearchTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.repo = init_repo(Path(self.tmp.name) / "repo")
        write(self.repo, "PaperLib/Sample/A.lean", LEMMA_A)
        write(self.repo, "PaperLib/Sample/B.lean", LEMMA_B)
        commit(self.repo, "main content")
        git(self.repo, "branch", "-f", "github/main", "main")
        self.addCleanup(self.tmp.cleanup)

    def test_exact_name_match(self):
        code, out = run_cli("check", "--repo", str(self.repo),
                            "--name", "PaperLib.Sample.foo_bar")
        self.assertEqual(code, 3)
        self.assertIn("PaperLib/Sample/A.lean:6", out)
        self.assertIn("fqn", out)

    def test_short_name_match_in_project_namespace(self):
        code, out = run_cli("check", "--repo", str(self.repo), "--name", "foo_bar")
        self.assertEqual(code, 3)
        self.assertIn("short", out)
        self.assertIn("PaperLib.Sample.foo_bar", out)

    def test_no_match_exits_zero(self):
        code, out = run_cli("check", "--repo", str(self.repo),
                            "--name", "PaperLib.Sample.never_declared")
        self.assertEqual(code, 0)
        self.assertIn("no duplicate", out)

    def test_json_mode_reports_locations(self):
        code, out = run_cli("check", "--repo", str(self.repo), "--json",
                            "--name", "PaperLib.Sample.foo_bar")
        self.assertEqual(code, 3)
        payload = json.loads(out)
        self.assertEqual(payload["queried"], 1)
        self.assertEqual(payload["duplicates"][0]["match"], "fqn")
        self.assertEqual(payload["duplicates"][0]["location"],
                         "PaperLib/Sample/A.lean:6")

    def test_branch_statement_match_finds_a_renamed_copy(self):
        git(self.repo, "checkout", "-q", "-b", "topic")
        write(self.repo, "PaperLib/Sample/C.lean", LEMMA_A_RENAMED)
        commit(self.repo, "re-prove the same statement under a new name")
        code, out = run_cli("check", "--repo", str(self.repo), "--json",
                            "--branch", "topic")
        self.assertEqual(code, 3)
        payload = json.loads(out)
        kinds = {row["match"] for row in payload["duplicates"]}
        self.assertEqual(kinds, {"statement"})
        self.assertEqual(payload["duplicates"][0]["location"],
                         "PaperLib/Sample/A.lean:6")

    def test_branch_with_only_new_mathematics_is_clean(self):
        git(self.repo, "checkout", "-q", "-b", "fresh")
        write(self.repo, "PaperLib/Sample/D.lean",
              LEMMA_B.replace("unrelated", "genuinely_new").replace("n * 1 = n",
                                                                    "n + 1 = 1 + n"))
        commit(self.repo, "new lemma")
        code, out = run_cli("check", "--repo", str(self.repo), "--branch", "fresh")
        self.assertEqual(code, 0, out)

    def test_missing_ref_is_advisory_and_never_reported_clean(self):
        code, out = run_cli("check", "--repo", str(self.repo),
                            "--ref", "github/nope",
                            "--name", "PaperLib.Sample.foo_bar")
        self.assertEqual(code, 4)
        self.assertIn("duplicate check skipped", out)
        self.assertNotIn("no duplicate", out)

    def test_missing_ref_in_json_mode_carries_the_skip(self):
        code, out = run_cli("check", "--repo", str(self.repo), "--json",
                            "--ref", "github/nope", "--name", "x")
        self.assertEqual(code, 4)
        payload = json.loads(out)
        self.assertIn("skipped", payload)
        self.assertNotIn("duplicates", payload)


class SweepTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.repo = init_repo(Path(self.tmp.name) / "repo")
        write(self.repo, "PaperLib/Sample/A.lean", LEMMA_A)
        commit(self.repo, "main content")
        git(self.repo, "branch", "-f", "github/main", "main")

        # PR 1: a renamed copy of a statement main already proves.
        git(self.repo, "checkout", "-q", "-b", "github/issue-1-copy")
        write(self.repo, "PaperLib/Sample/Copy.lean", LEMMA_A_RENAMED)
        commit(self.repo, "duplicate statement")

        # PR 2: the same short name in another namespace.
        git(self.repo, "checkout", "-q", "main")
        git(self.repo, "checkout", "-q", "-b", "github/issue-2-shortname")
        write(self.repo, "PaperLib/Games/S.lean", LEMMA_SHORT)
        commit(self.repo, "same short name")

        # PR 3: genuinely new mathematics.
        git(self.repo, "checkout", "-q", "main")
        git(self.repo, "checkout", "-q", "-b", "github/issue-3-new")
        write(self.repo, "PaperLib/Sample/New.lean", LEMMA_B)
        commit(self.repo, "new lemma")
        git(self.repo, "checkout", "-q", "main")

        self.prs = Path(self.tmp.name) / "prs.json"
        self.prs.write_text(json.dumps([
            {"number": 11, "head_ref": "issue-1-copy", "title": "copy",
             "url": "https://example.invalid/11"},
            {"number": 12, "head_ref": "issue-2-shortname", "title": "short",
             "url": "https://example.invalid/12"},
            {"number": 13, "head_ref": "issue-3-new", "title": "new",
             "url": "https://example.invalid/13"},
            {"number": 14, "head_ref": "issue-4-not-fetched", "title": "absent",
             "url": "https://example.invalid/14"},
        ]))
        self.addCleanup(self.tmp.cleanup)

    def test_sweep_flags_only_the_superseded_prs(self):
        code, out = run_cli("sweep", "--repo", str(self.repo), "--json",
                            "--prs-file", str(self.prs))
        self.assertEqual(code, 3)
        report = json.loads(out)
        self.assertEqual(report["flagged"], [11, 12])
        rows = {row["number"]: row for row in report["pull_requests"]}
        self.assertEqual(rows[11]["duplicates"][0]["match"], "statement")
        self.assertEqual(rows[12]["duplicates"][0]["match"], "short")
        self.assertEqual(rows[13]["new_declarations"], 1)
        self.assertEqual(rows[13]["duplicates"], [])
        self.assertEqual(rows[11]["by_kind"], {"fqn": 0, "statement": 1, "short": 0})
        self.assertEqual(report["flagged_by_name"], [])
        self.assertIn("not present locally", rows[14]["skipped"])

    def test_markdown_report_has_front_matter_and_the_headline(self):
        out_path = Path(self.tmp.name) / "report.md"
        code, _ = run_cli("sweep", "--repo", str(self.repo),
                          "--prs-file", str(self.prs), "--out", str(out_path),
                          "--issue", "576", "--pr", "999")
        self.assertEqual(code, 3)
        text = out_path.read_text()
        self.assertTrue(text.startswith("---\n"))
        self.assertIn('issue: "#576"', text)
        self.assertIn('pr: "#999"', text)
        self.assertIn("Open pull requests examined: **4**", text)
        self.assertIn("already contains: **2**", text)
        self.assertIn("#11", text)
        self.assertIn("#12", text)
        self.assertIn("fully qualified name** (the strongest signal): **0**", text)
        self.assertIn("skipped: head branch not present locally", text)

    def test_sweep_with_an_absent_ref_is_advisory_and_not_clean(self):
        code, out = run_cli("sweep", "--repo", str(self.repo),
                            "--ref", "github/nope", "--prs-file", str(self.prs))
        self.assertEqual(code, 4)
        self.assertIn("duplicate check skipped", out)

    def test_clean_sweep_exits_zero(self):
        prs = Path(self.tmp.name) / "clean.json"
        prs.write_text(json.dumps([
            {"number": 13, "head_ref": "issue-3-new", "title": "new", "url": ""},
        ]))
        code, out = run_cli("sweep", "--repo", str(self.repo), "--json",
                            "--prs-file", str(prs))
        self.assertEqual(code, 0)
        self.assertEqual(json.loads(out)["flagged"], [])


class ReportColumnTests(unittest.TestCase):
    """The per-PR table must count declarations, not matches, as overlap."""

    REPORT = {
        "ref": "github/main",
        "generated_at": "2026-09-17T00:00:00Z",
        "ref_declarations": 2,
        "pull_requests": [{
            "number": 11, "title": "one declaration, two matches", "url": "",
            "head_ref": "topic", "new_declarations": 1,
            "duplicates": [
                {"query": "PaperLib.Sample.foo_bar", "match": "fqn",
                 "fqn": "PaperLib.Sample.foo_bar", "location": "A.lean:6"},
                {"query": "PaperLib.Sample.foo_bar", "match": "short",
                 "fqn": "PaperLib.Games.foo_bar", "location": "S.lean:5"},
            ],
            "by_kind": {"fqn": 1, "statement": 0, "short": 1},
            "skipped": "",
        }],
        "flagged": [11],
        "flagged_by_name": [11],
    }

    def test_distinct_declarations_are_counted(self):
        self.assertEqual(
            dup_scan.matched_declarations(self.REPORT["pull_requests"][0]["duplicates"]),
            1)

    def test_overlap_column_cannot_exceed_the_new_declaration_column(self):
        text = dup_scan.render_sweep_markdown(
            self.REPORT, title="t", issue=576, pr=579)
        self.assertIn("| #11 | 1 | 1 | 2 | 1 | 0 | 1 |", text)
        self.assertIn("| matches |", text)
        self.assertIn('pr: "#579"', text)


if __name__ == "__main__":
    unittest.main()
