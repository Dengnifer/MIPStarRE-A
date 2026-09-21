#!/usr/bin/env python3
"""Train member selection, the refused-set memory, and the daemon's candidate scan.

Three rules are pinned here because each was paid for with a real incident:

* a FRESH PR is never a train member — it merges alone, and listing it makes the whole
  train refuse;
* a PR whose local branch tip differs from its GitHub head is excluded — an unpushed
  helper commit once had the same batch staged three times in a row;
* a member set that was refused once is never staged again by itself.

Plus the scan's own contract: only PRs that are CI-green AND review-clean at their head
(or explicitly adjudicated) become candidates, and the line format the daemon and
``local/bin/daemon_train.py`` both parse.

Offline: the selection function and the scan row builder are pure.
"""

from __future__ import annotations

import importlib.util
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SERVICE = ROOT / "local" / "bin" / "service"


def load(name: str, filename: str):
    spec = importlib.util.spec_from_file_location(name, SERVICE / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


HEAD_A = "a" * 40
HEAD_B = "b" * 40
HEAD_C = "c" * 40


def row(number: int, head: str, *, ok: bool = True, fresh: bool = False,
        local_tip: str | None = None, claim: str = "free") -> dict:
    return {"number": number, "head": head, "ok": ok, "fresh": fresh,
            "local_tip": head if local_tip is None else local_tip, "claim": claim}


class MemberSelectionTests(unittest.TestCase):
    def setUp(self) -> None:
        self.stage = load("kit_stage_train", "stage-train.py")

    def test_two_clean_stale_prs_make_a_train(self) -> None:
        members, reasons = self.stage.select_members([row(7, HEAD_A), row(9, HEAD_B)])
        self.assertEqual([m["number"] for m in members], [7, 9])
        self.assertEqual([m["head"] for m in members], [HEAD_A, HEAD_B])
        self.assertEqual(reasons, [])

    def test_a_fresh_pr_is_never_a_train_member(self) -> None:
        members, reasons = self.stage.select_members(
            [row(7, HEAD_A, fresh=True), row(9, HEAD_B), row(11, HEAD_C)])
        self.assertEqual([m["number"] for m in members], [9, 11])
        self.assertTrue(any("7 is fresh" in r for r in reasons), reasons)

    def test_a_fresh_pr_cannot_be_the_reason_a_train_forms(self) -> None:
        members, reasons = self.stage.select_members([row(7, HEAD_A, fresh=True), row(9, HEAD_B)])
        self.assertEqual(members, [])
        self.assertTrue(any("at least two" in r for r in reasons), reasons)

    def test_a_local_tip_behind_the_pr_head_is_excluded(self) -> None:
        members, reasons = self.stage.select_members(
            [row(7, HEAD_A, local_tip=HEAD_C), row(9, HEAD_B), row(11, HEAD_C)])
        self.assertEqual([m["number"] for m in members], [9, 11])
        self.assertTrue(any("local branch tip" in r for r in reasons), reasons)

    def test_a_branch_absent_locally_is_still_a_member(self) -> None:
        """No local branch is not evidence of a stale one — only a DIFFERENT tip is."""
        members, _ = self.stage.select_members([row(7, HEAD_A, local_tip=""), row(9, HEAD_B)])
        self.assertEqual([m["number"] for m in members], [7, 9])

    def test_a_claimed_pr_is_excluded(self) -> None:
        members, reasons = self.stage.select_members(
            [row(7, HEAD_A, claim="main-fix 7 claimed ..."), row(9, HEAD_B), row(11, HEAD_C)])
        self.assertEqual([m["number"] for m in members], [9, 11])
        self.assertTrue(any("claimed" in r for r in reasons), reasons)

    def test_a_pr_that_is_not_green_is_excluded(self) -> None:
        members, reasons = self.stage.select_members(
            [row(7, HEAD_A, ok=False), row(9, HEAD_B), row(11, HEAD_C)])
        self.assertEqual([m["number"] for m in members], [9, 11])
        self.assertTrue(any("not approved and green" in r for r in reasons), reasons)

    def test_a_refused_member_set_is_never_staged_again(self) -> None:
        rows = [row(7, HEAD_A), row(9, HEAD_B)]
        members, _ = self.stage.select_members(rows)
        key = ",".join(str(m["number"]) for m in members)
        again, reasons = self.stage.select_members(rows, refused={key})
        self.assertEqual(again, [])
        self.assertTrue(any("refused before" in r for r in reasons), reasons)

    def test_a_different_member_set_is_still_allowed_after_a_refusal(self) -> None:
        members, _ = self.stage.select_members(
            [row(7, HEAD_A), row(9, HEAD_B), row(11, HEAD_C)], refused={"7,9"})
        self.assertEqual([m["number"] for m in members], [7, 9, 11])


class RefusedMemoryTests(unittest.TestCase):
    def test_a_refusal_survives_a_restart(self) -> None:
        stage = load("kit_stage_train", "stage-train.py")
        with tempfile.TemporaryDirectory() as tmp:
            daemon = Path(tmp) / "daemon"
            self.assertEqual(stage.read_refused(daemon), set())
            stage.remember_refused(daemon, "7,9")
            stage.remember_refused(daemon, "11,13")
            self.assertEqual(stage.read_refused(daemon), {"7,9", "11,13"})

    def test_an_empty_key_is_not_remembered(self) -> None:
        stage = load("kit_stage_train", "stage-train.py")
        with tempfile.TemporaryDirectory() as tmp:
            daemon = Path(tmp) / "daemon"
            stage.remember_refused(daemon, "")
            self.assertEqual(stage.read_refused(daemon), set())


class DaemonScanTests(unittest.TestCase):
    def setUp(self) -> None:
        self.scan = load("kit_daemon_scan", "daemon-scan.py")

    @staticmethod
    def node(number: int, head: str, *, ci: str = "SUCCESS", review: str = "SUCCESS",
             branch: str | None = None, body: str | None = None) -> dict:
        if body is None:
            body = f"<!-- mipstarre-review pr={number} head={head} -->\nfine\n\nVERDICT: APPROVED"
        return {
            "number": number,
            "headRefName": branch if branch is not None else f"issue-{number}-a-slug",
            "headRefOid": head,
            "commits": {"nodes": [{"commit": {"status": {"contexts": [
                {"context": "local-ci/summary", "state": ci},
                {"context": "local-review/summary", "state": review}]}}}]},
            "reviews": {"nodes": [{"body": body}]},
        }

    def test_a_green_and_clean_pr_is_a_clean_candidate(self) -> None:
        self.assertEqual(self.scan.rows([self.node(7, HEAD_A)], set()),
                         [f"7:7:issue-7-a-slug:a-slug:clean:{HEAD_A}"])

    def test_an_unresolved_finding_is_not_clean(self) -> None:
        body = f"<!-- mipstarre-review pr=7 head={HEAD_A} -->\n- [ ] F1 open\n\nVERDICT: APPROVED"
        self.assertEqual(self.scan.rows([self.node(7, HEAD_A, body=body)], set()), [])

    def test_a_review_for_another_head_is_not_clean(self) -> None:
        body = f"<!-- mipstarre-review pr=7 head={HEAD_B} -->\nfine\n\nVERDICT: APPROVED"
        self.assertEqual(self.scan.rows([self.node(7, HEAD_A, body=body)], set()), [])

    def test_red_ci_is_never_a_candidate_even_when_adjudicated(self) -> None:
        self.assertEqual(self.scan.rows([self.node(7, HEAD_A, ci="FAILURE")], {"7"}), [])

    def test_an_adjudicated_pr_without_a_clean_review_is_an_adj_candidate(self) -> None:
        self.assertEqual(self.scan.rows([self.node(7, HEAD_A, review="FAILURE")], {"7"}),
                         [f"7:7:issue-7-a-slug:a-slug:adj:{HEAD_A}"])

    def test_a_branch_outside_the_naming_scheme_is_skipped(self) -> None:
        self.assertEqual(self.scan.rows([self.node(7, HEAD_A, branch="hotfix")], set()), [])

    def test_a_zero_padded_issue_number_is_normalised(self) -> None:
        self.assertEqual(self.scan.rows([self.node(7, HEAD_A, branch="issue-0042-a-slug")], set()),
                         [f"7:42:issue-0042-a-slug:a-slug:clean:{HEAD_A}"])

    def test_the_line_shape_matches_what_the_train_adapter_parses(self) -> None:
        import sys
        sys.path.insert(0, str(ROOT / "local" / "bin"))
        import daemon_train

        line = self.scan.rows([self.node(7, HEAD_A)], set())[0]
        self.assertIsNotNone(daemon_train.CANDIDATE.fullmatch(line))


class AutoMergeTests(unittest.TestCase):
    def test_the_skip_list_comes_from_the_state_directory(self) -> None:
        auto = load("kit_auto_merge", "auto-merge.py")
        with tempfile.TemporaryDirectory() as tmp:
            state = Path(tmp)
            loop = auto.Loop(Path(tmp), state, 240)
            self.assertEqual(loop.skip_set(), set())
            (state / "auto-merge.skip").write_text("212\n400\nnot-a-number\n", encoding="utf-8")
            self.assertEqual(loop.skip_set(), {212, 400})


if __name__ == "__main__":
    unittest.main()
