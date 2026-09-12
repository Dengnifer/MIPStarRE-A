#!/usr/bin/env python3
"""Regression tests for local/bin/ready_report.py.

Readiness, the reason classifier, the rendered comment and the suppression rule
are pure functions of GitHub payloads and daemon state, so every test here runs
offline against fixtures and a temporary runtime root.  No test touches GitHub.
"""

from __future__ import annotations

import io
import json
import os
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from datetime import datetime, timedelta, timezone
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
BIN_DIR = REPO_ROOT / "local" / "bin"
sys.path.insert(0, str(BIN_DIR))

import ready_report  # noqa: E402

NOW = datetime(2026, 9, 13, 6, 0, 0, tzinfo=timezone.utc)
HEAD = "a" * 40
OTHER = "b" * 40


def pull(number: int = 213, *, head: str = HEAD, branch: str = "issue-211-lines",
         draft: bool = False) -> dict:
    return {"number": number, "draft": draft,
            "head": {"sha": head, "ref": branch}}


def statuses(ci: str = "success", review: str = "success") -> dict:
    out = {}
    if ci:
        out["local-ci/summary"] = {"state": ci}
    if review:
        out["local-review/summary"] = {"state": review}
    return out


def review(head: str = HEAD, *, unchecked: int = 0, state: str = "COMMENTED",
           marked: bool = True) -> dict:
    ledger = "\n".join(f"- [ ] F{n} something" for n in range(1, unchecked + 1))
    body = ("<!-- mipstarre-review pr=213 head=%s -->\n" % head if marked else "")
    body += f"{ledger}\nVERDICT: APPROVED (code=0, prose=0)"
    return {"commit_id": head, "state": state, "body": body}


class ReadinessTestCase(unittest.TestCase):
    def test_green_pr_with_a_clean_ledger_is_ready(self) -> None:
        row = ready_report.readiness(pull(), statuses(), [review()])
        self.assertTrue(row["ready"], row["blockers"])
        self.assertEqual(row["issue"], 211)
        self.assertEqual(row["unchecked"], 0)

    def test_each_gate_blocks_on_its_own(self) -> None:
        cases = {
            "ci=failure": (pull(), statuses(ci="failure"), [review()]),
            "ci=absent": (pull(), statuses(ci=""), [review()]),
            "review=absent": (pull(), statuses(review=""), [review()]),
            "2 unchecked findings": (pull(), statuses(), [review(unchecked=2)]),
            "no exact-head review": (pull(), statuses(), [review(head=OTHER)]),
            "draft": (pull(draft=True), statuses(), [review()]),
            "CHANGES_REQUESTED": (pull(), statuses(),
                                  [review(), review(state="CHANGES_REQUESTED")]),
        }
        for blocker, (pr, st, reviews) in cases.items():
            with self.subTest(blocker=blocker):
                row = ready_report.readiness(pr, st, reviews)
                self.assertFalse(row["ready"])
                self.assertIn(blocker, row["blockers"])

    def test_unchecked_lines_match_the_review_ledger_shape(self) -> None:
        body = ("<!-- mipstarre-review -->\n"
                "  - [ ] indented finding\n"
                "* [ ] star finding\n"
                "- [x] resolved finding\n"
                "text - [ ] not at the start of a line\n")
        row = ready_report.readiness(
            pull(), statuses(), [{"commit_id": HEAD, "state": "COMMENTED", "body": body}])
        self.assertEqual(row["unchecked"], 2)

    def test_the_newest_marker_review_on_the_head_is_operative(self) -> None:
        rows = [review(unchecked=3), review(unchecked=0)]
        self.assertTrue(ready_report.readiness(pull(), statuses(), rows)["ready"])

    def test_branch_without_an_issue_number(self) -> None:
        row = ready_report.readiness(pull(branch="topic/experiment"), statuses(), [review()])
        self.assertIsNone(row["issue"])
        self.assertEqual(ready_report.issue_of("codex/issue-0042-slug"), 42)


class ReasonTestCase(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        root = Path(self._tmp.name)
        self.daemon = root / "daemon"
        self.lanes = root / "lanes"
        self.daemon.mkdir()
        self.lanes.mkdir()
        self.row = {"pr": 213, "head": HEAD, "issue": 211, "ready": True}

    def tearDown(self) -> None:
        self._tmp.cleanup()

    def classify(self, **kwargs):
        params = dict(daemon_dir=self.daemon, lanes_dir=self.lanes, fresh=True,
                      base_moved_min=7, adjudicating=False, now=NOW)
        params.update(kwargs)
        return ready_report.classify_reason(self.row, **params)

    def test_unexplained_is_the_alarm_case(self) -> None:
        reason = self.classify()
        self.assertEqual(reason["class"], "unexplained")
        self.assertIn("investigate", reason["detail"])

    def test_refreshing_names_the_live_pid_and_lane(self) -> None:
        (self.daemon / "pr213.refreshing").write_text(f"{os.getpid()}\n", encoding="utf-8")
        reason = self.classify()
        self.assertEqual(reason["class"], "refreshing")
        self.assertIn(str(os.getpid()), reason["detail"])
        self.assertIn("lane 211", reason["detail"])

    def test_a_dead_refresh_pid_is_not_a_reason(self) -> None:
        (self.daemon / "pr213.refreshing").write_text("999999999\n", encoding="utf-8")
        self.assertEqual(self.classify()["class"], "unexplained")

    def test_failed_marker_carries_the_daemon_class_and_reason(self) -> None:
        (self.daemon / "pr213.failed").write_text(json.dumps(
            {"pr": 213, "head": HEAD, "class": "build", "attempts": 2,
             "reason": "lake build failed"}), encoding="utf-8")
        reason = self.classify()
        self.assertEqual(reason["class"], "failed")
        self.assertIn("class=build", reason["detail"])
        self.assertIn("lake build failed", reason["detail"])
        self.assertIn("attempts=2", reason["detail"])

    def test_failed_marker_on_another_head_is_flagged(self) -> None:
        (self.daemon / "pr213.failed").write_text(json.dumps(
            {"head": OTHER, "class": "merge", "reason": "conflicted"}), encoding="utf-8")
        self.assertIn("marker on a different head", self.classify()["detail"])

    def test_legacy_touch_marker_is_reported_not_ignored(self) -> None:
        (self.daemon / "pr213.failed").touch()
        reason = self.classify()
        self.assertEqual(reason["class"], "failed")
        self.assertIn("legacy", reason["detail"])

    def test_parked_lane_reports_its_recorded_reason(self) -> None:
        (self.lanes / "211.needs-attention").write_text("worktree-mismatch\n", encoding="utf-8")
        reason = self.classify()
        self.assertEqual(reason["class"], "parked")
        self.assertIn("worktree-mismatch", reason["detail"])

    def test_awaiting_adjudication(self) -> None:
        reason = self.classify(adjudicating=True)
        self.assertEqual(reason["class"], "awaiting-adjudication")

    def test_stale_reports_minutes_since_the_base_moved(self) -> None:
        reason = self.classify(fresh=False)
        self.assertEqual(reason["class"], "stale")
        self.assertIn("7 min ago", reason["detail"])

    def test_unknown_freshness_is_never_reported_as_stale(self) -> None:
        self.assertEqual(self.classify(fresh=None)["class"], "unknown-freshness")

    def test_a_running_refresh_outranks_a_stale_base(self) -> None:
        (self.daemon / "pr213.refreshing").write_text(f"{os.getpid()}\n", encoding="utf-8")
        self.assertEqual(self.classify(fresh=False)["class"], "refreshing")


class RenderAndSuppressionTestCase(unittest.TestCase):
    def rows(self, *, detail: str = "stale: main moved 7 min ago; needs a refresh lane",
             key: str = "stale", ready: bool = True) -> list[dict]:
        return [
            {"pr": 213, "head": HEAD, "issue": 211, "ready": ready, "blockers": [],
             "reason": {"class": "stale", "key": key, "detail": detail}},
            {"pr": 300, "head": OTHER, "issue": 299, "ready": False,
             "blockers": ["ci=failure"]},
        ]

    def test_compact_header_and_one_line_per_ready_pr(self) -> None:
        body = ready_report.render(self.rows(), 2, window_min=60,
                                   ts="2026-09-13T06:00:00Z", unexplained=0)
        lines = body.strip().splitlines()
        self.assertEqual(lines[0], "ready 1, merged-this-hour 2")
        self.assertTrue(lines[1].startswith("- PR 213 (issue 211, head aaaaaaaa)"))
        self.assertIn("unexplained 0", body)
        self.assertNotIn("PR 300", body)

    def test_unexplained_count_is_flagged_as_an_alarm(self) -> None:
        body = ready_report.render(self.rows(), 0, window_min=60,
                                   ts="2026-09-13T06:00:00Z", unexplained=1)
        self.assertIn("alarm", body)

    def test_empty_ready_set_still_reports(self) -> None:
        body = ready_report.render(self.rows(ready=False), 0, window_min=60,
                                   ts="2026-09-13T06:00:00Z", unexplained=0)
        self.assertIn("ready 0, merged-this-hour 0", body)
        self.assertIn("no ready-but-open PR", body)

    def test_signature_ignores_elapsed_timers(self) -> None:
        first = ready_report.signature(self.rows(detail="refreshing pid 1 lane 211, 3 min",
                                                 key="refreshing"))
        later = ready_report.signature(self.rows(detail="refreshing pid 1 lane 211, 63 min",
                                                key="refreshing"))
        self.assertEqual(first, later)

    def test_signature_changes_with_the_reason_class(self) -> None:
        self.assertNotEqual(ready_report.signature(self.rows(key="stale")),
                            ready_report.signature(self.rows(key="failed:build:x")))

    def test_suppressed_only_when_identical_and_nothing_merged(self) -> None:
        digest = ready_report.signature(self.rows())
        state = {"signature": digest, "posted_at": "2026-09-13T05:00:00Z"}
        post, why = ready_report.should_post(state, digest, 0, NOW)
        self.assertFalse(post, why)

    def test_a_merge_always_posts(self) -> None:
        digest = ready_report.signature(self.rows())
        state = {"signature": digest, "posted_at": "2026-09-13T05:00:00Z"}
        self.assertTrue(ready_report.should_post(state, digest, 1, NOW)[0])

    def test_a_changed_ready_set_posts(self) -> None:
        state = {"signature": "other", "posted_at": "2026-09-13T05:00:00Z"}
        self.assertTrue(ready_report.should_post(
            state, ready_report.signature(self.rows()), 0, NOW)[0])

    def test_six_hour_floor_forces_a_post(self) -> None:
        digest = ready_report.signature(self.rows())
        old = (NOW - timedelta(hours=ready_report.FORCE_AFTER_H)).strftime(
            "%Y-%m-%dT%H:%M:%SZ")
        post, why = ready_report.should_post({"signature": digest, "posted_at": old},
                                             digest, 0, NOW)
        self.assertTrue(post)
        self.assertIn("floor", why)

    def test_first_run_and_force_both_post(self) -> None:
        digest = ready_report.signature(self.rows())
        self.assertTrue(ready_report.should_post({}, digest, 0, NOW)[0])
        self.assertTrue(ready_report.should_post(
            {"signature": digest, "posted_at": "2026-09-13T05:59:00Z"},
            digest, 0, NOW, force=True)[0])

    def test_unreadable_state_posts_rather_than_swallowing_the_report(self) -> None:
        digest = ready_report.signature(self.rows())
        post, why = ready_report.should_post(
            {"signature": digest, "posted_at": "not a timestamp"}, digest, 0, NOW)
        self.assertTrue(post, why)


class TelemetryTestCase(unittest.TestCase):
    def test_latency_rows_carry_the_class_and_a_summary(self) -> None:
        rows = [{"pr": 213, "head": HEAD, "ready": True,
                 "reason": {"class": "stale", "key": "stale", "detail": "stale: ..."}},
                {"pr": 300, "head": OTHER, "ready": False}]
        out = ready_report.latency_rows(rows, 2, 0, "2026-09-13T06:00:00Z")
        self.assertEqual(len(out), 2)
        self.assertEqual(out[0]["event"], "ready")
        self.assertEqual(out[0]["class"], "stale")
        self.assertEqual(out[-1]["event"], "report")
        self.assertIn("merged 2", out[-1]["reason"])

    def test_latency_file_is_dated_per_run(self) -> None:
        path = ready_report.latency_path(Path("/repo"), NOW)
        self.assertEqual(path.name, "merge-latency-2026-09-13.jsonl")
        self.assertEqual(path.parent, Path("/repo/results/telemetry"))


class MainFlowTestCase(unittest.TestCase):
    """The whole pass, with GitHub and git stubbed: one mutation, then records."""

    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        root = Path(self._tmp.name)
        self.cache = root / "cache"
        self.repo = root / "repo"
        (self.repo / "results" / "telemetry").mkdir(parents=True)
        (self.cache / "watchdog" / "daemon").mkdir(parents=True)
        self._env = dict(os.environ)
        os.environ["MIPSTARRE_CACHE_ROOT"] = str(self.cache)
        os.environ["MIPSTARRE_REPO_ROOT"] = str(self.repo)

        now = datetime.now(timezone.utc)
        recent = (now - timedelta(minutes=10)).strftime("%Y-%m-%dT%H:%M:%SZ")
        old = (now - timedelta(hours=5)).strftime("%Y-%m-%dT%H:%M:%SZ")
        self.posted: list[tuple[int, str, str]] = []

        def fake_api(path: str, **_kwargs):
            if path.startswith("pulls?state=open"):
                return [pull(), pull(300, head=OTHER, branch="issue-299-other")]
            if path.startswith("pulls?state=closed"):
                return [{"updated_at": recent, "merged_at": recent},
                        {"updated_at": old, "merged_at": old}]
            if path.startswith("issues/"):
                return []
            raise AssertionError(f"unexpected API call: {path}")

        def fake_statuses(head: str):
            return statuses() if head == HEAD else statuses(ci="failure")

        self._saved = {
            "api": ready_report.gh_common.api,
            "latest_statuses": ready_report.gh_common.latest_statuses,
            "pr_reviews": ready_report.gh_common.pr_reviews,
            "ensure_pr_comment": ready_report.gh_common.ensure_pr_comment,
            "head_is_fresh": ready_report.head_is_fresh,
            "base_moved_minutes": ready_report.base_moved_minutes,
        }
        ready_report.gh_common.api = fake_api
        ready_report.gh_common.latest_statuses = fake_statuses
        ready_report.gh_common.pr_reviews = lambda number: [review()]
        ready_report.gh_common.ensure_pr_comment = (
            lambda number, marker, body: self.posted.append((number, marker, body)))
        ready_report.head_is_fresh = lambda repo_root, head: False
        ready_report.base_moved_minutes = lambda repo_root, now: 12

    def tearDown(self) -> None:
        ready_report.gh_common.api = self._saved["api"]
        ready_report.gh_common.latest_statuses = self._saved["latest_statuses"]
        ready_report.gh_common.pr_reviews = self._saved["pr_reviews"]
        ready_report.gh_common.ensure_pr_comment = self._saved["ensure_pr_comment"]
        ready_report.head_is_fresh = self._saved["head_is_fresh"]
        ready_report.base_moved_minutes = self._saved["base_moved_minutes"]
        os.environ.clear()
        os.environ.update(self._env)
        self._tmp.cleanup()

    @staticmethod
    def run_main(argv: list[str]) -> int:
        out, err = io.StringIO(), io.StringIO()
        with redirect_stdout(out), redirect_stderr(err):
            return ready_report.main(argv)

    def latency_files(self) -> list[Path]:
        return sorted((self.repo / "results" / "telemetry").glob("merge-latency-*.jsonl"))

    def test_dry_run_publishes_and_records_nothing(self) -> None:
        self.assertEqual(self.run_main(["--issue", "27", "--dry-run"]), 0)
        self.assertEqual(self.posted, [])
        self.assertEqual(self.latency_files(), [])
        self.assertFalse(ready_report.state_path(self.cache).exists())

    def test_one_comment_then_the_records(self) -> None:
        self.assertEqual(self.run_main(["--issue", "27"]), 0)
        self.assertEqual(len(self.posted), 1)
        number, marker, body = self.posted[0]
        self.assertEqual(number, 27)
        self.assertIn(ready_report.REPORT_MARKER, marker)
        self.assertTrue(body.startswith("ready 1, merged-this-hour 1"))
        self.assertIn("stale: main moved 12 min ago", body)
        rows = [json.loads(line) for line
                in self.latency_files()[0].read_text("utf-8").splitlines()]
        self.assertEqual([row["event"] for row in rows], ["ready", "report"])
        state = json.loads(ready_report.state_path(self.cache).read_text("utf-8"))
        self.assertEqual(state["ready"], 1)
        self.assertEqual(state["unexplained"], 0)

    def test_an_unchanged_hour_is_suppressed(self) -> None:
        self.assertEqual(self.run_main(["--issue", "27"]), 0)
        self.assertEqual(self.run_main(["--issue", "27"]), 0)
        # The second pass sees the same ready set; the merge count is what
        # forces it, so drop the merges and check suppression holds.
        original = ready_report.merged_in_window
        ready_report.merged_in_window = lambda since: 0
        try:
            self.assertEqual(self.run_main(["--issue", "27"]), 0)
        finally:
            ready_report.merged_in_window = original
        self.assertEqual(len(self.posted), 2)

    def test_a_failed_post_writes_no_record(self) -> None:
        def boom(number, marker, body):
            raise ready_report.LayerError("gh api failed: 502")

        ready_report.gh_common.ensure_pr_comment = boom
        self.assertEqual(self.run_main(["--issue", "27"]), 2)
        self.assertEqual(self.latency_files(), [])
        self.assertFalse(ready_report.state_path(self.cache).exists())


if __name__ == "__main__":
    unittest.main()
