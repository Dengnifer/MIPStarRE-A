#!/usr/bin/env python3
"""Tests for the soft landing: classification, the manifest, the resume plan.

Nothing here starts codex, reaches GitHub or signals a real process.  The
process table is a fixture with fake pids, the registry rows are fixture spool
files under a temporary cache root, and the resume plan is ASSERTED as commands
— `resume_exec` is given a recording runner, so not one command is run.
"""

from __future__ import annotations

import json
import os
import signal
import sys
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
BIN_DIR = REPO_ROOT / "local" / "bin"
TOOLS = REPO_ROOT / "results" / "telemetry" / "owner-tools"
sys.path.insert(0, str(BIN_DIR))

import pause_landing as pl  # noqa: E402


def text(path: Path) -> str:
    return path.read_text(encoding="utf-8")


class FakeProcesses(pl.Processes):
    """A process table a test owns: fake pids, recorded signals, no sleeping."""

    def __init__(self, table: dict[int, str], *, ignores_term: tuple[int, ...] = (),
                 started: dict[int, float] | None = None) -> None:
        self.table = dict(table)
        self.ignores_term = set(ignores_term)
        self.started = dict(started or {})
        self.signals: list[tuple[int, int]] = []
        self.slept: list[float] = []

    def alive(self, pid: int) -> bool:
        return pid in self.table

    def cmdline(self, pid: int) -> str:
        return self.table.get(pid, "")

    def started_at(self, pid: int):
        return self.started.get(pid)

    def pids(self) -> list[int]:
        return sorted(self.table)

    def signal(self, pid: int, sig: int) -> bool:
        self.signals.append((pid, sig))
        if sig == signal.SIGKILL or (sig == signal.SIGTERM and pid not in self.ignores_term):
            self.table.pop(pid, None)
        return True

    def sleep(self, seconds: float) -> None:
        self.slept.append(seconds)


class LandingTestCase(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        root = Path(self._tmp.name)
        self.cache = root / "cache"
        self.checkout = root / "checkout"
        (self.cache / "watchdog" / "capacity" / "spool").mkdir(parents=True)
        (self.cache / "watchdog" / "daemon").mkdir(parents=True)
        (self.cache / "watchdog" / "lanes").mkdir(parents=True)
        (self.cache / "sessions").mkdir(parents=True)
        self.checkout.mkdir()
        self._env = dict(os.environ)
        os.environ["MIPSTARRE_CACHE_ROOT"] = str(self.cache)
        os.environ["MIPSTARRE_CHECKOUT"] = str(self.checkout)
        self.limits = pl.thresholds(REPO_ROOT)
        self.state = self.cache / "watchdog" / "pause-state.json"

    def tearDown(self) -> None:
        os.environ.clear()
        os.environ.update(self._env)
        self._tmp.cleanup()

    # -- fixtures --------------------------------------------------------

    def spool(self, name: str, role: str, pid: int, *, minutes: int = 0,
              worktree: str = "/w", issue: str = "1", pr: str | None = None,
              state: str = "running") -> None:
        spooled = "2026-09-14T00:00:00+0000"
        row = {"state": state, "name": name, "role": role, "issue": issue, "pr": pr,
               "worktree": worktree, "branch": f"issue-{issue}-x", "account": "second",
               "pid": pid, "spooled_at": spooled, "attempt": 1, "max_attempts": 5}
        (self.cache / "watchdog" / "capacity" / "spool" / f"{name}.json").write_text(
            json.dumps(row), encoding="utf-8")
        self._now = pl._parse_ts(spooled)

    def capture(self, name: str, thread: str) -> None:
        (self.cache / "sessions" / f"{name}.jsonl").write_text(
            json.dumps({"type": "thread.started", "thread_id": thread}) + "\n",
            encoding="utf-8")

    def at(self, minutes: int) -> float:
        return self._now + minutes * 60


# ---------------------------------------------------------------------------
# Requirement 2 — age-based classification, thresholds from the policy
# ---------------------------------------------------------------------------

class ThresholdTestCase(unittest.TestCase):
    def test_the_policy_file_is_the_home_of_every_threshold(self) -> None:
        policy = json.loads(text(REPO_ROOT / "local" / "capacity-policy.json"))
        self.assertIn("landing", policy, "local/capacity-policy.json must carry them")
        limits = pl.thresholds(REPO_ROOT)
        self.assertEqual(limits["source"], str(pl.policy_path(REPO_ROOT)))
        for key in ("young_max_min", "cutoff_lead_min"):
            self.assertEqual(limits[key], policy["landing"][key])
        for key in ("landing_lead_s", "last_call_s", "grace_s"):
            self.assertEqual(limits["phases"][key], policy["landing"]["phases"][key])

    def test_a_missing_policy_falls_back_to_the_documented_defaults(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            limits = pl.thresholds(Path(directory))
        self.assertEqual(limits["young_max_min"], pl.DEFAULTS["young_max_min"])
        self.assertIn("unreadable", limits["source"])

    def test_an_out_of_order_policy_is_corrected_not_obeyed(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "local").mkdir()
            (root / "local" / "capacity-policy.json").write_text(json.dumps(
                {"landing": {"phases": {"landing_lead_s": 10, "last_call_s": 300,
                                        "grace_s": -1}}}), encoding="utf-8")
            limits = pl.thresholds(root)
        self.assertGreater(limits["phases"]["landing_lead_s"],
                           limits["phases"]["last_call_s"],
                           "the landing must come before the last call")
        self.assertEqual(limits["phases"]["grace_s"], pl.DEFAULTS["phases"]["grace_s"])


class ClassifyTestCase(LandingTestCase):
    def rows(self, processes: FakeProcesses, minutes: int) -> list[dict]:
        return pl.classified(self.cache, processes, self.at(minutes), self.limits)

    def test_a_young_session_of_any_role_stops_at_once(self) -> None:
        self.spool("prover-1-a", "prover", 101)
        self.spool("reviewer-pr9-a", "reviewer", 102, pr="9")
        self.capture("prover-1-a", "thread-young")
        table = {101: "bash dispatch.sh prover-1-a", 102: "bash dispatch.sh reviewer-pr9-a"}
        rows = self.rows(FakeProcesses(table), self.limits["young_max_min"] - 1)
        self.assertEqual({row["name"]: row["action"] for row in rows},
                         {"prover-1-a": "stop-now", "reviewer-pr9-a": "stop-now"})
        self.assertTrue(all(row["class"] == "young" for row in rows))

    def test_a_mature_reviewer_runs_to_the_last_call_and_is_restarted(self) -> None:
        self.spool("reviewer-pr9-a", "reviewer", 102, pr="9")
        self.capture("reviewer-pr9-a", "thread-review")
        row, = self.rows(FakeProcesses({102: "bash dispatch.sh reviewer-pr9-a"}),
                         self.limits["young_max_min"] + 30)
        self.assertEqual(row["class"], "mature-finish")
        self.assertEqual(row["action"], "stop-at-last-call")
        self.assertEqual(row["resume"], "restart")
        self.assertFalse(row["resumable"], "a review is restarted, never resumed")

    def test_a_mature_prover_is_checkpointed_and_resumable(self) -> None:
        self.spool("prover-1-a", "prover", 101, worktree="/w/issue-1-x")
        self.capture("prover-1-a", "thread-prover")
        row, = self.rows(FakeProcesses({101: "bash dispatch.sh prover-1-a"}),
                         self.limits["young_max_min"] + 30)
        self.assertEqual(row["class"], "checkpoint")
        self.assertEqual(row["action"], "stop-at-last-call")
        self.assertEqual(row["resume"], "thread")
        self.assertTrue(row["resumable"])
        self.assertEqual(row["thread_id"], "thread-prover")
        self.assertEqual(row["worktree"], "/w/issue-1-x")

    def test_a_checkpointed_session_without_a_thread_id_is_not_resumable(self) -> None:
        self.spool("prover-2-a", "prover", 103)
        row, = self.rows(FakeProcesses({103: "bash dispatch.sh prover-2-a"}),
                         self.limits["young_max_min"] + 30)
        self.assertFalse(row["resumable"])
        self.assertEqual(row["resume"], "restart")
        self.assertIn("no thread id", row["reason"])

    def test_a_dead_pid_and_a_finished_spool_row_are_not_live(self) -> None:
        self.spool("prover-1-a", "prover", 101)
        self.spool("prover-3-a", "prover", 199, state="done")
        rows = pl.live_sessions(self.cache, FakeProcesses({}), self.at(1))
        self.assertEqual(rows, [])
        rows = pl.live_sessions(self.cache, FakeProcesses({199: "x"}), self.at(1))
        self.assertEqual(rows, [], "a spool row that is not 'running' is not a session")


# ---------------------------------------------------------------------------
# Requirement 2 — stopping: SIGTERM, then SIGKILL after the recorded grace
# ---------------------------------------------------------------------------

class StopTestCase(LandingTestCase):
    def test_the_landing_phase_stops_the_young_only(self) -> None:
        self.spool("prover-young", "prover", 101)
        self.spool("prover-old", "prover", 102)
        self.capture("prover-old", "t-old")
        processes = FakeProcesses({101: "bash dispatch.sh prover-young",
                                   102: "bash dispatch.sh prover-old"})
        sessions = [pl.classify(row, self.limits) for row in [
            {"name": "prover-young", "role": "prover", "pid": 101, "elapsed_min": 0},
            {"name": "prover-old", "role": "prover", "pid": 102, "elapsed_min": 45,
             "thread_id": "t-old"}]]
        landed = pl.land(sessions, "now", self.limits, processes)
        self.assertEqual([(pid, sig) for pid, sig in processes.signals],
                         [(101, signal.SIGTERM)])
        self.assertEqual([row["signal"] for row in landed], ["TERM", "pending"])
        self.assertIn(102, processes.table, "the mature session keeps running")

    def test_the_last_call_stops_what_is_left_and_escalates_after_the_grace(self) -> None:
        processes = FakeProcesses({102: "bash dispatch.sh prover-old"}, ignores_term=(102,))
        sessions = [pl.classify({"name": "prover-old", "role": "prover", "pid": 102,
                                 "elapsed_min": 45, "thread_id": "t"}, self.limits)]
        landed = pl.land(sessions, "last", self.limits, processes)
        self.assertEqual(processes.signals, [(102, signal.SIGTERM), (102, signal.SIGKILL)])
        self.assertEqual(processes.slept, [self.limits["phases"]["grace_s"]])
        self.assertEqual(landed[0]["signal"], "KILL")

    def test_a_recycled_pid_is_never_signalled(self) -> None:
        processes = FakeProcesses({77: "/usr/bin/someone-elses-job --forever"})
        sessions = [pl.classify({"name": "prover-old", "role": "prover", "pid": 77,
                                 "elapsed_min": 45, "thread_id": "t"}, self.limits)]
        landed = pl.land(sessions, "last", self.limits, processes)
        self.assertEqual(processes.signals, [])
        self.assertEqual(landed[0]["signal"], "not-ours")

    def test_a_dry_run_signals_nothing(self) -> None:
        processes = FakeProcesses({101: "bash dispatch.sh prover-young"})
        sessions = [pl.classify({"name": "prover-young", "role": "prover", "pid": 101,
                                 "elapsed_min": 0}, self.limits)]
        pl.land(sessions, "now", self.limits, processes, dry_run=True)
        self.assertEqual(processes.signals, [])
        self.assertEqual(processes.slept, [])


# ---------------------------------------------------------------------------
# Requirement 3 — the manifest, and its round trip through pause-state.json
# ---------------------------------------------------------------------------

class ManifestTestCase(LandingTestCase):
    def test_the_manifest_records_lanes_sessions_and_thresholds(self) -> None:
        self.spool("prover-7-a", "prover", 101, issue="7", worktree="/w/issue-7-x")
        self.capture("prover-7-a", "t-7")
        processes = FakeProcesses({101: "bash dispatch.sh prover-7-a",
                                   202: "bash /home/x/local/bin/lane.sh 7 slug prover"})
        (self.cache / "watchdog" / "lanes" / "7.ci.log").write_text("x", encoding="utf-8")
        manifest = pl.build_manifest(
            self.cache, processes, statuses=lambda sha: {pl.CI_STATUS: "success"},
            now=self.at(30), limits=self.limits, cutoff_at="2026-09-14T00:00:00Z",
            checkout=self.checkout)
        self.assertEqual(manifest["schema"], pl.SCHEMA)
        self.assertEqual(manifest["cutoff_at"], "2026-09-14T00:00:00Z")
        self.assertEqual(manifest["thresholds"]["young_max_min"],
                         self.limits["young_max_min"])
        lane, = manifest["lanes"]
        self.assertEqual((lane["issue"], lane["slug"], lane["step"], lane["pid"]),
                         ("7", "slug", "ci", 202))
        self.assertEqual(lane["branch"], "issue-7-slug")
        self.assertEqual(lane["statuses"], {pl.CI_STATUS: "success"})
        session, = manifest["sessions"]
        self.assertEqual(session["thread_id"], "t-7")
        self.assertTrue(session["resumable"])
        self.assertEqual(session["elapsed_min"], 30)

    def test_writing_the_manifest_keeps_the_rest_of_the_pause_record(self) -> None:
        self.state.write_text(json.dumps({"caps": {"primary": 5}, "speed": "fast"}),
                              encoding="utf-8")
        pl.write_manifest(self.state, {"schema": pl.SCHEMA, "lanes": [], "sessions": []})
        doc = json.loads(text(self.state))
        self.assertEqual(doc["caps"], {"primary": 5})
        self.assertEqual(doc["speed"], "fast")
        self.assertEqual(pl.read_manifest(self.state)["schema"], pl.SCHEMA)

    def test_a_record_without_a_landing_reads_back_as_empty(self) -> None:
        self.state.write_text(json.dumps({"caps": {}}), encoding="utf-8")
        self.assertEqual(pl.read_manifest(self.state), {})
        self.assertEqual(pl.read_manifest(self.cache / "nowhere.json"), {})

    def test_only_the_markers_the_landing_caused_are_recorded(self) -> None:
        daemon = self.cache / "watchdog" / "daemon"
        (daemon / "pr11.failed").write_text("old failure\n", encoding="utf-8")
        before = pl.failed_markers(self.cache)
        (daemon / "pr12.failed").write_text("exited 143\n", encoding="utf-8")
        (daemon / "notamarker").write_text("x", encoding="utf-8")
        new = pl.new_failed_markers(before, self.cache)
        self.assertEqual([row["pr"] for row in new], ["12"])
        self.assertEqual(new[0]["first_line"], "exited 143")
        self.assertTrue(new[0]["created_by_landing"])

    def test_the_lane_step_is_read_from_the_markers_lane_sh_leaves(self) -> None:
        lanes = self.cache / "watchdog" / "lanes"
        self.assertEqual(pl.lane_step(lanes, "5"), "warm")
        for marker, step in ((".dispatch.log", "dispatch"), (".pr.md", "publish"),
                             (".ci.log", "ci"), (".review.log", "review"),
                             (".done", "done")):
            (lanes / f"5{marker}").write_text("x", encoding="utf-8")
            self.assertEqual(pl.lane_step(lanes, "5"), step)


# ---------------------------------------------------------------------------
# Requirement 4 — the step skipping and the resume command plan
# ---------------------------------------------------------------------------

class StepSkippingTestCase(unittest.TestCase):
    def lane(self, **over) -> dict:
        row = {"issue": "7", "slug": "slug", "role": "prover", "branch": "issue-7-slug",
               "worktree": "/w/issue-7-slug", "head": "abc", "head_now": "abc",
               "step": "ci", "statuses": {}}
        row.update(over)
        return row

    def test_both_statuses_success_on_an_unchanged_head_runs_nothing(self) -> None:
        self.assertEqual(pl.lane_resume_step(self.lane(statuses={
            pl.CI_STATUS: "success", pl.REVIEW_STATUS: "success"})), "done")

    def test_ci_success_skips_ci_and_resumes_at_the_review(self) -> None:
        self.assertEqual(pl.lane_resume_step(self.lane(statuses={
            pl.CI_STATUS: "success"})), "review")

    def test_a_pending_ci_resumes_at_ci_not_at_the_review(self) -> None:
        self.assertEqual(pl.lane_resume_step(self.lane(statuses={
            pl.CI_STATUS: "pending", pl.REVIEW_STATUS: "success"})), "ci")

    def test_a_head_that_moved_resumes_the_whole_lane(self) -> None:
        self.assertEqual(pl.lane_resume_step(self.lane(head_now="def", statuses={
            pl.CI_STATUS: "success", pl.REVIEW_STATUS: "success"})), "dispatch")

    def test_an_unreadable_head_resumes_the_whole_lane(self) -> None:
        self.assertEqual(pl.lane_resume_step(self.lane(head=None, head_now=None)),
                         "dispatch")

    def test_a_lane_parked_before_ci_publishes_first(self) -> None:
        self.assertEqual(pl.lane_resume_step(self.lane(step="dispatch")), "publish")

    def test_a_finished_lane_is_left_alone(self) -> None:
        self.assertEqual(pl.lane_resume_step(self.lane(step="done")), "done")

    def test_every_resume_step_is_one_lane_sh_accepts(self) -> None:
        body = text(BIN_DIR / "lane.sh")
        block = body.split("case \"$LANE_RESUME_STEP\" in", 1)[1].split("esac", 1)[0]
        for step in ("dispatch", "publish", "ci", "review"):
            self.assertIn(step, block, f"lane.sh must accept LANE_RESUME_STEP={step}")


class ResumePlanTestCase(LandingTestCase):
    def manifest(self) -> dict:
        return {
            "schema": pl.SCHEMA,
            "lanes": [
                {"issue": "7", "slug": "slug", "role": "prover", "branch": "issue-7-slug",
                 "worktree": "/w/issue-7-slug", "head": "abc", "head_now": "abc",
                 "step": "ci", "statuses": {pl.CI_STATUS: "success"}},
                {"issue": "8", "slug": "other", "role": "orc", "branch": "issue-8-other",
                 "worktree": "/w/issue-8-other", "head": "def", "head_now": "def",
                 "step": "ci", "statuses": {pl.CI_STATUS: "success",
                                            pl.REVIEW_STATUS: "success"}},
            ],
            "sessions": [
                {"name": "prover-7-a", "role": "prover", "issue": "7", "pr": None,
                 "worktree": "/w/issue-7-slug", "thread_id": "t-7", "resume": "thread",
                 "resumable": True, "signal": "TERM"},
                {"name": "reviewer-pr9-a", "role": "reviewer", "issue": "pr9", "pr": "9",
                 "worktree": "/w/issue-9-z", "thread_id": "t-9", "resume": "restart",
                 "resumable": False, "signal": "KILL"},
                {"name": "prover-8-a", "role": "prover", "issue": "8", "pr": None,
                 "worktree": "/w/issue-8-other", "thread_id": "t-8", "resume": "thread",
                 "resumable": True, "signal": "pending"},
            ],
            "failed_markers": [
                {"path": str(self.cache / "watchdog/daemon/pr12.failed"), "pr": "12",
                 "created_by_landing": True, "first_line": "exited 143"},
                {"path": str(self.cache / "watchdog/daemon/pr11.failed"), "pr": "11",
                 "created_by_landing": False, "first_line": "a real failure"},
            ],
        }

    def test_the_plan_names_the_right_command_for_every_item(self) -> None:
        plan = pl.resume_plan(self.manifest(), self.checkout)
        kinds = [(entry["kind"], entry.get("issue") or entry.get("name") or entry.get("pr"))
                 for entry in plan]
        self.assertEqual(kinds, [("clear-marker", "12"), ("lane", "7"), ("lane", "8"),
                                 ("session", "prover-7-a"), ("session", "reviewer-pr9-a")])

    def test_a_marker_the_landing_did_not_create_is_left_alone(self) -> None:
        plan = pl.resume_plan(self.manifest(), self.checkout)
        cleared = [entry["pr"] for entry in plan if entry["kind"] == "clear-marker"]
        self.assertEqual(cleared, ["12"],
                         "a marker the landing did not cause is a real verdict")

    def test_a_lane_resumes_at_its_step_and_a_finished_one_runs_nothing(self) -> None:
        plan = {entry.get("issue"): entry
                for entry in pl.resume_plan(self.manifest(), self.checkout)
                if entry["kind"] == "lane"}
        self.assertEqual(plan["7"]["argv"], [
            "env", "LANE_RESUME_STEP=review",
            str(self.checkout / "local" / "bin" / "lane.sh"), "7", "slug", "prover"])
        self.assertIsNone(plan["8"]["argv"])
        self.assertIn("both summary statuses", plan["8"]["why"])

    def test_a_checkpointed_prover_is_resumed_on_its_own_thread(self) -> None:
        entry, = [row for row in pl.resume_plan(self.manifest(), self.checkout)
                  if row.get("name") == "prover-7-a"]
        self.assertEqual(entry["argv"], [
            str(self.checkout / "local" / "bin" / "dispatch.sh"),
            "--role", "prover", "--issue", "7", "--sandbox", "workspace-write",
            "--worktree", "/w/issue-7-slug", "--resume", "t-7", "--",
            pl.CONTINUE_PROMPT])

    def test_the_continue_prompt_says_worktree_and_milestone_commits(self) -> None:
        self.assertIn("worktree", pl.CONTINUE_PROMPT)
        self.assertIn("continue from that state", pl.CONTINUE_PROMPT)
        self.assertIn("Commit each proved lemma", pl.CONTINUE_PROMPT)

    def test_a_reviewer_is_restarted_from_scratch_not_resumed(self) -> None:
        entry, = [row for row in pl.resume_plan(self.manifest(), self.checkout)
                  if row.get("name") == "reviewer-pr9-a"]
        self.assertEqual(entry["argv"],
                         [str(self.checkout / "local" / "bin" / "review.sh"), "9"])
        self.assertNotIn("--resume", entry["argv"])

    def test_a_session_that_was_never_stopped_is_not_relaunched(self) -> None:
        names = [row.get("name") for row in pl.resume_plan(self.manifest(), self.checkout)
                 if row["kind"] == "session"]
        self.assertNotIn("prover-8-a", names,
                         "a session the landing did not signal is still running")

    def test_resume_exec_runs_the_planned_commands_and_nothing_else(self) -> None:
        marker = self.cache / "watchdog" / "daemon" / "pr12.failed"
        marker.write_text("exited 143\n", encoding="utf-8")
        launched: list[list[str]] = []

        def runner(argv):
            launched.append(argv)
            return 4242

        plan = pl.resume_plan(self.manifest(), self.checkout)
        done = pl.resume_exec(plan, runner=runner)
        self.assertFalse(marker.exists(), "the recorded marker is cleared")
        self.assertEqual(launched, [entry["argv"] for entry in plan if entry["argv"]
                                    and entry["kind"] != "clear-marker"])
        self.assertEqual(sum(1 for row in done if row["done"].startswith("launched")), 3)

    def test_resume_exec_dry_run_touches_nothing(self) -> None:
        marker = self.cache / "watchdog" / "daemon" / "pr12.failed"
        marker.write_text("exited 143\n", encoding="utf-8")
        launched: list[list[str]] = []
        done = pl.resume_exec(pl.resume_plan(self.manifest(), self.checkout),
                              runner=lambda argv: launched.append(argv), dry_run=True)
        self.assertTrue(marker.exists())
        self.assertEqual(launched, [])
        self.assertEqual({row["done"] for row in done},
                         {"would clear", "would launch", "nothing to run"})

    def test_the_plan_renders_as_commands_a_human_can_read(self) -> None:
        rendered = pl.format_plan(pl.resume_plan(self.manifest(), self.checkout))
        self.assertIn("LANE_RESUME_STEP=review", rendered)
        self.assertIn("--resume t-7", rendered)
        self.assertIn("# session reviewer-pr9-a (reviewer)", rendered)


# ---------------------------------------------------------------------------
# Requirements 1, 5 and 6 — the owner words, the prompt rule, the documents
# ---------------------------------------------------------------------------

class OwnerWordsTestCase(unittest.TestCase):
    def test_the_cutoff_word_stops_admission_and_signals_nothing(self) -> None:
        body = text(TOOLS / "owner-pause.sh")
        self.assertIn("--cutoff) CUTOFF=1", body)
        block = body.split("# --- the cutoff word", 1)[1].split("\nfi\n", 1)[0]
        self.assertIn("stop_admission", block)
        self.assertIn("write_state cutoff", block)
        for forbidden in ("kill ", "pgrep", "install-crons.sh", "capacityd.stop"):
            self.assertNotIn(forbidden, block,
                             f"the cutoff word must not reach '{forbidden}'")

    def test_the_pause_classifies_before_it_sweeps(self) -> None:
        body = text(TOOLS / "owner-pause.sh")
        land = body.index('land --phase now')
        last = body.index('land --phase last')
        sweep = body.index("PATTERNS='")
        self.assertLess(land, last, "the young are stopped before the last call")
        self.assertLess(last, sweep, "the anchored sweep is the leftover pass")

    def test_the_kill_table_is_still_anchored(self) -> None:
        table = text(TOOLS / "owner-pause.sh").split("PATTERNS='", 1)[1].split("'", 1)[0]
        for line in table.splitlines():
            if line.strip():
                self.assertTrue(line.startswith("^"), f"unanchored pattern: {line!r}")

    def test_no_landing_threshold_is_written_into_the_pause_script(self) -> None:
        body = text(TOOLS / "owner-pause.sh")
        for key in ("landing_lead_s", "last_call_s", "grace_s", "young_max_min"):
            self.assertIn(f"pl_get {key}", body,
                          f"{key} must be read from the policy, never written here")

    def test_the_dry_run_prints_the_rule_and_the_thresholds(self) -> None:
        body = text(TOOLS / "owner-pause.sh")
        self.assertIn("landing_rule", body)
        self.assertIn("THRESHOLD_SRC", body)
        self.assertIn("cutoff_plan", body)

    def test_the_resume_puts_the_work_back_after_the_postconditions(self) -> None:
        body = text(TOOLS / "owner-resume.sh")
        gate = body.index('if [ "$RC" -ne 0 ]; then')
        work = body.index("resume-exec")
        self.assertLess(gate, work, "no lane is relaunched into an unhealthy run")
        self.assertLess(work, body.index("tmux has-session", gate))
        self.assertIn("--no-work) WORK=0", body)

    def test_the_prover_prompt_and_persona_carry_the_milestone_rule(self) -> None:
        dispatch = text(BIN_DIR / "dispatch.sh")
        block = dispatch.split("case \"$ROLE\" in\n    prover|mathfix", 1)[1]
        self.assertIn("Commit each proved lemma", block)
        self.assertIn("BEFORE you start the next one", block)
        persona = text(REPO_ROOT / "local" / "personas" / "prover.md")
        self.assertIn("Commit at every milestone", persona)

    def test_the_protocol_and_the_readme_describe_both_words(self) -> None:
        protocol = text(REPO_ROOT / "local" / "protocols" / "full-speed-mode.md")
        readme = text(TOOLS / "README.md")
        for document in (protocol, readme):
            self.assertIn("--cutoff", document)
            self.assertIn("pause_landing.py", document)
            self.assertIn("local-review/summary", document)


if __name__ == "__main__":
    unittest.main()
