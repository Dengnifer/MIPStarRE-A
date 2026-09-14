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
import re
import signal
import subprocess
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
                 started: dict[int, float] | None = None,
                 parents: dict[int, int] | None = None,
                 environs: dict[int, dict[str, str]] | None = None,
                 uids: dict[int, int] | None = None) -> None:
        self.table = dict(table)
        self.ignores_term = set(ignores_term)
        self.started = dict(started or {})
        self.parents = dict(parents or {})
        self.environs = dict(environs or {})
        self.uids = dict(uids or {})
        self.signals: list[tuple[int, int]] = []
        self.slept: list[float] = []

    def alive(self, pid: int) -> bool:
        return pid in self.table

    def cmdline(self, pid: int) -> str:
        return self.table.get(pid, "")

    def started_at(self, pid: int):
        return self.started.get(pid)

    def ppid(self, pid: int):
        return self.parents.get(pid)

    def environ(self, pid: int) -> dict[str, str]:
        return dict(self.environs.get(pid, {}))

    def owner_uid(self, pid: int):
        # Ours unless a test says otherwise: /proc is not consulted for a fake pid.
        return self.uids.get(pid, os.getuid())

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

    def test_an_unreadable_command_line_is_spared_not_signalled(self) -> None:
        # /proc/<pid>/cmdline reads back empty for a zombie, for another user's
        # process under hidepid, and in a plain race.  The old guard treated that
        # as permission to signal: `cmd` was falsy, so the whole check was skipped.
        processes = FakeProcesses({999999: ""})
        sessions = [pl.classify({"name": "prover-old", "role": "prover", "pid": 999999,
                                 "elapsed_min": 45, "thread_id": "t"}, self.limits)]
        landed = pl.land(sessions, "last", self.limits, processes)
        self.assertEqual(processes.signals, [], "an unverified pid is never signalled")
        self.assertEqual(landed[0]["signal"], "not-ours")

    def test_a_different_dispatch_on_a_recycled_pid_is_not_ours(self) -> None:
        # `"dispatch.sh" in cmd` says the pid is *a* dispatcher, never that it is
        # THIS session's: ghz runs codex for at least seven other users.
        processes = FakeProcesses({
            77: "bash /home/other/local/bin/dispatch.sh --role reviewer --issue pr544 "
                "--worktree /home/other/.worktrees/issue-544-x"})
        sessions = [pl.classify({"name": "prover-7-a", "role": "prover", "issue": "7",
                                 "worktree": "/w/issue-7-slug", "pid": 77,
                                 "elapsed_min": 45, "thread_id": "t"}, self.limits)]
        landed = pl.land(sessions, "last", self.limits, processes)
        self.assertEqual(processes.signals, [])
        self.assertEqual(landed[0]["signal"], "not-ours")

    def test_the_recorded_worktree_identifies_a_real_dispatcher(self) -> None:
        # dispatch.sh mints the session name itself, so the command line does not
        # carry it; the worktree and the role/issue pair are what it does carry.
        cmd = ("bash /p/local/bin/dispatch.sh --role prover --issue 7 "
               "--worktree /w/issue-7-slug --sandbox workspace-write")
        processes = FakeProcesses({101: cmd})
        sessions = [pl.classify({"name": "prover-7-a", "role": "prover", "issue": "7",
                                 "worktree": "/w/issue-7-slug", "pid": 101,
                                 "elapsed_min": 45, "thread_id": "t"}, self.limits)]
        landed = pl.land(sessions, "last", self.limits, processes)
        self.assertEqual(landed[0]["signal"], "TERM")

    def test_the_codex_child_is_signalled_with_its_dispatcher(self) -> None:
        # The spool records dispatch.sh's pid, and its `trap 'exit 143' TERM` is
        # deferred while `codex … | tee` is the foreground job: a TERM to the
        # wrapper alone does nothing and codex keeps spending quota.
        processes = FakeProcesses(
            {101: "bash /p/local/bin/dispatch.sh --role prover --issue 7 --worktree /w",
             501: "codex exec --json -C /w", 502: "tee /c/sessions/prover-7-a.jsonl"},
            parents={501: 101, 502: 101})
        sessions = [pl.classify({"name": "prover-7-a", "role": "prover", "issue": "7",
                                 "worktree": "/w", "pid": 101, "elapsed_min": 45,
                                 "thread_id": "t"}, self.limits)]
        pl.land(sessions, "last", self.limits, processes)
        self.assertIn((501, signal.SIGTERM), processes.signals,
                      "the codex process must be stopped, not only its wrapper")
        self.assertIn((101, signal.SIGTERM), processes.signals)

    def test_the_grace_is_slept_once_for_the_phase_not_once_per_session(self) -> None:
        # grace_s x sessions is what made the landing run past the owner's
        # deadline: 17 sessions x 20 s is 340 s inside a 90 s window.
        table = {}
        sessions = []
        for index in range(17):
            pid = 200 + index
            table[pid] = (f"bash /p/local/bin/dispatch.sh --role prover --issue {index} "
                          f"--worktree /w/issue-{index}-x")
            sessions.append(pl.classify(
                {"name": f"prover-{index}-a", "role": "prover", "issue": str(index),
                 "worktree": f"/w/issue-{index}-x", "pid": pid, "elapsed_min": 45,
                 "thread_id": "t"}, self.limits))
        processes = FakeProcesses(table, ignores_term=tuple(table))
        landed = pl.land(sessions, "last", self.limits, processes)
        self.assertEqual(processes.slept, [self.limits["phases"]["grace_s"]],
                         "one grace for the whole phase, whatever the session count")
        self.assertEqual(len([row for row in landed if row["signal"] == "KILL"]), 17)

    def test_the_last_call_also_stops_a_row_an_earlier_phase_missed(self) -> None:
        # `land --phase now` can die (a corrupt record, a /proc permission error)
        # with young rows still `pending`.  If the last call only looked at
        # `stop-at-last-call`, those rows would never be stopped OR recorded, and
        # the anchored sweep would hard-kill them behind the manifest's back.
        processes = FakeProcesses(
            {101: "bash /p/local/bin/dispatch.sh --role prover --issue 7 --worktree /w"})
        sessions = [pl.classify({"name": "prover-young", "role": "prover", "issue": "7",
                                 "worktree": "/w", "pid": 101, "elapsed_min": 0},
                                self.limits)]
        self.assertEqual(sessions[0]["action"], "stop-now")
        landed = pl.land(sessions, "last", self.limits, processes)
        self.assertEqual(landed[0]["signal"], "TERM")

    def test_a_killed_wrapper_has_its_slot_claim_and_spool_row_freed(self) -> None:
        # A SIGKILL skips dispatch.sh's EXIT cleanup, and the leaked account slot
        # is counted by account_router.reserve: the resumed run would admit fewer
        # workers than its restored cap until the janitor expired it.
        slot = self.cache / "accounts" / "second" / "101"
        slot.parent.mkdir(parents=True)
        slot.write_text("x", encoding="utf-8")
        claim = self.cache / "locks" / "branch-issue-7-slug.claim"
        claim.mkdir(parents=True)
        (claim / "pid").write_text("101\n", encoding="utf-8")
        (claim / "session").write_text("prover-7-a\n", encoding="utf-8")
        spool = self.cache / "watchdog" / "capacity" / "spool" / "prover-7-a.json"
        spool.write_text("{}", encoding="utf-8")
        processes = FakeProcesses(
            {101: "bash /p/local/bin/dispatch.sh --role prover --issue 7 --worktree /w"},
            ignores_term=(101,))
        sessions = [pl.classify({"name": "prover-7-a", "role": "prover", "issue": "7",
                                 "worktree": "/w", "pid": 101, "elapsed_min": 45,
                                 "thread_id": "t", "spool": str(spool)}, self.limits)]
        landed = pl.land(sessions, "last", self.limits, processes, root=self.cache)
        self.assertEqual(landed[0]["signal"], "KILL")
        self.assertFalse(slot.exists(), "the account slot is freed")
        self.assertFalse(claim.exists(), "the branch claim is released")
        self.assertFalse(spool.exists(), "the spool row cannot outlive the session")

    def test_a_session_that_stops_on_term_keeps_its_locks(self) -> None:
        # A wrapper that took the TERM runs its own cleanup; taking its locks
        # apart from the outside would race with it.
        slot = self.cache / "accounts" / "second" / "101"
        slot.parent.mkdir(parents=True)
        slot.write_text("x", encoding="utf-8")
        processes = FakeProcesses(
            {101: "bash /p/local/bin/dispatch.sh --role prover --issue 7 --worktree /w"})
        sessions = [pl.classify({"name": "prover-7-a", "role": "prover", "issue": "7",
                                 "worktree": "/w", "pid": 101, "elapsed_min": 45,
                                 "thread_id": "t"}, self.limits)]
        landed = pl.land(sessions, "last", self.limits, processes, root=self.cache)
        self.assertEqual(landed[0]["signal"], "TERM")
        self.assertTrue(slot.exists(), "cleanup belongs to the process that can run it")

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

    def test_another_users_lane_is_not_this_runs_work(self) -> None:
        # `pids()` walks all of /proc and ghz hosts at least seven other users.
        # A stranger's lane.sh recorded here would be relaunched by the resume.
        processes = FakeProcesses({202: "bash /home/other/lane.sh 7 slug prover"},
                                  uids={202: os.getuid() + 1})
        self.assertEqual(pl.live_lanes(self.cache, processes, lambda sha: {},
                                       self.checkout), [])

    def test_a_lanes_own_environment_is_recorded_with_it(self) -> None:
        # The merge daemon starts refresh lanes with LANE_BRANCH and stacked-PR
        # lanes with SKIP_REVIEW=1.  Neither appears in /proc/<pid>/cmdline, so a
        # relaunch that dropped them would resolve the wrong branch, or pay for a
        # review that must be skipped.
        processes = FakeProcesses(
            {202: "bash /p/local/bin/lane.sh 7 slug prover"},
            environs={202: {"LANE_BRANCH": "codex/issue-7-slug", "SKIP_REVIEW": "1",
                            "HOME": "/home/drx"}})
        lane, = pl.live_lanes(self.cache, processes, lambda sha: {}, self.checkout)
        self.assertEqual(lane["env"], {"LANE_BRANCH": "codex/issue-7-slug",
                                       "SKIP_REVIEW": "1"})
        self.assertEqual(lane["branch"], "codex/issue-7-slug",
                         "LANE_BRANCH is the branch lane.sh itself would use")
        self.assertEqual(lane["worktree"],
                         str(self.checkout / ".worktrees" / "codex/issue-7-slug"))

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

    def test_the_marker_snapshot_survives_the_json_round_trip(self) -> None:
        # `manifest` writes the snapshot into pause-state.json and `land --phase
        # last` reads it back, so it must carry the mtimes: a snapshot of bare
        # paths would make every pre-existing marker look landing-caused, and
        # the resume would clear a real failure verdict.
        daemon = self.cache / "watchdog" / "daemon"
        (daemon / "pr11.failed").write_text("a real failure\n", encoding="utf-8")
        snapshot = pl.failed_markers(self.cache)
        self.assertTrue(all(isinstance(value, float) for value in snapshot.values()))
        restored = json.loads(json.dumps(snapshot))
        self.assertEqual(pl.new_failed_markers(restored, self.cache), [],
                         "nothing changed, so the landing caused no marker")

    def test_a_second_manifest_keeps_the_first_landings_record(self) -> None:
        # The lock only blocks a CONCURRENT pause; a second owner-pause.sh after
        # the first finished reaches `manifest` again.
        first = {"schema": pl.SCHEMA, "lanes": [], "failed_markers": [{"pr": "12"}],
                 "markers_before": {"/a/pr11.failed": 1.0},
                 "sessions": [{"name": "prover-7-a", "signal": "KILL",
                               "thread_id": "t-7", "stopped_at": "then"}]}
        fresh = {"schema": pl.SCHEMA, "lanes": [], "failed_markers": [],
                 "markers_before": {"/a/pr11.failed": 2.0, "/a/pr12.failed": 3.0},
                 "sessions": [{"name": "prover-9-a", "signal": "pending"}]}
        merged = pl.merge_manifest(first, fresh)
        self.assertEqual([row["name"] for row in merged["sessions"]],
                         ["prover-7-a", "prover-9-a"])
        self.assertEqual(merged["sessions"][0]["signal"], "KILL",
                         "the first landing's signals and thread ids survive")
        self.assertEqual(merged["markers_before"], {"/a/pr11.failed": 1.0},
                         "the EARLIEST snapshot decides what is pre-existing")
        self.assertEqual(merged["failed_markers"], [{"pr": "12"}])

    def test_the_marker_snapshot_is_taken_before_the_daemon_is_stopped(self) -> None:
        # owner-pause.sh stops the merge daemon at T+0:30 and the daemon is the
        # only writer of daemon/pr<N>.failed, so the snapshot must be taken at
        # T+0:00 — at the landing phase the difference is empty by construction.
        body = text(TOOLS / "owner-pause.sh")
        snapshot = body.index('"$LANDING" markers')
        daemon_stop = body.index('kill_recorded "$D/daemon.pid"')
        landing = body.index('"$LANDING" manifest')
        self.assertLess(snapshot, daemon_stop,
                        "the markers are snapshotted before the daemon is stopped")
        self.assertLess(snapshot, landing)

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

    def test_a_pending_ci_resumes_at_ci_and_skips_the_finished_review(self) -> None:
        lane = self.lane(statuses={pl.CI_STATUS: "pending", pl.REVIEW_STATUS: "success"})
        self.assertEqual(pl.lane_resume_step(lane), "ci")
        # LANE_RESUME_STEP=ci skips only the merge and the build; the review block
        # runs unconditionally, so the most expensive step of the lane would be
        # paid a second time on a head that already carries a finished review.
        self.assertEqual(pl.lane_env(lane, "ci")["SKIP_REVIEW"], "1")

    def test_a_head_that_moved_resumes_the_whole_lane(self) -> None:
        self.assertEqual(pl.lane_resume_step(self.lane(head_now="def", statuses={
            pl.CI_STATUS: "success", pl.REVIEW_STATUS: "success"})), "dispatch")

    def test_an_unreadable_head_resumes_the_whole_lane(self) -> None:
        self.assertEqual(pl.lane_resume_step(self.lane(head=None, head_now=None)),
                         "dispatch")

    def test_a_lane_stopped_before_publication_resumes_at_dispatch(self) -> None:
        # Its head is unchanged because its worker had not finished, not because
        # the work is done.  `publish` sets SKIP_DISPATCH=1, which skips lane.sh's
        # `dispatch exit 0` and uncommitted-worker-changes gates and spends a full
        # CI run and a full review on an unfinished proof.
        for step in ("warm", "dispatch"):
            self.assertEqual(pl.lane_resume_step(self.lane(step=step)), "dispatch")

    def test_a_lane_that_reached_publication_resumes_at_publish(self) -> None:
        # `publish` is exactly the lane that left a <issue>.pr.md behind.
        self.assertEqual(pl.lane_resume_step(self.lane(step="publish")), "publish")

    def test_a_finished_lane_is_left_alone(self) -> None:
        self.assertEqual(pl.lane_resume_step(self.lane(step="done")), "done")

    def test_every_resume_step_is_one_lane_sh_accepts(self) -> None:
        body = text(BIN_DIR / "lane.sh")
        block = body.split("case \"$LANE_RESUME_STEP\" in", 1)[1].split("esac", 1)[0]
        for step in ("dispatch", "publish", "ci", "review"):
            self.assertIn(step, block, f"lane.sh must accept LANE_RESUME_STEP={step}")

    def test_the_relaunch_argv_is_one_the_next_pause_can_still_see(self) -> None:
        # `env LANE_RESUME_STEP=… lane.sh …` has `env` as argv[0], which matches
        # neither LANE_RE nor owner-pause.sh's anchored sweep: after one cycle the
        # lane would run through the next pause unseen, still pushing and opening
        # PRs after the owner was told the run was paused.
        argv = pl.lane_command(self.lane(), "ci", Path("/p"))
        self.assertEqual(argv, ["bash", "/p/local/bin/lane.sh", "7", "slug", "prover"])
        self.assertTrue(pl.LANE_RE.match(" ".join(argv)), "the next pause must see it")
        sweep = text(TOOLS / "owner-pause.sh").split("PATTERNS='", 1)[1].split("'", 1)[0]
        self.assertTrue(any(re.search(pattern, " ".join(argv))
                            for pattern in sweep.splitlines() if pattern.strip()),
                        "the anchored sweep must see it too")


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
                 "worktree": "/w/issue-7-slug", "branch": "issue-7-slug",
                 "thread_id": "t-7", "resume": "thread",
                 "resumable": True, "signal": "TERM"},
                {"name": "reviewer-pr9-a", "role": "reviewer", "issue": "pr9", "pr": "9",
                 "worktree": "/w/issue-9-z", "thread_id": "t-9", "resume": "restart",
                 "resumable": False, "signal": "KILL"},
                {"name": "prover-8-a", "role": "prover", "issue": "8", "pr": None,
                 "worktree": "/w/issue-8-other", "thread_id": "t-8", "resume": "thread",
                 "resumable": True, "signal": "pending"},
                # a checkpointed writer with no lane of its own: the meta layer
                # dispatches these directly, and they are the plan's own items
                {"name": "prover-31-a", "role": "prover", "issue": "31", "pr": None,
                 "worktree": "/w/issue-31-solo", "branch": "issue-31-solo",
                 "thread_id": "t-31", "resume": "thread", "resumable": True,
                 "signal": "KILL", "sandbox": "read-only", "account": "second",
                 "job_class": "hard", "effort": "ultra",
                 "hardness_reason": "stage-4.3 proof", "persona": "main:local/personas/prover.md",
                 "persona_ref": "main"},
                # and one whose thread id was never captured
                {"name": "prover-32-a", "role": "prover", "issue": "32", "pr": None,
                 "worktree": "/w/issue-32-lost", "thread_id": None, "resume": "restart",
                 "resumable": False, "signal": "KILL"},
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
                                 ("session", "prover-7-a"), ("session", "reviewer-pr9-a"),
                                 ("session", "prover-31-a"), ("session", "prover-32-a")])

    def test_a_lane_and_its_own_worker_are_never_both_launched(self) -> None:
        # lane.sh dispatches into the lane's worktree, so its prover is BOTH a
        # lane and a session.  Launching both put two writers into one worktree:
        # a `git merge` and a `lake build` in a tree a codex session is editing, a
        # PR opened on a moving head, and a branch claim the loser dies 5 on.
        plan = pl.resume_plan(self.manifest(), self.checkout)
        launched = [entry for entry in plan if entry.get("argv")]
        worktrees = [entry.get("worktree") for entry in launched
                     if entry["kind"] == "session"]
        self.assertNotIn("/w/issue-7-slug", worktrees)
        owned, = [entry for entry in plan if entry.get("name") == "prover-7-a"]
        self.assertIsNone(owned["argv"])
        self.assertEqual(owned["owned_by_lane"], "7")
        self.assertIn("lane 7 owns this worktree", owned["why"])
        # and the lane itself IS relaunched, at the step the pause recorded
        lane, = [entry for entry in plan
                 if entry["kind"] == "lane" and entry.get("issue") == "7"]
        self.assertTrue(lane["argv"])

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
            "bash", str(self.checkout / "local" / "bin" / "lane.sh"),
            "7", "slug", "prover"])
        self.assertEqual(plan["7"]["env"], {"LANE_RESUME_STEP": "review"})
        self.assertIsNone(plan["8"]["argv"])
        self.assertIn("both summary statuses", plan["8"]["why"])

    def test_a_checkpointed_prover_is_resumed_on_its_own_thread(self) -> None:
        # Every field the spool recorded travels back: account_router refuses a
        # resume whose model differs from the thread's observed model, and the
        # model is selected from the role, job class, effort and hardness reason.
        entry, = [row for row in pl.resume_plan(self.manifest(), self.checkout)
                  if row.get("name") == "prover-31-a"]
        self.assertEqual(entry["argv"], [
            str(self.checkout / "local" / "bin" / "dispatch.sh"),
            "--role", "prover", "--issue", "31", "--sandbox", "read-only",
            "--worktree", "/w/issue-31-solo", "--job-class", "hard",
            "--effort", "ultra", "--hardness-reason", "stage-4.3 proof",
            "--account", "second", "--persona", "local/personas/prover.md",
            "--persona-ref", "main", "--resume", "t-31", "--", pl.CONTINUE_PROMPT])

    def test_the_sandbox_is_the_one_the_session_was_dispatched_with(self) -> None:
        entry, = [row for row in pl.resume_plan(self.manifest(), self.checkout)
                  if row.get("name") == "prover-31-a"]
        self.assertIn("read-only", entry["argv"],
                      "a read-only role must not be resumed with write access")

    def test_a_writer_without_a_thread_id_gets_a_fresh_session_not_silence(self) -> None:
        # It was stopped mid-work and its worktree still holds that work; the old
        # plan returned None for it, so nothing was ever put back and no line said so.
        entry, = [row for row in pl.resume_plan(self.manifest(), self.checkout)
                  if row.get("name") == "prover-32-a"]
        self.assertEqual(entry["argv"][:8], [
            str(self.checkout / "local" / "bin" / "dispatch.sh"),
            "--role", "prover", "--issue", "32", "--sandbox", "workspace-write",
            "--worktree"])
        self.assertNotIn("--resume", entry["argv"])
        self.assertEqual(entry["argv"][-1], pl.RESTART_PROMPT)
        self.assertIn("worktree", pl.RESTART_PROMPT)

    def test_a_session_that_cannot_be_rebuilt_is_named_loudly(self) -> None:
        manifest = self.manifest()
        manifest["sessions"] = [{"name": "prover-none", "role": "prover", "issue": "",
                                 "worktree": "/w/x", "signal": "KILL",
                                 "resume": "restart"}]
        entry, = [row for row in pl.resume_plan(manifest, self.checkout)
                  if row["kind"] == "session"]
        self.assertIsNone(entry["argv"], "dispatch.sh exits 2 on an empty --issue")
        self.assertIn("STOPPED AND NOT PUT BACK", entry["why"])

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
        launched: list[tuple[list[str], dict]] = []

        def runner(argv, env=None):
            launched.append((argv, env or {}))
            return 4242

        plan = pl.resume_plan(self.manifest(), self.checkout)
        done = pl.resume_exec(plan, runner=runner)
        self.assertFalse(marker.exists(), "the recorded marker is cleared")
        self.assertEqual([argv for argv, _ in launched],
                         [entry["argv"] for entry in plan if entry["argv"]
                          and entry["kind"] != "clear-marker"])
        self.assertEqual(sum(1 for row in done if row["done"].startswith("launched")), 4)
        lane_env = [env for argv, env in launched if argv[0] == "bash"][0]
        self.assertEqual(lane_env["LANE_RESUME_STEP"], "review",
                         "the step travels in the environment, not in argv[0]")

    def test_one_failed_launch_does_not_cost_the_rest_of_the_plan(self) -> None:
        # A missing review.sh, or a lane.sh that lost its executable bit, used to
        # raise out of the loop: every later item was skipped and the ones already
        # launched were invisible, so a hand replay would double-launch them.
        seen: list[list[str]] = []

        def runner(argv, env=None):
            seen.append(argv)
            if argv[0].endswith("review.sh"):
                raise FileNotFoundError(argv[0])
            return 4242

        plan = pl.resume_plan(self.manifest(), self.checkout)
        done = pl.resume_exec(plan, runner=runner)
        failed = [row for row in done if row["done"].startswith("FAILED")]
        self.assertEqual(len(failed), 1)
        self.assertIn("review.sh", failed[0]["done"])
        self.assertEqual(sum(1 for row in done if row["done"].startswith("launched")), 3,
                         "the items after the failure are still launched")

    def test_a_replayed_manifest_launches_nothing_a_second_time(self) -> None:
        # owner-resume.sh is re-run routinely ("the resume message was not
        # delivered"); a second replay means two lane.sh for one worktree and two
        # `codex exec resume` on one thread id.
        manifest = self.manifest()
        done = pl.resume_exec(pl.resume_plan(manifest, self.checkout),
                              runner=lambda argv, env=None: 4242)
        pl.stamp_replay(manifest, done)
        self.assertTrue(manifest["replayed_at"])
        self.assertEqual(pl.resume_plan(manifest, self.checkout), [],
                         "a replayed manifest is not a plan any more")
        self.assertTrue(pl.resume_plan(manifest, self.checkout, force=True),
                        "--force is the deliberate way back in")

    def test_resume_exec_dry_run_touches_nothing(self) -> None:
        marker = self.cache / "watchdog" / "daemon" / "pr12.failed"
        marker.write_text("exited 143\n", encoding="utf-8")
        launched: list[list[str]] = []
        done = pl.resume_exec(pl.resume_plan(self.manifest(), self.checkout),
                              runner=lambda argv, env=None: launched.append(argv),
                              dry_run=True)
        self.assertTrue(marker.exists())
        self.assertEqual(launched, [])
        self.assertEqual({row["done"] for row in done},
                         {"would clear", "would launch", "nothing to run"})

    def test_the_plan_renders_as_commands_a_human_can_read(self) -> None:
        rendered = pl.format_plan(pl.resume_plan(self.manifest(), self.checkout))
        self.assertIn("LANE_RESUME_STEP=review", rendered)
        self.assertIn("--resume t-31", rendered)
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
        land = body.index('land_phase now')
        last = body.index('land_phase last')
        sweep = body.index("PATTERNS='")
        self.assertLess(land, last, "the young are stopped before the last call")
        self.assertLess(last, sweep, "the anchored sweep is the leftover pass")

    def test_a_failed_landing_phase_is_not_swallowed_by_the_pipe(self) -> None:
        # `python3 … | sed 's/^/   /' || fail_phase …` reads the status of `sed`,
        # which is always 0, so no landing failure ever reached pause-state.json.
        body = text(TOOLS / "owner-pause.sh")
        block = body.split("land_phase() {", 1)[1].split("\n}", 1)[0]
        self.assertIn("PIPESTATUS[0]", block)
        self.assertIn("fail_phase", block)
        self.assertNotIn('land --phase now | sed', body)
        self.assertNotIn('land --phase last | sed', body)

    def test_the_statuses_are_read_after_the_young_are_stopped(self) -> None:
        # The GitHub reads are bounded by STATUS_BUDGET_S, which is most of the
        # landing window; the young must be stopped inside it.
        body = text(TOOLS / "owner-pause.sh")
        self.assertLess(body.index('"$LANDING" manifest'), body.index("land_phase now"))
        self.assertIn("--no-github", body.split('"$LANDING" manifest', 1)[1][:200])
        self.assertLess(body.index("land_phase now"), body.index('"$LANDING" statuses'))

    def test_every_shell_fallback_equals_the_modules_default(self) -> None:
        # The fallbacks are deliberate, but they are not a second home for the
        # numbers: last_call_s stood at 60 here while the policy and the module
        # said 90, so the degraded path scheduled a different plan.
        body = text(TOOLS / "owner-pause.sh")
        flat = dict(pl.DEFAULTS["phases"])
        flat.update({key: pl.DEFAULTS[key] for key in ("young_max_min", "cutoff_lead_min")})
        found = dict(re.findall(r"pl_get ([a-z_]+) (\d+)", body))
        self.assertTrue(found, "the pause script must read every threshold with pl_get")
        for key, value in found.items():
            self.assertIn(key, flat, f"pl_get {key} is not a landing threshold")
            self.assertEqual(int(value), flat[key],
                             f"the {key} fallback must equal pause_landing.DEFAULTS")

    def test_the_pause_writes_every_marker_the_resume_requires(self) -> None:
        # owner-resume.sh's post-condition requires watchdog/paused as the proof
        # that the pause it is clearing was real.  Nothing wrote it, so a clean
        # owner-pause.sh -> owner-resume.sh pair exited 5 at the post-condition
        # and the whole work-resume section was unreachable in production.
        pause = text(TOOLS / "owner-pause.sh")
        resume = text(TOOLS / "owner-resume.sh")
        required = set(re.findall(r'\[ ! -e "\$W/([a-z-]+)" \]', resume))
        self.assertIn("paused", required)
        for marker in required:
            self.assertTrue(re.search(rf'> "\$W/{marker}"', pause),
                            f"owner-pause.sh must write $W/{marker}")

    def test_the_resume_clears_the_cutoff_marker(self) -> None:
        # Nothing else removes it, and a surviving one makes the next --cutoff
        # re-assert admission silently: the main session is never told.
        resume = text(TOOLS / "owner-resume.sh")
        block = resume.split('rm -f "$W/paused"', 1)[1].split("\n", 1)[0]
        self.assertIn("cutoff", block)

    def test_the_work_resume_is_replayed_at_most_once(self) -> None:
        resume = text(TOOLS / "owner-resume.sh")
        self.assertIn("resume-exec", resume)
        self.assertIn("WORK_RC", resume)
        self.assertIn("-eq 4", resume, "a partial replay is not a total failure")

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
        work = body.index('"$LANDING" resume-exec')
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

    def test_the_cutoff_word_really_writes_the_markers_the_resume_reads(self) -> None:
        # The one end-to-end run: owner-pause.sh --cutoff against a scratch cache
        # root, with no run-mode and no owner-say, touching no live state.  It is
        # the path that proves watchdog/paused and watchdog/drain are written.
        with tempfile.TemporaryDirectory() as directory:
            cache = Path(directory) / "cache"
            env = dict(os.environ)
            env.update({"MIPSTARRE_CACHE_ROOT": str(cache),
                        "MIPSTARRE_REPO_ROOT": str(REPO_ROOT),
                        "MIPSTARRE_OWNER_BIN": str(cache / "owner-bin"),
                        "MIPSTARRE_RUN_MODE": str(cache / "no-run-mode.py"),
                        "MIPSTARRE_OWNER_SAY": str(cache / "no-say.sh")})
            done = subprocess.run(["bash", str(TOOLS / "owner-pause.sh"), "--cutoff",
                                   "--reason", "test"], env=env, capture_output=True,
                                  text=True, timeout=120)
            self.assertEqual(done.returncode, 0, done.stderr)
            watchdog = cache / "watchdog"
            for marker in ("drain", "paused", "cutoff"):
                self.assertTrue((watchdog / marker).exists(),
                                f"the cutoff must write watchdog/{marker}: {done.stderr}")
            record = json.loads(text(watchdog / "pause-state.json"))
            self.assertEqual(record["status"], "cutoff")

    def test_a_recorded_cap_is_never_lowered_to_zero_by_a_later_write(self) -> None:
        # After a cutoff the live cap files are 0 BY DESIGN, so a pause word that
        # read them recorded `primary 0` as the cap to restore and the documented
        # fallback resumed the run with no admission at all.
        body = text(TOOLS / "owner-pause.sh")
        self.assertIn("saved_caps", body, "the caps come from the run mode's saved_caps")
        self.assertIn("caps_kept_from", body,
                      "a later write_state must not lower a recorded nonzero cap")

    def test_the_protocol_and_the_readme_describe_both_words(self) -> None:
        protocol = text(REPO_ROOT / "local" / "protocols" / "full-speed-mode.md")
        readme = text(TOOLS / "README.md")
        for document in (protocol, readme):
            self.assertIn("--cutoff", document)
            self.assertIn("pause_landing.py", document)
            self.assertIn("local-review/summary", document)


if __name__ == "__main__":
    unittest.main()
