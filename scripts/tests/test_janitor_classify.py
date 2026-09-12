#!/usr/bin/env python3
"""Unit tests for the classification and cap rules of ``local/bin/janitor.sh``.

The janitor is bash, so its pure decision functions are tested by sourcing the
script with ``MIPSTARRE_JANITOR_SOURCE_ONLY=1`` (which defines the functions and
runs no pass) and calling them.  What is pinned here is exactly what the
2026-09-12 recovery scripts got wrong:

* every reason string a lane can park with maps to its class, and only ``merge``
  and ``build`` are repairable;
* a capture that ended cleanly is never re-dispatched, whatever earlier
  reconnects it contains;
* the retry ledger caps at 2 per ``(pr, role, head_sha)``;
* a lane numbered 7 and a lane numbered 1342 are both picked up — no
  ``/[0-9]{3}\\.needs-attention$`` digit filter — and no ``-mmin`` age filter
  hides a marker that one poll missed.

Run: ``python3 -m unittest scripts/tests/test_janitor_classify.py``
"""

from __future__ import annotations

import json
import os
import subprocess
import tempfile
import time
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
JANITOR = REPO_ROOT / "local" / "bin" / "janitor.sh"


class JanitorShellTestCase(unittest.TestCase):
    """Base: one temporary cache root per test, and a helper that calls one function."""

    def setUp(self) -> None:
        self.assertTrue(JANITOR.is_file(), f"missing {JANITOR}")
        self._tmp = tempfile.TemporaryDirectory()
        self.cache = Path(self._tmp.name) / "cache"
        self.lanes = self.cache / "watchdog" / "lanes"
        self.janitor_state = self.cache / "watchdog" / "janitor"
        self.lanes.mkdir(parents=True)
        self.janitor_state.mkdir(parents=True)
        self.addCleanup(self._tmp.cleanup)

    def call(self, snippet: str, *, check: bool = True) -> subprocess.CompletedProcess:
        env = dict(os.environ)
        env.update({
            "MIPSTARRE_JANITOR_SOURCE_ONLY": "1",
            "MIPSTARRE_CACHE_ROOT": str(self.cache),
            "MIPSTARRE_REPO_ROOT": str(REPO_ROOT),
            "MIPSTARRE_JANITOR_CLASSIFIER": "builtin",
            "MIPSTARRE_JANITOR_RETRY_CAP": "2",
            "MIPSTARRE_JANITOR_REPAIR_CAP": "2",
        })
        script = f'. "{JANITOR}"\n{snippet}\n'
        result = subprocess.run(["bash", "-c", script], capture_output=True,
                                text=True, env=env)
        if check and result.returncode not in (0, 1):
            self.fail(f"bash snippet failed ({result.returncode}): {result.stderr}")
        return result

    def out(self, snippet: str) -> str:
        return self.call(snippet).stdout.strip()

    def status(self, snippet: str) -> int:
        return self.call(snippet).returncode


class TestSourcingRunsNothing(JanitorShellTestCase):
    def test_sourcing_defines_functions_and_runs_no_pass(self) -> None:
        result = self.call("declare -F classify_reason >/dev/null && echo defined")
        self.assertEqual(result.stdout.strip(), "defined")
        self.assertFalse((self.janitor_state / "report.md").exists(),
                         "sourcing the janitor must not run a pass")


class TestReasonClasses(JanitorShellTestCase):
    """Every string is one a lane runner actually writes into <N>.needs-attention."""

    CASES = {
        "2026-09-12T05:12:03Z merging github/main conflicted in "
        "/home/drx/MIPStarRE-qpbt/.worktrees/issue-338-extended-direct-coefficient-loss":
            "merge",
        "2026-09-12T05:40:00Z lake build before push failed (see "
        "/home/drx/.cache/mipstarre-dev/watchdog/lanes/342.build.log)": "build",
        "2026-09-12T05:41:00Z lake build of changed modules failed (see 342.build.log)":
            "build",
        "2026-09-12T05:42:00Z pre-push gate failed (see 342.push.log)": "gate",
        "2026-09-12T05:43:00Z no commits ahead of main for #342": "no-commits",
        "2026-09-12T05:44:00Z worker left uncommitted changes (see 342.dispatch.log)":
            "dirty-worktree",
        "2026-09-12T05:45:00Z worktree-mismatch: .worktrees/issue-213-x holds "
        "issue-213-y, not the PR head": "worktree-mismatch",
        "2026-09-12T05:46:00Z no-slot: waited 1800s for a free account slot": "no-slot",
        "2026-09-12T05:47:00Z merge of github/main left paths missing that main "
        "carries (issue #222): MIPStarRE/QPBT/Combining/Points.lean": "merge-loss",
        "2026-09-12T05:48:00Z pr_open failed after direct push": "pr-open",
        "2026-09-12T05:49:00Z something nobody has seen before": "unknown",
    }

    def test_each_reason_maps_to_its_class(self) -> None:
        for text, expected in self.CASES.items():
            with self.subTest(reason=text[:60]):
                self.assertEqual(self.out(f'classify_reason {json.dumps(text)}'), expected)

    def test_only_merge_and_build_are_repairable(self) -> None:
        for klass in ("merge", "build"):
            self.assertEqual(self.status(f"repairable_class {klass}"), 0, klass)
        for klass in ("gate", "no-commits", "dirty-worktree", "worktree-mismatch",
                      "no-slot", "merge-loss", "pr-open", "unknown"):
            self.assertEqual(self.status(f"repairable_class {klass}"), 1, klass)

    def test_merge_loss_is_never_repaired_as_a_merge_conflict(self) -> None:
        """The issue-#222 guard must not be handed to an orc as a conflict."""
        text = ("merge of github/main left paths missing that main carries "
                "(issue #222): MIPStarRE/QPBT/Combining/Points.lean")
        self.assertEqual(self.out(f"classify_reason {json.dumps(text)}"), "merge-loss")
        self.assertEqual(self.status("repairable_class merge-loss"), 1)


class TestCaptureClasses(JanitorShellTestCase):
    def write_capture(self, name: str, lines: list) -> Path:
        path = Path(self._tmp.name) / name
        path.write_text("".join(json.dumps(line) + "\n" for line in lines),
                        encoding="utf-8")
        return path

    def test_clean_capture_is_never_redispatched(self) -> None:
        capture = self.write_capture("clean.jsonl", [
            {"type": "thread.started", "thread_id": "abc"},
            {"type": "item.completed", "item": {"text": "proved it"}},
            {"type": "turn.completed", "usage": {"input_tokens": 10}},
        ])
        self.assertEqual(self.out(f'capture_class "{capture}"'), "clean")
        self.assertEqual(self.status("redispatchable_class clean"), 1)

    def test_a_recovered_reconnect_still_counts_as_clean(self) -> None:
        """A session that reconnected once and then finished is not a failure."""
        capture = self.write_capture("recovered.jsonl", [
            {"type": "item.completed", "text": "stream error; Reconnecting... 1/5"},
            {"type": "turn.completed", "usage": {"input_tokens": 10}},
        ])
        self.assertEqual(self.out(f'capture_class "{capture}"'), "clean")

    def test_exhausted_reconnect(self) -> None:
        capture = self.write_capture("exhausted.jsonl", [
            {"type": "item.completed", "text": "stream disconnected; Reconnecting... 4/5"},
            {"type": "item.completed", "text": "stream disconnected; Reconnecting... 5/5"},
        ])
        self.assertEqual(self.out(f'capture_class "{capture}"'), "reconnect-exhausted")
        self.assertEqual(self.status("redispatchable_class reconnect-exhausted"), 0)

    def test_endpoint_5xx(self) -> None:
        capture = self.write_capture("relay.jsonl", [
            {"type": "error", "message": "503 Service Unavailable (relay-us7)"},
        ])
        self.assertEqual(self.out(f'capture_class "{capture}"'), "endpoint-5xx")
        self.assertEqual(self.status("redispatchable_class endpoint-5xx"), 0)

    def test_concurrency_limit(self) -> None:
        capture = self.write_capture("limit.jsonl", [
            {"type": "error", "message": "Concurrency limit exceeded"},
        ])
        self.assertEqual(self.out(f'capture_class "{capture}"'), "concurrency-limit")
        self.assertEqual(self.status("redispatchable_class concurrency-limit"), 0)

    def test_missing_and_unknown_captures_are_not_redispatched(self) -> None:
        missing = Path(self._tmp.name) / "nope.jsonl"
        self.assertEqual(self.out(f'capture_class "{missing}"'), "empty")
        self.assertEqual(self.status("redispatchable_class empty"), 1)
        odd = self.write_capture("odd.jsonl", [{"type": "item.started"}])
        self.assertEqual(self.out(f'capture_class "{odd}"'), "unknown")
        self.assertEqual(self.status("redispatchable_class unknown"), 1)


class TestLedgerCaps(JanitorShellTestCase):
    def attempts(self, key: str, count: int, ledger: str = "retries.jsonl") -> None:
        path = self.janitor_state / ledger
        with path.open("a", encoding="utf-8") as handle:
            for index in range(count):
                handle.write(json.dumps({"ts": "2026-09-12T06:00:0%dZ" % index,
                                         "key": key, "event": "attempt",
                                         "action": "redispatch"}) + "\n")
            # Outcome rows must not be counted as attempts.
            handle.write(json.dumps({"ts": "2026-09-12T06:10:00Z", "key": key,
                                     "event": "outcome", "outcome": "died"}) + "\n")

    def test_retry_key_is_pr_role_head(self) -> None:
        self.assertEqual(self.out("retry_key 342 reviewer deadbeef"), "pr342:reviewer:deadbeef")

    def test_ledger_caps_at_two(self) -> None:
        key = "pr342:reviewer:deadbeefdeadbeefdeadbeefdeadbeefdeadbeef"
        self.assertEqual(self.out(f'ledger_count "{self.janitor_state}/retries.jsonl" "{key}"'), "0")
        self.assertEqual(self.status(f'retry_allow "{key}"'), 0)
        self.attempts(key, 1)
        self.assertEqual(self.status(f'retry_allow "{key}"'), 0, "one attempt still allows a second")
        self.attempts(key, 1)
        self.assertEqual(self.out(f'ledger_count "{self.janitor_state}/retries.jsonl" "{key}"'), "2")
        self.assertEqual(self.status(f'retry_allow "{key}"'), 1, "the cap is 2 attempts")

    def test_the_cap_is_per_pr_role_head(self) -> None:
        exhausted = "pr342:reviewer:aaa"
        self.attempts(exhausted, 2)
        self.assertEqual(self.status(f'retry_allow "{exhausted}"'), 1)
        # Same PR and role, a new head: a fresh budget, because it is new work.
        self.assertEqual(self.status('retry_allow "pr342:reviewer:bbb"'), 0)
        # Same PR and head, another role: also independent.
        self.assertEqual(self.status('retry_allow "pr342:prover:aaa"'), 0)

    def test_repair_cap_is_per_lane(self) -> None:
        self.attempts("lane:7", 2, ledger="repairs.jsonl")
        self.assertEqual(self.status("repair_allow 7"), 1)
        self.assertEqual(self.status("repair_allow 1342"), 0)

    def test_a_malformed_ledger_line_is_skipped_not_fatal(self) -> None:
        path = self.janitor_state / "retries.jsonl"
        path.write_text("not json\n" + json.dumps(
            {"key": "pr9:reviewer:x", "event": "attempt"}) + "\n", encoding="utf-8")
        self.assertEqual(self.out(f'ledger_count "{path}" "pr9:reviewer:x"'), "1")


class TestLaneSelection(JanitorShellTestCase):
    def marker(self, lane: str, text: str = "merging github/main conflicted",
               age_s: int = 0) -> Path:
        path = self.lanes / f"{lane}.needs-attention"
        path.write_text(f"2026-09-12T05:00:00Z {text}\n", encoding="utf-8")
        if age_s:
            stamp = time.time() - age_s
            os.utime(path, (stamp, stamp))
        return path

    def test_lane_seven_and_lane_1342_are_both_picked_up(self) -> None:
        self.marker("7")
        self.marker("1342")
        listed = sorted(Path(line).name for line in self.out("list_lane_markers").splitlines())
        self.assertEqual(listed, ["1342.needs-attention", "7.needs-attention"])

    def test_no_age_filter_hides_a_marker_one_poll_missed(self) -> None:
        self.marker("42", age_s=6 * 3600)
        listed = self.out("list_lane_markers").splitlines()
        self.assertEqual([Path(line).name for line in listed], ["42.needs-attention"])

    def test_lane_id_accepts_every_number_and_rejects_non_numbers(self) -> None:
        for lane in ("7", "042", "100", "1342", "1000"):
            with self.subTest(lane=lane):
                self.assertEqual(
                    self.out(f'lane_id_of "{self.lanes}/{lane}.needs-attention"'), lane)
        for name in ("daemon10.log", "pr342.failed", "stacks"):
            with self.subTest(name=name):
                self.assertEqual(self.status(f'lane_id_of "{self.lanes}/{name}"'), 1)

    def test_lane_id_of_every_lane_state_suffix(self) -> None:
        for suffix in ("done", "needs-attention", "task.md", "lane.log", "thread",
                       "build.log", "repair-task.md"):
            with self.subTest(suffix=suffix):
                self.assertEqual(self.out(f'lane_id_of "{self.lanes}/1342.{suffix}"'), "1342")

    def test_empty_lane_directory_lists_nothing(self) -> None:
        self.assertEqual(self.out("list_lane_markers"), "")

    def test_branch_is_resolved_from_the_record_not_from_the_lane_number(self) -> None:
        self.marker("1342", text=("merging github/main conflicted in "
                                  "/home/drx/MIPStarRE-qpbt/.worktrees/"
                                  "issue-338-extended-direct-coefficient-loss"))
        self.assertEqual(self.out("lane_branch 1342"),
                         "issue-338-extended-direct-coefficient-loss")

    def test_branch_falls_back_to_the_dispatch_record(self) -> None:
        self.marker("1349", text="lake build before push failed")
        (self.cache / "watchdog" / "meta-dispatched.txt").write_text(
            "autofix 443\nlane 1349 PR 349 issue-346-direct-k-one-soundness-any-strategy\n",
            encoding="utf-8")
        self.assertEqual(self.out("lane_branch 1349"),
                         "issue-346-direct-k-one-soundness-any-strategy")

    def test_unresolvable_branch_is_empty_not_guessed(self) -> None:
        self.marker("512", text="lake build before push failed")
        self.assertEqual(self.out("lane_branch 512"), "")


class TestSpoolExpiry(JanitorShellTestCase):
    def entry(self, name: str, payload: dict) -> Path:
        spool = self.cache / "watchdog" / "capacity" / "spool"
        spool.mkdir(parents=True, exist_ok=True)
        path = spool / name
        path.write_text(json.dumps(payload), encoding="utf-8")
        return path

    def test_entry_past_the_run_cutoff_is_expired(self) -> None:
        path = self.entry("prover-1.json", {"role": "prover", "issue": "342"})
        self.assertEqual(self.status(f'spool_is_expired "{path}" "2026-09-12T08:00:00Z"'), 0)

    def test_entry_before_the_cutoff_survives(self) -> None:
        path = self.entry("prover-2.json", {"role": "prover", "issue": "342"})
        self.assertEqual(self.status(f'spool_is_expired "{path}" "2099-01-01T00:00:00Z"'), 1)

    def test_own_deadline_expires_without_a_cutoff(self) -> None:
        path = self.entry("prover-3.json", {"role": "prover", "deadline": "2026-09-12T08:00:00Z"})
        self.assertEqual(self.status(f'spool_is_expired "{path}" ""'), 0)

    def test_unparsable_entry_is_kept_not_dropped(self) -> None:
        spool = self.cache / "watchdog" / "capacity" / "spool"
        spool.mkdir(parents=True, exist_ok=True)
        path = spool / "broken.json"
        path.write_text("{not json", encoding="utf-8")
        self.assertEqual(self.status(f'spool_is_expired "{path}" "2026-09-12T08:00:00Z"'), 1)


class TestClassifierSelection(JanitorShellTestCase):
    """``auto`` prefers telemetry.py's classify-failure (W2) and falls back to the
    builtin patterns when that subcommand does not exist or errors."""

    def stage(self, telemetry_body: str) -> Path:
        staged = Path(self._tmp.name) / "bin"
        staged.mkdir(exist_ok=True)
        (staged / "janitor.sh").write_text(JANITOR.read_text(encoding="utf-8"),
                                           encoding="utf-8")
        (staged / "telemetry.py").write_text(telemetry_body, encoding="utf-8")
        return staged / "janitor.sh"

    def call_staged(self, script_path: Path, snippet: str) -> subprocess.CompletedProcess:
        env = dict(os.environ)
        env.update({"MIPSTARRE_JANITOR_SOURCE_ONLY": "1",
                    "MIPSTARRE_CACHE_ROOT": str(self.cache),
                    "MIPSTARRE_REPO_ROOT": str(REPO_ROOT),
                    "MIPSTARRE_JANITOR_CLASSIFIER": "auto"})
        return subprocess.run(["bash", "-c", f'. "{script_path}"\n{snippet}\n'],
                              capture_output=True, text=True, env=env)

    def capture(self) -> Path:
        path = Path(self._tmp.name) / "cap.jsonl"
        path.write_text(json.dumps({"type": "item.completed", "text": "…"}) + "\n",
                        encoding="utf-8")
        return path

    def test_auto_uses_telemetry_when_it_offers_classify_failure(self) -> None:
        script = self.stage(
            "import sys\n"
            "if sys.argv[1:2] != ['classify-failure']:\n"
            "    sys.exit(2)\n"
            "if '--help' in sys.argv:\n"
            "    print('usage'); sys.exit(0)\n"
            "print('endpoint_5xx')\n")
        result = self.call_staged(script, f'capture_class "{self.capture()}"')
        self.assertEqual(result.stdout.strip(), "endpoint-5xx")

    def test_auto_falls_back_when_telemetry_has_no_such_subcommand(self) -> None:
        script = self.stage("import sys\nsys.exit(2)\n")
        result = self.call_staged(script, f'capture_class "{self.capture()}"')
        self.assertEqual(result.stdout.strip(), "unknown",
                         "the builtin classifier must answer when telemetry cannot")


class TestRedispatchRoles(JanitorShellTestCase):
    def test_default_roles(self) -> None:
        self.assertEqual(self.status("role_redispatchable reviewer"), 0)
        self.assertEqual(self.status("role_redispatchable prover"), 1,
                         "a prover's work is re-planned by its owning session, not duplicated")


if __name__ == "__main__":
    unittest.main()
