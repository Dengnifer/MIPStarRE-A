#!/usr/bin/env python3
"""AIMD behaviour of local/bin/capacity_controller.py.

Everything runs against a temporary cache root and a synthetic
``sessions.jsonl``; the shipped ``local/capacity-policy.json`` is the policy
under test, so a knob file that stops validating fails here first.
"""

from __future__ import annotations

import contextlib
import io
import json
import os
import re
import sys
import tempfile
import unittest
from datetime import datetime, timedelta, timezone
from pathlib import Path
from unittest import mock

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "local" / "bin"))

import capacity_controller as cc  # noqa: E402

NUMERIC = re.compile(r"\A[0-9]+\n\Z")
T0 = datetime(2026, 9, 13, 4, 0, 0, tzinfo=timezone.utc)


def at(seconds: int) -> str:
    return (T0 + timedelta(seconds=seconds)).strftime("%Y-%m-%dT%H:%M:%SZ")


class CapacityHarness(unittest.TestCase):
    """Temporary cache root, temporary telemetry, a two-account brief."""

    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        root = Path(self.tmp.name)
        self.cache = root / "cache"
        self.telemetry = root / "telemetry"
        self.telemetry.mkdir(parents=True)
        self.watchdog = self.cache / "watchdog"
        self.watchdog.mkdir(parents=True)
        environment = mock.patch.dict(os.environ, {
            "MIPSTARRE_CACHE_ROOT": str(self.cache),
            "MIPSTARRE_TELEMETRY_DIR": str(self.telemetry),
            "MIPSTARRE_REPO_ROOT": str(REPO_ROOT),
        })
        environment.start()
        self.addCleanup(environment.stop)
        os.environ.pop("MIPSTARRE_CAPACITY_POLICY", None)
        os.environ.pop("MIPSTARRE_CAPACITY_PROBE_CMD", None)
        os.environ.pop("MIPSTARRE_RUN_MODE", None)
        self.write_run_mode()

    # -- fixtures ----------------------------------------------------------

    def write_run_mode(self, *, primary=5, second=30, reserved=2,
                       enabled=(True, True)) -> None:
        document = {
            "schema": "mipstarre-run-mode/1",
            "brief_sha256": "0" * 64,
            "run": {"label": "test run", "speed": "fast", "occupancy_target": 0.8},
            "accounts": [
                {"name": "primary", "label": "relay-us7", "endpoint": "relay-us7",
                 "codex_home": str(self.cache / "codex-primary"),
                 "nominal_limit": primary, "external_reserved": 0, "enabled": enabled[0]},
                {"name": "second", "label": "space", "endpoint": "api.finite-dimensional.space",
                 "codex_home": str(self.cache / "codex-second"),
                 "nominal_limit": second, "external_reserved": reserved, "enabled": enabled[1]},
            ],
        }
        (self.watchdog / "run-mode.json").write_text(json.dumps(document), encoding="utf-8")

    def session(self, seconds: int, endpoint: str, failure_class: str) -> None:
        row = {"name": f"prover-{seconds}", "role": "prover", "issue": "1",
               "start": at(seconds), "end": at(seconds), "status": "failed", "exit": 4,
               "endpoint": endpoint, "failure_class": failure_class,
               "failure_detail": f"synthetic {failure_class}"}
        with (self.telemetry / "sessions.jsonl").open("a", encoding="utf-8") as handle:
            handle.write(json.dumps(row) + "\n")

    def invoke(self, *argv: str, live=None, expect: int = 0) -> str:
        """Run the controller with a chosen live census; returns its stdout."""
        live = live or {"primary": 0, "second": 0}
        out, err = io.StringIO(), io.StringIO()
        with mock.patch.object(cc, "count_live", return_value=dict(live)), \
                mock.patch.object(cc, "count_waiters", return_value=0), \
                contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = cc.main(list(argv))
        self.assertEqual(code, expect, f"argv={argv}\n{out.getvalue()}{err.getvalue()}")
        return out.getvalue()

    def tick(self, seconds: int, live=None, expect: int = 0) -> str:
        return self.invoke("--now", at(seconds), "tick", live=live, expect=expect)

    # -- assertions --------------------------------------------------------

    def cap_file(self, name: str) -> int:
        text = (self.watchdog / name).read_text(encoding="utf-8")
        self.assertRegex(text, NUMERIC, f"{name} must be a bare nonnegative integer")
        return int(text)

    def caps(self) -> dict:
        return {"primary": self.cap_file("max-codex-primary"),
                "second": self.cap_file("max-codex-second"),
                "total": self.cap_file("max-codex")}

    def state(self) -> dict:
        return json.loads((self.watchdog / "capacity" / "state.json").read_text(encoding="utf-8"))

    def assert_consistent(self) -> None:
        caps = self.caps()
        self.assertEqual(caps["total"], caps["primary"] + caps["second"],
                         "max-codex must be mechanically the sum of the per-account caps")
        state = self.state()
        for name in ("primary", "second"):
            self.assertEqual(state["accounts"][name]["cap"], caps[name],
                             f"{name}: state.json and the derived cap file disagree")


class SeedTests(CapacityHarness):
    def test_init_seeds_ceiling_and_sum(self) -> None:
        self.invoke("--now", at(0), "init")
        self.assertEqual(self.caps(), {"primary": 5, "second": 28, "total": 33})
        self.assert_consistent()

    def test_external_reserved_lowers_the_ceiling(self) -> None:
        self.write_run_mode(second=30, reserved=10)
        self.invoke("--now", at(0), "init")
        self.assertEqual(self.state()["accounts"]["second"]["ceiling"], 20)
        self.assertEqual(self.caps()["second"], 20)

    def test_disabled_account_is_never_dispatched_to(self) -> None:
        self.write_run_mode(enabled=(False, True))
        self.invoke("--now", at(0), "init")
        self.assertEqual(self.caps()["primary"], 0)
        self.tick(60, live={"primary": 0, "second": 0})
        self.assertEqual(self.caps()["primary"], 0)

    def test_tick_seeds_when_state_is_absent(self) -> None:
        self.tick(0)
        self.assertEqual(self.caps()["total"], 33)
        self.assert_consistent()


class IncreaseTests(CapacityHarness):
    def setUp(self) -> None:
        super().setUp()
        self.invoke("--now", at(0), "init")
        self.invoke("--now", at(0), "set", "primary", "2")

    def test_increase_needs_a_full_quiet_window(self) -> None:
        busy = {"primary": 4, "second": 0}
        self.tick(10, live=busy)
        self.assertEqual(self.caps()["primary"], 2, "the first quiet tick only starts the window")
        self.tick(70, live=busy)
        self.assertEqual(self.caps()["primary"], 2, "60 s is not the 120 s quiet window")
        self.tick(140, live=busy)
        self.assertEqual(self.caps()["primary"], 3, "a full quiet window adds exactly one slot")
        self.assert_consistent()

    def test_one_slot_per_window_and_never_more(self) -> None:
        busy = {"primary": 4, "second": 0}
        self.tick(10, live=busy)
        self.tick(140, live=busy)
        self.tick(150, live=busy)
        self.assertEqual(self.caps()["primary"], 3, "a second increase inside the window")
        self.tick(400, live=busy)
        self.assertEqual(self.caps()["primary"], 4)

    def test_increase_stops_at_the_brief_ceiling(self) -> None:
        busy = {"primary": 9, "second": 0}
        for seconds in range(10, 2000, 130):
            self.tick(seconds, live=busy)
        self.assertEqual(self.caps()["primary"], 5, "the brief's ceiling is never exceeded")

    def test_idle_slots_are_not_evidence_of_headroom(self) -> None:
        idle = {"primary": 0, "second": 0}
        self.tick(10, live=idle)
        self.tick(200, live=idle)
        self.assertEqual(self.caps()["primary"], 2,
                         "live < cap - 1: the cap nobody uses must not grow")

    def test_a_death_blocks_the_climb_without_cutting_the_cap(self) -> None:
        busy = {"primary": 4, "second": 0}
        self.session(5, "relay-us7", "endpoint_5xx")
        self.tick(10, live=busy)
        self.assertEqual(self.state()["accounts"]["primary"]["health"], "degraded",
                         "one 5xx is below the trip threshold but is not nothing")
        self.tick(140, live=busy)
        self.assertEqual(self.caps()["primary"], 2,
                         "a death blocks the climb and never cuts the cap")


class DecreaseTests(CapacityHarness):
    def setUp(self) -> None:
        super().setUp()
        self.invoke("--now", at(0), "init")

    def test_first_refusal_steps_below_the_refused_concurrency(self) -> None:
        self.session(10, "api.finite-dimensional.space", "concurrency_limit")
        self.tick(20, live={"primary": 0, "second": 20})
        self.assertEqual(self.caps()["second"], 19,
                         "cap = min(cap, live_at_first_refusal - 1)")
        self.assert_consistent()

    def test_further_refusal_in_the_window_multiplies(self) -> None:
        self.session(10, "api.finite-dimensional.space", "concurrency_limit")
        self.tick(20, live={"primary": 0, "second": 20})
        self.session(30, "api.finite-dimensional.space", "concurrency_limit")
        self.tick(40, live={"primary": 0, "second": 19})
        self.assertEqual(self.caps()["second"], 15, "ceil(19 * 0.75)")

    def test_refusal_records_the_observed_floor(self) -> None:
        self.session(10, "api.finite-dimensional.space", "concurrency_limit")
        self.tick(20, live={"primary": 0, "second": 20})
        self.assertEqual(self.state()["accounts"]["second"]["observed_refusal_floor"], 20)
        estimate = json.loads(
            (self.watchdog / "capacity" / "limit-estimate.json").read_text(encoding="utf-8"))
        self.assertEqual(estimate["accounts"]["second"]["refusals_5m"], 1)

    def test_a_refusal_is_acted_on_exactly_once(self) -> None:
        self.session(10, "api.finite-dimensional.space", "concurrency_limit")
        self.tick(20, live={"primary": 0, "second": 20})
        self.tick(25, live={"primary": 0, "second": 19})
        self.assertEqual(self.caps()["second"], 19,
                         "re-reading the same row must not decrease again")

    def test_a_refusal_never_cuts_the_other_account(self) -> None:
        self.session(10, "api.finite-dimensional.space", "concurrency_limit")
        self.tick(20, live={"primary": 4, "second": 20})
        self.assertEqual(self.caps()["primary"], 5, "endpoint attribution keeps keys separate")

    def test_decrease_stops_at_the_floor(self) -> None:
        for step in range(0, 12):
            self.session(10 + step * 20, "api.finite-dimensional.space", "concurrency_limit")
            self.tick(20 + step * 20, live={"primary": 0, "second": 1})
        self.assertGreaterEqual(self.caps()["second"], 1, "the floor holds an enabled account")


class NeutralClassTests(CapacityHarness):
    """A class the policy does not name degrades to today's static behaviour."""

    def setUp(self) -> None:
        super().setUp()
        self.invoke("--now", at(0), "init")
        self.invoke("--now", at(0), "set", "second", "10")

    def test_unknown_neither_decreases(self) -> None:
        self.session(10, "api.finite-dimensional.space", "unknown")
        self.tick(20, live={"primary": 0, "second": 10})
        self.assertEqual(self.caps()["second"], 10)

    def test_a_rotted_pattern_neither_decreases(self) -> None:
        self.session(10, "api.finite-dimensional.space", "brand_new_provider_wording")
        self.tick(20, live={"primary": 0, "second": 10})
        self.assertEqual(self.caps()["second"], 10)

    def test_unknown_does_not_block_the_climb(self) -> None:
        self.session(10, "api.finite-dimensional.space", "unknown")
        busy = {"primary": 0, "second": 10}
        self.tick(20, live=busy)
        self.tick(200, live=busy)
        self.assertEqual(self.caps()["second"], 11,
                         "neutral means neutral: the cap walks to the owner's ceiling")


class OperatorSetTests(CapacityHarness):
    def setUp(self) -> None:
        super().setUp()
        self.invoke("--now", at(0), "init")

    def test_set_clamps_to_the_ceiling(self) -> None:
        self.invoke("--now", at(0), "set", "second", "999")
        self.assertEqual(self.caps()["second"], 28)

    def test_set_refuses_a_negative_cap(self) -> None:
        self.invoke("--now", at(0), "set", "second", "-1", expect=cc.EXIT_FAIL)
        self.assertEqual(self.caps()["second"], 28, "a refused set changes nothing")

    def test_set_refuses_an_unknown_account(self) -> None:
        self.invoke("--now", at(0), "set", "third", "4", expect=cc.EXIT_FAIL)

    def test_set_gives_the_operator_a_full_quiet_window(self) -> None:
        self.invoke("--now", at(0), "set", "second", "10")
        busy = {"primary": 0, "second": 10}
        self.tick(60, live=busy)
        self.assertEqual(self.caps()["second"], 10)
        self.tick(200, live=busy)
        self.assertEqual(self.caps()["second"], 11)


class FailureBehaviourTests(CapacityHarness):
    def setUp(self) -> None:
        super().setUp()
        self.invoke("--now", at(0), "init")
        self.before = self.caps()

    def test_malformed_policy_leaves_the_cap_files_untouched(self) -> None:
        bad = Path(self.tmp.name) / "bad-policy.json"
        bad.write_text("{ this is not json", encoding="utf-8")
        self.invoke("--policy", str(bad), "--now", at(60), "tick", expect=cc.EXIT_FAIL)
        self.assertEqual(self.caps(), self.before)

    def test_policy_with_a_wrong_schema_is_refused(self) -> None:
        bad = Path(self.tmp.name) / "v2-policy.json"
        bad.write_text(json.dumps({"schema_version": 2}), encoding="utf-8")
        self.invoke("--policy", str(bad), "--now", at(60), "tick", expect=cc.EXIT_FAIL)
        self.assertEqual(self.caps(), self.before)

    def test_a_policy_may_not_carry_the_ceiling(self) -> None:
        policy = json.loads((REPO_ROOT / "local" / "capacity-policy.json").read_text())
        policy["ceiling_source"] = "policy"
        bad = Path(self.tmp.name) / "ceiling-policy.json"
        bad.write_text(json.dumps(policy), encoding="utf-8")
        self.invoke("--policy", str(bad), "--now", at(60), "tick", expect=cc.EXIT_FAIL)

    def test_malformed_run_mode_leaves_the_cap_files_untouched(self) -> None:
        (self.watchdog / "run-mode.json").write_text("{]", encoding="utf-8")
        self.invoke("--now", at(60), "tick", expect=cc.EXIT_FAIL)
        self.assertEqual(self.caps(), self.before)

    def test_missing_run_mode_is_loud_not_zero_capacity(self) -> None:
        (self.watchdog / "run-mode.json").unlink()
        self.invoke("--now", at(60), "tick", expect=cc.EXIT_FAIL)
        self.assertEqual(self.caps(), self.before, "never 'zero capacity', never 'unlimited'")

    def test_reserved_above_nominal_is_refused(self) -> None:
        self.write_run_mode(second=4, reserved=9)
        self.invoke("--now", at(60), "tick", expect=cc.EXIT_FAIL)
        self.assertEqual(self.caps(), self.before)

    def test_a_malformed_session_row_does_not_stop_the_loop(self) -> None:
        with (self.telemetry / "sessions.jsonl").open("a", encoding="utf-8") as handle:
            handle.write("{not json at all\n")
        self.session(10, "api.finite-dimensional.space", "concurrency_limit")
        self.tick(20, live={"primary": 0, "second": 20})
        self.assertEqual(self.caps()["second"], 19)


class RecordTests(CapacityHarness):
    def test_one_capacity_row_per_tick(self) -> None:
        self.invoke("--now", at(0), "init")
        self.tick(60)
        self.tick(120)
        rows = [json.loads(line) for line in
                (self.telemetry / "stages.jsonl").read_text(encoding="utf-8").splitlines() if line]
        ticks = [row for row in rows if row.get("stage") == "capacity"
                 and row.get("event") == "tick"]
        self.assertEqual(len(ticks), 2)
        self.assertIn("accounts", ticks[0]["capacity"])
        self.assertEqual(ticks[0]["capacity"]["accounts"]["primary"]["cap"], 5)

    def test_estimate_carries_the_measurement_fields(self) -> None:
        self.invoke("--now", at(0), "init")
        self.tick(60, live={"primary": 3, "second": 0})
        estimate = json.loads(
            (self.watchdog / "capacity" / "limit-estimate.json").read_text(encoding="utf-8"))
        row = estimate["accounts"]["second"]
        for field in ("nominal", "external_reserved", "cap_now", "live", "waiters",
                      "refusals_5m", "deaths_5m_by_class", "measured_limit",
                      "observed_refusal_floor", "external_inferred", "health", "updated"):
            self.assertIn(field, row)

    def test_measured_limit_needs_a_sustained_clean_window(self) -> None:
        self.invoke("--now", at(0), "init")
        busy = {"primary": 4, "second": 12}
        self.tick(10, live=busy)
        self.tick(300, live=busy)
        self.assertIsNone(self.state()["accounts"]["second"]["measured_limit"],
                          "five minutes is not the ten-minute hold")
        self.tick(700, live=busy)
        self.assertEqual(self.state()["accounts"]["second"]["measured_limit"], 12)

    def test_init_carries_the_measurement_into_the_next_run(self) -> None:
        self.invoke("--now", at(0), "init")
        busy = {"primary": 4, "second": 12}
        self.tick(10, live=busy)
        self.tick(700, live=busy)
        self.invoke("--now", at(800), "init")
        self.assertEqual(self.caps()["second"], 12,
                         "the next run starts below the cliff, not above it")
        self.assertEqual(self.state()["accounts"]["second"]["measured_limit"], 12)

    def test_init_force_discards_the_measurement(self) -> None:
        self.invoke("--now", at(0), "init")
        busy = {"primary": 4, "second": 12}
        self.tick(10, live=busy)
        self.tick(700, live=busy)
        self.invoke("--now", at(800), "init", "--force")
        self.assertEqual(self.caps()["second"], 28)

    def test_dry_run_writes_nothing(self) -> None:
        self.invoke("--now", at(0), "init", "--dry-run")
        self.assertFalse((self.watchdog / "max-codex").exists())
        self.assertFalse((self.watchdog / "capacity" / "state.json").exists())


if __name__ == "__main__":
    unittest.main()
