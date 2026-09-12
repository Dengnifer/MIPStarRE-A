#!/usr/bin/env python3
"""Endpoint health in local/bin/capacity_controller.py.

The 05:30Z-05:58Z relay-us7 outage of 2026-09-12 in miniature: three 503 deaths
inside two minutes must take the account to cap 0 without a human, and the way
back must be a half-open probe that restores one slot, not the pre-outage cap.
The probe never runs `codex` here — ``MIPSTARRE_CAPACITY_PROBE_CMD`` points at a
script that records its calls and returns a chosen status.
"""

from __future__ import annotations

import contextlib
import fcntl
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
T0 = datetime(2026, 9, 12, 5, 30, 0, tzinfo=timezone.utc)
ENDPOINT = "relay-us7"


def at(seconds: int) -> str:
    return (T0 + timedelta(seconds=seconds)).strftime("%Y-%m-%dT%H:%M:%SZ")


class HealthHarness(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        root = Path(self.tmp.name)
        self.cache = root / "cache"
        self.telemetry = root / "telemetry"
        self.telemetry.mkdir(parents=True)
        self.watchdog = self.cache / "watchdog"
        self.watchdog.mkdir(parents=True)
        self.codex_home = root / "codex-primary"
        self.probe_log = root / "probe.log"
        self.probe_rc = root / "probe.rc"
        self.probe_rc.write_text("0\n", encoding="utf-8")
        probe = root / "probe.sh"
        probe.write_text(
            "#!/bin/sh\n"
            f'printf "%s %s\\n" "$MIPSTARRE_CAPACITY_PROBE" "$CODEX_HOME" >> "{self.probe_log}"\n'
            f'exit "$(cat "{self.probe_rc}")"\n', encoding="utf-8")
        probe.chmod(0o755)
        environment = mock.patch.dict(os.environ, {
            "MIPSTARRE_CACHE_ROOT": str(self.cache),
            "MIPSTARRE_TELEMETRY_DIR": str(self.telemetry),
            "MIPSTARRE_REPO_ROOT": str(REPO_ROOT),
            "MIPSTARRE_CAPACITY_PROBE_CMD": str(probe),
        })
        environment.start()
        self.addCleanup(environment.stop)
        os.environ.pop("MIPSTARRE_CAPACITY_POLICY", None)
        os.environ.pop("MIPSTARRE_RUN_MODE", None)
        (self.watchdog / "run-mode.json").write_text(json.dumps({
            "schema": "mipstarre-run-mode/1", "brief_sha256": "1" * 64,
            "run": {"label": "outage test"},
            "accounts": [
                {"name": "primary", "endpoint": ENDPOINT, "codex_home": str(self.codex_home),
                 "nominal_limit": 30, "external_reserved": 0, "enabled": True},
                {"name": "second", "endpoint": "api.finite-dimensional.space",
                 "codex_home": str(self.cache / "codex-second"),
                 "nominal_limit": 10, "external_reserved": 0, "enabled": True}],
        }), encoding="utf-8")
        self.invoke("--now", at(0), "init")

    # -- helpers -----------------------------------------------------------

    def invoke(self, *argv: str, live=None, expect: int = 0) -> str:
        live = live or {"primary": 0, "second": 0}
        out, err = io.StringIO(), io.StringIO()
        with mock.patch.object(cc, "count_live", return_value=dict(live)), \
                mock.patch.object(cc, "count_waiters", return_value=0), \
                contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = cc.main(list(argv))
        self.assertEqual(code, expect, f"argv={argv}\n{out.getvalue()}{err.getvalue()}")
        return out.getvalue()

    def tick(self, seconds: int, live=None) -> None:
        self.invoke("--now", at(seconds), "tick", live=live)

    def outage(self, *offsets: int, account_endpoint: str = ENDPOINT) -> None:
        with (self.telemetry / "sessions.jsonl").open("a", encoding="utf-8") as handle:
            for offset in offsets:
                handle.write(json.dumps({
                    "name": f"reviewer-{offset}", "role": "reviewer", "issue": "1",
                    "start": at(offset), "end": at(offset), "status": "failed", "exit": 1,
                    "endpoint": account_endpoint, "failure_class": "endpoint_5xx",
                    "failure_detail": "503 Service Unavailable"}) + "\n")

    def cap(self, account: str = "primary") -> int:
        text = (self.watchdog / f"max-codex-{account}").read_text(encoding="utf-8")
        self.assertRegex(text, NUMERIC)
        return int(text)

    def health(self, account: str = "primary") -> dict:
        return json.loads(
            (self.watchdog / "capacity" / f"health-{account}.json").read_text(encoding="utf-8"))

    def probe_calls(self) -> list[str]:
        if not self.probe_log.exists():
            return []
        return [line for line in self.probe_log.read_text(encoding="utf-8").splitlines() if line]


class TripTests(HealthHarness):
    def test_three_in_the_window_trips_to_cap_zero(self) -> None:
        self.assertEqual(self.cap(), 30)
        self.outage(10, 40, 70)
        self.tick(80, live={"primary": 20, "second": 0})
        self.assertEqual(self.health()["state"], "down")
        self.assertEqual(self.cap(), 0, "a dead endpoint stops consuming sessions at once")
        self.assertEqual(self.health()["consecutive_5xx"], 3)

    def test_two_in_the_window_is_degraded_not_down(self) -> None:
        self.outage(10, 40)
        self.tick(50, live={"primary": 20, "second": 0})
        self.assertEqual(self.health()["state"], "degraded")
        self.assertEqual(self.cap(), 30, "below the threshold the cap is not cut")

    def test_three_spread_beyond_the_window_do_not_trip(self) -> None:
        self.outage(10, 100, 200)
        self.tick(210, live={"primary": 20, "second": 0})
        self.assertEqual(self.health()["state"], "degraded")
        self.assertEqual(self.cap(), 30)

    def test_the_other_account_is_untouched(self) -> None:
        self.outage(10, 40, 70)
        self.tick(80, live={"primary": 20, "second": 5})
        self.assertEqual(self.health("second")["state"], "up")
        self.assertEqual(self.cap("second"), 10)

    def test_the_trip_is_recorded_in_the_stage_row(self) -> None:
        self.outage(10, 40, 70)
        self.tick(80, live={"primary": 20, "second": 0})
        rows = [json.loads(line) for line in
                (self.telemetry / "stages.jsonl").read_text(encoding="utf-8").splitlines() if line]
        trip = [row for row in rows if row.get("stage") == "capacity"
                and "endpoint down" in row.get("note", "")]
        self.assertEqual(len(trip), 1)


class RecoveryTests(HealthHarness):
    def trip(self) -> None:
        self.outage(10, 40, 70)
        self.tick(80, live={"primary": 20, "second": 0})
        self.assertEqual(self.health()["state"], "down")

    def test_two_consecutive_probes_restore_exactly_one_slot(self) -> None:
        self.trip()
        self.tick(100, live={"primary": 0, "second": 0})
        self.assertEqual(self.probe_calls(), [], "the backoff has not elapsed")
        self.tick(115, live={"primary": 0, "second": 0})
        self.assertEqual(len(self.probe_calls()), 1)
        self.assertEqual(self.health()["state"], "down", "one success is not two")
        self.assertEqual(self.health()["probes_ok"], 1)
        self.assertEqual(self.cap(), 0)
        self.tick(150, live={"primary": 0, "second": 0})
        self.assertEqual(len(self.probe_calls()), 2)
        self.assertEqual(self.health()["state"], "up")
        self.assertEqual(self.cap(), 1,
                         "recovery restores one slot, never the pre-outage cap of 30")

    def test_the_cap_climbs_from_one_by_aimd(self) -> None:
        self.trip()
        self.tick(115)
        self.tick(150)
        self.assertEqual(self.cap(), 1)
        busy = {"primary": 1, "second": 0}
        self.tick(200, live=busy)
        self.tick(340, live=busy)
        self.assertEqual(self.cap(), 1, "the deaths are still inside the five-minute window")
        self.tick(400, live=busy)
        self.tick(530, live=busy)
        self.assertEqual(self.cap(), 2, "one slot per quiet window, from one")

    def test_a_failed_probe_doubles_the_backoff(self) -> None:
        self.trip()
        self.probe_rc.write_text("1\n", encoding="utf-8")
        self.tick(115)
        self.assertEqual(len(self.probe_calls()), 1)
        self.assertEqual(self.health()["backoff_s"], 60)
        self.assertEqual(self.health()["state"], "down")
        self.tick(150)
        self.assertEqual(len(self.probe_calls()), 1, "the doubled backoff has not elapsed")
        self.tick(180)
        self.assertEqual(len(self.probe_calls()), 2)
        self.assertEqual(self.health()["backoff_s"], 120)

    def test_a_failure_after_a_success_restarts_the_count(self) -> None:
        self.trip()
        self.tick(115)
        self.assertEqual(self.health()["probes_ok"], 1)
        self.probe_rc.write_text("1\n", encoding="utf-8")
        self.tick(150)
        self.assertEqual(self.health()["probes_ok"], 0, "consecutive means consecutive")
        self.assertEqual(self.health()["state"], "down")

    def test_the_probe_carries_the_account_codex_home(self) -> None:
        self.trip()
        self.tick(115)
        self.assertEqual(self.probe_calls(), [f"primary {self.codex_home}"])

    def test_a_hold_stops_the_probe_and_freezes_the_cap(self) -> None:
        self.trip()
        (self.watchdog / "capacity" / "hold").touch()
        self.tick(115)
        self.tick(400)
        self.assertEqual(self.probe_calls(), [], "the probe never runs under a hold")
        self.assertEqual(self.cap(), 0)
        self.assertEqual(self.health()["state"], "down", "health handling continues under a hold")

    def test_the_probe_is_single_flight(self) -> None:
        self.trip()
        lock_file = self.watchdog / "capacity" / "probe-primary.lock"
        lock_file.parent.mkdir(parents=True, exist_ok=True)
        with lock_file.open("a") as held:
            fcntl.flock(held, fcntl.LOCK_EX)
            self.tick(115)
        self.assertEqual(self.probe_calls(), [],
                         "another tick holds the probe lock; this one must not probe")
        self.assertEqual(self.health()["state"], "down")

    def test_recovery_survives_a_later_clean_window(self) -> None:
        self.trip()
        self.tick(115)
        self.tick(150)
        self.assertEqual(self.health()["state"], "up")
        self.tick(400)
        self.assertEqual(self.health()["state"], "up",
                         "the outage rows are outside the window and must not re-trip")


class HoldTests(HealthHarness):
    def test_a_hold_freezes_a_healthy_cap(self) -> None:
        self.invoke("--now", at(0), "set", "primary", "4")
        (self.watchdog / "capacity" / "hold").touch()
        busy = {"primary": 4, "second": 0}
        self.tick(10, live=busy)
        self.tick(400, live=busy)
        self.assertEqual(self.cap(), 4, "the operator owns the number while the file exists")
        (self.watchdog / "capacity" / "hold").unlink()
        self.tick(500, live=busy)
        self.tick(700, live=busy)
        self.assertEqual(self.cap(), 5, "removing the hold hands the number back to AIMD")

    def test_a_hold_freezes_the_tick_not_the_explicit_commands(self) -> None:
        (self.watchdog / "capacity" / "hold").touch()
        self.invoke("--now", at(10), "set", "primary", "7")
        self.assertEqual(self.cap(), 7, "an explicit operator command acts under a hold")
        self.tick(200, live={"primary": 7, "second": 0})
        self.tick(400, live={"primary": 7, "second": 0})
        self.assertEqual(self.cap(), 7, "but the tick still does not move it")


if __name__ == "__main__":
    unittest.main()
