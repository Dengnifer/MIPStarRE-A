#!/usr/bin/env python3
"""pause → resume round trip of local/bin/capacity_controller.py.

The 2026-09-12 pause chain wrote ``watchdog/caps-before-pause`` in one format, a
later phase overwrote it with another (``primary 0 second 0 total 0``), and the
resume script's ``grep -o '^primary=[0-9]*'`` then restored nothing — it would
have written *empty* cap files, and every dispatch would have died at
``invalid literal for int()``.  These tests hold the two properties that make
that impossible: the saved caps live inside ``state.json``, and no cap file is
ever empty or non-numeric at any point of the cycle.
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
T0 = datetime(2026, 9, 12, 8, 0, 0, tzinfo=timezone.utc)
CAP_FILES = ("max-codex", "max-codex-primary", "max-codex-second")


def at(seconds: int) -> str:
    return (T0 + timedelta(seconds=seconds)).strftime("%Y-%m-%dT%H:%M:%SZ")


class RoundTripTests(unittest.TestCase):
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
        for name in ("MIPSTARRE_CAPACITY_POLICY", "MIPSTARRE_CAPACITY_PROBE_CMD",
                     "MIPSTARRE_RUN_MODE"):
            os.environ.pop(name, None)
        (self.watchdog / "run-mode.json").write_text(json.dumps({
            "schema": "mipstarre-run-mode/1", "brief_sha256": "2" * 64,
            "run": {"label": "pause round trip"},
            "accounts": [
                {"name": "primary", "endpoint": "relay-us7",
                 "codex_home": str(self.cache / "codex-primary"),
                 "nominal_limit": 5, "external_reserved": 0, "enabled": True},
                {"name": "second", "endpoint": "api.finite-dimensional.space",
                 "codex_home": str(self.cache / "codex-second"),
                 "nominal_limit": 30, "external_reserved": 2, "enabled": True}],
        }), encoding="utf-8")
        self.invoke("--now", at(0), "init")
        self.invoke("--now", at(0), "set", "second", "22")

    # -- helpers -----------------------------------------------------------

    def invoke(self, *argv: str, live=None, expect: int = 0) -> str:
        live = live or {"primary": 0, "second": 0}
        out, err = io.StringIO(), io.StringIO()
        with mock.patch.object(cc, "count_live", return_value=dict(live)), \
                mock.patch.object(cc, "count_waiters", return_value=0), \
                contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = cc.main(list(argv))
        self.assertEqual(code, expect, f"argv={argv}\n{out.getvalue()}{err.getvalue()}")
        self.assert_cap_files_sane()
        return out.getvalue()

    def tick(self, seconds: int, live=None) -> None:
        self.invoke("--now", at(seconds), "tick", live=live)

    def assert_cap_files_sane(self) -> None:
        """No cap file is ever empty, absent or non-numeric once a run is seeded."""
        for name in CAP_FILES:
            path = self.watchdog / name
            if not path.exists():
                continue
            text = path.read_text(encoding="utf-8")
            self.assertRegex(text, NUMERIC, f"{name} must stay a bare nonnegative integer")

    def caps(self) -> dict:
        return {name: int((self.watchdog / f"max-codex-{name}").read_text(encoding="utf-8"))
                for name in ("primary", "second")}

    def total(self) -> int:
        return int((self.watchdog / "max-codex").read_text(encoding="utf-8"))

    def state(self) -> dict:
        return json.loads((self.watchdog / "capacity" / "state.json").read_text(encoding="utf-8"))

    # -- the round trip ----------------------------------------------------

    def test_pause_then_resume_brings_the_caps_back(self) -> None:
        before = self.caps()
        self.assertEqual(before, {"primary": 5, "second": 22})
        self.invoke("--now", at(60), "pause", "--reason", "owner word 08:18Z")
        self.assertEqual(self.caps(), {"primary": 0, "second": 0})
        self.assertEqual(self.total(), 0)
        self.invoke("--now", at(900), "resume")
        self.assertEqual(self.caps(), before, "resume restores the caps the pause saved")
        self.assertEqual(self.total(), 27)

    def test_the_saved_caps_live_inside_state_json(self) -> None:
        self.invoke("--now", at(60), "pause")
        state = self.state()
        self.assertEqual(state["accounts"]["second"]["saved_cap"], 22)
        self.assertEqual(state["accounts"]["primary"]["saved_cap"], 5)
        self.assertIsNotNone(state["paused_at"])
        self.assertFalse((self.watchdog / "caps-before-pause").exists(),
                         "the caps are never written to a second file a later phase can clobber")

    def test_a_second_pause_does_not_clobber_the_saved_caps(self) -> None:
        self.invoke("--now", at(60), "pause")
        self.invoke("--now", at(120), "pause")
        self.assertEqual(self.state()["accounts"]["second"]["saved_cap"], 22)
        self.invoke("--now", at(900), "resume")
        self.assertEqual(self.caps(), {"primary": 5, "second": 22})

    def test_a_tick_while_paused_holds_zero_and_keeps_the_save(self) -> None:
        self.invoke("--now", at(60), "pause")
        self.tick(120, live={"primary": 0, "second": 0})
        self.tick(400, live={"primary": 0, "second": 0})
        self.assertEqual(self.caps(), {"primary": 0, "second": 0},
                         "AIMD must not climb out of a pause")
        self.assertEqual(self.state()["accounts"]["second"]["saved_cap"], 22)
        self.invoke("--now", at(900), "resume")
        self.assertEqual(self.caps(), {"primary": 5, "second": 22})

    def test_resume_re_enters_aimd_at_the_saved_value(self) -> None:
        self.invoke("--now", at(60), "pause")
        self.invoke("--now", at(900), "resume")
        busy = {"primary": 0, "second": 22}
        self.tick(910, live=busy)
        self.assertEqual(self.caps()["second"], 22, "the quiet window restarts at resume")
        self.tick(1040, live=busy)
        self.assertEqual(self.caps()["second"], 23, "and then AIMD climbs from the saved value")

    def test_resume_yields_zero_for_a_down_endpoint(self) -> None:
        self.invoke("--now", at(60), "pause")
        (self.watchdog / "capacity" / "health-primary.json").write_text(json.dumps({
            "account": "primary", "endpoint": "relay-us7", "state": "down", "since": at(0),
            "consecutive_5xx": 3, "next_probe_at": at(3600), "backoff_s": 30, "probes_ok": 0}),
            encoding="utf-8")
        self.invoke("--now", at(900), "resume")
        self.assertEqual(self.caps(), {"primary": 0, "second": 22},
                         "health outranks a saved number")
        self.assertEqual(self.total(), 22)

    def test_resume_without_state_is_loud(self) -> None:
        (self.watchdog / "capacity" / "state.json").unlink()
        self.invoke("--now", at(900), "resume", expect=cc.EXIT_FAIL)

    def test_every_cap_file_stays_numeric_through_the_cycle(self) -> None:
        # assert_cap_files_sane runs after every invoke; this walks the whole
        # cycle so that guard sees each state of it.
        self.tick(10, live={"primary": 5, "second": 22})
        self.invoke("--now", at(60), "pause")
        self.tick(70, live={"primary": 3, "second": 10})
        self.invoke("--now", at(900), "resume")
        self.tick(910, live={"primary": 5, "second": 22})
        self.invoke("--now", at(920), "set", "primary", "0")
        self.assertEqual(self.caps()["primary"], 0,
                         "set is the supported replacement for echo 0 > max-codex-primary")
        self.assertEqual(self.total(), self.caps()["primary"] + self.caps()["second"])

    def test_state_json_is_the_record_a_hand_edit_is_not(self) -> None:
        (self.watchdog / "max-codex-second").write_text("99\n", encoding="utf-8")
        self.tick(10, live={"primary": 0, "second": 0})
        self.assertEqual(self.caps()["second"], 22,
                         "the controller is the sole writer; a hand edit is overwritten")

    def test_pause_and_resume_are_recorded(self) -> None:
        self.invoke("--now", at(60), "pause", "--reason", "owner word")
        self.invoke("--now", at(900), "resume")
        rows = [json.loads(line) for line in
                (self.telemetry / "stages.jsonl").read_text(encoding="utf-8").splitlines() if line]
        events = [row["event"] for row in rows if row.get("stage") == "capacity"]
        self.assertIn("pause", events)
        self.assertIn("resume", events)

    def test_dry_run_pause_changes_nothing(self) -> None:
        before = self.caps()
        self.invoke("--now", at(60), "pause", "--dry-run")
        self.assertEqual(self.caps(), before)
        self.assertIsNone(self.state()["paused_at"])


if __name__ == "__main__":
    unittest.main()
