#!/usr/bin/env python3
"""The two additive admission inputs of local/bin/account_router.py.

`watchdog/drain` releases a queued dispatch cleanly instead of having it killed,
and an endpoint the capacity controller marked `down` is treated as cap 0 —
without which `choose_account` *prefers* the dead account, because its sessions
keep dying and freeing slots.

The first class of test here is the one that matters most: **absent files must
change nothing.**  Every existing invariant is re-asserted alongside — dead
markers are reaped, a permission-denied pid stays occupied, a dry run neither
waits nor reserves, and an explicit account never spills to the other one.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path
from unittest import mock

REPO_ROOT = Path(__file__).resolve().parents[2]
ROUTER = REPO_ROOT / "local" / "bin" / "account_router.py"
sys.path.insert(0, str(ROUTER.parent))

import account_router as ar  # noqa: E402


class RouterHarness(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.watchdog = self.root / "watchdog"
        self.watchdog.mkdir(parents=True)
        self.accounts = self.root / "accounts"
        self.set_caps(primary=2, second=2)

    def set_caps(self, *, primary: int, second: int) -> None:
        (self.watchdog / "max-codex-primary").write_text(f"{primary}\n", encoding="utf-8")
        (self.watchdog / "max-codex-second").write_text(f"{second}\n", encoding="utf-8")
        (self.watchdog / "max-codex").write_text(f"{primary + second}\n", encoding="utf-8")

    def mark_health(self, account: str, state: str) -> None:
        path = self.watchdog / "capacity" / f"health-{account}.json"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps({"account": account, "state": state,
                                    "since": "2026-09-12T05:58:00Z", "consecutive_5xx": 3,
                                    "next_probe_at": "2026-09-12T06:08:00Z"}), encoding="utf-8")

    def occupy(self, account: str, pid: int) -> None:
        directory = self.accounts / account
        directory.mkdir(parents=True, exist_ok=True)
        (directory / str(pid)).touch()

    def dead_pid(self) -> int:
        process = subprocess.Popen([sys.executable, "-c", "pass"])
        process.wait()
        return process.pid

    def cli(self, *argv: str) -> subprocess.CompletedProcess:
        return subprocess.run([sys.executable, str(ROUTER), *argv],
                              capture_output=True, text=True, timeout=60)


class AbsentFilesChangeNothingTests(RouterHarness):
    """The regression that matters: with neither new file, nothing moved."""

    def test_reserve_still_reserves(self) -> None:
        selected = ar.reserve(self.root, "auto", os.getpid(), 0)
        self.assertIn(selected, ar.ACCOUNTS)
        self.assertTrue((self.accounts / selected / str(os.getpid())).exists())

    def test_effective_caps_are_the_cap_files(self) -> None:
        self.set_caps(primary=3, second=7)
        self.assertEqual(ar.effective_caps(self.root), [3, 7])

    def test_a_missing_cap_file_is_still_zero(self) -> None:
        (self.watchdog / "max-codex-primary").unlink()
        self.assertEqual(ar.effective_caps(self.root)[0], 0)

    def test_a_negative_cap_is_still_refused(self) -> None:
        (self.watchdog / "max-codex-second").write_text("-1\n", encoding="utf-8")
        with self.assertRaises(ValueError):
            ar.effective_caps(self.root)

    def test_health_of_an_account_with_no_file_is_up(self) -> None:
        self.assertEqual(ar.health_state(self.root, "primary"), "up")

    def test_an_unreadable_health_file_is_up(self) -> None:
        path = self.watchdog / "capacity" / "health-primary.json"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("{not json", encoding="utf-8")
        self.assertEqual(ar.health_state(self.root, "primary"), "up",
                         "a malformed health file must not narrow admission by accident")
        self.assertEqual(ar.effective_caps(self.root), [2, 2])

    def test_an_unknown_state_is_up(self) -> None:
        self.mark_health("primary", "wobbly")
        self.assertEqual(ar.health_state(self.root, "primary"), "up")

    def test_full_capacity_still_refuses(self) -> None:
        self.set_caps(primary=1, second=0)
        self.occupy("primary", os.getpid())
        with self.assertRaises(ValueError):
            ar.reserve(self.root, "auto", os.getpid(), 0)


class DrainTests(RouterHarness):
    def test_drain_releases_a_queued_dispatch_at_once(self) -> None:
        self.set_caps(primary=0, second=0)
        (self.watchdog / "drain").touch()
        started = time.monotonic()
        with self.assertRaises(ar.DrainRequested):
            ar.reserve(self.root, "auto", os.getpid(), 30)
        self.assertLess(time.monotonic() - started, 5,
                        "a waiter must release itself, not sit out its wait")

    def test_drain_reserves_nothing(self) -> None:
        (self.watchdog / "drain").touch()
        with self.assertRaises(ar.DrainRequested):
            ar.reserve(self.root, "auto", os.getpid(), 0)
        self.assertFalse((self.accounts / "primary" / str(os.getpid())).exists())
        self.assertFalse((self.accounts / "second" / str(os.getpid())).exists())

    def test_drain_has_its_own_exit_status(self) -> None:
        (self.watchdog / "drain").touch()
        result = self.cli("reserve", str(self.root), "auto", str(os.getpid()), "0")
        self.assertEqual(result.returncode, ar.DRAIN_EXIT)
        self.assertIn("drain", result.stderr)
        self.assertNotEqual(ar.DRAIN_EXIT, 4,
                            "a pause must be distinguishable from a bad request")

    def test_removing_the_drain_file_restores_admission(self) -> None:
        (self.watchdog / "drain").touch()
        with self.assertRaises(ar.DrainRequested):
            ar.reserve(self.root, "auto", os.getpid(), 0)
        (self.watchdog / "drain").unlink()
        self.assertIn(ar.reserve(self.root, "auto", os.getpid(), 0), ar.ACCOUNTS)


class DownEndpointTests(RouterHarness):
    def test_a_down_account_is_cap_zero(self) -> None:
        self.mark_health("primary", "down")
        self.assertEqual(ar.effective_caps(self.root), [0, 2])

    def test_a_degraded_account_keeps_its_cap(self) -> None:
        self.mark_health("primary", "degraded")
        self.assertEqual(ar.effective_caps(self.root), [2, 2])

    def test_the_dead_account_is_no_longer_preferred(self) -> None:
        # The self-accelerating outage: primary's sessions keep dying, so its
        # live count is the lowest and choose_account keeps picking it.
        self.mark_health("primary", "down")
        self.occupy("second", os.getpid())
        for _ in range(3):
            self.assertEqual(ar.reserve(self.root, "auto", os.getpid(), 0, dry_run=True),
                             "second")

    def test_an_explicit_down_account_refuses_rather_than_spilling(self) -> None:
        self.mark_health("primary", "down")
        with self.assertRaises(ValueError):
            ar.reserve(self.root, "primary", os.getpid(), 0)
        self.assertFalse((self.accounts / "second" / str(os.getpid())).exists(),
                         "an explicit account never spills to the other one")

    def test_health_never_widens_capacity(self) -> None:
        self.set_caps(primary=0, second=0)
        self.mark_health("primary", "up")
        self.mark_health("second", "up")
        self.assertEqual(ar.effective_caps(self.root), [0, 0])


class PreservedInvariantTests(RouterHarness):
    def test_dead_markers_are_reaped(self) -> None:
        dead = self.dead_pid()
        self.set_caps(primary=1, second=0)
        self.occupy("primary", dead)
        self.assertEqual(ar.reserve(self.root, "primary", os.getpid(), 0), "primary")
        self.assertFalse((self.accounts / "primary" / str(dead)).exists())

    def test_a_permission_denied_pid_stays_occupied(self) -> None:
        self.set_caps(primary=1, second=0)
        self.occupy("primary", 424242)
        with mock.patch("os.kill", side_effect=PermissionError):
            self.assertEqual(ar.live_pids(self.accounts / "primary"), {424242})
            with self.assertRaises(ValueError):
                ar.reserve(self.root, "primary", os.getpid(), 0)
        self.assertTrue((self.accounts / "primary" / "424242").exists(),
                        "a pid owned by another user is live, not stale")

    def test_a_dry_run_reserves_nothing(self) -> None:
        selected = ar.reserve(self.root, "auto", os.getpid(), 0, dry_run=True)
        self.assertIn(selected, ar.ACCOUNTS)
        self.assertFalse((self.accounts / selected / str(os.getpid())).exists())

    def test_a_dry_run_does_not_wait(self) -> None:
        self.set_caps(primary=0, second=0)
        started = time.monotonic()
        with self.assertRaises(ValueError):
            ar.reserve(self.root, "auto", os.getpid(), 30, dry_run=True)
        self.assertLess(time.monotonic() - started, 5)

    def test_an_explicit_account_never_spills(self) -> None:
        self.set_caps(primary=0, second=5)
        with self.assertRaises(ValueError):
            ar.reserve(self.root, "primary", os.getpid(), 0)

    def test_a_bad_request_is_still_rejected(self) -> None:
        with self.assertRaises(ValueError):
            ar.reserve(self.root, "third", os.getpid(), 0)
        with self.assertRaises(ValueError):
            ar.reserve(self.root, "auto", 0, 0)
        with self.assertRaises(ValueError):
            ar.reserve(self.root, "auto", os.getpid(), -1)


if __name__ == "__main__":
    unittest.main()
