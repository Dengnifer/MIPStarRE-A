#!/usr/bin/env python3
"""N named accounts through `local/bin/account_router.py`.

Two key names were hard-coded through the layer — ``ACCOUNTS = ("primary",
"second")``, ``for account in primary second``, the ``--account`` choices — so
the owner's third key could not be expressed at all.  These cases check the
generalization and, just as importantly, that the two historical names keep
behaving exactly as they did: every existing brief, cap file and session row
must survive untouched.

Nothing here contacts ghz: temporary directories, no ``gh``, no ``codex``.
"""

from __future__ import annotations

import json
import os
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "local" / "bin"))

import account_router as ar  # noqa: E402
import accounts_file as af  # noqa: E402


class RouterHarness(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name) / "cache"
        self.watchdog = self.root / "watchdog"
        self.watchdog.mkdir(parents=True)
        (self.root / "accounts").mkdir(parents=True)
        environment = mock.patch.dict(os.environ, {
            "MIPSTARRE_CACHE_ROOT": str(self.root)})
        environment.start()
        self.addCleanup(environment.stop)
        os.environ.pop("MIPSTARRE_CODEX_HOME_SECOND", None)

    def caps(self, **values: int) -> None:
        for name, value in values.items():
            (self.watchdog / f"max-codex-{name}").write_text(f"{value}\n",
                                                             encoding="utf-8")

    def accounts(self, *entries: dict) -> None:
        af.save(list(entries), root=self.root, actor="test", action="write",
                detail="fixture")

    def entry(self, name: str, ceiling: int = 10, **fields) -> dict:
        row = {"name": name, "label": name, "endpoint": f"api.{name}.example",
               "codex_home": str(self.root / f"codex-{name}"), "ceiling": ceiling,
               "external_reserved": 0, "enabled": True, "note": ""}
        row.update(fields)
        return row

    def occupy(self, account: str, count: int) -> None:
        directory = self.root / "accounts" / account
        directory.mkdir(parents=True, exist_ok=True)
        for index in range(count):
            # Our own pid is alive by definition, so these markers count as live
            # without spawning anything.
            (directory / str(os.getpid() - index if os.getpid() - index > 0
                             else index + 1)).touch()

    def health_down(self, account: str) -> None:
        path = self.watchdog / "capacity" / f"health-{account}.json"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps({"state": "down", "reason": "auth: 401"}),
                        encoding="utf-8")


class TestAccountNames(RouterHarness):
    def test_the_live_file_is_the_first_source(self) -> None:
        self.accounts(self.entry("primary", 5), self.entry("second", 30),
                      self.entry("third", 8))
        self.assertEqual(ar.account_names(self.root), ("primary", "second", "third"))

    def test_cap_files_are_the_second_source(self) -> None:
        self.caps(primary=5, second=28, third=8)
        self.assertEqual(ar.account_names(self.root), ("primary", "second", "third"))
        self.assertNotIn("max-codex", ar.account_names(self.root))

    def test_the_two_historical_names_are_the_last_fallback(self) -> None:
        self.assertEqual(ar.account_names(self.root), ar.DEFAULT_ACCOUNTS)

    def test_an_invalid_file_falls_through_instead_of_stopping_dispatch(self) -> None:
        # The capacity controller reports that error loudly; admission must not
        # stop because the owner mistyped a field.
        (self.watchdog / "accounts.json").write_text("{oops", encoding="utf-8")
        self.caps(primary=5, second=28)
        self.assertEqual(ar.account_names(self.root), ("primary", "second"))

    def test_homes_come_from_the_file_with_the_historical_defaults(self) -> None:
        self.accounts(self.entry("primary", 5), self.entry("third", 8))
        homes = ar.account_homes(self.root)
        self.assertEqual(homes["third"], self.root / "codex-third")
        self.assertIn("second", homes)  # the historical default survives


class TestEffectiveCaps(RouterHarness):
    def test_a_down_endpoint_is_zero(self) -> None:
        self.caps(primary=5, second=28)
        self.health_down("primary")
        self.assertEqual(ar.effective_caps(self.root), [0, 28])

    def test_an_account_the_owner_disabled_is_zero_before_the_next_tick(self) -> None:
        # Between the owner's edit and the controller's tick — up to 60 s — the
        # cap file still holds the old number.  Reading the file here closes the
        # window, and can only ever narrow admission.
        self.accounts(self.entry("primary", 5), self.entry("second", 30, enabled=False))
        self.caps(primary=5, second=28)
        self.assertEqual(ar.effective_caps(self.root), [5, 0])

    def test_a_missing_cap_file_is_zero_not_unlimited(self) -> None:
        self.accounts(self.entry("primary", 5), self.entry("third", 8))
        self.caps(primary=5)
        self.assertEqual(ar.effective_caps(self.root), [5, 0])

    def test_a_negative_cap_is_refused(self) -> None:
        self.caps(primary=-1, second=1)
        with self.assertRaises(ValueError):
            ar.effective_caps(self.root)


class TestChooseAccount(RouterHarness):
    def test_two_accounts_behave_exactly_as_before(self) -> None:
        names = ("primary", "second")
        # The historical rule was live[0]*caps[1] <= live[1]*caps[0] -> primary.
        for live, caps, expected in (
                ([0, 0], [5, 30], "primary"),
                ([5, 0], [5, 30], "second"),
                ([1, 6], [5, 30], "primary"),
                ([2, 6], [5, 30], "second"),
                ([1, 6], [5, 30], "primary")):
            with self.subTest(live=live, caps=caps):
                historical = ("primary" if live[0] * caps[1] <= live[1] * caps[0]
                              else "second")
                self.assertEqual(ar.choose_account(live, caps, names), expected)
                self.assertEqual(ar.choose_account(live, caps, names), historical)

    def test_the_emptiest_key_wins_across_three(self) -> None:
        names = ("primary", "second", "third")
        self.assertEqual(ar.choose_account([4, 3, 0], [5, 30, 8], names), "third")
        self.assertEqual(ar.choose_account([4, 3, 7], [5, 30, 8], names), "second")

    def test_a_zero_cap_is_never_chosen(self) -> None:
        # Treating a zero cap as infinitely free is how a dead endpoint attracted
        # every dispatch on 2026-09-12.
        names = ("primary", "second")
        self.assertEqual(ar.choose_account([0, 0], [0, 4], names), "second")


class TestReserve(RouterHarness):
    def test_a_third_account_is_reservable(self) -> None:
        self.accounts(self.entry("primary", 5), self.entry("second", 30),
                      self.entry("third", 8))
        self.caps(primary=0, second=0, third=2)
        self.assertEqual(ar.reserve(self.root, "auto", 4242, 0, True), "third")
        self.assertEqual(ar.reserve(self.root, "third", 4242, 0, True), "third")

    def test_an_unconfigured_name_is_refused_by_name(self) -> None:
        self.accounts(self.entry("primary", 5), self.entry("second", 30))
        self.caps(primary=5, second=28)
        with self.assertRaises(ValueError) as caught:
            ar.reserve(self.root, "fourth", 4242, 0, True)
        self.assertIn("fourth", str(caught.exception))
        self.assertIn("accounts.sh add", str(caught.exception))

    def test_a_full_account_is_not_a_candidate(self) -> None:
        self.accounts(self.entry("primary", 5), self.entry("second", 30))
        self.caps(primary=1, second=4)
        self.occupy("primary", 1)
        self.assertEqual(ar.reserve(self.root, "auto", 4242, 0, True), "second")

    def test_exhausted_capacity_raises_rather_than_choosing_anyway(self) -> None:
        self.caps(primary=0, second=0)
        with self.assertRaises(ValueError) as caught:
            ar.reserve(self.root, "auto", 4242, 0, True)
        self.assertIn("capacity exhausted", str(caught.exception))

    def test_drain_still_releases_a_queued_reservation(self) -> None:
        self.accounts(self.entry("primary", 5))
        self.caps(primary=0)
        (self.watchdog / "drain").write_text("", encoding="utf-8")
        with self.assertRaises(ar.DrainRequested):
            ar.reserve(self.root, "auto", 4242, 0, True)

    def test_a_dry_run_reserves_nothing(self) -> None:
        self.accounts(self.entry("primary", 5))
        self.caps(primary=5)
        ar.reserve(self.root, "auto", 4242, 0, True)
        self.assertFalse((self.root / "accounts" / "primary" / "4242").exists())


class TestAffinity(RouterHarness):
    def test_a_retired_account_still_owns_its_thread(self) -> None:
        # Affinity is judged on the recorded name, not on today's list: reading a
        # historical row as "not an account" would silently turn a resume into a
        # fresh thread.
        self.assertTrue(ar.is_account_name("retired-key"))
        self.assertFalse(ar.is_account_name(""))
        self.assertFalse(ar.is_account_name("Not Valid"))
        self.assertFalse(ar.is_account_name(None))

    def test_resume_account_reads_any_valid_name(self) -> None:
        registry = self.root / "sessions.jsonl"
        registry.write_text(json.dumps({
            "name": "prover-1", "thread_id": "abc", "account": "third"}) + "\n",
            encoding="utf-8")
        self.assertEqual(ar.resume_account("abc", registry, {}), "third")


if __name__ == "__main__":
    unittest.main()
