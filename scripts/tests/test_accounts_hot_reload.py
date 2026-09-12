#!/usr/bin/env python3
"""The live accounts file, read by the capacity controller on every tick.

The owner's real situation: one to three endpoints, each key's concurrency limit
moving during the run as the endpoint's admin reassigns slots, as a key becomes
invalid, or as one runs out of quota.  On 2026-09-12 every one of those events
reached the pipeline as a message to a session that had to be idle to receive
it, and the caps were edited by hand ten times.  These cases are the mechanism
that replaces both: an edit between two ticks changes the effective cap, a
disabled key is cap 0 with no probe, and a key the provider refuses disables
itself with a reason and probes its own way back.

The probe never runs `codex`: ``MIPSTARRE_CAPACITY_PROBE_CMD`` points at a script
that records its calls and returns a chosen status.  Nothing here contacts ghz.
"""

from __future__ import annotations

import contextlib
import io
import json
import os
import sys
import tempfile
import unittest
from datetime import datetime, timedelta, timezone
from pathlib import Path
from unittest import mock

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "local" / "bin"))

import accounts_file as af  # noqa: E402
import capacity_controller as cc  # noqa: E402

T0 = datetime(2026, 9, 13, 5, 0, 0, tzinfo=timezone.utc)


def at(seconds: int) -> str:
    return (T0 + timedelta(seconds=seconds)).strftime("%Y-%m-%dT%H:%M:%SZ")


class HotReloadHarness(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        root = Path(self.tmp.name)
        self.cache = root / "cache"
        self.telemetry = root / "telemetry"
        self.telemetry.mkdir(parents=True)
        self.watchdog = self.cache / "watchdog"
        self.watchdog.mkdir(parents=True)
        self.probe_log = root / "probe.log"
        self.probe_rc = root / "probe.rc"
        self.probe_rc.write_text("0\n", encoding="utf-8")
        probe = root / "probe.sh"
        probe.write_text(
            "#!/bin/sh\n"
            f'printf "%s\\n" "$MIPSTARRE_CAPACITY_PROBE" >> "{self.probe_log}"\n'
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
        # The run mode holds the briefing; the accounts file holds the truth.
        (self.watchdog / "run-mode.json").write_text(json.dumps({
            "schema": "mipstarre-run-mode/1", "brief_sha256": "2" * 64,
            "run": {"label": "hot reload"},
            "accounts": [
                {"name": "primary", "endpoint": "relay-us7",
                 "codex_home": str(self.cache / "codex-primary"),
                 "nominal_limit": 5, "external_reserved": 0, "enabled": True},
                {"name": "second", "endpoint": "api.finite-dimensional.space",
                 "codex_home": str(self.cache / "codex-second"),
                 "nominal_limit": 30, "external_reserved": 2, "enabled": True}],
        }), encoding="utf-8")
        self.write_accounts([
            {"name": "primary", "label": "relay-us7", "endpoint": "relay-us7",
             "codex_home": str(self.cache / "codex-primary"), "ceiling": 5,
             "external_reserved": 0, "enabled": True, "note": ""},
            {"name": "second", "label": "space",
             "endpoint": "api.finite-dimensional.space",
             "codex_home": str(self.cache / "codex-second"), "ceiling": 30,
             "external_reserved": 2, "enabled": True, "note": ""},
        ])
        self.invoke("--now", at(0), "init")

    # -- helpers -----------------------------------------------------------

    def write_accounts(self, entries: list[dict]) -> None:
        af.save(entries, root=self.cache, actor="test", action="write",
                detail="test fixture")

    def edit(self, name: str, **fields) -> None:
        entries = af.load(self.cache)
        af.apply_fields(entries, name, {key: str(value) for key, value in fields.items()})
        af.save(entries, root=self.cache, actor="owner", action="set",
                detail=f"{name} {fields}")

    def invoke(self, *argv: str, live=None, expect: int = 0) -> str:
        live = live or {}
        out, err = io.StringIO(), io.StringIO()
        with mock.patch.object(cc, "count_live",
                               side_effect=lambda names: {n: live.get(n, 0) for n in names}), \
                mock.patch.object(cc, "count_waiters", return_value=0), \
                contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = cc.main(list(argv))
        self.assertEqual(code, expect, f"argv={argv}\n{out.getvalue()}{err.getvalue()}")
        return out.getvalue() + err.getvalue()

    def tick(self, seconds: int, live=None) -> str:
        return self.invoke("--now", at(seconds), "tick", live=live)

    def cap(self, account: str) -> int:
        return int((self.watchdog / f"max-codex-{account}").read_text(encoding="utf-8"))

    def health(self) -> dict:
        path = self.watchdog / "capacity" / "health.json"
        return json.loads(path.read_text(encoding="utf-8"))["accounts"]

    def failure(self, offset: int, endpoint: str, failure_class: str,
                detail: str = "") -> None:
        with (self.telemetry / "sessions.jsonl").open("a", encoding="utf-8") as handle:
            handle.write(json.dumps({
                "name": f"prover-{failure_class}-{offset}", "role": "prover",
                "issue": "1", "start": at(offset), "end": at(offset),
                "status": "failed", "exit": 1, "endpoint": endpoint,
                "failure_class": failure_class,
                "failure_detail": detail or failure_class}) + "\n")


class TestCeilingIsLive(HotReloadHarness):
    def test_the_file_supersedes_the_run_mode(self) -> None:
        # The run mode says 30; the live file says 30 too, and 2 are reserved.
        self.tick(60)
        self.assertEqual(self.cap("second"), 28)

    def test_lowering_the_ceiling_takes_effect_at_the_next_tick(self) -> None:
        self.tick(60)
        self.assertEqual(self.cap("second"), 28)
        self.edit("second", ceiling=12)          # the admin took slots back
        self.tick(120)
        self.assertEqual(self.cap("second"), 10)  # 12 - 2 reserved
        self.assertEqual(self.cap("primary"), 5)  # untouched

    def test_raising_the_ceiling_lets_aimd_creep_again_but_never_jumps(self) -> None:
        self.edit("second", ceiling=6)
        self.tick(60)
        self.assertEqual(self.cap("second"), 4)
        self.edit("second", ceiling=30)
        self.tick(120, live={"second": 4})
        # A ceiling is a ceiling, not a target: the cap does not leap to 28.
        self.assertLessEqual(self.cap("second"), 5)

    def test_raising_reserved_narrows_the_share_immediately(self) -> None:
        self.tick(60)
        self.edit("second", reserved=25)
        self.tick(120)
        self.assertEqual(self.cap("second"), 5)

    def test_disabled_is_cap_zero_and_no_probe(self) -> None:
        self.tick(60)
        self.edit("second", enabled="false")
        self.tick(120)
        self.assertEqual(self.cap("second"), 0)
        self.assertEqual(self.cap("primary"), 5)
        self.assertEqual(self.probe_calls(), [])
        self.edit("second", enabled="true")
        self.tick(180)
        self.assertGreaterEqual(self.cap("second"), 1)

    def test_a_removed_entry_is_cap_zero_and_leaves_the_others_alone(self) -> None:
        self.tick(60)
        entries = [entry for entry in af.load(self.cache) if entry["name"] != "second"]
        af.save(entries, root=self.cache, actor="owner", action="remove",
                detail="second")
        self.tick(120)
        self.assertEqual(self.cap("second"), 0)
        self.assertEqual(self.cap("primary"), 5)
        self.assertNotIn("second", self.health())

    def test_an_added_key_gets_a_cap_a_health_row_and_a_probe(self) -> None:
        entries = af.load(self.cache)
        af.add(entries, "third", endpoint="api.third.example",
               codex_home=str(self.cache / "codex-third"), ceiling=8)
        af.save(entries, root=self.cache, actor="owner", action="add", detail="third")
        self.tick(120)
        self.assertGreaterEqual(self.cap("third"), 1)
        self.assertEqual(self.health()["third"]["state"], "up")

    def test_an_invalid_file_never_zeroes_the_caps(self) -> None:
        self.tick(60)
        before = {name: self.cap(name) for name in ("primary", "second")}
        (self.watchdog / "accounts.json").write_text("{oops", encoding="utf-8")
        output = self.invoke("--now", at(120), "tick", expect=cc.EXIT_FAIL)
        self.assertIn("accounts.json", output)
        self.assertEqual({name: self.cap(name) for name in ("primary", "second")}, before)

    def probe_calls(self) -> list[str]:
        if not self.probe_log.exists():
            return []
        return [line for line in self.probe_log.read_text(encoding="utf-8").splitlines()
                if line]


class TestMeasuredHealth(HotReloadHarness):
    def probe_calls(self) -> list[str]:
        if not self.probe_log.exists():
            return []
        return [line for line in self.probe_log.read_text(encoding="utf-8").splitlines()
                if line]

    def test_one_auth_failure_disables_the_key_with_a_reason(self) -> None:
        # A 401 is not a statistic: no amount of AIMD makes an invalid key valid.
        self.tick(60)
        self.failure(90, "api.finite-dimensional.space", "auth", "401 Unauthorized")
        self.probe_rc.write_text("1\n", encoding="utf-8")
        self.tick(120)
        self.assertEqual(self.cap("second"), 0)
        row = self.health()["second"]
        self.assertEqual(row["state"], "down")
        self.assertIn("auth", row["reason"])
        self.assertIn("401", row["reason"])
        self.assertEqual(row["disabled_by"], "auth")
        self.assertEqual(self.cap("primary"), 5)   # the other key is untouched

    def test_insufficient_balance_disables_the_key(self) -> None:
        self.tick(60)
        self.failure(90, "api.finite-dimensional.space", "insufficient_balance",
                     "INSUFFICIENT_BALANCE")
        self.probe_rc.write_text("1\n", encoding="utf-8")
        self.tick(120)
        self.assertEqual(self.cap("second"), 0)
        self.assertEqual(self.health()["second"]["disabled_by"], "insufficient_balance")

    def test_a_single_5xx_does_not_disable_but_three_do(self) -> None:
        self.failure(30, "relay-us7", "endpoint_5xx", "503 Service Unavailable")
        self.tick(60)
        self.assertGreater(self.cap("primary"), 0)
        self.assertEqual(self.health()["primary"]["state"], "degraded")
        self.failure(70, "relay-us7", "endpoint_5xx", "503 Service Unavailable")
        self.failure(80, "relay-us7", "endpoint_5xx", "503 Service Unavailable")
        self.probe_rc.write_text("1\n", encoding="utf-8")
        self.tick(120)
        self.assertEqual(self.cap("primary"), 0)
        self.assertIn("endpoint_5xx", self.health()["primary"]["reason"])

    def test_a_disabled_key_probes_its_own_way_back(self) -> None:
        self.tick(60)
        self.failure(90, "api.finite-dimensional.space", "auth", "403 Forbidden")
        self.probe_rc.write_text("1\n", encoding="utf-8")
        self.tick(120)
        self.assertEqual(self.cap("second"), 0)
        # The key-invalid backoff starts longer than the 5xx one: a key does not
        # become valid again in thirty seconds.
        self.assertGreaterEqual(self.health()["second"]["backoff_s"], 300)
        self.probe_rc.write_text("0\n", encoding="utf-8")
        self.tick(120 + 400)
        self.tick(120 + 500)
        self.assertEqual(self.health()["second"]["state"], "up")
        self.assertGreaterEqual(len(self.probe_calls()), 2)
        # Never back to the pre-outage cap: the endpoint that just came back is
        # the last thing to hand twenty sessions.
        self.assertEqual(self.cap("second"), 1)

    def test_probe_command_reports_and_records(self) -> None:
        self.tick(60)
        output = self.invoke("--now", at(120), "probe", "second")
        self.assertIn("second", output)
        self.assertEqual(self.probe_calls(), ["second"])

    def test_probe_skips_a_key_the_owner_disabled(self) -> None:
        self.edit("second", enabled="false")
        output = self.invoke("--now", at(120), "probe", "second")
        self.assertIn("disabled", output)
        self.assertEqual(self.probe_calls(), [])

    def test_probe_refuses_while_the_run_is_paused(self) -> None:
        # The invariant `tick` documents and enforces — "a pause can never fire
        # `codex exec` on the owner's keys" — has to hold on the path the owner
        # is actually told to use (owner-tools/accounts.sh probe).
        self.tick(60)
        self.invoke("--now", at(120), "pause")
        output = self.invoke("--now", at(180), "probe", "second", expect=cc.EXIT_FAIL)
        self.assertIn("PAUSED", output)
        self.assertEqual(self.probe_calls(), [])

    def test_probe_refuses_while_the_caps_are_held(self) -> None:
        self.tick(60)
        (self.watchdog / "capacity").mkdir(parents=True, exist_ok=True)
        (self.watchdog / "capacity" / "hold").write_text("frozen\n", encoding="utf-8")
        output = self.invoke("--now", at(180), "probe", "second", expect=cc.EXIT_FAIL)
        self.assertIn("HOLD", output)
        self.assertEqual(self.probe_calls(), [])

    def test_probe_force_overrides_the_pause_deliberately(self) -> None:
        self.tick(60)
        self.invoke("--now", at(120), "pause")
        self.invoke("--now", at(180), "probe", "second", "--force")
        self.assertEqual(self.probe_calls(), ["second"])

    def test_probe_dry_run_spends_no_session(self) -> None:
        self.tick(60)
        output = self.invoke("--now", at(120), "probe", "second", "--dry-run")
        self.assertIn("would probe", output)
        self.assertEqual(self.probe_calls(), [])

    def test_health_json_carries_every_key(self) -> None:
        self.tick(60)
        rows = self.health()
        self.assertEqual(sorted(rows), ["primary", "second"])
        self.assertEqual(rows["second"]["endpoint"], "api.finite-dimensional.space")
        self.assertEqual(rows["second"]["ceiling"], 28)


class TestSharedEndpoint(HotReloadHarness):
    """Two keys on ONE endpoint — the owner's stated topology (accounts-spec.md:
    one to three endpoints, each with one or two API keys).  Attribution by
    endpoint alone names neither key, and getting it wrong is not neutral: AIMD
    multiplicatively decreases the innocent key while the refusing one creeps up,
    and one `auth` row disables the wrong key at `disable_threshold` 1."""

    def setUp(self) -> None:
        super().setUp()
        self.write_accounts([
            {"name": "keya", "label": "keya", "endpoint": "api.shared.example",
             "codex_home": str(self.cache / "codex-a"), "ceiling": 10,
             "external_reserved": 0, "enabled": True, "note": ""},
            {"name": "keyb", "label": "keyb", "endpoint": "api.shared.example",
             "codex_home": str(self.cache / "codex-b"), "ceiling": 10,
             "external_reserved": 0, "enabled": True, "note": ""},
        ])

    def row(self, offset: int, account: str, failure_class: str, detail: str) -> None:
        """One session row naming BOTH the shared endpoint and the key."""
        with (self.telemetry / "sessions.jsonl").open("a", encoding="utf-8") as handle:
            handle.write(json.dumps({
                "name": f"prover-{account}-{offset}", "role": "prover", "issue": "1",
                "start": at(offset), "end": at(offset), "status": "failed", "exit": 1,
                "endpoint": "api.shared.example", "account": account,
                "failure_class": failure_class, "failure_detail": detail}) + "\n")

    def test_each_key_owns_its_own_refusals(self) -> None:
        rows = [{"account": "keya", "endpoint": "api.shared.example",
                 "failure_class": "concurrency_limit", "_ts": T0},
                {"account": "keyb", "endpoint": "api.shared.example",
                 "failure_class": "concurrency_limit", "_ts": T0}]
        accounts = cc.load_run_mode()["accounts"]
        endpoints, ambiguous = cc.attribution_map(accounts)
        self.assertEqual(ambiguous, ["api.shared.example"])
        roles = {"concurrency_limit": "refusal"}
        for name in ("keya", "keyb"):
            counters = cc.observe(rows, name, endpoints, roles, T0,
                                  counter_window_s=300, fivexx_window_s=120)
            self.assertEqual(counters["refusals"], 1, name)

    def test_a_row_naming_only_the_shared_endpoint_charges_neither_key(self) -> None:
        rows = [{"endpoint": "api.shared.example",
                 "failure_class": "concurrency_limit", "_ts": T0}]
        accounts = cc.load_run_mode()["accounts"]
        endpoints, _ = cc.attribution_map(accounts)
        roles = {"concurrency_limit": "refusal"}
        for name in ("keya", "keyb"):
            counters = cc.observe(rows, name, endpoints, roles, T0,
                                  counter_window_s=300, fivexx_window_s=120)
            self.assertEqual(counters["refusals"], 0, name)

    def test_one_auth_failure_disables_the_key_that_produced_it(self) -> None:
        # `disable_threshold` is 1, so attribution is the whole decision here:
        # with the endpoint map last-writer-wins, one 401 on keyb took keya out
        # of service instead — cap 0 with a reason naming the wrong key.
        self.tick(60)
        self.row(90, "keyb", "auth", "401 Unauthorized")
        self.tick(120)
        rows = self.health()
        self.assertEqual(rows["keyb"]["state"], "down")
        self.assertEqual(rows["keya"]["state"], "up")
        self.assertIn("401", rows["keyb"]["reason"])
        self.assertEqual(self.cap("keyb"), 0)
        self.assertGreater(self.cap("keya"), 0)


class TestDerivedFiles(HotReloadHarness):
    def gate(self) -> str:
        path = self.watchdog / "account-mode"
        return path.read_text(encoding="utf-8").strip() if path.exists() else ""

    def test_a_second_enabled_key_opens_the_path_shim_gate(self) -> None:
        # The PATH shim refuses every non-default CODEX_HOME while this file says
        # `primary`.  It used to be written only by run_mode.py apply|pause|resume,
        # so `accounts.sh add` produced a key every dispatch to which died at the
        # shim with exit 4 — and those deaths are neutral, so the cap never fell.
        self.write_accounts([
            {"name": "primary", "label": "relay-us7", "endpoint": "relay-us7",
             "codex_home": str(self.cache / "codex-primary"), "ceiling": 5,
             "external_reserved": 0, "enabled": True, "note": ""}])
        self.assertEqual(self.gate(), "primary")
        self.tick(60)
        self.assertEqual(self.gate(), "primary")
        self.write_accounts([
            {"name": "primary", "label": "relay-us7", "endpoint": "relay-us7",
             "codex_home": str(self.cache / "codex-primary"), "ceiling": 5,
             "external_reserved": 0, "enabled": True, "note": ""},
            {"name": "third", "label": "third", "endpoint": "api.third.example",
             "codex_home": str(self.cache / "codex-third"), "ceiling": 8,
             "external_reserved": 0, "enabled": True, "note": ""}])
        # Already open at the write, with no run_mode.py apply and no tick.
        self.assertEqual(self.gate(), "both")
        self.tick(120)
        self.assertEqual(self.gate(), "both")

    def test_disabling_the_second_key_closes_it_again(self) -> None:
        self.tick(60)
        self.assertEqual(self.gate(), "both")
        self.edit("second", enabled="false")
        self.assertEqual(self.gate(), "primary")

    def test_a_removed_account_does_not_keep_a_live_cap_file(self) -> None:
        # That stale file is what account_router's fallback glob picks up when
        # accounts.json is unreadable, so a removed key would go on being
        # admitted at the ceiling it had when the owner removed it.
        self.tick(60)
        self.assertEqual(self.cap("second"), 28)
        self.write_accounts([
            {"name": "primary", "label": "relay-us7", "endpoint": "relay-us7",
             "codex_home": str(self.cache / "codex-primary"), "ceiling": 5,
             "external_reserved": 0, "enabled": True, "note": ""}])
        self.tick(120)
        self.assertEqual(self.cap("second"), 0)
        self.assertTrue((self.watchdog / "max-codex-second").exists())


if __name__ == "__main__":
    unittest.main()
