#!/usr/bin/env python3
"""Regressions for the blocking findings of PR 552's review round 1.

Each test names the defect it pins.  They are grouped here rather than spread
across the seven work-item test files because they are one review's findings and
they should fail together if the review's conclusions are undone.
"""

from __future__ import annotations

import io
import json
import os
import re
import shutil
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from datetime import datetime, timedelta, timezone
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
BIN_DIR = REPO_ROOT / "local" / "bin"
TOOLS = REPO_ROOT / "results/telemetry/owner-tools"
sys.path.insert(0, str(BIN_DIR))

import capacity_controller as cc  # noqa: E402
import run_mode  # noqa: E402

TEMPLATE = TOOLS / "run-brief.template.json"
SHIM_TEMPLATE = TOOLS / "owner-bin-codex"


def text(path: Path) -> str:
    return path.read_text(encoding="utf-8")


# ---------------------------------------------------------------------------
# Finding 1 — the merge daemon pushed straight to main
# ---------------------------------------------------------------------------

class TelemetryPublicationTestCase(unittest.TestCase):
    """No tool in the layer may call `git push` directly."""

    PUBLISHERS = ("merge-daemon.sh", "owner-pause.sh", "owner-resume.sh")

    def test_nothing_in_the_layer_pushes_main_directly(self) -> None:
        # checked-push.sh is the exception: it IS the publisher.
        offenders = []
        for path in list(TOOLS.glob("*.sh")) + list(BIN_DIR.glob("*.sh")):
            if path.name == "checked-push.sh":
                continue
            for number, line in enumerate(text(path).splitlines(), 1):
                stripped = line.strip()
                if stripped.startswith("#"):
                    continue
                if re.search(r"\bgit\b[^|;&]*\bpush\b[^|;&]*\bmain\b", stripped):
                    offenders.append(f"{path.name}:{number}: {stripped}")
        self.assertEqual(
            offenders, [],
            "a publish to main goes through local/bin/checked-push.sh, which runs "
            "the pre-push gate outside the transport, pushes with "
            "--force-with-lease and re-verifies the tree and the SHA afterwards:\n"
            + "\n".join(offenders))

    def test_the_publishers_call_checked_push(self) -> None:
        for name in self.PUBLISHERS:
            with self.subTest(tool=name):
                self.assertIn("checked-push.sh", text(TOOLS / name))

    def test_the_daemon_stages_explicit_paths(self) -> None:
        daemon = text(TOOLS / "merge-daemon.sh")
        self.assertNotIn("git add results/telemetry\n", daemon)
        self.assertIn("$telemetry_paths", daemon)
        conf = text(TOOLS / "daemon.conf")
        self.assertIn("telemetry_paths", conf)
        # the knob must name files, not the directory
        row = [line for line in conf.splitlines() if line.startswith(': "${telemetry_paths')]
        self.assertTrue(row, "daemon.conf must define telemetry_paths")
        self.assertNotIn("results/telemetry ", row[0].replace(":=", " "))


# ---------------------------------------------------------------------------
# Finding 2 — per-tick rows in a committed file
# ---------------------------------------------------------------------------

class StagesJsonlTestCase(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        root = Path(self._tmp.name)
        self.cache, self.repo = root / "cache", root / "repo"
        (self.repo / "results/telemetry").mkdir(parents=True)
        self._env = dict(os.environ)
        os.environ["MIPSTARRE_CACHE_ROOT"] = str(self.cache)
        os.environ["MIPSTARRE_REPO_ROOT"] = str(self.repo)

    def tearDown(self) -> None:
        os.environ.clear()
        os.environ.update(self._env)
        self._tmp.cleanup()

    def test_a_tick_never_reaches_stages_jsonl(self) -> None:
        summary = {"ts": "2026-09-13T05:00:00Z", "max_codex": 7, "accounts": {}}
        path = cc.append_tick(summary, "primary 3/5 up")
        self.assertTrue(path.exists())
        self.assertEqual(path, self.cache / "watchdog/capacity/ticks.jsonl")
        self.assertFalse((self.repo / "results/telemetry/stages.jsonl").exists(),
                         "a 60-second tick must not append to the committed log")

    def test_append_stage_refuses_a_non_transition(self) -> None:
        with self.assertRaises(cc.ControllerError):
            cc.append_stage("tick", {"ts": "2026-09-13T05:00:00Z"}, "note")

    def test_transitions_do_reach_stages_jsonl(self) -> None:
        for event in ("init", "pause", "resume", "endpoint-trip", "endpoint-recovered"):
            cc.append_stage(event, {"ts": "2026-09-13T05:00:00Z"}, f"note for {event}")
        rows = [json.loads(line) for line
                in text(self.repo / "results/telemetry/stages.jsonl").splitlines()]
        self.assertEqual([row["event"] for row in rows],
                         ["init", "pause", "resume", "endpoint-trip", "endpoint-recovered"])
        self.assertEqual({row["stage"] for row in rows}, {"capacity"})

    def test_ticks_are_trimmed_by_their_own_writer(self) -> None:
        keep = cc.TICKS_KEEP
        cc.TICKS_KEEP = 5
        try:
            for index in range(12):
                path = cc.append_tick({"ts": f"2026-09-13T05:00:{index:02d}Z"}, "n")
        finally:
            cc.TICKS_KEEP = keep
        self.assertEqual(len(text(path).strip().splitlines()), 5)

    def test_meta_md_declares_the_operational_stages(self) -> None:
        meta = text(REPO_ROOT / "local/protocols/meta.md")
        for event in ("endpoint-trip", "endpoint-recovered", "run-mode-apply"):
            self.assertIn(event, meta,
                          "meta.md's stages.jsonl schema must declare every event "
                          "this layer writes (amendment procedure step 5)")
        self.assertIn("ticks.jsonl", meta)


# ---------------------------------------------------------------------------
# Finding 3 — a pause that kept ticking
# ---------------------------------------------------------------------------

class PausedControllerTestCase(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        root = Path(self._tmp.name)
        self.cache, self.repo = root / "cache", root / "repo"
        (self.repo / "results/telemetry").mkdir(parents=True)
        (self.cache / "watchdog/capacity").mkdir(parents=True)
        self._env = dict(os.environ)
        os.environ["MIPSTARRE_CACHE_ROOT"] = str(self.cache)
        os.environ["MIPSTARRE_REPO_ROOT"] = str(self.repo)
        self.policy = json.loads(text(REPO_ROOT / "local/capacity-policy.json"))
        self.now = datetime(2026, 9, 13, 5, 0, tzinfo=timezone.utc)

    def tearDown(self) -> None:
        os.environ.clear()
        os.environ.update(self._env)
        self._tmp.cleanup()

    def run_mode_doc(self) -> dict:
        return {
            "brief_ref": "test",
            "accounts": {
                "primary": {"name": "primary", "label": "relay", "endpoint": "relay",
                            "codex_home": "~/.codex", "nominal_limit": 5,
                            "external_reserved": 0, "enabled": True},
            },
        }

    def paused_state(self) -> dict:
        state = cc.new_state("test")
        state["paused_at"] = cc.ts(self.now - timedelta(minutes=5))
        state["accounts"]["primary"] = dict(cc.new_account_state("primary"), cap=4)
        return state

    def test_a_recovering_endpoint_cannot_raise_a_cap_while_paused(self) -> None:
        # health is `down` and its probe is due: without the ordering fix the
        # `recovered` branch runs before the `paused` test and writes cap 1.
        health = {"account": "primary", "endpoint": "relay", "state": "down",
                  "since": cc.ts(self.now - timedelta(minutes=10)), "probes_ok": 1,
                  "consecutive_5xx": 0, "backoff_s": 30,
                  "next_probe_at": cc.ts(self.now - timedelta(minutes=1)),
                  "updated": cc.ts(self.now)}
        cc._write_json(cc.health_path("primary"), health)  # noqa: SLF001
        probed = []
        original = cc.probe_account
        cc.probe_account = lambda *a, **k: probed.append(a) or True  # type: ignore[assignment]
        try:
            summary = cc.tick(self.now, policy=self.policy, run_mode=self.run_mode_doc(),
                              state=self.paused_state(), dry_run=True)
        finally:
            cc.probe_account = original
        self.assertEqual(summary["accounts"]["primary"]["cap"], 0,
                         "a paused run has cap 0, whatever the endpoint is doing")
        self.assertEqual(probed, [],
                         "a paused run must not spend the owner's key on a probe")

    def test_a_paused_tick_never_probes(self) -> None:
        health = {"account": "primary", "endpoint": "relay", "state": "down",
                  "since": cc.ts(self.now), "probes_ok": 0, "consecutive_5xx": 3,
                  "backoff_s": 30, "next_probe_at": cc.ts(self.now - timedelta(hours=1)),
                  "updated": cc.ts(self.now)}
        cc._write_json(cc.health_path("primary"), health)  # noqa: SLF001
        calls = []
        original = cc.probe_account
        cc.probe_account = lambda *a, **k: calls.append(a) or False  # type: ignore[assignment]
        try:
            cc.tick(self.now, policy=self.policy, run_mode=self.run_mode_doc(),
                    state=self.paused_state(), dry_run=True)
        finally:
            cc.probe_account = original
        self.assertEqual(calls, [])

    def test_owner_pause_stops_capacityd_and_owner_resume_starts_it(self) -> None:
        pause = text(TOOLS / "owner-pause.sh")
        self.assertIn("capacity/capacityd.stop", pause)
        self.assertIn("capacityd.pid", pause)
        self.assertIn("capacityd\\.sh", pause, "capacityd belongs in the kill table")
        resume = text(TOOLS / "owner-resume.sh")
        self.assertIn('rm -f "$D/stop"', resume)
        self.assertIn("capacityd.stop", resume)
        self.assertIn("capacityd.sh", resume)
        self.assertIn("POST-CONDITION: no capacity controller is running", resume)

    def test_the_kill_table_is_anchored_as_it_claims(self) -> None:
        pause = text(TOOLS / "owner-pause.sh")
        table = pause.split("PATTERNS='", 1)[1].split("'", 1)[0]
        for line in table.splitlines():
            if line.strip():
                self.assertTrue(line.startswith("^"),
                                f"unanchored pattern in the kill table: {line!r}")


# ---------------------------------------------------------------------------
# Findings 4 and 9 — nothing started capacityd
# ---------------------------------------------------------------------------

class CapacitydIsStartedTestCase(unittest.TestCase):
    def test_install_sh_can_start_the_loop(self) -> None:
        install = text(TOOLS / "install.sh")
        self.assertIn("--start-loops", install)
        self.assertIn("capacityd.sh", install)
        self.assertRegex(install, r"setsid nohup bash \"\$CAPD\"")

    def test_the_crontab_carries_a_restart_row(self) -> None:
        crons = text(TOOLS / "install-crons.sh")
        self.assertIn("capacityd.sh", crons)
        self.assertIn("capacityd\\.sh", crons, "the row must be in OWNED_RE too")
        self.assertIn("capacityd.stop", crons, "the row must respect the stop file")

    def test_capacityd_is_single_instance(self) -> None:
        daemon = text(TOOLS / "capacityd.sh")
        self.assertIn("flock -n 9", daemon,
                      "a restart row plus a resume must never make two controllers")

    def test_the_runbook_names_the_start_step(self) -> None:
        doc = text(REPO_ROOT / "local/protocols/full-speed-mode.md")
        self.assertIn("--start-loops", doc)
        self.assertIn("run-start sequence", doc)


# ---------------------------------------------------------------------------
# Finding 5 — the health probe's telemetry exception
# ---------------------------------------------------------------------------

class ProbeExceptionTestCase(unittest.TestCase):
    def test_all_three_documents_name_the_exception(self) -> None:
        # Whitespace-normalised: these documents are hard-wrapped, so the phrase
        # is routinely split across two lines.
        for path in (REPO_ROOT / "local/protocols/meta.md",
                     REPO_ROOT / "local/protocols/capacity.md",
                     REPO_ROOT / "AGENTS.md"):
            with self.subTest(document=path.name):
                body = re.sub(r"\s+", " ", text(path))
                self.assertIn("health probe", body)
                self.assertIn("capacity_controller.py", body)
                self.assertIn("dispatch.sh", body)


# ---------------------------------------------------------------------------
# Finding 6 — fix-lane.sh's unreachable exit 3
# ---------------------------------------------------------------------------

class FixLaneExitTestCase(unittest.TestCase):
    def test_a_failed_dispatch_exits_three(self) -> None:
        body = text(TOOLS / "fix-lane.sh")
        after = body.split('outcome dispatch-failed', 1)[1]
        self.assertIn("exit 3", after.split("# ---")[0],
                      "documented exit 3 must be reachable: a failed dispatch "
                      "never touched the worktree, so the lane must not relaunch")

    def test_the_daemon_only_marks_a_repair_done_on_success(self) -> None:
        body = text(TOOLS / "merge-daemon.sh")
        block = body.split("launch_repair()", 1)[1].split("try_merge()", 1)[0]
        self.assertIn('if [ "$frc" -eq 0 ]; then', block)
        self.assertIn('touch "$D/pr$PR.repair-done"', block)


# ---------------------------------------------------------------------------
# Findings 10-13 — the owner-experience gaps
# ---------------------------------------------------------------------------

class OwnerExperienceTestCase(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        root = Path(self._tmp.name)
        self.cache, self.repo = root / "cache", root / "repo"
        (self.repo / "results/telemetry/owner-tools").mkdir(parents=True)
        shutil.copy(TEMPLATE, self.repo / "results/telemetry/owner-tools/run-brief.template.json")
        shutil.copy(SHIM_TEMPLATE, self.repo / "results/telemetry/owner-tools/owner-bin-codex")
        (self.cache / "owner-bin").mkdir(parents=True)
        shim = self.cache / "owner-bin" / "codex"
        shutil.copy(SHIM_TEMPLATE, shim)
        shim.chmod(0o755)
        self._env = dict(os.environ)
        os.environ["MIPSTARRE_CACHE_ROOT"] = str(self.cache)
        os.environ["MIPSTARRE_REPO_ROOT"] = str(self.repo)
        os.environ.pop("MIPSTARRE_OWNER_BIN", None)
        self.brief = self.cache / "watchdog" / "run-brief.json"
        self.brief.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy(TEMPLATE, self.brief)

    def tearDown(self) -> None:
        os.environ.clear()
        os.environ.update(self._env)
        self._tmp.cleanup()

    def run_cli(self, argv: list[str]) -> tuple[int, str, str]:
        out, err = io.StringIO(), io.StringIO()
        with redirect_stdout(out), redirect_stderr(err):
            code = run_mode.main(argv)
        return code, out.getvalue(), err.getvalue()

    def write_brief(self, mutate) -> None:
        doc = json.loads(text(TEMPLATE))
        mutate(doc)
        self.brief.write_text(json.dumps(doc), encoding="utf-8")

    # -- finding 12: models.override was inert ---------------------------

    def test_apply_writes_the_model_override_knob(self) -> None:
        self.write_brief(lambda doc: doc["models"].update(override="astra-all"))
        code, out, err = self.run_cli(["apply"])
        self.assertEqual(code, 0, err)
        knob = self.cache / "watchdog" / "model-override"
        self.assertTrue(knob.exists(), "models.override must write the runtime knob "
                                       "model_policy.py reads, or the field does nothing")
        self.assertEqual(json.loads(text(knob))["mode"], "astra-all")
        self.assertIn("model override astra-all active", out)

    def test_apply_removes_the_knob_when_the_brief_says_null(self) -> None:
        knob = self.cache / "watchdog" / "model-override"
        knob.parent.mkdir(parents=True, exist_ok=True)
        knob.write_text("astra-all\n", encoding="utf-8")
        self.assertEqual(self.run_cli(["apply"])[0], 0)
        self.assertFalse(knob.exists(),
                         "`override: null` must clear a knob left by an earlier run")

    def test_the_override_reaches_model_policy(self) -> None:
        self.write_brief(lambda doc: doc["models"].update(override="astra-all"))
        self.assertEqual(self.run_cli(["apply"])[0], 0)
        import model_policy  # noqa: PLC0415 - after the knob exists
        override = model_policy.runtime_override()
        self.assertIsNotNone(override)
        self.assertEqual(override["mode"], "astra-all")

    # -- finding 14: the launcher's values ------------------------------

    def test_main_session_values_come_from_the_brief(self) -> None:
        self.write_brief(lambda doc: doc["run"].update(
            main={"model": "gpt-6-astra", "effort": "high", "codex_home": "~/.codex"}))
        self.assertEqual(self.run_cli(["apply"])[0], 0)
        for key, want in (("main.model", "gpt-6-astra"), ("main.effort", "high"),
                          ("main.codex_home", "~/.codex")):
            with self.subTest(key=key):
                code, out, err = self.run_cli(["get", key])
                self.assertEqual(code, 0, f"run_mode.py get {key} must resolve: {err}")
                self.assertEqual(out.strip(), want)

    def test_main_defaults_keep_an_older_brief_working(self) -> None:
        self.write_brief(lambda doc: doc["run"].pop("main", None))
        self.assertEqual(self.run_cli(["apply"])[0], 0)
        self.assertEqual(self.run_cli(["get", "main.model"])[1].strip(), "gpt-6-astra")
        self.assertEqual(self.run_cli(["get", "main.effort"])[1].strip(), "xhigh")

    def test_a_bad_main_effort_fails_at_briefing_time(self) -> None:
        self.write_brief(lambda doc: doc["run"].update(main={"effort": "ludicrous"}))
        code, _, err = self.run_cli(["apply"])
        self.assertEqual(code, 2)
        self.assertIn("run.main.effort", err)

    # -- finding 13: the resume post-condition --------------------------

    def test_enabled_is_queryable_at_the_spelling_owner_resume_uses(self) -> None:
        self.write_brief(lambda doc: doc["accounts"][0].update(enabled=False))
        self.assertEqual(self.run_cli(["apply"])[0], 0)
        code, out, err = self.run_cli(["get", "enabled.primary"])
        self.assertEqual(code, 0, err)
        self.assertEqual(out.strip(), "no")
        self.assertEqual(self.run_cli(["get", "enabled.second"])[1].strip(), "yes")

    def test_owner_resume_queries_that_spelling_and_compares_to_it(self) -> None:
        body = text(TOOLS / "owner-resume.sh")
        self.assertIn('get "enabled.$name"', body)
        self.assertNotIn('account.$name.enabled', body)
        self.assertIn('[ "$enabled" != no ]', body,
                      "run_mode answers yes/no, never true/false")


if __name__ == "__main__":
    unittest.main()
