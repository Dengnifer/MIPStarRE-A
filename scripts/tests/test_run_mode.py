#!/usr/bin/env python3
"""Regression tests for local/bin/run_mode.py.

Everything runs against a temporary `MIPSTARRE_CACHE_ROOT` and a temporary
repository root, so no test touches the real runtime state or the committed
telemetry.  The committed brief template and shim template are copied in, so a
change to either that breaks `apply` fails here.
"""

from __future__ import annotations

import io
import json
import os
import shutil
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
BIN_DIR = REPO_ROOT / "local" / "bin"
sys.path.insert(0, str(BIN_DIR))

import run_mode  # noqa: E402
from wf_util import LayerError  # noqa: E402

TEMPLATE = REPO_ROOT / "results/telemetry/owner-tools/run-brief.template.json"
SHIM_TEMPLATE = REPO_ROOT / "results/telemetry/owner-tools/owner-bin-codex"


def run(argv: list[str]) -> tuple[int, str, str]:
    out, err = io.StringIO(), io.StringIO()
    with redirect_stdout(out), redirect_stderr(err):
        code = run_mode.main(argv)
    return code, out.getvalue(), err.getvalue()


class RunModeTestCase(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        root = Path(self._tmp.name)
        self.cache = root / "cache"
        self.repo = root / "repo"
        (self.repo / "results/telemetry/owner-tools").mkdir(parents=True)
        (self.repo / "results/telemetry").mkdir(exist_ok=True)
        shutil.copy(TEMPLATE, self.repo / "results/telemetry/owner-tools/run-brief.template.json")
        shutil.copy(SHIM_TEMPLATE, self.repo / "results/telemetry/owner-tools/owner-bin-codex")
        (self.cache / "owner-bin").mkdir(parents=True)
        self.shim = self.cache / "owner-bin" / "codex"
        shutil.copy(SHIM_TEMPLATE, self.shim)
        self.shim.chmod(0o755)
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

    # -- helpers ---------------------------------------------------------

    def write_brief(self, mutate) -> Path:
        doc = json.loads(TEMPLATE.read_text(encoding="utf-8"))
        mutate(doc)
        self.brief.write_text(json.dumps(doc), encoding="utf-8")
        return self.brief

    def cap(self, name: str) -> str:
        return (self.cache / "watchdog" / name).read_text(encoding="utf-8").strip()

    def mode(self) -> dict:
        return json.loads((self.cache / "watchdog" / "run-mode.json").read_text("utf-8"))

    # -- apply -----------------------------------------------------------

    def test_template_applies_and_derives_caps(self) -> None:
        code, out, _ = run(["apply"])
        self.assertEqual(code, 0, out)
        self.assertEqual(self.cap("max-codex-primary"), "5")
        self.assertEqual(self.cap("max-codex-second"), "28")   # 30 ceiling - 2 reserved
        self.assertEqual(self.cap("max-codex"), "33")          # mechanically the sum
        mode = self.mode()
        self.assertEqual(mode["derived"]["floor"], 26)         # int(0.8 * 33)
        self.assertEqual(len(mode["brief_sha256"]), 64)
        self.assertFalse(mode["paused"])

    def test_apply_records_the_brief_digest_and_one_decision_row(self) -> None:
        self.assertEqual(run(["apply"])[0], 0)
        stages = (self.repo / "results/telemetry/stages.jsonl").read_text("utf-8").strip()
        rows = [json.loads(line) for line in stages.splitlines()]
        self.assertEqual([row["event"] for row in rows], ["run-mode-apply"])
        self.assertIn(self.mode()["brief_sha256"], rows[0]["note"])
        register = (self.repo / "results/telemetry/design-decisions.md").read_text("utf-8")
        self.assertEqual(register.strip().count("\n"), 0, "exactly one row is appended")
        self.assertIn("Run mode applied", register)

    def test_dry_run_writes_nothing(self) -> None:
        code, out, _ = run(["apply", "--dry-run"])
        self.assertEqual(code, 0)
        self.assertIn("would write", out)
        self.assertFalse((self.cache / "watchdog" / "run-mode.json").exists())
        self.assertFalse((self.cache / "watchdog" / "max-codex").exists())
        self.assertFalse((self.repo / "results/telemetry/stages.jsonl").exists())

    def test_measured_limit_seeds_the_starting_cap_below_the_ceiling(self) -> None:
        estimate = self.cache / "watchdog" / "capacity" / "limit-estimate.json"
        estimate.parent.mkdir(parents=True, exist_ok=True)
        estimate.write_text(json.dumps(
            {"accounts": {"second": {"measured_limit": 12},
                          "primary": {"measured_limit": 0}}}), encoding="utf-8")
        self.assertEqual(run(["apply"])[0], 0)
        self.assertEqual(self.cap("max-codex-second"), "12")
        # clamp(1, ...) — a measured zero never means "no capacity at all".
        self.assertEqual(self.cap("max-codex-primary"), "1")
        self.assertEqual(self.cap("max-codex"), "13")

    def test_malformed_limit_estimate_is_ignored_not_fatal(self) -> None:
        estimate = self.cache / "watchdog" / "capacity" / "limit-estimate.json"
        estimate.parent.mkdir(parents=True, exist_ok=True)
        estimate.write_text("{not json", encoding="utf-8")
        self.assertEqual(run(["apply"])[0], 0)
        self.assertEqual(self.cap("max-codex-second"), "28")

    def test_disabled_account_is_zero_and_never_dispatched(self) -> None:
        self.write_brief(lambda doc: doc["accounts"][0].update(enabled=False))
        self.assertEqual(run(["apply"])[0], 0)
        self.assertEqual(self.cap("max-codex-primary"), "0")
        self.assertEqual(self.cap("max-codex"), "28")

    # -- validation ------------------------------------------------------

    def test_invalid_briefs_exit_2_and_name_the_key(self) -> None:
        cases = {
            "accounts[1].external_reserved":
                lambda doc: doc["accounts"][1].update(external_reserved=30),
            "run.occupancy_target": lambda doc: doc["run"].update(occupancy_target=1.5),
            "run.speed": lambda doc: doc["run"].update(speed="turbo"),
            "models.override": lambda doc: doc["models"].update(override="sol-all"),
            "run.progress_issue": lambda doc: doc["run"].update(progress_issue=0),
            "run.tempo": lambda doc: doc["run"].update(tempo="brisk"),
            "accounts[0].endpoint": lambda doc: doc["accounts"][0].pop("endpoint"),
            "accounts[1].nominal_limit":
                lambda doc: doc["accounts"][1].update(nominal_limit="30"),
            # A brief may name ANY number of accounts (W10: the two historical
            # names are entries, not a closed set), so the rejected case is a
            # name outside the character class, not an unfamiliar one.
            "accounts[0].name": lambda doc: doc["accounts"][0].update(name="Third Key"),
            "schema": lambda doc: doc.update(schema="mipstarre-run-brief/2"),
            "accounts": lambda doc: doc.update(accounts=[]),
        }
        for key, mutate in cases.items():
            with self.subTest(key=key):
                self.write_brief(mutate)
                code, _, err = run(["apply"])
                self.assertEqual(code, 2, f"{key} should be rejected")
                self.assertIn(key, err)
                self.assertIn("run-brief.template.json", err)
                self.assertFalse((self.cache / "watchdog" / "max-codex").exists())

    def test_occupancy_target_above_one_and_reserved_over_limit_both_fail(self) -> None:
        # The two the work item names explicitly, asserted as their own case.
        self.write_brief(lambda doc: doc["accounts"][1].update(external_reserved=30))
        self.assertEqual(run(["apply", "--dry-run"])[0], 2)
        self.write_brief(lambda doc: doc["run"].update(occupancy_target=1.5))
        self.assertEqual(run(["apply", "--dry-run"])[0], 2)

    def test_issue_numbers_must_differ(self) -> None:
        self.write_brief(lambda doc: doc["run"].update(estimate_issue=27))
        code, _, err = run(["apply"])
        self.assertEqual(code, 2)
        self.assertIn("three different issues", err)

    def test_missing_brief_names_template_and_destination(self) -> None:
        self.brief.unlink()
        code, _, err = run(["apply"])
        self.assertEqual(code, 2)
        self.assertIn("run-brief.template.json", err)
        self.assertIn(str(self.brief), err)
        self.assertFalse((self.cache / "watchdog" / "max-codex").exists())

    def test_until_my_word_is_accepted(self) -> None:
        self.write_brief(lambda doc: doc["run"].update(dispatch_cutoff="until my word"))
        self.assertEqual(run(["apply"])[0], 0)
        code, out, _ = run(["get", "dispatch_cutoff"])
        self.assertEqual((code, out.strip()), (0, "until my word"))

    # -- cap files -------------------------------------------------------

    def test_write_caps_refuses_non_numeric_values(self) -> None:
        for bad in ({"primary": None, "second": 1}, {"primary": "5", "second": 1},
                    {"primary": -1, "second": 1}):
            with self.subTest(bad=bad):
                with self.assertRaises(LayerError):
                    run_mode.write_caps(bad)

    def test_cap_files_are_numeric_through_pause_and_resume(self) -> None:
        self.assertEqual(run(["apply"])[0], 0)
        for step in ("pause", "resume", "pause", "resume"):
            with self.subTest(step=step):
                self.assertEqual(run([step])[0], 0)
                for name in ("max-codex-primary", "max-codex-second", "max-codex"):
                    text = self.cap(name)
                    self.assertTrue(text and text.isdigit(), f"{name} is {text!r}")

    def test_pause_saves_the_caps_and_resume_restores_them(self) -> None:
        self.assertEqual(run(["apply"])[0], 0)
        self.assertEqual(run(["pause", "--reason", "owner word"])[0], 0)
        self.assertEqual((self.cap("max-codex-primary"), self.cap("max-codex-second"),
                          self.cap("max-codex")), ("0", "0", "0"))
        self.assertEqual(self.mode()["saved_caps"], {"primary": 5, "second": 28})
        # A second pause must not overwrite the saved caps with its own zeros.
        self.assertEqual(run(["pause"])[0], 0)
        self.assertEqual(self.mode()["saved_caps"], {"primary": 5, "second": 28})
        self.assertEqual(run(["resume"])[0], 0)
        self.assertEqual((self.cap("max-codex-primary"), self.cap("max-codex-second"),
                          self.cap("max-codex")), ("5", "28", "33"))
        self.assertFalse(self.mode()["paused"])

    def test_resume_never_restores_an_enabled_account_to_zero(self) -> None:
        self.assertEqual(run(["apply"])[0], 0)
        self.assertEqual(run(["pause"])[0], 0)
        mode = self.mode()
        mode["saved_caps"] = {"primary": 0, "second": 0}   # a clobbered save file
        (self.cache / "watchdog" / "run-mode.json").write_text(json.dumps(mode), "utf-8")
        code, _, err = run(["resume"])
        self.assertEqual(code, 0)
        self.assertIn("instead of zero capacity", err)
        self.assertEqual(self.cap("max-codex-primary"), "5")

    def test_floor_is_zero_while_paused(self) -> None:
        self.assertEqual(run(["apply"])[0], 0)
        self.assertEqual(run(["pause"])[0], 0)
        self.assertEqual(run(["get", "floor"])[1].strip(), "0")

    # -- get / show ------------------------------------------------------

    def test_get_returns_every_key_the_components_use(self) -> None:
        self.assertEqual(run(["apply"])[0], 0)
        expected = {
            "speed": "fast", "floor": "26", "cap.primary": "5", "cap.second": "28",
            "endpoint.second": "api.finite-dimensional.space",
            "progress_issue": "27", "estimate_issue": "168",
            "owner_inbox_issue": "500", "dispatch_cutoff": "2026-09-13T08:00:00Z",
            "pause_deadline_min": "15", "turn_max": "8", "max_codex": "33",
        }
        for key, want in expected.items():
            with self.subTest(key=key):
                code, out, _ = run(["get", key])
                self.assertEqual((code, out.strip()), (0, want))
        code, out, _ = run(["get", "codex_home.second"])
        self.assertEqual(code, 0)
        self.assertTrue(out.strip().endswith("codex-home-yxy"))
        self.assertNotIn("~", out)

    def test_get_unknown_key_exits_2(self) -> None:
        self.assertEqual(run(["apply"])[0], 0)
        code, _, err = run(["get", "occupancy"])
        self.assertEqual(code, 2)
        self.assertIn("unknown key", err)

    def test_get_without_a_run_mode_exits_2(self) -> None:
        code, _, err = run(["get", "speed"])
        self.assertEqual(code, 2)
        self.assertIn("never as zero capacity", err)

    def test_unreadable_run_mode_exits_2(self) -> None:
        self.assertEqual(run(["apply"])[0], 0)
        (self.cache / "watchdog" / "run-mode.json").write_text("{broken", encoding="utf-8")
        self.assertEqual(run(["get", "speed"])[0], 2)
        self.assertEqual(run(["show"])[0], 2)

    def test_empty_cap_file_reads_as_unknown_not_zero(self) -> None:
        self.assertEqual(run(["apply"])[0], 0)
        (self.cache / "watchdog" / "max-codex-second").write_text("", encoding="utf-8")
        code, out, err = run(["get", "cap.second"])
        self.assertEqual((code, out.strip()), (0, "28"), "falls back to the record")
        self.assertIn("empty or non-numeric", err)

    def test_show_carries_no_literal_cap_from_a_script(self) -> None:
        self.assertEqual(run(["apply"])[0], 0)
        text = run(["show"])[1]
        for fragment in ("cap primary", "occupancy", "issues", "max-codex"):
            self.assertIn(fragment, text)

    # -- speed / shim ----------------------------------------------------

    def test_set_speed_regenerates_the_shim_in_both_directions(self) -> None:
        self.assertEqual(run(["apply"])[0], 0)          # brief says fast
        # The committed template documents both renderings in its header and
        # filters a service_tier argument out of its own arguments, so every
        # assertion here is on the rendered SPEED_ARGS line, never on the file.
        self.assertIn("SPEED_ARGS=(-c 'service_tier=\"priority\"')",
                      self.shim.read_text("utf-8"))
        self.assertEqual(run(["set", "speed", "default"])[0], 0)
        self.assertIn("\nSPEED_ARGS=()", self.shim.read_text("utf-8"))
        self.assertNotIn("SPEED_ARGS=(-c", self.shim.read_text("utf-8"))
        self.assertEqual(run(["get", "speed"])[1].strip(), "default")
        self.assertEqual(run(["get", "turn_max"])[1].strip(), "20")
        self.assertEqual(run(["set", "speed", "fast"])[0], 0)
        self.assertIn("SPEED_ARGS=(-c 'service_tier=\"priority\"')",
                      self.shim.read_text("utf-8"))
        self.assertEqual(self.shim.stat().st_mode & 0o777, 0o755)

    def test_set_speed_names_who_picks_the_change_up(self) -> None:
        self.assertEqual(run(["apply"])[0], 0)
        out = run(["set", "speed", "default"])[1]
        self.assertIn("main TUI (NO", out)
        self.assertIn("worker sessions dispatched from now on (yes)", out)

    def test_set_speed_refuses_a_hand_edited_shim_and_prints_the_diff(self) -> None:
        self.assertEqual(run(["apply"])[0], 0)
        self.shim.write_text(self.shim.read_text("utf-8") + "\n# emergency edit\n", "utf-8")
        code, _, err = run(["set", "speed", "default"])
        self.assertEqual(code, 3)
        self.assertIn("refusing to discard an emergency hand-edit", err)
        self.assertIn("# emergency edit", err)
        self.assertIn("# emergency edit", self.shim.read_text("utf-8"))

    def test_render_shim_is_idempotent_and_supports_an_explicit_placeholder(self) -> None:
        template = ("#!/usr/bin/env bash\nexec codex " + run_mode.SPEED_PLACEHOLDER +
                    "-c 'features.multi_agent=false' \"$@\"\n")
        fast = run_mode.render_shim(template, "fast")
        default = run_mode.render_shim(template, "default")
        self.assertIn('service_tier="priority"', fast)
        self.assertNotIn("service_tier", default)
        self.assertNotIn(run_mode.SPEED_PLACEHOLDER, fast + default)
        self.assertEqual(run_mode.render_shim(fast, "fast"), fast)
        self.assertEqual(run_mode.render_shim(fast, "default"), default)

    def test_render_shim_refuses_a_template_with_no_position(self) -> None:
        with self.assertRaises(LayerError):
            run_mode.render_shim("#!/bin/sh\nexec codex \"$@\"\n", "fast")

    def test_apply_reports_a_missing_shim_without_losing_the_caps(self) -> None:
        self.shim.unlink()
        code, _, err = run(["apply"])
        self.assertEqual(code, 0)
        self.assertIn("shim was NOT regenerated", err)
        self.assertEqual(self.cap("max-codex"), "33")

    # -- models.override resolved from the speed tier (W9) ---------------

    def knob(self) -> Path:
        return self.cache / "watchdog" / "model-override"

    def test_fast_speed_with_no_override_puts_every_role_on_the_hard_model(self) -> None:
        """The owner's full speed rule, as a default rather than a field to remember."""
        self.assertEqual(json.loads(TEMPLATE.read_text("utf-8"))["models"]["override"], None)
        code, out, err = run(["apply"])
        self.assertEqual(code, 0, err)
        self.assertEqual(self.mode()["run"]["speed"], "fast")
        self.assertEqual(self.mode()["models"]["effective"], "astra-all")
        self.assertEqual(json.loads(self.knob().read_text("utf-8"))["mode"], "astra-all")
        self.assertIn("model override astra-all active", out)
        self.assertEqual(run(["get", "model_override"])[1].strip(), "astra-all")
        self.assertEqual(run(["get", "model_override_briefed"])[1].strip(), "null")
        self.assertIn("run.speed fast", run(["get", "model_override_source"])[1])

    def test_policy_is_how_a_fast_run_keeps_the_published_policy(self) -> None:
        self.write_brief(lambda doc: doc["models"].update(override="policy"))
        code, out, err = run(["apply"])
        self.assertEqual(code, 0, err)
        self.assertIsNone(self.mode()["models"]["effective"])
        self.assertFalse(self.knob().exists())
        self.assertEqual(run(["get", "model_override"])[1].strip(), "none")
        self.assertEqual(run(["get", "model_override_briefed"])[1].strip(), "policy")

    def test_default_speed_leaves_the_published_policy_in_charge(self) -> None:
        self.write_brief(lambda doc: doc["run"].update(speed="default"))
        self.assertEqual(run(["apply"])[0], 0)
        self.assertIsNone(self.mode()["models"]["effective"])
        self.assertFalse(self.knob().exists())

    def test_an_explicit_astra_all_holds_at_default_speed(self) -> None:
        self.write_brief(lambda doc: (doc["run"].update(speed="default"),
                                      doc["models"].update(override="astra-all")))
        self.assertEqual(run(["apply"])[0], 0)
        self.assertEqual(self.mode()["models"]["effective"], "astra-all")
        self.assertEqual(json.loads(self.knob().read_text("utf-8"))["mode"], "astra-all")

    def test_an_unknown_override_word_fails_at_briefing_time(self) -> None:
        self.write_brief(lambda doc: doc["models"].update(override="astra-some"))
        code, _, err = run(["apply"])
        self.assertEqual(code, 2)
        self.assertIn("models.override", err)
        self.assertIn("'policy'", err)

    def test_set_speed_re_resolves_the_override_in_both_directions(self) -> None:
        self.assertEqual(run(["apply"])[0], 0)
        self.assertTrue(self.knob().exists())
        code, out, err = run(["set", "speed", "default"])
        self.assertEqual(code, 0, err)
        self.assertFalse(self.knob().exists(),
                         "leaving fast speed must return the routine roles to the policy")
        self.assertIsNone(self.mode()["models"]["effective"])
        self.assertIn("model override cleared", out)
        self.assertEqual(run(["set", "speed", "fast"])[0], 0)
        self.assertEqual(json.loads(self.knob().read_text("utf-8"))["mode"], "astra-all")
        self.assertEqual(run(["get", "model_override"])[1].strip(), "astra-all")

    def test_set_speed_does_not_override_an_explicit_policy_brief(self) -> None:
        self.write_brief(lambda doc: doc["models"].update(override="policy"))
        self.assertEqual(run(["apply"])[0], 0)
        self.assertEqual(run(["set", "speed", "default"])[0], 0)
        self.assertEqual(run(["set", "speed", "fast"])[0], 0)
        self.assertFalse(self.knob().exists(),
                         "an explicit 'policy' is a decision, not an omission")

    def test_the_template_documents_what_null_means(self) -> None:
        comment = " ".join(json.loads(TEMPLATE.read_text("utf-8"))["_comment"])
        for fragment in ("astra-all", "policy", "reviewers", "run.speed"):
            self.assertIn(fragment, comment)

    def test_show_names_the_effective_override_and_its_source(self) -> None:
        self.assertEqual(run(["apply"])[0], 0)
        line = [row for row in run(["show"])[1].splitlines() if row.startswith("models")][0]
        self.assertIn("astra-all", line)
        self.assertIn("run.speed fast", line)

    # -- `set speed` regenerates the crontab (W9) ------------------------

    def install_crons(self, body: str) -> Path:
        path = self.cache / "owner-bin" / "install-crons.sh"
        path.write_text(body, encoding="utf-8")
        path.chmod(0o755)
        return path

    def test_set_speed_regenerates_the_crontab(self) -> None:
        receipt = self.cache / "crons-ran"
        self.install_crons("#!/bin/sh\nprintf ran > %s\n" % receipt)
        self.assertEqual(run(["apply"])[0], 0)
        code, out, err = run(["set", "speed", "default"])
        self.assertEqual(code, 0, err)
        self.assertEqual(receipt.read_text("utf-8"), "ran",
                         "the estimate cadence lives in the crontab; a speed change "
                         "that does not regenerate it is not a speed change")
        self.assertIn("crontab regenerated", out)

    def test_a_failing_crontab_installer_never_loses_the_speed_change(self) -> None:
        self.install_crons("#!/bin/sh\necho 'crontab -l was empty' >&2\nexit 3\n")
        self.assertEqual(run(["apply"])[0], 0)
        code, out, _ = run(["set", "speed", "default"])
        self.assertEqual(code, 0)
        self.assertIn("crontab NOT regenerated", out)
        self.assertIn("crontab -l was empty", out)
        self.assertEqual(run(["get", "speed"])[1].strip(), "default")

    def test_a_missing_crontab_installer_says_which_command_installs_it(self) -> None:
        self.assertEqual(run(["apply"])[0], 0)
        out = run(["set", "speed", "default"])[1]
        self.assertIn("is not installed", out)
        self.assertIn("install.sh --crons", out)

    def test_set_speed_dry_run_still_writes_nothing(self) -> None:
        receipt = self.cache / "crons-ran"
        self.install_crons("#!/bin/sh\nprintf ran > %s\n" % receipt)
        self.assertEqual(run(["apply"])[0], 0)
        code, out, _ = run(["set", "speed", "default", "--dry-run"])
        self.assertEqual(code, 0)
        self.assertIn("would regenerate the crontab", out)
        self.assertFalse(receipt.exists())
        self.assertEqual(run(["get", "speed"])[1].strip(), "fast")
        self.assertTrue(self.knob().exists())


if __name__ == "__main__":
    unittest.main()
