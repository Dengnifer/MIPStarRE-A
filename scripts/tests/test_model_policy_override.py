#!/usr/bin/env python3
"""Tests for the owner's model override in local/bin/model_policy.py.

The override replaces the `sol -> astra` rewrite that lived inside the PATH
shim on 2026-09-12 and made sessions.jsonl record a model that never ran.  It
may only narrow toward the hard model, it may never lower effort, and the rows
it produces are excluded from the Sol:Astra ratio rather than read as
violations.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
BIN_DIR = REPO_ROOT / "local" / "bin"
sys.path.insert(0, str(BIN_DIR))

import model_policy  # noqa: E402

POLICY = {
    "schema_version": 2,
    "default_model": "gpt-5.6-sol",
    "hard_model": "gpt-6-astra",
    "main_model": "gpt-6-astra",
    "effort": "ultra",
}


class _Base(unittest.TestCase):
    """Runs against a throwaway cache root and a stubbed published policy."""

    policy_extra: dict = {}

    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.cache = Path(self._tmp.name) / "cache"
        (self.cache / "watchdog").mkdir(parents=True)
        self._env = os.environ.get("MIPSTARRE_CACHE_ROOT")
        os.environ["MIPSTARRE_CACHE_ROOT"] = str(self.cache)
        self._loader = model_policy.load_policy
        policy = dict(POLICY, **self.policy_extra)
        model_policy.load_policy = lambda: dict(policy)  # type: ignore[assignment]

    def tearDown(self) -> None:
        model_policy.load_policy = self._loader  # type: ignore[assignment]
        if self._env is None:
            os.environ.pop("MIPSTARRE_CACHE_ROOT", None)
        else:
            os.environ["MIPSTARRE_CACHE_ROOT"] = self._env
        self._tmp.cleanup()

    def set_knob(self, text: str) -> None:
        (self.cache / "watchdog" / "model-override").write_text(text, encoding="utf-8")


# ── no override ─────────────────────────────────────────────────────────────


class NoOverrideTests(_Base):
    def test_a_routine_job_stays_on_the_default_model(self) -> None:
        selection = model_policy.select_model("prover", "general")
        self.assertEqual(selection["model"], "gpt-5.6-sol")
        self.assertIsNone(selection["override_mode"])
        self.assertIsNone(selection["override_source"])

    def test_an_explicit_hard_model_for_a_routine_job_is_still_refused(self) -> None:
        with self.assertRaises(ValueError):
            model_policy.select_model("prover", "general", "gpt-6-astra")


# ── the runtime knob ────────────────────────────────────────────────────────


class RuntimeOverrideTests(_Base):
    def test_a_routine_job_runs_the_hard_model(self) -> None:
        self.set_knob("astra-all\n")
        selection = model_policy.select_model("prover", "general")
        self.assertEqual(selection["model"], "gpt-6-astra")
        self.assertEqual(selection["override_mode"], "astra-all")
        self.assertIn("model-override", selection["override_source"])

    def test_every_role_and_job_class_narrows(self) -> None:
        self.set_knob("astra-all")
        for role, job_class in (("prover", "general"), ("reviewer", "independent_review"),
                                ("simplifier", "bounded"), ("scout", "routine"),
                                ("blueprint", "review_directed_nonsemantic_cleanup")):
            with self.subTest(role=role, job_class=job_class):
                self.assertEqual(
                    model_policy.select_model(role, job_class)["model"], "gpt-6-astra")

    def test_an_explicit_hard_request_stops_being_a_conflict(self) -> None:
        self.set_knob("astra-all")
        selection = model_policy.select_model("prover", "general", "gpt-6-astra")
        self.assertEqual(selection["model"], "gpt-6-astra")

    def test_an_explicit_cheap_request_is_refused_loudly(self) -> None:
        # The override narrows; it cannot be talked back out of.
        self.set_knob("astra-all")
        with self.assertRaises(ValueError) as caught:
            model_policy.select_model("prover", "general", "gpt-5.6-sol")
        self.assertIn("override", str(caught.exception))

    def test_effort_is_never_lowered(self) -> None:
        self.set_knob("astra-all")
        for effort in ("xhigh", "high", "max", ""):
            with self.subTest(effort), self.assertRaises(ValueError):
                model_policy.select_model("prover", "general", "auto", effort)

    def test_a_hard_job_still_needs_its_reason(self) -> None:
        self.set_knob("astra-all")
        with self.assertRaises(ValueError):
            model_policy.select_model("prover", "escalated")
        selection = model_policy.select_model(
            "prover", "escalated", hardness_reason="new source-semantic decision")
        self.assertEqual(selection["classification"], "hard")

    def test_an_unknown_mode_fails_closed(self) -> None:
        self.set_knob("sol-all\n")
        with self.assertRaises(ValueError) as caught:
            model_policy.select_model("prover", "general")
        self.assertIn("unknown model override mode", str(caught.exception))

    def test_an_off_word_is_not_an_override(self) -> None:
        for word in ("", "  ", "none\n", "off\n", "null\n"):
            with self.subTest(repr(word)):
                self.set_knob(word)
                self.assertEqual(
                    model_policy.select_model("prover", "general")["model"], "gpt-5.6-sol")

    def test_the_knob_may_carry_the_brief_object(self) -> None:
        self.set_knob(json.dumps({"mode": "astra-all", "reason": "owner briefing 04:00Z",
                                  "set_by": "owner"}))
        selection = model_policy.select_model("prover", "general")
        self.assertEqual(selection["model"], "gpt-6-astra")
        self.assertIn("owner briefing 04:00Z", selection["rationale"])

    def test_an_expired_override_is_inactive(self) -> None:
        self.set_knob(json.dumps({"mode": "astra-all", "expires": "2020-01-01T00:00:00Z"}))
        self.assertEqual(
            model_policy.select_model("prover", "general")["model"], "gpt-5.6-sol")


# ── the reviewed policy object ──────────────────────────────────────────────


class PolicyObjectOverrideTests(_Base):
    policy_extra = {"override": {"mode": "astra-all", "reason": "full speed run",
                                 "set_by": "owner"}}

    def test_the_committed_override_is_honoured(self) -> None:
        selection = model_policy.select_model("prover", "general")
        self.assertEqual(selection["model"], "gpt-6-astra")
        self.assertEqual(selection["override_source"], "policy:local/model-policy.json")

    def test_the_runtime_knob_wins(self) -> None:
        self.set_knob("none")
        self.assertEqual(
            model_policy.select_model("prover", "general")["override_source"],
            "policy:local/model-policy.json",
            "an `off` knob does not un-set a committed override; it is simply absent",
        )


class PolicyValidatorTests(_Base):
    def test_an_unknown_override_field_is_refused(self) -> None:
        with self.assertRaises(ValueError):
            model_policy._validate_override({"mode": "astra-all", "effort": "high"},
                                            "policy:test")

    def test_an_unknown_mode_in_the_policy_is_refused(self) -> None:
        with self.assertRaises(ValueError):
            model_policy._validate_override({"mode": "everything-cheap"}, "policy:test")

    def test_a_naive_expiry_is_refused(self) -> None:
        with self.assertRaises(ValueError):
            model_policy._validate_override({"mode": "astra-all",
                                             "expires": "2099-01-01T00:00:00"},
                                            "policy:test")

    def test_the_shipped_policy_file_validates(self) -> None:
        raw = json.loads((REPO_ROOT / "local" / "model-policy.json")
                         .read_text(encoding="utf-8"))
        self.assertIn("override", raw)
        self.assertIsNone(model_policy._validate_override(raw.get("override"),
                                                          "policy:shipped"))


# ── the ratio audit ─────────────────────────────────────────────────────────


class RatioExclusionTests(unittest.TestCase):
    ACTIVATION = "2026-09-12T00:00:00+00:00"

    def _row(self, thread: str, model: str, **extra) -> dict:
        row = {"thread_id": thread, "root_thread_id": "root", "dispatch_kind": "new",
               "activation_at": self.ACTIVATION, "start": "2026-09-12T04:00:00+00:00",
               "effective_model": model, "selected_model": model}
        row.update(extra)
        return row

    def test_override_rows_are_excluded_not_counted_as_violations(self) -> None:
        rows = [self._row("t1", "gpt-5.6-sol"),
                self._row("t2", "gpt-6-astra", hardness_reason="hard"),
                self._row("t3", "gpt-6-astra", override_mode="astra-all"),
                self._row("t4", "gpt-6-astra", override_mode="astra-all")]
        report = model_policy.dispatch_ratio(rows, self.ACTIVATION)
        self.assertEqual(report["sol"], 1)
        self.assertEqual(report["astra"], 1)
        self.assertEqual(report["override_excluded"], 2)
        self.assertEqual(report["unknown"], 0)


# ── the callers' self-check ─────────────────────────────────────────────────


class CallerSelfCheckTests(unittest.TestCase):
    def test_autofix_defaults_the_fix_model_to_empty(self) -> None:
        text = (BIN_DIR / "autofix.sh").read_text(encoding="utf-8")
        self.assertIn('FIX_MODEL="${MIPSTARRE_FIX_MODEL:-}"', text)
        self.assertNotIn('MIPSTARRE_FIX_MODEL:-gpt-6-astra', text)
        self.assertIn("check_fix_model", text)

    def test_review_resolves_its_models_before_any_work(self) -> None:
        text = (BIN_DIR / "review.sh").read_text(encoding="utf-8")
        self.assertIn("policy_model", text)
        self.assertLess(text.index("policy_model()"), text.index("resolve_worktree()"))

    def test_the_shim_carries_no_model_rewrite(self) -> None:
        text = (BIN_DIR / "codex-policy-shim.sh").read_text(encoding="utf-8")
        body = "\n".join(line for line in text.splitlines()
                         if not line.lstrip().startswith("#"))
        self.assertNotIn("model=gpt-6-astra", body)
        self.assertNotIn("shim-rewrite", body)

    def test_both_scripts_pass_bash_syntax(self) -> None:
        for name in ("autofix.sh", "review.sh", "dispatch.sh", "codex-policy-shim.sh"):
            with self.subTest(name):
                result = subprocess.run(["bash", "-n", str(BIN_DIR / name)],
                                        capture_output=True, text=True)
                self.assertEqual(result.returncode, 0, result.stderr)


if __name__ == "__main__":
    unittest.main()
