#!/usr/bin/env python3
"""The apply -> pause -> resume round trip with the capacity controller present.

`test_run_mode.py` runs against a stub repository root that carries the two
committed templates and nothing else, so `run_mode.py` finds no capacity
controller there and zeroes and restores the cap files itself.  That is a real
configuration, but it is not the one a run uses, and the integration of the two
tools had a defect only this configuration shows: with the controller installed
but never seeded, `pause` asked it to save caps it had no state for, it saved
zeros, and `resume` restored its floor -- a briefed 5/28/33 came back as 1/1/2
while the resume message announced 5/28/33.  That is the 2026-09-12 failure the
two tools exist to prevent, so it is pinned here.

The repository root is a temporary directory whose ``local/bin`` is a symlink to
the real one: the tools under test are the committed files, while every record
they write (stages.jsonl, design-decisions.md) lands in the temporary tree.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
BIN = REPO_ROOT / "local" / "bin"
RUN_MODE = BIN / "run_mode.py"
CONTROLLER = BIN / "capacity_controller.py"
POLICY = REPO_ROOT / "local" / "capacity-policy.json"
TEMPLATE = REPO_ROOT / "results/telemetry/owner-tools/run-brief.template.json"
SHIM = REPO_ROOT / "results/telemetry/owner-tools/owner-bin-codex"


class CapacityRoundTripTestCase(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        root = Path(self._tmp.name)
        self.repo = root / "repo"
        self.cache = root / "cache"
        (self.repo / "local").mkdir(parents=True)
        (self.repo / "results/telemetry/owner-tools").mkdir(parents=True)
        (self.repo / "local" / "bin").symlink_to(BIN)
        shutil.copy(POLICY, self.repo / "local" / "capacity-policy.json")
        shutil.copy(TEMPLATE, self.repo / "results/telemetry/owner-tools"
                    / "run-brief.template.json")
        shutil.copy(SHIM, self.repo / "results/telemetry/owner-tools"
                    / "owner-bin-codex")
        self.watchdog = self.cache / "watchdog"
        self.watchdog.mkdir(parents=True)
        shutil.copy(TEMPLATE, self.watchdog / "run-brief.json")

    def tearDown(self) -> None:
        self._tmp.cleanup()

    # -- helpers ---------------------------------------------------------

    def run_mode(self, *argv: str) -> subprocess.CompletedProcess:
        env = dict(os.environ)
        env["MIPSTARRE_REPO_ROOT"] = str(self.repo)
        env["MIPSTARRE_CACHE_ROOT"] = str(self.cache)
        return subprocess.run([sys.executable, str(RUN_MODE), *argv],
                              cwd=self.repo, env=env, capture_output=True,
                              text=True)

    def caps(self) -> dict[str, str]:
        out = {}
        for name in ("max-codex-primary", "max-codex-second", "max-codex"):
            out[name] = (self.watchdog / name).read_text(encoding="utf-8").strip()
        return out

    # -- tests -----------------------------------------------------------

    def test_apply_seeds_the_controller_state(self) -> None:
        done = self.run_mode("apply")
        self.assertEqual(done.returncode, 0, done.stderr)
        state = json.loads((self.watchdog / "capacity" / "state.json")
                           .read_text(encoding="utf-8"))
        self.assertEqual(state["accounts"]["primary"]["cap"], 5)
        self.assertEqual(state["accounts"]["second"]["cap"], 28)

    def test_pause_and_resume_return_the_briefed_caps(self) -> None:
        self.assertEqual(self.run_mode("apply").returncode, 0)
        briefed = self.caps()
        self.assertEqual(briefed, {"max-codex-primary": "5",
                                   "max-codex-second": "28",
                                   "max-codex": "33"})
        done = self.run_mode("pause")
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertEqual(self.caps(), {"max-codex-primary": "0",
                                       "max-codex-second": "0",
                                       "max-codex": "0"})
        done = self.run_mode("resume")
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertEqual(self.caps(), briefed,
                         "the round trip must return the briefed caps, never the floor")
        # And the message must carry the numbers the files carry.
        self.assertIn("caps primary 5, second 28, max-codex 33", done.stdout)

    def test_a_second_pause_keeps_the_saved_caps(self) -> None:
        self.assertEqual(self.run_mode("apply").returncode, 0)
        self.assertEqual(self.run_mode("pause").returncode, 0)
        self.assertEqual(self.run_mode("pause").returncode, 0)
        self.assertEqual(self.run_mode("resume").returncode, 0)
        self.assertEqual(self.caps()["max-codex"], "33")

    def test_resume_refuses_to_announce_caps_the_files_do_not_carry(self) -> None:
        self.assertEqual(self.run_mode("apply").returncode, 0)
        self.assertEqual(self.run_mode("pause").returncode, 0)
        # Something else writes a cap file behind the controller's back.
        state_path = self.watchdog / "capacity" / "state.json"
        state = json.loads(state_path.read_text(encoding="utf-8"))
        state["accounts"]["second"]["saved_cap"] = 3
        state_path.write_text(json.dumps(state), encoding="utf-8")
        done = self.run_mode("resume")
        self.assertNotEqual(done.returncode, 0)
        self.assertIn("post-condition", done.stdout + done.stderr)

    def test_the_controller_is_resolved_under_the_repository_root(self) -> None:
        # The controller resolves its policy under MIPSTARRE_REPO_ROOT, so
        # run_mode must take the controller from there too; a stub root without
        # one falls back to writing the cap files itself rather than running a
        # controller against another root's data.
        env = dict(os.environ)
        bare = Path(self._tmp.name) / "bare"
        (bare / "results/telemetry/owner-tools").mkdir(parents=True)
        shutil.copy(TEMPLATE, bare / "results/telemetry/owner-tools"
                    / "run-brief.template.json")
        shutil.copy(SHIM, bare / "results/telemetry/owner-tools" / "owner-bin-codex")
        env["MIPSTARRE_REPO_ROOT"] = str(bare)
        env["MIPSTARRE_CACHE_ROOT"] = str(self.cache)
        for argv in (["apply"], ["pause"], ["resume"]):
            done = subprocess.run([sys.executable, str(RUN_MODE), *argv],
                                  cwd=bare, env=env, capture_output=True, text=True)
            self.assertEqual(done.returncode, 0, done.stderr)
        self.assertEqual(self.caps()["max-codex"], "33")
        self.assertFalse((self.watchdog / "capacity" / "state.json").exists(),
                         "no controller in that root, so none of its state either")
        self.assertTrue(CONTROLLER.is_file(), "the real controller is still installed")


if __name__ == "__main__":
    unittest.main()
