#!/usr/bin/env python3
"""Focused regressions for PR 552's supplemental contract repair."""

from __future__ import annotations

import io
import json
import os
import shutil
import subprocess
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
BIN = ROOT / "local/bin"
TOOLS = ROOT / "results/telemetry/owner-tools"
import sys
sys.path.insert(0, str(BIN))
import account_router  # noqa: E402
import run_mode  # noqa: E402


def text(path: Path) -> str:
    return path.read_text(encoding="utf-8")


class AutofixLoopTests(unittest.TestCase):
    def run_loop(self, verdict: str, review_rc: int = 0
                 ) -> tuple[subprocess.CompletedProcess, Path]:
        tmp = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, tmp, True)
        (tmp / "local/bin").mkdir(parents=True)
        (tmp / "local/bin/autofix.sh").write_text(
            '#!/bin/sh\nmkdir -p "$(dirname "$MIPSTARRE_AUTOFIX_ROUND_RESULT")"\n'
            'printf \'{"outcome":"fixed"}\\n\' > "$MIPSTARRE_AUTOFIX_ROUND_RESULT"\n'
            'touch "$TEST_ROOT/fix" "$TEST_ROOT/ci"\n', encoding="utf-8")
        (tmp / "local/bin/review.sh").write_text(
            '#!/bin/sh\nprintf "%s\\n" "$*" > "$TEST_ROOT/review.args"\n'
            '[ "$TEST_REVIEW_RC" -eq 0 ] || exit "$TEST_REVIEW_RC"\n'
            'printf "%s\\n0\\n" "$TEST_VERDICT" > "$TEST_ROOT/verdict"\n', encoding="utf-8")
        for path in (tmp / "local/bin/autofix.sh", tmp / "local/bin/review.sh"):
            path.chmod(0o755)
        source = text(BIN / "autofix.sh")
        function = source.split("run_fix_loop() {", 1)[1].split(
            '\n}\n\nif [ "$LOOP"', 1)[0]
        script = f'''set -u
ROOT="$TEST_ROOT"; CACHE="$TEST_ROOT/cache"; PR_ARG=552; LOOP_CAP=1; MODE=review
log() {{ :; }}; warn() {{ :; }}; die() {{ echo "$*" >&2; exit 1; }}
pr_head_sha() {{ echo newhead; }}
loop_verdict() {{
  [ -f "$TEST_ROOT/verdict" ] && cat "$TEST_ROOT/verdict" || printf 'NONE\\n0\\n'
}}
run_fix_loop() {{{function}
}}
run_fix_loop
'''
        env = dict(os.environ, TEST_ROOT=str(tmp), TEST_VERDICT=verdict,
                   TEST_REVIEW_RC=str(review_rc))
        return subprocess.run(["bash", "-c", script], text=True, capture_output=True, env=env), tmp

    def test_full_round_forces_a_real_review(self) -> None:
        done, tmp = self.run_loop("APPROVED")
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertTrue((tmp / "fix").exists() and (tmp / "ci").exists())
        self.assertIn("--force-review", text(tmp / "review.args"))

    def test_failed_review_with_no_verdict_stops(self) -> None:
        done, _ = self.run_loop("NONE", review_rc=9)
        self.assertEqual(done.returncode, 2)


class LaneContractTests(unittest.TestCase):
    def test_failed_dispatch_gate_precedes_every_downstream_phase(self) -> None:
        source = text(BIN / "lane.sh")
        gate = source.index('[ "$DRC" -eq 0 ]')
        for marker in ('rev-list --count', 'merge -q --no-edit', 'lake build MIPStarRE.QPBT',
                       'local/bin/pr_open.py', 'local/bin/ci.sh', 'TOOL=lane.sh VERSION='):
            self.assertLess(gate, source.index(marker, gate))

    def test_nonconforming_issue_title_is_normalized_in_captured_pr_args(self) -> None:
        tmp = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, tmp, True)
        (tmp / "local/bin").mkdir(parents=True)
        capture = tmp / "args.json"
        (tmp / "local/bin/pr_open.py").write_text(
            '#!/usr/bin/env python3\nimport json,os,sys\n'
            'json.dump(sys.argv[1:], open(os.environ["CAPTURE"], "w")); print(99)\n',
            encoding="utf-8")
        (tmp / "local/bin/pr_open.py").chmod(0o755)
        source = text(BIN / "lane.sh")
        block = source.split('log "opening PR"', 1)[1].split('[ -n "$PR" ]', 1)[0]
        script = ('log(){ :; }; STATE="$PWD/state"; mkdir -p "$STATE"; N=550; '
                  'ISSUE_TITLE="Prove the Pauli lemma"; BEFORE=a; AFTER=b; W="$PWD"; '
                  'BR=issue-550-pauli; ' + block)
        env = dict(os.environ, CAPTURE=str(capture), PATH=f"{tmp}/bin:{os.environ['PATH']}")
        done = subprocess.run(["bash", "-c", script], cwd=tmp, env=env,
                              text=True, capture_output=True)
        self.assertEqual(done.returncode, 0, done.stderr)
        args = json.loads(text(capture))
        self.assertEqual(args[args.index("--title") + 1], "feat(QPBT): Prove the Pauli lemma")
        body = text(tmp / "state/550.pr.md")
        self.assertIn("### Motivation\n", body)
        self.assertIn("### Description\n", body)
        self.assertIn("### Testing\n", body)


class TransactionAndAffinityTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.tmp, True)
        self.cache, self.repo = self.tmp / "cache", self.tmp / "repo"
        (self.cache / "watchdog/capacity").mkdir(parents=True)
        (self.repo / "results/telemetry/owner-tools").mkdir(parents=True)
        shutil.copy(TOOLS / "run-brief.template.json",
                    self.cache / "watchdog/run-brief.json")
        self.env = mock.patch.dict(os.environ, {"MIPSTARRE_CACHE_ROOT": str(self.cache),
                                               "MIPSTARRE_REPO_ROOT": str(self.repo)})
        self.env.start(); self.addCleanup(self.env.stop)

    def test_failed_controller_and_derived_write_restore_prior_outputs(self) -> None:
        paths = [self.cache / "watchdog/run-mode.json", self.cache / "watchdog/max-codex",
                 self.cache / "watchdog/capacity/state.json", self.cache / "watchdog/account-mode"]
        for index, path in enumerate(paths):
            path.parent.mkdir(parents=True, exist_ok=True); path.write_text(f"old-{index}\n")
        before = {path: path.read_bytes() for path in paths}
        def failed_controller(*_args, **_kwargs):
            paths[1].write_text("99\n"); paths[2].write_text("new\n")
            return False, "injected validation failure"
        with mock.patch.object(run_mode, "call_controller", side_effect=failed_controller), \
                redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
            self.assertNotEqual(run_mode.main(["apply"]), 0)
        self.assertEqual({path: path.read_bytes() for path in paths}, before)
        with mock.patch.object(run_mode, "call_controller", return_value=(True, "ok")), \
                mock.patch.object(run_mode, "write_account_mode", side_effect=OSError("write")), \
                redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
            self.assertNotEqual(run_mode.main(["apply"]), 0)
        self.assertEqual({path: path.read_bytes() for path in paths}, before)

    def test_custom_brief_homes_drive_resume_affinity(self) -> None:
        primary, second = self.tmp / "p", self.tmp / "s"
        mode = {"accounts": [{"name": "primary", "codex_home": str(primary)},
                              {"name": "second", "codex_home": str(second)}]}
        (self.cache / "watchdog/run-mode.json").write_text(json.dumps(mode))
        homes = account_router.account_homes(self.cache)
        thread = "019e93a5-e370-7aa1-ba77-6373dbdd6a61"
        rollout = primary / "sessions" / f"rollout-{thread}.jsonl"
        rollout.parent.mkdir(parents=True); rollout.touch()
        self.assertEqual(homes, {"primary": primary, "second": second})
        self.assertEqual(account_router.resume_account(thread, self.tmp / "missing", homes),
                         "primary")


class ResumeAndProtocolTests(unittest.TestCase):
    def test_both_crontab_restore_paths_gate_progress(self) -> None:
        source = text(TOOLS / "owner-resume.sh")
        block = source.split('if [ "$CRON_OK" -eq 1 ]; then', 1)[1].split(
            '\nfi\n\n# --- 3.', 1)[0]
        for installed in (True, False):
            with self.subTest(installed=installed), tempfile.TemporaryDirectory() as directory:
                root = Path(directory); crons = root / "crons"; cron = root / "crontab"
                if installed:
                    crons.write_text("#!/bin/sh\nexit 8\n"); crons.chmod(0o755)
                cron.write_text("#!/bin/sh\nexit 9\n"); cron.chmod(0o755)
                script = (f'CRON_OK=1; CRONS={crons!s}; CRONTAB_BIN={cron!s}; CRON_BAK=x; '
                          'log(){ :; }; resume_incomplete(){ echo "$1"; exit 5; }; if true; then'
                          + block + '\nfi')
                done = subprocess.run(["bash", "-c", script], text=True, capture_output=True)
                self.assertEqual(done.returncode, 5)

    def test_postconditions_precede_message_and_success_telemetry(self) -> None:
        source = text(TOOLS / "owner-resume.sh")
        gate = source.index('if [ "$RC" -ne 0 ]; then')
        self.assertLess(gate, source.index('tmux has-session', gate))
        self.assertLess(gate, source.index('"stage": "operator", "event": "resume"'))
        self.assertIn('python3 "$RUN_MODE" pause', source)
        self.assertIn('touch "$D/stop"', source)

    def test_protocol_contract_words_are_aligned(self) -> None:
        meta = text(ROOT / "local/protocols/meta.md")
        self.assertIn("telemetry.py event", meta)
        self.assertIn("`auth`, `unknown`", meta)
        speed = text(ROOT / "local/protocols/full-speed-mode.md")
        self.assertIn("`both` whenever `second` is", speed)


if __name__ == "__main__":
    unittest.main()
