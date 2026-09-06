#!/usr/bin/env python3
"""Regression tests for dispatch commands and pre-commit workflow behavior."""

from __future__ import annotations

import json
import fcntl
import importlib.util
from concurrent.futures import ThreadPoolExecutor, TimeoutError
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import tempfile
import unittest
from unittest import mock


REPO_ROOT = Path(__file__).resolve().parents[2]
DISPATCH = REPO_ROOT / "local" / "bin" / "dispatch.sh"
TELEMETRY = REPO_ROOT / "local" / "bin" / "telemetry.py"
PRE_COMMIT = REPO_ROOT / ".githooks" / "pre-commit"
THREAD_ID = "019e93a5-e370-7aa1-ba77-6373dbdd6a61"
ROUTER = DISPATCH.with_name("account_router.py")
SPEC = importlib.util.spec_from_file_location("account_router", ROUTER)
router = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(router)
HOST_PROCESS_SCAN = router.host_processes


class DispatchCommandTests(unittest.TestCase):
    def recorded_dispatch(self, model: str | None, account: str = "auto",
                          exit_code: int = 0, empty_second_home: bool = False,
                          effort: str | None = None,
                          config_model: str = "gpt-config-default",
                          continue_from: bool = False) -> dict[str, object]:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            repo = root / "repo"
            local_bin = repo / "local" / "bin"
            local_bin.mkdir(parents=True)
            shutil.copy2(DISPATCH, local_bin / "dispatch.sh")
            shutil.copy2(TELEMETRY, local_bin / "telemetry.py")
            shutil.copy2(ROUTER, local_bin / "account_router.py")
            (repo / "AGENTS.md").write_text("# Test repository\n", encoding="utf-8")
            subprocess.run(["git", "init", "-q"], cwd=repo, check=True)

            fake_bin = root / "bin"
            fake_bin.mkdir()
            fake_codex = fake_bin / "codex"
            fake_codex.write_text(
                "#!/bin/sh\n"
                'test "$(find "$MIPSTARRE_CACHE_ROOT/accounts" -name "[0-9]*" | wc -l)"'
                ' -eq 1 || exit 98\n'
                'printf "%s" "${CODEX_HOME-unset}" > "$HOME/selected-home"\n'
                f"printf '%s\\n' '{{\"type\":\"thread.started\","
                f"\"thread_id\":\"{THREAD_ID}\"}}'\nexit {exit_code}\n",
                encoding="utf-8",
            )
            fake_codex.chmod(0o755)

            home = root / "home"
            home.mkdir()
            primary = home / ".codex"
            primary.mkdir()
            (primary / "config.toml").write_text(
                f'model = "{config_model}"\n', encoding="utf-8"
            )
            second = (home / ".cache/mipstarre-dev/codex-home-yxy"
                      if empty_second_home else root / "second")
            second.mkdir(parents=True)
            (second / "config.toml").write_text('model = "gpt-second-default"\n')
            rollout_home = second if account == "second" else primary
            rollout = rollout_home / "sessions/2026/09/06" / f"rollout-{THREAD_ID}.jsonl"
            rollout.parent.mkdir(parents=True)
            rollout.touch()
            env = os.environ.copy()
            env.update(
                {
                    "HOME": str(home),
                    "CODEX_HOME": "/inherited-home-must-not-leak",
                    "MIPSTARRE_CODEX_ACCOUNT": account,
                    "MIPSTARRE_CODEX_HOME_SECOND": "" if empty_second_home else str(second),
                    "MIPSTARRE_ACCOUNT_WAIT": "0",
                    "MIPSTARRE_CACHE_ROOT": str(root / "cache"),
                    "PATH": f"{fake_bin}{os.pathsep}{env.get('PATH', '')}",
                }
            )
            env.pop("MIPSTARRE_CODEX_MODEL", None)
            if model is not None:
                env["MIPSTARRE_CODEX_MODEL"] = model
            watchdog = root / 'cache/watchdog'
            watchdog.mkdir(parents=True)
            (watchdog / 'account-mode').write_text('both' if account == 'second' else 'primary')

            dispatch_args = [
                str(local_bin / "dispatch.sh"),
                "--role",
                "scout",
                "--issue",
                "model-record",
                "--worktree",
                str(repo),
                "--no-persona",
                "--skip-hook-check",
            ]
            if effort is not None:
                dispatch_args.extend(["--effort", effort])
            if continue_from:
                subprocess.run(['git', '-c', 'user.name=Test', '-c', 'user.email=test@test',
                                'commit', '--allow-empty', '-qm', 'checkpoint'], cwd=repo, check=True)
                previous = dict(name='prior', account='second', thread_id='old-thread',
                                issue='model-record', status='done', wall_s=20)
                registry = repo / 'results/telemetry/sessions.jsonl'
                registry.parent.mkdir(parents=True)
                registry.write_text(json.dumps(previous) + '\n')
                budget = root / 'budget.json'
                budget.write_text(json.dumps(dict(anchor='2026-09-05T19:24:00Z', attempts=7,
                    attempt_limit=10, working_seconds=12452, sessions=['prior'])))
                handoff = root / 'handoff.json'
                handoff.write_text(json.dumps(dict(previous_session='prior', checkpoint='HEAD',
                                                   budget_file=str(budget))))
                dispatch_args.extend(['--continue-from', str(handoff)])
            dispatch_args.extend(["--", "test prompt"])
            result = subprocess.run(
                dispatch_args,
                cwd=repo,
                env=env,
                check=False,
                capture_output=True,
                text=True,
            )
            self.assertEqual(result.returncode, exit_code, result.stderr)
            selected = "second" if account == "second" else "primary"
            self.assertEqual((home / "selected-home").read_text(),
                             str(second) if selected == "second" else "unset")
            self.assertFalse(list((root / "cache" / "accounts").glob("*/[0-9]*")))
            records = (repo / "results" / "telemetry" / "sessions.jsonl").read_text(
                encoding="utf-8"
            ).splitlines()
            self.assertEqual(len(records), 2 if continue_from else 1)
            if continue_from:
                self.assertEqual(json.loads(records[0]), previous)
                self.assertEqual(json.loads(budget.read_text())['working_seconds'], 12452)
            record = json.loads(records[-1])
            self.assertEqual(record["rollout"], str(rollout))
            return record

    def dispatch_command(
        self, *extra: str, model: str = "gpt-6-astra", effort: str | None = "high",
        include_persona: bool = False,
    ) -> list[str]:
        with tempfile.TemporaryDirectory() as cache_root:
            fake_bin = Path(cache_root) / "bin"
            fake_bin.mkdir()
            fake_codex = fake_bin / "codex"
            fake_codex.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            fake_codex.chmod(0o755)
            home = Path(cache_root) / "home"
            rollout = home / ".codex/sessions/2026/09/06" / f"rollout-{THREAD_ID}.jsonl"
            rollout.parent.mkdir(parents=True)
            rollout.touch()
            env = os.environ.copy()
            env.update(
                {
                    "MIPSTARRE_CACHE_ROOT": cache_root,
                    "HOME": str(home),
                    "MIPSTARRE_CODEX_ACCOUNT": "auto",
                    "MIPSTARRE_CODEX_HOME_SECOND": str(home / "second"),
                    "MIPSTARRE_CODEX_MODEL": model,
                    "PATH": f"{fake_bin}{os.pathsep}{env.get('PATH', '')}",
                }
            )
            (Path(cache_root) / 'watchdog').mkdir()
            (Path(cache_root) / 'watchdog/account-mode').write_text('both')
            dispatch_args = [
                str(DISPATCH),
                "--role",
                "scout",
                "--issue",
                "dispatch-argv",
                "--worktree",
                str(REPO_ROOT),
                "--sandbox",
                "read-only",
                *([] if include_persona else ["--no-persona"]),
                "--skip-hook-check",
                "--dry-run",
                *extra,
            ]
            if effort is not None:
                dispatch_args.extend(["--effort", effort])
            dispatch_args.extend(["--", "test prompt"])
            result = subprocess.run(
                dispatch_args,
                cwd=REPO_ROOT,
                env=env,
                check=True,
                capture_output=True,
                text=True,
            )
        self.last_dispatch_stdout = result.stdout
        command_line = next(
            line.removeprefix("command: ")
            for line in result.stdout.splitlines()
            if line.startswith("command: ")
        )
        return shlex.split(command_line)

    def assert_common_exec_options(self, argv: list[str]) -> None:
        self.assertEqual(argv[:3], ["codex", "exec", "--json"])
        self.assertEqual(argv[3:7], ["-C", str(REPO_ROOT), "--sandbox", "read-only"])
        self.assertEqual(argv[7:11], ['-c', 'features.multi_agent=false', '-c',
                                    'agents.max_concurrent_threads_per_session=1'])
        self.assertEqual(argv[11], "-o")
        self.assertTrue(argv[12].endswith(".last.md"))
        self.assertEqual(
            argv[13:17],
            ["-m", "gpt-6-astra", "-c", "model_reasoning_effort=max"],
        )

    def test_fresh_argv_keeps_all_exec_options_before_prompt(self) -> None:
        argv = self.dispatch_command()

        self.assert_common_exec_options(argv)
        self.assertEqual(argv[17:], ["--", "<prompt>"])

    def test_resume_argv_places_exec_options_before_subcommand(self) -> None:
        argv = self.dispatch_command("--resume", THREAD_ID)

        self.assert_common_exec_options(argv)
        self.assertEqual(argv[17:], ["resume", "--", THREAD_ID, "<prompt>"])

    def test_astra_normalizes_omitted_and_legacy_ultra_effort(self) -> None:
        for role in ('orc', 'prover', 'reviewer', 'simplifier', 'blueprint', 'splitter',
                     'scout', 'mathfix'):
            for effort in (None, 'ultra', 'xhigh', 'max', 'high'):
                with self.subTest(role=role, effort=effort):
                    argv = self.dispatch_command('--role', role, effort=effort)
                    self.assertIn('model_reasoning_effort=max', argv)

    def test_sol_is_rejected_for_every_role(self) -> None:
        for role in ('orc', 'prover', 'reviewer', 'simplifier', 'blueprint', 'splitter',
                     'scout', 'mathfix'):
            with self.assertRaises(subprocess.CalledProcessError):
                self.dispatch_command('--role', role, model='gpt-5.6-sol')

    def test_astra_mathfix_selects_max_effort_and_persona(self) -> None:
        for effort in (None, "ultra", "xhigh"):
            with self.subTest(effort=effort):
                argv = self.dispatch_command(
                    "--role", "mathfix", "--sandbox", "workspace-write",
                    "--persona-ref", "main", model="gpt-6-astra", effort=effort,
                    include_persona=True,
                )

                self.assertEqual(
                    argv[3:7], ["-C", str(REPO_ROOT), "--sandbox", "workspace-write"]
                )
                self.assertEqual(argv[argv.index("-m") + 1], "gpt-6-astra")
                self.assertIn("model_reasoning_effort=max", argv)
                self.assertIn(
                    "persona: main:local/personas/mathfix.md", self.last_dispatch_stdout
                )
                self.assertIn(
                    "# Persona: mathematical-gap repair", self.last_dispatch_stdout
                )

    def test_mathfix_rejects_non_astra_or_non_xhigh_dispatches(self) -> None:
        for model, effort in (("gpt-5.6-sol", "ultra"),
                              ("test-model", "xhigh"), ("astra", "high")):
            with self.subTest(model=model, effort=effort):
                with self.assertRaises(subprocess.CalledProcessError) as failure:
                    self.dispatch_command("--role", "mathfix", model=model, effort=effort)
                self.assertEqual(failure.exception.returncode, 4)
                self.assertIn("owner policy requires gpt-6-astra", failure.exception.stderr)

    def test_telemetry_accepts_mathfix_role(self) -> None:
        result = subprocess.run(
            ["python3", str(TELEMETRY), "session-summarize", "--help"],
            check=True,
            capture_output=True,
            text=True,
        )

        self.assertIn("mathfix", result.stdout)

    def test_registry_records_explicit_model_override(self) -> None:
        record = self.recorded_dispatch("gpt-6-astra")

        self.assertEqual(record["model"], "gpt-6-astra")

    def test_registry_records_effective_requested_effort(self) -> None:
        for effort in (None, "ultra", "xhigh"):
            with self.subTest(model="astra", effort=effort):
                record = self.recorded_dispatch("gpt-6-astra", effort=effort)
                self.assertEqual(record["requested_effort"], "max")

        record = self.recorded_dispatch(
            None, effort=None, config_model="gpt-6-astra"
        )
        self.assertEqual(record["requested_effort"], "max")

    def test_registry_resolves_account_config_model(self) -> None:
        for model in (None, ""):
            with self.subTest(model=model):
                record = self.recorded_dispatch(model)

                self.assertEqual(record["model"], "gpt-6-astra")
                self.assertEqual(record["account"], "primary")

    def test_empty_model_uses_owner_policy(self) -> None:
        self.assertIn('gpt-6-astra', self.dispatch_command(model=''))

    def test_secondary_checkpoint_continuation_preserves_budget_and_history(self) -> None:
        record = self.recorded_dispatch(None, continue_from=True)
        self.assertEqual(record['account'], 'primary')
        self.assertEqual(record['continuation']['previous_thread_id'], 'old-thread')
        self.assertEqual(record['continuation']['budget']['working_seconds'], 12452)

    def test_second_account_environment_and_failed_session_cleanup(self) -> None:
        record = self.recorded_dispatch(None, "second", exit_code=7)
        self.assertEqual(record["account"], "second")
        self.assertEqual(record["model"], "gpt-6-astra")
        self.assertEqual(record["status"], "failed")

    def test_empty_secondary_home_uses_default_for_model_and_execution(self) -> None:
        record = self.recorded_dispatch(None, "second", empty_second_home=True)
        self.assertEqual(record["account"], "second")
        self.assertEqual(record["model"], "gpt-6-astra")

    def test_account_argument_validation_and_override(self) -> None:
        for value in ("invalid", "", "secondary"):
            with self.subTest(value=value), self.assertRaises(subprocess.CalledProcessError) as failure:
                self.dispatch_command("--account", value)
            self.assertEqual(failure.exception.returncode, 2)
        self.dispatch_command("--account", "second")
        self.assertIn("account: second", self.last_dispatch_stdout)

    def test_resume_rejects_cross_account_override(self) -> None:
        with self.assertRaises(subprocess.CalledProcessError) as failure:
            self.dispatch_command("--resume", THREAD_ID, "--account", "second")
        self.assertIn("resume belongs to primary", failure.exception.stderr)

    def test_session_status_preserves_legacy_row_without_model(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            registry = Path(directory) / "sessions.jsonl"
            legacy = {
                "name": "scout-legacy-20260830-01",
                "role": "scout",
                "issue": "legacy",
                "status": "done",
            }
            registry.write_text(json.dumps(legacy) + "\n", encoding="utf-8")

            result = subprocess.run(
                [
                    "python3",
                    str(TELEMETRY),
                    "session-status",
                    "--name",
                    legacy["name"],
                    "--status",
                    "archived",
                    "--registry",
                    str(registry),
                ],
                check=True,
                capture_output=True,
                text=True,
            )

            archived = json.loads(result.stdout)
            self.assertEqual(archived["status"], "archived")
            self.assertNotIn("model", archived)
            self.assertNotIn("requested_effort", archived)

    def test_workspace_write_grants_only_resolved_external_lake(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            worktree, target = root / "worktree", root / "lake" / "main"
            worktree.mkdir()
            subprocess.run(["git", "init", "-q", "-b", "main"], cwd=worktree, check=True)
            target.mkdir(parents=True)
            (worktree / ".lake").symlink_to(target, target_is_directory=True)
            with mock.patch.dict(os.environ, {"MIPSTARRE_LAKE_ROOT": str(target.parent)}):
                argv = self.dispatch_command("--role", "prover", "--worktree", str(worktree),
                                             "--sandbox", "workspace-write")
        self.assertEqual(argv[argv.index("--add-dir") + 1], str(target.resolve()))
        self.assertLess(argv.index("--add-dir"), argv.index("-o"))

    def test_pre_commit_budget_counts_dispatch_tests(self) -> None:
        self.assertIn(
            "scripts/tests/test_dispatch.py",
            PRE_COMMIT.read_text(encoding="utf-8"),
        )


class AccountRouterTests(unittest.TestCase):
    def setUp(self) -> None:
        patcher = mock.patch.object(router, 'host_processes', return_value=({}, {}))
        patcher.start()
        self.addCleanup(patcher.stop)

    def test_host_scan_handles_global_options_without_reading_prompt_as_command(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in ('1', 'self', '100', '200'):
                (root / name).mkdir()
            (root / '1/comm').write_text('systemd')
            (root / 'self/status').write_text(f'NSpid:\t{os.getpid()}')
            for pid, arguments in ((100, ['codex', '-m', 'gpt-6-astra', '-c',
                                          'model_reasoning_effort=max', 'exec', '--', 'prompt']),
                                   (200, ['codex', '-m', 'gpt-6-astra', '--', 'exec'])):
                process = root / str(pid)
                (process / 'status').write_text(f'Name:\tcodex\nPPid:\t{200 if pid == 100 else 1}')
                (process / 'cmdline').write_bytes(b'\0'.join(arg.encode() for arg in arguments))
                (process / 'environ').write_bytes(b'HOME=/test')
            def mapped_path(path):
                return root / str(path).removeprefix('/proc').lstrip('/') if str(path).startswith(
                    '/proc') else Path(path)
            with mock.patch.object(router, 'Path', side_effect=mapped_path), \
                 mock.patch.dict(os.environ, {'MIPSTARRE_CODEX_HOME_SECOND': '/second'}):
                self.assertEqual(HOST_PROCESS_SCAN()[1],
                                 {100: ('primary', False), 200: ('primary', True)})

    def test_mode_changes_disabled_caps_and_preserved_both_settings(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            watchdog = root / 'watchdog'
            watchdog.mkdir()
            mode = watchdog / 'account-mode'
            self.assertEqual(router.reserve(root, 'auto', 123, 0, True), 'primary')
            with self.assertRaisesRegex(ValueError, 'disabled'):
                router.reserve(root, 'second', 123, 0, True)
            (watchdog / 'max-codex-primary').write_text('0')
            with self.assertRaises(ValueError):
                router.reserve(root, 'auto', 123, 0, True)
            mode.write_text('both')
            self.assertEqual(router.reserve(root, 'auto', 123, 0, True), 'second')
            preserved = watchdog / 'account-mode-both-preserved.json'
            settings = '{"max_codex":19,"primary":10,"second":9}'
            preserved.write_text(settings)
            self.assertEqual(router.reserve(root, 'auto', 123, 0, True), 'primary')
            mode.write_text('primary')
            with self.assertRaises(ValueError):
                router.reserve(root, 'auto', 123, 0, True)
            self.assertEqual(preserved.read_text(), settings)
            self.assertEqual((watchdog / 'max-codex-primary').read_text(), '0')
            mode.write_text('invalid')
            with self.assertRaises(ValueError):
                router.reserve(root, 'auto', 123, 0, True)

    def test_secondary_resume_cannot_override_primary_mode(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            registry = root / 'registry'
            registry.write_text(json.dumps(dict(thread_id=THREAD_ID, account='second')))
            with mock.patch.dict(os.environ, {'HOME': directory,
                                              'MIPSTARRE_CODEX_MODEL': 'gpt-6-astra'}):
                for account in ('auto', 'primary', 'second'):
                    with mock.patch('sys.argv', [str(ROUTER), directory, account, '123', '0',
                         str(registry), '--resume', THREAD_ID]), mock.patch('sys.stderr'), \
                         self.assertRaises(SystemExit) as failure:
                        router.main()
                    self.assertEqual(failure.exception.code, 4)
            self.assertFalse(list(root.glob('accounts/*/[0-9]*')))

    def test_host_visibility_failure_does_not_delete_reservations(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            marker = root / 'accounts/primary/123'
            marker.parent.mkdir(parents=True)
            marker.touch()
            with mock.patch.object(router, 'host_processes', side_effect=PermissionError), \
                 mock.patch.object(router.os, 'kill', side_effect=ProcessLookupError), \
                 self.assertRaises(PermissionError):
                router.reserve(root, 'auto', 456, 0, False)
            self.assertTrue(marker.exists())

    def test_main_additional_uses_orphans_and_reservation_reconciliation(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            marker = root / 'accounts/primary/100'
            marker.parent.mkdir(parents=True)
            marker.touch()
            parents = {101: 100, 100: 1, 200: 1, 300: 1, 400: 1, 500: 1, 600: 1}
            processes = {101: ('primary', False), 600: ('primary', False),
                         **{pid: ('primary', True) for pid in (200, 300, 400, 500)}}
            with mock.patch.object(router, 'host_processes', return_value=(parents, processes)), \
                 mock.patch.object(router.os, 'kill'):
                self.assertEqual(router.occupancy(root), ([2, 0], [4, 0]))
            with mock.patch.object(router, 'occupancy', return_value=([8, 0], [4, 0])), \
                 self.assertRaises(ValueError):
                router.reserve(root, 'auto', 123, 0, False)
            (root / 'watchdog').mkdir()
            (root / 'watchdog/primary-external-reserved').write_text('1')
            with mock.patch.object(router, 'occupancy', return_value=([7, 0], [4, 0])), \
                 self.assertRaises(ValueError):
                router.reserve(root, 'auto', 123, 0, False)

    def test_last_primary_slot_is_atomic_under_contention(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'watchdog').mkdir()
            (root / 'watchdog/max-codex-primary').write_text('1')
            def attempt(pid):
                try:
                    return router.reserve(root, 'auto', pid, 0, False)
                except ValueError:
                    return 'full'
            with mock.patch.object(router.os, 'kill'), ThreadPoolExecutor(8) as pool:
                results = list(pool.map(attempt, range(100, 108)))
            self.assertEqual(results.count('primary'), 1)
            self.assertEqual(results.count('full'), 7)

    def test_runtime_shim_requests_max_and_preserves_prompt(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            home = Path(directory)
            binary = home / '.local/bin/codex'
            binary.parent.mkdir(parents=True)
            binary.write_text('#!/usr/bin/env python3\nimport json, sys\nprint(json.dumps(sys.argv[1:]))')
            binary.chmod(0o755)
            environment = dict(os.environ, HOME=directory, CODEX_HOME=str(home / '.codex'),
                               MIPSTARRE_CACHE_ROOT=str(home / 'cache'))
            shim = str(DISPATCH.with_name('codex-policy-shim.sh'))
            for effort in (None, 'ultra', 'xhigh', 'max', 'low'):
                arguments = [] if effort is None else ['-c', f'model_reasoning_effort="{effort}"']
                result = subprocess.run(['bash', shim, 'exec', '-m', 'gpt-6-astra', *arguments,
                                         '--', 'prompt with model_reasoning_effort=ultra'],
                    env=environment, capture_output=True, text=True, check=True)
                argv = json.loads(result.stdout)
                self.assertIn('model_reasoning_effort="max"', argv)
                self.assertIn('features.multi_agent=false', argv)
                self.assertTrue(argv[-1].endswith('prompt with model_reasoning_effort=ultra'))
            for arguments in (['-m', 'gpt-5.6-sol'], ['-c', 'model="gpt-5.6-sol"']):
                self.assertEqual(subprocess.run(['bash', shim, *arguments], env=environment,
                    capture_output=True).returncode, 4)
            for arguments in (['--config=model_reasoning_effort=ultra'],
                              ['-cmodel_reasoning_effort=xhigh'],
                              ['--config', 'features.multi_agent=true']):
                result = subprocess.run(['bash', shim, 'exec', *arguments, '--', 'prompt'],
                    env=environment, capture_output=True, text=True, check=True)
                self.assertIn('model_reasoning_effort="max"', json.loads(result.stdout))
            environment['CODEX_HOME'] = str(home / 'second')
            self.assertEqual(subprocess.run(['bash', shim, 'exec'], env=environment,
                capture_output=True).returncode, 4)

    def test_empty_secondary_home_resume_uses_default_rollout(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            second = root / ".cache/mipstarre-dev/codex-home-yxy"
            rollout = second / "sessions" / f"rollout-{THREAD_ID}.jsonl"
            rollout.parent.mkdir(parents=True)
            rollout.touch()
            (second / "config.toml").write_text('model = "gpt-second-default"\n')
            (root / 'cache/watchdog').mkdir(parents=True)
            (root / 'cache/watchdog/account-mode').write_text('both')
            with mock.patch.dict(os.environ, {
                "HOME": str(root), "MIPSTARRE_CODEX_HOME_SECOND": "",
                "MIPSTARRE_CODEX_MODEL": "",
            }), mock.patch("sys.argv", [
                str(ROUTER), str(root / "cache"), "auto", "123", "0",
                str(root / "registry.jsonl"), "--resume", THREAD_ID, "--dry-run",
            ]), mock.patch("builtins.print") as output:
                router.main()
            self.assertEqual(output.call_args_list,
                             [mock.call("second"), mock.call("gpt-6-astra")])

    def test_resume_skips_bad_rows_without_losing_affinity_or_conflicts(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            registry = root / "registry.jsonl"
            homes = {account: root / account for account in router.ACCOUNTS}
            bad_rows = '\n  \n{"truncated":\nnull\n[]\n42\n'
            record = json.dumps({"thread_id": THREAD_ID, "account": "second"})
            registry.write_text(bad_rows + record + "\n")
            with mock.patch("sys.stderr") as stderr:
                self.assertEqual(router.resume_account(THREAD_ID, registry, homes), "second")
            self.assertIn("skipping malformed registry record", str(stderr.write.call_args_list))
            rollout = homes["second"] / "sessions" / f"rollout-{THREAD_ID}.jsonl"
            rollout.parent.mkdir(parents=True)
            rollout.touch()
            with mock.patch("sys.stderr"):
                registry.write_text(bad_rows)
                self.assertEqual(router.resume_account(THREAD_ID, registry, homes), "second")
                registry.write_text(bad_rows + json.dumps(
                    {"thread_id": THREAD_ID, "account": "primary"}))
                with self.assertRaises(ValueError):
                    router.resume_account(THREAD_ID, registry, homes)

    def test_resume_waits_for_registry_writer(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            registry = root / "registry.jsonl"
            with registry.open("w") as writer, ThreadPoolExecutor(1) as pool:
                fcntl.flock(writer, fcntl.LOCK_EX)
                writer.write('{"thread_id":')
                writer.flush()
                homes = {account: root / account for account in router.ACCOUNTS}
                try:
                    pending = pool.submit(router.resume_account, THREAD_ID, registry, homes)
                    with self.assertRaises(TimeoutError):
                        pending.result(timeout=0.1)
                    writer.write(json.dumps(THREAD_ID) + ', "account": "second"}\n')
                    writer.flush()
                finally:
                    fcntl.flock(writer, fcntl.LOCK_UN)
                self.assertEqual(pending.result(timeout=5), "second")

    def test_concurrent_reservations_do_not_overbook(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "watchdog").mkdir()
            (root / 'watchdog/account-mode').write_text('both')
            for account in router.ACCOUNTS:
                (root / "watchdog" / f"max-codex-{account}").write_text("8")
            with mock.patch.object(router.os, "kill"), ThreadPoolExecutor(16) as pool:
                selected = list(pool.map(
                    lambda pid: router.reserve(root, "auto", pid, 0, False), range(100, 116)
                ))
            self.assertEqual(selected.count("primary"), 8)
            self.assertEqual(selected.count("second"), 8)

    def test_model_comparison_prefers_registry_and_keeps_rollout_fallback(self) -> None:
        spec = importlib.util.spec_from_file_location(
            "model_compare", REPO_ROOT / "results/telemetry/model-comparison/compare.py"
        )
        compare = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(compare)
        with mock.patch.object(compare, "model_from_stream", side_effect=[None, "gpt-legacy"]) as scan:
            self.assertEqual(compare.derive_model({"model": "gpt-explicit"}, {}),
                             ("gpt-explicit", "registry"))
            scan.assert_not_called()
            self.assertEqual(compare.derive_model({"rollout": "/legacy"}, {}),
                             ("gpt-legacy", "rollout"))

    def test_chooser_uses_ratios_and_primary_ties(self) -> None:
        for live, caps, expected in (
            ([0, 0], [9, 10], "primary"), ([1, 1], [9, 10], "second"),
            ([9, 10], [9, 10], "primary"), ([10, 10], [9, 10], "second"),
            ([2, 3], [4, 6], "primary"), ([0, 1], [1, 10], "primary"),
        ):
            with self.subTest(live=live, caps=caps):
                self.assertEqual(router.choose_account(live, caps), expected)

    def test_stale_cleanup_preserves_live_and_permission_denied_pids(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for pid in ("11", "12", "13"):
                (root / pid).touch()
            with mock.patch.object(router.os, "kill", side_effect=[
                ProcessLookupError(), None, PermissionError()
            ]):
                self.assertEqual(len(router.live_pids(root)), 2)
            self.assertEqual(len(list(root.iterdir())), 2)

    def test_caps_wait_timeout_and_explicit_affinity(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "watchdog").mkdir()
            for account in router.ACCOUNTS:
                (root / "watchdog" / f"max-codex-{account}").write_text("1")
            with mock.patch.object(router, 'occupancy', return_value=([1, 0], [1, 0])), \
                 mock.patch.object(router.time, "monotonic", side_effect=[0, 0, 0, 21]), \
                 mock.patch.object(router.time, "sleep") as sleep:
                for account in router.ACCOUNTS:
                    (root / "accounts" / account).mkdir(parents=True)
                with self.assertRaisesRegex(ValueError, 'capacity exhausted'):
                    router.reserve(root, "auto", 123, 20, False)
                sleep.assert_called_once_with(20)
                self.assertFalse((root / "accounts/primary/123").exists())
            (root / 'watchdog/account-mode').write_text('both')
            self.assertEqual(router.reserve(root, "second", os.getpid(), 0, False), "second")

    def test_resume_registry_and_legacy_rollout_affinity(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            registry = root / "registry.jsonl"
            homes = {account: root / account for account in router.ACCOUNTS}
            registry.write_text(json.dumps({"thread_id": THREAD_ID, "account": "second"}))
            self.assertEqual(router.resume_account(THREAD_ID, registry, homes), "second")
            registry.unlink()
            rollout = homes["second"] / "sessions/2026/09/06" / f"rollout-{THREAD_ID}.jsonl"
            rollout.parent.mkdir(parents=True)
            rollout.touch()
            self.assertEqual(router.resume_account(THREAD_ID, registry, homes), "second")
            with self.assertRaises(ValueError):
                router.resume_account("unknown", registry, homes)
            registry.write_text(json.dumps({"thread_id": THREAD_ID, "account": "primary"}))
            with self.assertRaises(ValueError):
                router.resume_account(THREAD_ID, registry, homes)

    def test_invalid_caps_fail_and_dry_run_does_not_reserve(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.assertEqual(router.reserve(root, "auto", 123, 0, True), "primary")
            self.assertFalse(list((root / "accounts").glob("*/[0-9]*")))
            (root / "watchdog").mkdir()
            (root / "watchdog/max-codex-primary").write_text("0")
            with self.assertRaises(ValueError):
                router.reserve(root, "auto", 123, 0, False)


class PreCommitBudgetTests(unittest.TestCase):
    def git(self, repo: Path, *args: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            ["git", *args],
            cwd=repo,
            check=True,
            capture_output=True,
            text=True,
        )

    def new_repo(self) -> tuple[Path, str]:
        temporary_directory = tempfile.TemporaryDirectory()
        self.addCleanup(temporary_directory.cleanup)
        repo = Path(temporary_directory.name)
        self.git(repo, "init", "--initial-branch=feature")
        self.git(repo, "config", "user.email", "hook-test@example.invalid")
        self.git(repo, "config", "user.name", "Hook Test")
        (repo / "README").write_text("root\n", encoding="utf-8")
        self.git(repo, "add", "README")
        self.git(repo, "commit", "-m", "root")
        return repo, self.git(repo, "rev-parse", "HEAD").stdout.strip()

    def commit_file(self, repo: Path, path: str, lines: int) -> None:
        target = repo / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text("line\n" * lines, encoding="utf-8")
        self.git(repo, "add", path)
        self.git(repo, "commit", "-m", f"add {path}")

    def run_hook(self, repo: Path) -> subprocess.CompletedProcess[str]:
        env = os.environ.copy()
        env["MIPSTARRE_SKIP_HOOKS"] = "1"
        env.pop("MIPSTARRE_INFRA_OVERRIDE", None)
        return subprocess.run(
            [str(PRE_COMMIT)],
            cwd=repo,
            env=env,
            check=False,
            capture_output=True,
            text=True,
        )

    def test_main_merge_exempts_inherited_workflow_lines(self) -> None:
        repo, root = self.new_repo()
        self.commit_file(repo, "feature.txt", 1)
        self.git(repo, "switch", "--create", "main", root)
        self.commit_file(repo, "local/inherited.txt", 1001)
        self.git(repo, "update-ref", "refs/remotes/github/main", "HEAD")
        self.git(repo, "switch", "feature")
        self.git(repo, "merge", "--no-commit", "--no-ff", "main")

        result = self.run_hook(repo)

        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("main-history merge", result.stdout)

    def test_non_main_merge_keeps_workflow_lines_budgeted(self) -> None:
        repo, root = self.new_repo()
        self.commit_file(repo, "feature.txt", 1)
        self.git(repo, "update-ref", "refs/remotes/github/main", root)
        self.git(repo, "switch", "--create", "side", root)
        self.commit_file(repo, "local/side.txt", 1001)
        self.git(repo, "switch", "feature")
        self.git(repo, "merge", "--no-commit", "--no-ff", "side")

        result = self.run_hook(repo)

        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("non-main merge", result.stdout)
        self.assertIn("staged workflow-layer change is 1001 lines", result.stdout)

    def test_standalone_workflow_test_growth_is_budgeted(self) -> None:
        paths = (
            "scripts/tests/test_pre_push_hook.py",
            "scripts/tests/test_ready_packets.py",
        )
        for path in paths:
            with self.subTest(path=path):
                repo, _ = self.new_repo()
                target = repo / path
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text("line\n" * 1001, encoding="utf-8")
                self.git(repo, "add", path)

                result = self.run_hook(repo)

                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                self.assertIn("staged workflow-layer change is 1001 lines", result.stdout)


if __name__ == "__main__":
    unittest.main()
