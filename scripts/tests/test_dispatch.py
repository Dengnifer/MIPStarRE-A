#!/usr/bin/env python3
"""Regression tests for dispatch commands and pre-commit workflow behavior."""

from __future__ import annotations

import json
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


class DispatchCommandTests(unittest.TestCase):
    def recorded_dispatch(self, model: str | None) -> dict[str, object]:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            repo = root / "repo"
            local_bin = repo / "local" / "bin"
            local_bin.mkdir(parents=True)
            shutil.copy2(DISPATCH, local_bin / "dispatch.sh")
            shutil.copy2(TELEMETRY, local_bin / "telemetry.py")
            (repo / "AGENTS.md").write_text("# Test repository\n", encoding="utf-8")
            subprocess.run(["git", "init", "-q"], cwd=repo, check=True)

            fake_bin = root / "bin"
            fake_bin.mkdir()
            fake_codex = fake_bin / "codex"
            fake_codex.write_text(
                "#!/bin/sh\n"
                f"printf '%s\\n' '{{\"type\":\"thread.started\","
                f"\"thread_id\":\"{THREAD_ID}\"}}'\n",
                encoding="utf-8",
            )
            fake_codex.chmod(0o755)

            home = root / "home"
            home.mkdir()
            env = os.environ.copy()
            env.update(
                {
                    "HOME": str(home),
                    "MIPSTARRE_CACHE_ROOT": str(root / "cache"),
                    "PATH": f"{fake_bin}{os.pathsep}{env.get('PATH', '')}",
                }
            )
            env.pop("MIPSTARRE_CODEX_MODEL", None)
            if model is not None:
                env["MIPSTARRE_CODEX_MODEL"] = model

            subprocess.run(
                [
                    str(local_bin / "dispatch.sh"),
                    "--role",
                    "scout",
                    "--issue",
                    "model-record",
                    "--worktree",
                    str(repo),
                    "--no-persona",
                    "--skip-hook-check",
                    "--",
                    "test prompt",
                ],
                cwd=repo,
                env=env,
                check=True,
                capture_output=True,
                text=True,
            )
            records = (repo / "results" / "telemetry" / "sessions.jsonl").read_text(
                encoding="utf-8"
            ).splitlines()
            self.assertEqual(len(records), 1)
            return json.loads(records[0])

    def dispatch_command(
        self, *extra: str, model: str = "test-model", effort: str = "high",
        include_persona: bool = False,
    ) -> list[str]:
        with tempfile.TemporaryDirectory() as cache_root:
            fake_bin = Path(cache_root) / "bin"
            fake_bin.mkdir()
            fake_codex = fake_bin / "codex"
            fake_codex.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            fake_codex.chmod(0o755)
            env = os.environ.copy()
            env.update(
                {
                    "MIPSTARRE_CACHE_ROOT": cache_root,
                    "MIPSTARRE_CODEX_MODEL": model,
                    "PATH": f"{fake_bin}{os.pathsep}{env.get('PATH', '')}",
                }
            )
            result = subprocess.run(
                [
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
                    "--effort",
                    effort,
                    "--dry-run",
                    *extra,
                    "--",
                    "test prompt",
                ],
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
        self.assertEqual(argv[7], "-o")
        self.assertTrue(argv[8].endswith(".last.md"))
        self.assertEqual(
            argv[9:13],
            ["-m", "test-model", "-c", "model_reasoning_effort=high"],
        )

    def test_fresh_argv_keeps_all_exec_options_before_prompt(self) -> None:
        argv = self.dispatch_command()

        self.assert_common_exec_options(argv)
        self.assertEqual(argv[13:], ["--", "<prompt>"])

    def test_resume_argv_places_exec_options_before_subcommand(self) -> None:
        argv = self.dispatch_command("--resume", THREAD_ID)

        self.assert_common_exec_options(argv)
        self.assertEqual(argv[13:], ["resume", "--", THREAD_ID, "<prompt>"])

    def test_future_astra_mathfix_selects_model_effort_and_persona(self) -> None:
        # HEAD remains the pre-merge branch tip while a merge commit is being prepared.
        argv = self.dispatch_command(
            "--role", "mathfix", "--sandbox", "workspace-write", "--persona-ref", "main",
            model="astra", effort="ultra", include_persona=True,
        )

        self.assertEqual(argv[3:7], ["-C", str(REPO_ROOT), "--sandbox", "workspace-write"])
        self.assertEqual(argv[argv.index("-m") + 1], "astra")
        self.assertIn("model_reasoning_effort=ultra", argv)
        self.assertIn("persona: main:local/personas/mathfix.md", self.last_dispatch_stdout)
        self.assertIn("# Persona: mathematical-gap repair", self.last_dispatch_stdout)

    def test_mathfix_rejects_non_astra_or_non_ultra_dispatches(self) -> None:
        for model, effort in (("", "ultra"), ("test-model", "ultra"), ("astra", "high")):
            with self.subTest(model=model, effort=effort):
                with self.assertRaises(subprocess.CalledProcessError) as failure:
                    self.dispatch_command("--role", "mathfix", model=model, effort=effort)
                self.assertEqual(failure.exception.returncode, 4)
                self.assertIn("mathfix requires an astra model", failure.exception.stderr)

    def test_telemetry_accepts_mathfix_role(self) -> None:
        result = subprocess.run(
            ["python3", str(TELEMETRY), "session-summarize", "--help"],
            check=True,
            capture_output=True,
            text=True,
        )

        self.assertIn("mathfix", result.stdout)

    def test_registry_records_explicit_model_override(self) -> None:
        record = self.recorded_dispatch("gpt-test-explicit")

        self.assertEqual(record["model"], "gpt-test-explicit")

    def test_registry_omits_model_when_dispatch_leaves_it_unresolved(self) -> None:
        for model in (None, ""):
            with self.subTest(model=model):
                record = self.recorded_dispatch(model)

                self.assertNotIn("model", record)

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
