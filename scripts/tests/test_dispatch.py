#!/usr/bin/env python3
"""Regression tests for dispatch commands and pre-commit workflow behavior."""

from __future__ import annotations

import os
from pathlib import Path
import shlex
import subprocess
import tempfile
import unittest


REPO_ROOT = Path(__file__).resolve().parents[2]
DISPATCH = REPO_ROOT / "local" / "bin" / "dispatch.sh"
PRE_COMMIT = REPO_ROOT / ".githooks" / "pre-commit"
THREAD_ID = "019e93a5-e370-7aa1-ba77-6373dbdd6a61"


class DispatchCommandTests(unittest.TestCase):
    def dispatch_command(self, *extra: str) -> list[str]:
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
                    "MIPSTARRE_CODEX_MODEL": "test-model",
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
                    "--no-persona",
                    "--skip-hook-check",
                    "--effort",
                    "high",
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
        self.commit_file(repo, "local/inherited.txt", 401)
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
        self.commit_file(repo, "local/side.txt", 401)
        self.git(repo, "switch", "feature")
        self.git(repo, "merge", "--no-commit", "--no-ff", "side")

        result = self.run_hook(repo)

        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("non-main merge", result.stdout)
        self.assertIn("staged workflow-layer change is 401 lines", result.stdout)


if __name__ == "__main__":
    unittest.main()
