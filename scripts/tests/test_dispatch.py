#!/usr/bin/env python3
"""Regression tests for local agent-session command assembly."""

from __future__ import annotations

import os
from pathlib import Path
import shlex
import subprocess
import tempfile
import unittest


REPO_ROOT = Path(__file__).resolve().parents[2]
DISPATCH = REPO_ROOT / "local" / "bin" / "dispatch.sh"
THREAD_ID = "019e93a5-e370-7aa1-ba77-6373dbdd6a61"


class DispatchCommandTests(unittest.TestCase):
    def dispatch_command(self, *extra: str) -> list[str]:
        with tempfile.TemporaryDirectory() as cache_root:
            env = os.environ.copy()
            env.update(
                {
                    "MIPSTARRE_CACHE_ROOT": cache_root,
                    "MIPSTARRE_CODEX_MODEL": "test-model",
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


if __name__ == "__main__":
    unittest.main()
