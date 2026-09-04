"""Regression tests for the local pre-push hook."""

from __future__ import annotations

import os
from pathlib import Path
import re
import subprocess
import tempfile
import unittest


REPO_ROOT = Path(__file__).resolve().parents[2]
PRE_PUSH = REPO_ROOT / ".githooks" / "pre-push"
CHECKED_PUSH = REPO_ROOT / "local" / "bin" / "checked-push.sh"


class PrePushHookTests(unittest.TestCase):
    def git(self, repo: Path, *args: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            ["git", *args],
            cwd=repo,
            check=True,
            capture_output=True,
            text=True,
        )

    def new_push_repo(self, root: Path) -> tuple[Path, Path, Path, Path]:
        repo = root / "work"
        remote = root / "remote.git"
        fetch_remote = root / "fetch.git"
        repo.mkdir()
        self.git(repo, "init", "--quiet")
        self.git(repo, "symbolic-ref", "HEAD", "refs/heads/main")
        self.git(repo, "config", "user.email", "hook-test@example.invalid")
        self.git(repo, "config", "user.name", "Hook Test")
        self.git(root, "init", "--quiet", "--bare", str(remote))
        self.git(root, "init", "--quiet", "--bare", str(fetch_remote))

        (repo / "payload").write_text("first\n", encoding="utf-8")
        self.git(repo, "add", "payload")
        self.git(repo, "commit", "--quiet", "-m", "first")
        self.git(repo, "remote", "add", "test", str(fetch_remote))
        self.git(repo, "remote", "set-url", "--push", "test", str(remote))
        self.git(repo, "config", "core.hooksPath", ".githooks")

        hook_log = root / "hook.log"
        receive_marker = root / "receive-started"
        hooks = repo / ".githooks"
        hooks.mkdir()
        hook = hooks / "pre-push"
        hook.write_text(
            """#!/bin/sh
set -eu
if [ "${MIPSTARRE_SKIP_HOOKS:-}" = "1" ]; then
  [ -e "$RECEIVE_MARKER" ] || exit 91
  printf 'transport-skip\\n' >> "$HOOK_LOG"
  exit 0
fi
[ ! -e "$RECEIVE_MARKER" ] || exit 92
read local_ref local_sha remote_ref remote_sha
printf 'preflight|%s|%s|%s|%s\\n' \
  "$local_ref" "$local_sha" "$remote_ref" "$remote_sha" >> "$HOOK_LOG"
[ "${FAIL_GATE:-}" != "1" ] || exit 23
""",
            encoding="utf-8",
        )
        hook.chmod(0o755)

        receive_pack = root / "receive-pack"
        receive_pack.write_text(
            """#!/bin/sh
set -eu
: > "$RECEIVE_MARKER"
exec git-receive-pack "$@"
""",
            encoding="utf-8",
        )
        receive_pack.chmod(0o755)
        self.git(repo, "config", "remote.test.receivepack", str(receive_pack))
        return repo, remote, hook_log, receive_marker

    def run_checked_push(
        self,
        repo: Path,
        hook_log: Path,
        receive_marker: Path,
        *,
        fail_gate: bool = False,
    ) -> subprocess.CompletedProcess[str]:
        env = dict(
            os.environ,
            HOOK_LOG=str(hook_log),
            RECEIVE_MARKER=str(receive_marker),
            MIPSTARRE_SKIP_HOOKS="1",
        )
        if fail_gate:
            env["FAIL_GATE"] = "1"
        return subprocess.run(
            [
                str(CHECKED_PUSH),
                "--repo-root",
                str(repo),
                "test",
                "refs/heads/main:refs/heads/main",
            ],
            cwd=repo,
            env=env,
            check=False,
            capture_output=True,
            text=True,
        )

    def test_lake_and_python_checks_clear_hook_git_environment(self) -> None:
        text = PRE_PUSH.read_text()
        self.assertIn("run_outside_git_env()", text)
        self.assertIn("git rev-parse --local-env-vars", text)
        self.assertIn('unset "$name"', text)
        self.assertIn("lean_file_to_module()", text)
        self.assertIn("refreshing compiled Lean modules for checkdecls", text)

        self.assertIn("run_outside_git_env lake env lean", text)
        self.assertIn('run_outside_git_env lake build "$LEAN_MODULE"', text)
        self.assertIn("run_outside_git_env lake exe checkdecls", text)
        self.assertIn("run_outside_git_env lake build", text)
        self.assertIn("run_outside_git_env python3 scripts/check_paper_gap_note_style.py", text)
        self.assertIn("run_outside_git_env python3 scripts/check_statement_paper_origin.py", text)
        self.assertIn(
            "run_outside_git_env python3 scripts/audit_new_proof_obligation_metadata.py",
            text,
        )
        self.assertIn("run_outside_git_env python3 scripts/audit_paper_facing_proof_debt.py", text)
        self.assertIn("run_outside_git_env python3 scripts/blueprint_lean_sync.py", text)
        self.assertIn("run_outside_git_env sh -c 'cd blueprint && leanblueprint web'", text)

        unwrapped_tool_command = re.compile(r"^\s*(lake|python3|leanblueprint)\b", re.MULTILINE)
        self.assertIsNone(unwrapped_tool_command.search(text))

    def test_checked_push_runs_gate_before_receive_transport(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_directory:
            repo, remote, hook_log, receive_marker = self.new_push_repo(
                Path(temporary_directory)
            )
            first_head = self.git(repo, "rev-parse", "HEAD").stdout.strip()

            result = self.run_checked_push(repo, hook_log, receive_marker)

            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(
                hook_log.read_text(encoding="utf-8").splitlines(),
                [
                    "preflight|refs/heads/main|"
                    f"{first_head}|refs/heads/main|{'0' * 40}",
                    "transport-skip",
                ],
            )
            self.assertEqual(
                self.git(remote, "rev-parse", "refs/heads/main").stdout.strip(),
                first_head,
            )

            receive_marker.unlink()
            hook_log.write_text("", encoding="utf-8")
            (repo / "payload").write_text("second\n", encoding="utf-8")
            self.git(repo, "commit", "--quiet", "-am", "second")
            second_head = self.git(repo, "rev-parse", "HEAD").stdout.strip()

            result = self.run_checked_push(repo, hook_log, receive_marker)

            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(
                hook_log.read_text(encoding="utf-8").splitlines(),
                [
                    "preflight|refs/heads/main|"
                    f"{second_head}|refs/heads/main|{first_head}",
                    "transport-skip",
                ],
            )

    def test_checked_push_gate_failure_never_starts_receive_transport(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_directory:
            repo, remote, hook_log, receive_marker = self.new_push_repo(
                Path(temporary_directory)
            )

            result = self.run_checked_push(
                repo,
                hook_log,
                receive_marker,
                fail_gate=True,
            )

            self.assertEqual(result.returncode, 23, result.stdout + result.stderr)
            self.assertFalse(receive_marker.exists())
            remote_ref = subprocess.run(
                ["git", "rev-parse", "--verify", "refs/heads/main"],
                cwd=remote,
                check=False,
                capture_output=True,
                text=True,
            )
            self.assertNotEqual(remote_ref.returncode, 0)
            self.assertEqual(len(hook_log.read_text(encoding="utf-8").splitlines()), 1)

    def test_repository_publishers_use_checked_push(self) -> None:
        sources = {
            name: (REPO_ROOT / path).read_text(encoding="utf-8")
            for name, path in {
                "pr_open.py": "local/bin/pr_open.py",
                "github-sync.sh": "local/bin/github-sync.sh",
                "autofix.sh": "local/bin/autofix.sh",
            }.items()
        }
        for name, source in sources.items():
            with self.subTest(name=name):
                self.assertIn("checked-push.sh", source)
        self.assertNotIn('git(repo_root, "push", "github"', sources["pr_open.py"])
        self.assertNotIn('git push github "refs/heads/$ref', sources["github-sync.sh"])
        self.assertNotIn('git -C "$ROOT" push github', sources["autofix.sh"])


if __name__ == "__main__":
    unittest.main()
