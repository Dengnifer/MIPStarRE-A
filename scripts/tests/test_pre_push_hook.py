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
  if [ -n "${MIPSTARRE_EXPECTED_PUSH_TUPLE:-}" ]; then
    if IFS= read -r actual_tuple; then
      if IFS= read -r extra_tuple; then
        exit 94
      fi
      printf 'transport-advertised|%s\\n' "$actual_tuple" >> "$HOOK_LOG"
      [ "$actual_tuple" = "$MIPSTARRE_EXPECTED_PUSH_TUPLE" ] || exit 95
    else
      printf 'transport-noop\\n' >> "$HOOK_LOG"
    fi
  else
    printf 'transport-bypass\\n' >> "$HOOK_LOG"
  fi
  exit 0
fi
[ ! -e "$RECEIVE_MARKER" ] || exit 92
read local_ref local_sha remote_ref remote_sha
printf 'preflight|%s|%s|%s|%s\\n' \
  "$local_ref" "$local_sha" "$remote_ref" "$remote_sha" >> "$HOOK_LOG"
if [ -n "${EXPECTED_PAYLOAD:-}" ]; then
  actual_payload="$(cat payload)"
  printf 'checked-payload|%s\\n' "$actual_payload" >> "$HOOK_LOG"
  [ "$actual_payload" = "$EXPECTED_PAYLOAD" ] || exit 96
fi
[ -z "${MOVE_LOCAL_REF_TO:-}" ] || git update-ref "$local_ref" "$MOVE_LOCAL_REF_TO"
[ -z "${MOVE_REMOTE_TO:-}" ] || \
  git --git-dir="$PUSH_REMOTE" update-ref "$remote_ref" "$MOVE_REMOTE_TO"
[ "${FAIL_GATE:-}" != "1" ] || exit 23
""",
            encoding="utf-8",
        )
        hook.chmod(0o755)
        self.git(repo, "add", ".githooks/pre-push")
        self.git(repo, "commit", "--quiet", "-m", "install pre-push hook")

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
        bypass: bool = False,
        move_local_ref_to: str | None = None,
        move_remote_to: str | None = None,
        push_remote: Path | None = None,
        expected_payload: str | None = None,
        local_branch: str = "main",
        remote_branch: str | None = None,
    ) -> subprocess.CompletedProcess[str]:
        env = dict(
            os.environ,
            HOOK_LOG=str(hook_log),
            RECEIVE_MARKER=str(receive_marker),
        )
        env.pop("MIPSTARRE_SKIP_HOOKS", None)
        env.pop("MIPSTARRE_EXPECTED_PUSH_TUPLE", None)
        if fail_gate:
            env["FAIL_GATE"] = "1"
        if bypass:
            env["MIPSTARRE_SKIP_HOOKS"] = "1"
        if move_local_ref_to is not None:
            env["MOVE_LOCAL_REF_TO"] = move_local_ref_to
        if move_remote_to is not None:
            env["MOVE_REMOTE_TO"] = move_remote_to
        if push_remote is not None:
            env["PUSH_REMOTE"] = str(push_remote)
        if expected_payload is not None:
            env["EXPECTED_PAYLOAD"] = expected_payload
        remote_branch = remote_branch or local_branch
        return subprocess.run(
            [
                str(CHECKED_PUSH),
                "--repo-root",
                str(repo),
                "test",
                f"refs/heads/{local_branch}:refs/heads/{remote_branch}",
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
                    "transport-advertised|"
                    f"{first_head} {first_head} refs/heads/main {'0' * 40}",
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
                    "transport-advertised|"
                    f"{second_head} {second_head} refs/heads/main {first_head}",
                ],
            )

            receive_marker.unlink()
            hook_log.write_text("", encoding="utf-8")

            no_op = self.run_checked_push(repo, hook_log, receive_marker)

            self.assertEqual(no_op.returncode, 0, no_op.stdout + no_op.stderr)
            self.assertEqual(
                hook_log.read_text(encoding="utf-8").splitlines(),
                [
                    "preflight|refs/heads/main|"
                    f"{second_head}|refs/heads/main|{second_head}",
                    "transport-noop",
                ],
            )

    def test_checked_push_validates_local_refs_registered_worktree(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_directory:
            root = Path(temporary_directory)
            repo, remote, hook_log, receive_marker = self.new_push_repo(root)
            self.git(repo, "branch", "publish")
            publish_worktree = root / "publish"
            self.git(repo, "worktree", "add", "--quiet", str(publish_worktree), "publish")

            (publish_worktree / "payload").write_text("publish\n", encoding="utf-8")
            self.git(publish_worktree, "commit", "--quiet", "-am", "publish bytes")
            publish_head = self.git(publish_worktree, "rev-parse", "HEAD").stdout.strip()

            (repo / "payload").write_text("main\n", encoding="utf-8")
            self.git(repo, "commit", "--quiet", "-am", "main bytes")

            result = self.run_checked_push(
                repo,
                hook_log,
                receive_marker,
                expected_payload="publish",
                local_branch="publish",
            )

            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(
                hook_log.read_text(encoding="utf-8").splitlines(),
                [
                    "preflight|refs/heads/publish|"
                    f"{publish_head}|refs/heads/publish|{'0' * 40}",
                    "checked-payload|publish",
                    "transport-advertised|"
                    f"{publish_head} {publish_head} refs/heads/publish {'0' * 40}",
                ],
            )
            self.assertEqual(
                self.git(remote, "rev-parse", "refs/heads/publish").stdout.strip(),
                publish_head,
            )

    def test_checked_push_rejects_dirty_ref_worktree(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_directory:
            repo, _, hook_log, receive_marker = self.new_push_repo(
                Path(temporary_directory)
            )
            (repo / "payload").write_text("dirty\n", encoding="utf-8")

            result = self.run_checked_push(repo, hook_log, receive_marker)

            self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
            self.assertIn("working tree", result.stderr)
            self.assertIn("differs from refs/heads/main", result.stderr)
            self.assertFalse(receive_marker.exists())
            self.assertFalse(hook_log.exists())

    def test_checked_push_rejects_ref_without_worktree(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_directory:
            repo, _, hook_log, receive_marker = self.new_push_repo(
                Path(temporary_directory)
            )
            self.git(repo, "branch", "unowned")

            result = self.run_checked_push(
                repo,
                hook_log,
                receive_marker,
                local_branch="unowned",
            )

            self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
            self.assertIn("not checked out in a registered worktree", result.stderr)
            self.assertFalse(receive_marker.exists())
            self.assertFalse(hook_log.exists())

    def test_checked_push_rejects_local_ref_movement_during_gate(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_directory:
            repo, remote, hook_log, receive_marker = self.new_push_repo(
                Path(temporary_directory)
            )
            validated_head = self.git(repo, "rev-parse", "HEAD").stdout.strip()
            (repo / "payload").write_text("moved\n", encoding="utf-8")
            self.git(repo, "commit", "--quiet", "-am", "moved")
            moved_head = self.git(repo, "rev-parse", "HEAD").stdout.strip()
            self.git(repo, "update-ref", "refs/heads/main", validated_head, moved_head)
            self.git(repo, "restore", "--source=HEAD", "--staged", "--worktree", ".")

            result = self.run_checked_push(
                repo,
                hook_log,
                receive_marker,
                move_local_ref_to=moved_head,
            )

            self.assertNotEqual(result.returncode, 0)
            self.assertIn("changed during preflight", result.stderr)
            self.assertFalse(receive_marker.exists())
            remote_ref = subprocess.run(
                ["git", "rev-parse", "--verify", "refs/heads/main"],
                cwd=remote,
                check=False,
                capture_output=True,
                text=True,
            )
            self.assertNotEqual(remote_ref.returncode, 0)

    def test_checked_push_rejects_remote_ref_movement_during_gate(self) -> None:
        for native_hook in ("missing", "stale"):
            with self.subTest(native_hook=native_hook), tempfile.TemporaryDirectory() as temp:
                repo, remote, hook_log, receive_marker = self.new_push_repo(Path(temp))
                initial = self.run_checked_push(repo, hook_log, receive_marker)
                self.assertEqual(initial.returncode, 0, initial.stdout + initial.stderr)
                first_head = self.git(repo, "rev-parse", "HEAD").stdout.strip()

                receive_marker.unlink()
                hook_log.write_text("", encoding="utf-8")
                (repo / "payload").write_text("middle\n", encoding="utf-8")
                self.git(repo, "commit", "--quiet", "-am", "middle")
                middle_head = self.git(repo, "rev-parse", "HEAD").stdout.strip()
                self.git(remote, "fetch", "--quiet", str(repo), middle_head)
                (repo / "payload").write_text("target\n", encoding="utf-8")
                self.git(repo, "commit", "--quiet", "-am", "target")
                target_head = self.git(repo, "rev-parse", "HEAD").stdout.strip()

                hooks_path = Path(temp) / f"{native_hook}-hooks"
                if native_hook == "stale":
                    hooks_path.mkdir()
                    stale_hook = hooks_path / "pre-push"
                    stale_hook.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
                    stale_hook.chmod(0o755)
                self.git(repo, "config", "core.hooksPath", str(hooks_path))

                result = self.run_checked_push(
                    repo,
                    hook_log,
                    receive_marker,
                    move_remote_to=middle_head,
                    push_remote=remote,
                )

                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(
                    self.git(remote, "rev-parse", "refs/heads/main").stdout.strip(),
                    middle_head,
                )
                self.assertEqual(
                    hook_log.read_text(encoding="utf-8").splitlines(),
                    [
                        "preflight|refs/heads/main|"
                        f"{target_head}|refs/heads/main|{first_head}",
                    ],
                )

    def test_checked_push_preserves_emergency_bypass(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_directory:
            repo, remote, hook_log, receive_marker = self.new_push_repo(
                Path(temporary_directory)
            )
            head = self.git(repo, "rev-parse", "HEAD").stdout.strip()

            result = self.run_checked_push(
                repo,
                hook_log,
                receive_marker,
                bypass=True,
            )

            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(
                hook_log.read_text(encoding="utf-8").splitlines(),
                ["transport-bypass"],
            )
            self.assertEqual(
                self.git(remote, "rev-parse", "refs/heads/main").stdout.strip(),
                head,
            )

    def test_pre_push_confirmation_requires_the_exact_tuple(self) -> None:
        expected = f"{'1' * 40} {'1' * 40} refs/heads/main {'0' * 40}"
        env = dict(
            os.environ,
            MIPSTARRE_SKIP_HOOKS="1",
            MIPSTARRE_EXPECTED_PUSH_TUPLE=expected,
        )
        accepted = subprocess.run(
            [str(PRE_PUSH), "test", "unused"],
            cwd=REPO_ROOT,
            env=env,
            input=f"{expected}\n",
            check=False,
            capture_output=True,
            text=True,
        )
        rejected = subprocess.run(
            [str(PRE_PUSH), "test", "unused"],
            cwd=REPO_ROOT,
            env=env,
            input=f"{expected[:-1]}2\n",
            check=False,
            capture_output=True,
            text=True,
        )
        no_op = subprocess.run(
            [str(PRE_PUSH), "test", "unused"],
            cwd=REPO_ROOT,
            env=env,
            input="",
            check=False,
            capture_output=True,
            text=True,
        )

        self.assertEqual(accepted.returncode, 0, accepted.stdout + accepted.stderr)
        self.assertNotEqual(rejected.returncode, 0)
        self.assertIn("changed after preflight", rejected.stderr)
        self.assertEqual(no_op.returncode, 0, no_op.stdout + no_op.stderr)
        self.assertIn("already current", no_op.stdout)

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
                "install_git_hooks.sh": "scripts/install_git_hooks.sh",
            }.items()
        }
        for name, source in sources.items():
            with self.subTest(name=name):
                self.assertIn("checked-push.sh", source)
        self.assertNotIn('git(repo_root, "push", "github"', sources["pr_open.py"])
        self.assertNotIn('git push github "refs/heads/$ref', sources["github-sync.sh"])
        self.assertNotIn('git -C "$ROOT" push github', sources["autofix.sh"])
        self.assertIn(
            "MIPSTARRE_HOOK_FULL=1 when invoking local/bin/checked-push.sh",
            sources["install_git_hooks.sh"],
        )


if __name__ == "__main__":
    unittest.main()
