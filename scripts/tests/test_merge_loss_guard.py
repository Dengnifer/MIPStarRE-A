"""Regression tests for the merge-time silent-loss guard."""

from __future__ import annotations

import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


REPO_ROOT = Path(__file__).resolve().parents[2]
GUARD = REPO_ROOT / "local" / "bin" / "merge_loss_guard.py"
PRE_COMMIT = REPO_ROOT / ".githooks" / "pre-commit"


class MergeLossGuardTests(unittest.TestCase):
    def git(self, repo: Path, *args: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            ["git", *args],
            cwd=repo,
            check=True,
            capture_output=True,
            text=True,
        )

    def run_guard(
        self, repo: Path, *extra: str
    ) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [sys.executable, str(GUARD), "--repo", str(repo), *extra],
            check=False,
            capture_output=True,
            text=True,
        )

    def run_pre_commit(self, repo: Path) -> subprocess.CompletedProcess[str]:
        env = os.environ.copy()
        env["MIPSTARRE_SKIP_HOOKS"] = "1"
        return subprocess.run(
            [str(PRE_COMMIT)],
            cwd=repo,
            env=env,
            check=False,
            capture_output=True,
            text=True,
        )

    def write(self, repo: Path, path: str, content: str) -> None:
        target = repo / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(content, encoding="utf-8")

    def new_diverged_repo(self) -> Path:
        temporary_directory = tempfile.TemporaryDirectory()
        self.addCleanup(temporary_directory.cleanup)
        repo = Path(temporary_directory.name)
        self.git(repo, "init", "--quiet", "--initial-branch=branch")
        self.git(repo, "config", "user.email", "merge-guard@example.invalid")
        self.git(repo, "config", "user.name", "Merge Guard Test")

        self.write(repo, "incoming-only.txt", "base\n")
        self.write(repo, "second-incoming-only.txt", "base\n")
        self.write(repo, "combined.txt", "one\ntwo\nthree\n")
        self.write(repo, "branch-delete.txt", "delete me\n")
        self.git(repo, "add", ".")
        self.git(repo, "commit", "--quiet", "-m", "base")
        base = self.git(repo, "rev-parse", "HEAD").stdout.strip()

        self.write(repo, "combined.txt", "branch\ntwo\nthree\n")
        self.git(repo, "rm", "--quiet", "branch-delete.txt")
        self.git(repo, "commit", "--quiet", "-am", "branch work")

        self.git(repo, "switch", "--quiet", "--create", "incoming", base)
        self.write(repo, "incoming-only.txt", "incoming\n")
        self.write(repo, "second-incoming-only.txt", "incoming\n")
        self.write(repo, "combined.txt", "one\ntwo\nincoming\n")
        self.write(repo, "incoming new.txt", "new\n")
        self.git(repo, "add", ".")
        self.git(repo, "commit", "--quiet", "-m", "incoming work")
        self.git(repo, "switch", "--quiet", "branch")
        return repo

    def prepare_merge(self, repo: Path) -> None:
        self.git(repo, "merge", "--quiet", "--no-commit", "--no-ff", "incoming")

    def reset_merge_result_to_branch(self, repo: Path) -> None:
        self.git(repo, "restore", "--source=HEAD", "--staged", "--worktree", ".")

    def test_clean_combined_merge_passes_and_branch_deletion_is_preserved(self) -> None:
        repo = self.new_diverged_repo()
        self.prepare_merge(repo)

        result = self.run_guard(repo)

        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("merge-loss guard: ok", result.stdout)
        self.assertFalse((repo / "branch-delete.txt").exists())
        self.assertTrue((repo / "incoming new.txt").exists())

    def test_pending_whole_tree_ours_result_lists_deletions_and_reversions(self) -> None:
        repo = self.new_diverged_repo()
        self.prepare_merge(repo)
        self.reset_merge_result_to_branch(repo)

        result = self.run_guard(repo)

        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("DELETED  incoming new.txt", result.stdout)
        self.assertIn("REVERTED incoming-only.txt", result.stdout)
        self.assertIn("REVERTED second-incoming-only.txt", result.stdout)
        self.assertNotIn("combined.txt", result.stdout)
        self.assertNotIn("branch-delete.txt", result.stdout)

    def test_pre_commit_refuses_loss_before_blanket_hook_bypass(self) -> None:
        repo = self.new_diverged_repo()
        self.prepare_merge(repo)
        self.reset_merge_result_to_branch(repo)

        result = self.run_pre_commit(repo)

        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("checking the merge result for silent incoming loss", result.stdout)
        self.assertIn("DELETED  incoming new.txt", result.stdout)
        self.assertNotIn("hook skipped", result.stdout)

    def test_committed_whole_tree_ours_result_is_auditable(self) -> None:
        repo = self.new_diverged_repo()
        self.prepare_merge(repo)
        self.reset_merge_result_to_branch(repo)
        self.git(repo, "commit", "--quiet", "--no-verify", "-m", "bad merge")

        result = self.run_guard(repo, "--commit", "HEAD")

        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("DELETED  incoming new.txt", result.stdout)
        self.assertIn("REVERTED incoming-only.txt", result.stdout)
        self.assertIn("REVERTED second-incoming-only.txt", result.stdout)
        self.assertNotIn("combined.txt", result.stdout)

    def test_ordinary_commit_without_merge_head_is_ignored(self) -> None:
        repo = self.new_diverged_repo()

        result = self.run_guard(repo)

        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "")

    def test_criss_cross_history_with_multiple_merge_bases_passes(self) -> None:
        temporary_directory = tempfile.TemporaryDirectory()
        self.addCleanup(temporary_directory.cleanup)
        repo = Path(temporary_directory.name)
        self.git(repo, "init", "--quiet", "--initial-branch=branch")
        self.git(repo, "config", "user.email", "merge-guard@example.invalid")
        self.git(repo, "config", "user.name", "Merge Guard Test")
        self.write(repo, "base.txt", "base\n")
        self.git(repo, "add", ".")
        self.git(repo, "commit", "--quiet", "-m", "base")
        base = self.git(repo, "rev-parse", "HEAD").stdout.strip()

        self.write(repo, "left.txt", "left\n")
        self.git(repo, "add", ".")
        self.git(repo, "commit", "--quiet", "-m", "left")
        left = self.git(repo, "rev-parse", "HEAD").stdout.strip()
        self.git(repo, "switch", "--quiet", "--create", "incoming", base)
        self.write(repo, "right.txt", "right\n")
        self.git(repo, "add", ".")
        self.git(repo, "commit", "--quiet", "-m", "right")
        right = self.git(repo, "rev-parse", "HEAD").stdout.strip()

        self.git(repo, "switch", "--quiet", "branch")
        self.git(repo, "merge", "--quiet", "--no-edit", right)
        self.git(repo, "switch", "--quiet", "incoming")
        self.git(repo, "merge", "--quiet", "--no-edit", left)
        self.write(repo, "incoming-after.txt", "incoming after\n")
        self.git(repo, "add", ".")
        self.git(repo, "commit", "--quiet", "-m", "incoming after")
        self.git(repo, "switch", "--quiet", "branch")
        self.write(repo, "branch-after.txt", "branch after\n")
        self.git(repo, "add", ".")
        self.git(repo, "commit", "--quiet", "-m", "branch after")
        self.prepare_merge(repo)

        bases = self.git(repo, "merge-base", "--all", "HEAD", "MERGE_HEAD")
        result = self.run_guard(repo)

        self.assertEqual(len(bases.stdout.splitlines()), 2)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_explicit_ours_resolution_of_recorded_conflict_passes(self) -> None:
        temporary_directory = tempfile.TemporaryDirectory()
        self.addCleanup(temporary_directory.cleanup)
        repo = Path(temporary_directory.name)
        self.git(repo, "init", "--quiet", "--initial-branch=branch")
        self.git(repo, "config", "user.email", "merge-guard@example.invalid")
        self.git(repo, "config", "user.name", "Merge Guard Test")
        self.write(repo, "conflict.txt", "base\n")
        self.git(repo, "add", ".")
        self.git(repo, "commit", "--quiet", "-m", "base")
        base = self.git(repo, "rev-parse", "HEAD").stdout.strip()
        self.write(repo, "conflict.txt", "branch\n")
        self.git(repo, "commit", "--quiet", "-am", "branch")
        self.git(repo, "switch", "--quiet", "--create", "incoming", base)
        self.write(repo, "conflict.txt", "incoming\n")
        self.git(repo, "commit", "--quiet", "-am", "incoming")
        self.git(repo, "switch", "--quiet", "branch")
        merge = subprocess.run(
            ["git", "merge", "--no-commit", "--no-ff", "incoming"],
            cwd=repo,
            check=False,
            capture_output=True,
            text=True,
        )
        self.assertEqual(merge.returncode, 1)
        self.git(repo, "checkout", "--ours", "conflict.txt")
        self.git(repo, "add", "conflict.txt")

        result = self.run_guard(repo)

        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
