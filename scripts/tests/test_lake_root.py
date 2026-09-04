#!/usr/bin/env python3
"""Regression tests for external per-worktree Lake directories."""

from __future__ import annotations

import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "local" / "bin"))
import pr_merge  # noqa: E402

HELPER = REPO_ROOT / "local" / "bin" / "lake-root.sh"
WARMER = REPO_ROOT / "local" / "bin" / "warm-worktree.sh"
HOUSEKEEPING = REPO_ROOT / "local" / "bin" / "housekeeping.sh"


def run(argv: list[str | Path], *, env: dict[str, str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [str(item) for item in argv], cwd=REPO_ROOT, env=env,
        text=True, capture_output=True, check=False,
    )


def git(repo: Path, *args: str) -> None:
    result = subprocess.run(
        ["git", *args], cwd=repo, text=True, capture_output=True, check=False,
    )
    if result.returncode != 0:
        raise AssertionError(result.stderr)


class LakeRootTests(unittest.TestCase):
    def setUp(self) -> None:
        holder = tempfile.TemporaryDirectory()
        self.addCleanup(holder.cleanup)
        self.tmp = Path(holder.name)
        self.lake_root = self.tmp / "external-lake"
        self.env = dict(os.environ, MIPSTARRE_LAKE_ROOT=str(self.lake_root))

    def make_repo(self, name: str, branch: str) -> Path:
        repo = self.tmp / name
        repo.mkdir()
        git(repo, "init", "-q")
        git(repo, "symbolic-ref", "HEAD", f"refs/heads/{branch}")
        git(repo, "-c", "user.name=Test", "-c", "user.email=test@example.invalid",
            "commit", "-q", "--allow-empty", "-m", "seed")
        return repo

    def test_prepare_places_lake_by_full_branch_and_is_idempotent(self) -> None:
        repo = self.make_repo("worktree", "codex/issue-test")
        target = self.lake_root / "codex" / "issue-test"
        first = run([HELPER, "prepare", repo], env=self.env)
        second = run([HELPER, "prepare", repo, "--check"], env=self.env)
        self.assertEqual(first.returncode, 0, first.stderr)
        self.assertEqual(second.returncode, 0, second.stderr)
        self.assertTrue((repo / ".lake").is_symlink())
        self.assertEqual(os.readlink(repo / ".lake"), str(target))
        self.assertTrue(target.is_dir())

    def test_prepare_preserves_populated_lake_and_conflicting_link(self) -> None:
        populated = self.make_repo("populated", "issue-populated")
        (populated / ".lake").mkdir()
        (populated / ".lake" / "keep").write_text("build", encoding="utf-8")
        result = run([HELPER, "prepare", populated], env=self.env)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual((populated / ".lake" / "keep").read_text(), "build")

        linked = self.make_repo("linked", "issue-linked")
        other = self.tmp / "other-lake"
        other.mkdir()
        (linked / ".lake").symlink_to(other)
        result = run([HELPER, "prepare", linked], env=self.env)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(os.readlink(linked / ".lake"), str(other))

    def test_warmer_honors_lake_root_without_fetching_or_building(self) -> None:
        repo = self.make_repo("warm", "issue-warm")
        for name in ("lean-toolchain", "lake-manifest.json", "lakefile.toml"):
            (repo / name).write_text(name, encoding="utf-8")
        fake_bin = self.tmp / "bin"
        fake_bin.mkdir()
        fake_lake = fake_bin / "lake"
        fake_lake.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
        fake_lake.chmod(0o755)
        env = dict(self.env, PATH=f"{fake_bin}:{self.env['PATH']}",
                   MIPSTARRE_CACHE_ROOT=str(self.tmp / "cache"))
        result = run(
            [WARMER, repo, "--force-cold", "--skip-packages", "--no-build"], env=env,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(os.readlink(repo / ".lake"),
                         str(self.lake_root / "issue-warm"))

    def test_cleanup_refuses_active_branch_then_removes_retired_tree(self) -> None:
        repo = self.make_repo("cleanup-owner", "main")
        worktree = self.tmp / "cleanup-worktree"
        git(repo, "branch", "issue-cleanup")
        git(repo, "worktree", "add", "-q", str(worktree), "issue-cleanup")
        self.assertEqual(run([HELPER, "prepare", worktree], env=self.env).returncode, 0)
        target = self.lake_root / "issue-cleanup"
        (target / "artifact").write_text("generated", encoding="utf-8")
        active = run([HELPER, "cleanup", repo, "issue-cleanup"], env=self.env)
        self.assertNotEqual(active.returncode, 0)
        self.assertTrue(target.is_dir())
        git(repo, "worktree", "remove", "--force", str(worktree))
        retired = run([HELPER, "cleanup", repo, "issue-cleanup"], env=self.env)
        self.assertEqual(retired.returncode, 0, retired.stderr)
        self.assertFalse(target.exists())

    def test_merge_cleanup_calls_housekeeping_after_worktree_removal(self) -> None:
        listing = "worktree /tmp/retired\nbranch refs/heads/issue-retired\n"
        completed = subprocess.CompletedProcess([], 0, "", "removed\n")
        with mock.patch.object(pr_merge, "git", return_value=listing), \
                mock.patch.object(pr_merge, "git_ok", side_effect=[True, True]), \
                mock.patch.object(pr_merge.subprocess, "run", return_value=completed) as cleanup:
            with mock.patch.dict(os.environ, self.env):
                pr_merge.remove_branch_and_worktree(REPO_ROOT, "issue-retired")
        cleanup.assert_called_once_with(
            [str(HOUSEKEEPING), "lake-cleanup", "issue-retired"], cwd=str(REPO_ROOT),
            text=True, capture_output=True, check=False,
        )


if __name__ == "__main__":
    unittest.main()
