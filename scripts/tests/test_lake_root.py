#!/usr/bin/env python3
"""Regression tests for external per-worktree Lake directories."""

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
HOUSEKEEPING = HELPER.parent / "housekeeping.sh"

def run(argv: list[str | Path], *, env: dict[str, str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run([str(item) for item in argv], cwd=REPO_ROOT, env=env,
                          text=True, capture_output=True)

def git(repo: Path, *args: str) -> None:
    subprocess.run(["git", *args], cwd=repo, text=True, capture_output=True, check=True)

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
        git(repo, "init", "-q", "-b", branch)
        git(repo, "-c", "user.name=Test", "-c", "user.email=test@example.invalid",
            "commit", "-q", "--allow-empty", "-m", "seed")
        return repo

    def assert_rejected(self, argv, message, env=None) -> None:
        result = run(argv, env=env or self.env)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn(message, result.stderr)
    def test_prepare_places_lake_by_branch_and_is_idempotent(self) -> None:
        repo = self.make_repo("worktree", "issue-test")
        target = self.lake_root / "issue-test"
        run([HELPER, "prepare", repo], env=self.env)
        second = run([HELPER, "prepare", repo, "--check"], env=self.env)
        self.assertEqual(second.returncode, 0, second.stderr)
        self.assertEqual(os.readlink(repo / ".lake"), str(target))
        self.assertTrue(target.is_dir())

    def test_prepare_preserves_populated_lake_and_conflicting_link(self) -> None:
        populated = self.make_repo("populated", "issue-populated")
        (populated / ".lake").mkdir()
        (populated / ".lake" / "keep").write_text("build", encoding="utf-8")
        self.assert_rejected([HELPER, "prepare", populated], "populated")
        self.assertEqual((populated / ".lake" / "keep").read_text(), "build")
        linked = self.make_repo("linked", "issue-linked")
        other = self.tmp / "other-lake"
        other.mkdir()
        (linked / ".lake").symlink_to(other)
        self.assert_rejected([HELPER, "prepare", linked], "points to")
        self.assertEqual(os.readlink(linked / ".lake"), str(other))

    def test_warmer_honors_lake_root_without_fetching_or_building(self) -> None:
        repo = self.make_repo("warm", "issue-warm")
        for name in ("lean-toolchain", "lake-manifest.json", "lakefile.toml"):
            (repo / name).write_text(name, encoding="utf-8")
        fake_lake = self.tmp / "bin" / "lake"
        fake_lake.parent.mkdir()
        fake_lake.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
        fake_lake.chmod(0o755)
        env = dict(self.env, PATH=f"{fake_lake.parent}:{self.env['PATH']}",
                   MIPSTARRE_CACHE_ROOT=str(self.tmp / "cache"))
        result = run([WARMER, repo, "--force-cold", "--skip-packages", "--no-build"], env=env)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(os.readlink(repo / ".lake"), str(self.lake_root / "issue-warm"))
        for script in (WARMER, HOUSEKEEPING):
            help_result = run([script, "--help"], env=self.env)
            self.assertEqual(help_result.returncode, 0, help_result.stderr)
            self.assertIn("MIPSTARRE_LAKE_ROOT", help_result.stdout)

    def test_cleanup_refuses_active_and_detached_targets_then_removes_retired(self) -> None:
        repo = self.make_repo("cleanup-owner", "main")
        worktree = self.tmp / "cleanup-worktree"
        git(repo, "branch", "issue-cleanup")
        git(repo, "worktree", "add", "-q", str(worktree), "issue-cleanup")
        self.assertEqual(run([HELPER, "prepare", worktree], env=self.env).returncode, 0)
        target = self.lake_root / "issue-cleanup"
        (target / "artifact").write_text("generated", encoding="utf-8")
        self.assert_rejected([HELPER, "cleanup", repo, "issue-cleanup"], "target already used")
        git(worktree, "switch", "--detach", "--quiet")
        detached = run([HELPER, "cleanup", repo, "issue-cleanup"], env=self.env)
        self.assertIn("already used", detached.stderr)
        git(worktree, "switch", "--quiet", "issue-cleanup")
        (worktree / ".lake").unlink()
        git(repo, "worktree", "remove", "--force", str(worktree))
        retired = run([HELPER, "cleanup", repo, "issue-cleanup"], env=self.env)
        self.assertEqual(retired.returncode, 0, retired.stderr)
        self.assertFalse(target.exists())

    def test_cleanup_rejects_roots_resolving_to_filesystem_root(self) -> None:
        repo = self.make_repo("root-guard", "main")
        alias = self.tmp / "root-alias"
        alias.symlink_to("/", target_is_directory=True)
        for root in ("/tmp/..", str(alias)):
            env = dict(self.env, MIPSTARRE_LAKE_ROOT=root)
            self.assert_rejected([HELPER, "cleanup", repo, "root-guard"],
                                 "must not resolve to /", env)

    def test_branch_target_is_one_component_and_not_a_symlink(self) -> None:
        repo = self.make_repo("branch-guard", "codex/issue-escape")
        self.assert_rejected([HELPER, "prepare", repo], "one path component")
        self.lake_root.mkdir()
        for branch in ("../issue-escape", "codex/issue-escape"):
            self.assert_rejected([HELPER, "cleanup", repo, branch], "one path component")
        outside = self.tmp / "outside"
        outside.mkdir()
        (outside / "keep").write_text("build", encoding="utf-8")
        (self.lake_root / "issue-link").symlink_to(outside, target_is_directory=True)
        self.assert_rejected([HELPER, "cleanup", repo, "issue-link"], "must not be a symlink")
        self.assertTrue((outside / "keep").is_file())

    def test_prepare_and_cleanup_reject_shared_cache_overlap(self) -> None:
        repo = self.make_repo("shared-cache-guard", "packages")
        cache = self.tmp / "cache"
        cases = ((cache / "hot-main" / "repo", cache),
                 (self.lake_root, self.lake_root / "packages"), (cache, cache))
        for root, cache_root in cases:
            env = dict(self.env, MIPSTARRE_CACHE_ROOT=str(cache_root),
                       MIPSTARRE_LAKE_ROOT=str(root))
            self.assert_rejected([HELPER, "prepare", repo], "overlaps shared cache", env)
            root.mkdir(parents=True, exist_ok=True)
            self.assert_rejected([HELPER, "cleanup", repo, "packages"],
                                 "overlaps shared cache", env)

    def test_prepare_rejects_lake_root_inside_another_checkout(self) -> None:
        repo = self.make_repo("root-in-checkout", "main")
        worktree = self.tmp / "linked-checkout"
        git(repo, "branch", "issue-linked")
        git(repo, "worktree", "add", "-q", str(worktree), "issue-linked")
        lake_root = repo / "build-products"
        lake_root.mkdir()
        env = dict(self.env, MIPSTARRE_LAKE_ROOT=str(lake_root))
        for argv in ([HELPER, "prepare", worktree],
                     [HELPER, "cleanup", repo, "issue-linked"]):
            self.assert_rejected(argv, "overlaps registered worktree", env)

    def test_merge_cleanup_runs_when_worktree_is_already_gone(self) -> None:
        completed = subprocess.CompletedProcess([], 0, "", "removed\n")
        with mock.patch.object(pr_merge, "git", return_value=""), \
             mock.patch.object(pr_merge, "git_ok", return_value=True), \
             mock.patch.object(pr_merge.subprocess, "run", return_value=completed) as cleanup, \
             mock.patch.object(pr_merge.sys, "stderr") as stderr, \
             mock.patch.dict(os.environ, self.env):
            pr_merge.remove_branch_and_worktree(REPO_ROOT, "issue-retired")
        stderr.write.assert_any_call("warning: no worktree found for issue-retired; "
                                     "attempting .lake cleanup\n")
        cleanup.assert_called_once_with(
            [str(HOUSEKEEPING), "lake-cleanup", "issue-retired"], cwd=str(REPO_ROOT),
            text=True, capture_output=True, check=False,
        )

    def test_merge_cleanup_warns_when_lake_root_is_unset(self) -> None:
        with mock.patch.object(pr_merge, "git", return_value=""), \
             mock.patch.object(pr_merge, "git_ok", return_value=True), \
             mock.patch.object(pr_merge.subprocess, "run") as cleanup, \
             mock.patch.object(pr_merge.sys, "stderr") as stderr, \
             mock.patch.dict(os.environ, {"MIPSTARRE_LAKE_ROOT": ""}):
            pr_merge.remove_branch_and_worktree(REPO_ROOT, "issue-retired")
        cleanup.assert_not_called()
        stderr.write.assert_any_call("warning: MIPSTARRE_LAKE_ROOT is unset; cannot clean "
                                     ".lake for issue-retired\n")
