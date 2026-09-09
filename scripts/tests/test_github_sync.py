"""Offline publication regressions using an actual local bare Git remote."""

from pathlib import Path
import os
import shutil
import subprocess
import tempfile
import unittest


SOURCE = Path(__file__).resolve().parents[2] / "local/bin/github-sync.sh"


class GithubSyncTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.directory = Path(self.temporary.name)
        self.repo = self.directory / "repo"
        self.remote = self.directory / "remote.git"
        self.repo.mkdir()
        self.log = self.directory / "pushes"
        self.env = dict(os.environ, SYNC_TEST_LOG=str(self.log))
        subprocess.run(["git", "init", "--bare", str(self.remote)], check=True,
                       capture_output=True)
        self.git("init", "-b", "main")
        self.git("config", "user.name", "Sync regression")
        self.git("config", "user.email", "sync-test@example.invalid")
        self.git("config", "commit.gpgsign", "false")
        self.git("config", "core.hooksPath", str(self.repo / ".git/hooks"))
        local = self.repo / "local/bin"
        local.mkdir(parents=True)
        shutil.copyfile(SOURCE, local / "github-sync.sh")
        (local / "checked-push.sh").write_text(
            '#!/usr/bin/env bash\nset -euo pipefail\n'
            'printf "%s\\n" "$4" >> "$SYNC_TEST_LOG"\n'
            '[ "${SYNC_TEST_FAIL_PUSH:-0}" != 1 ] || exit 23\n'
            '[ "$(wc -l < "$SYNC_TEST_LOG")" -ne "${SYNC_TEST_FAIL_PUSH_AT:-0}" ] || exit 23\n'
            '[ -z "$(git -C "$2" status --porcelain)" ] || exit 24\n'
            'git -C "$2" push "$3" "$4"\n'
        )
        (local / "checked-push.sh").chmod(0o755)
        (local / "gh_common.py").write_text(
            'import os, pathlib, sys\n'
            'if os.environ.get("SYNC_TEST_FAIL_SNAPSHOT") == "1": sys.exit(7)\n'
            'assert sys.argv[1:3] == ["snapshot", "--out-dir"]\n'
            'path = pathlib.Path(sys.argv[3]) / "metadata.json"\n'
            'path.write_text("new snapshot\\n")\n'
        )
        snapshot = self.repo / "results/telemetry/github-snapshot"
        snapshot.mkdir(parents=True)
        (snapshot / "metadata.json").write_text("old snapshot\n")
        (snapshot.parent / "builds.jsonl").write_text("")
        self.git("add", ".")
        self.git("commit", "-m", "Initial state")
        self.git("remote", "add", "github", str(self.remote))
        self.git("push", "github", "refs/heads/main:refs/heads/main")
        self.initial = self.git("rev-parse", "main")
        self.git("branch", "issue-1-example")
        shim = self.directory / "bin"
        shim.mkdir()
        (shim / "sleep").write_text("#!/bin/sh\nexit 0\n")
        (shim / "sleep").chmod(0o755)
        self.env["PATH"] = str(shim) + os.pathsep + self.env["PATH"]

    def git(self, *args):
        return subprocess.run(["git", "-C", str(self.repo), *args], check=True,
                              capture_output=True, text=True).stdout.strip()

    def remote_ref(self, ref):
        return subprocess.run(["git", "--git-dir", str(self.remote), "rev-parse", ref],
                              check=True, capture_output=True, text=True).stdout.strip()

    def sync(self, *refs, **settings):
        return subprocess.run(["bash", str(self.repo / "local/bin/github-sync.sh"), *refs],
                              cwd=self.repo, env=dict(self.env, **settings),
                              capture_output=True, text=True, timeout=30)

    def test_main_publishes_snapshot_commit_and_leaves_clean_aligned(self):
        result = self.sync("main")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertNotEqual(self.git("rev-parse", "main"), self.initial)
        self.assertEqual(self.git("rev-parse", "main"), self.remote_ref("main"))
        self.assertEqual(self.git("status", "--porcelain"), "")
        self.assertEqual(self.log.read_text().splitlines(),
                         ["refs/heads/main:refs/heads/main"] * 2)

    def test_default_is_main(self):
        result = self.sync()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(self.git("rev-parse", "main"), self.remote_ref("main"))

    def test_branch_only_never_publishes_main(self):
        result = self.sync("issue-1-example")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(self.remote_ref("main"), self.initial)
        self.assertEqual(self.remote_ref("issue-1-example"), self.git("rev-parse", "issue-1-example"))
        self.assertEqual(self.log.read_text().splitlines(),
                         ["refs/heads/issue-1-example:refs/heads/issue-1-example"])
        self.assertEqual(self.git("status", "--porcelain"), "")

    def test_failed_publication_remains_failure(self):
        result = self.sync("main", SYNC_TEST_FAIL_PUSH="1")
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(self.remote_ref("main"), self.initial)
        self.assertEqual(len(self.log.read_text().splitlines()), 5)

    def test_final_snapshot_publication_failure_remains_failure(self):
        result = self.sync("main", SYNC_TEST_FAIL_PUSH_AT="2")
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(self.remote_ref("main"), self.initial)
        self.assertNotEqual(self.git("rev-parse", "main"), self.initial)
        self.assertEqual(self.git("status", "--porcelain"), "")
        self.assertIn("snapshot commit remains local", result.stderr)

    def test_missing_ref_failure_survives_successful_main_publication(self):
        result = self.sync("push", "main")
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(self.git("rev-parse", "main"), self.remote_ref("main"))
        self.assertEqual(self.log.read_text().splitlines(),
                         ["refs/heads/main:refs/heads/main"] * 2)

    def test_snapshot_commit_failure_is_not_reported_as_success(self):
        hook = self.repo / ".git/hooks/pre-commit"
        hook.write_text("#!/bin/sh\nexit 9\n")
        hook.chmod(0o755)
        result = self.sync("main")
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(self.remote_ref("main"), self.initial)
        self.assertIn("could not commit the snapshot", result.stderr)

    def test_snapshot_read_failure_is_warned_but_does_not_mask_push_failure(self):
        success = self.sync("main", SYNC_TEST_FAIL_SNAPSHOT="1")
        self.assertEqual(success.returncode, 0, success.stdout + success.stderr)
        self.assertIn("record snapshot failed", success.stderr)
        failure = self.sync("main", SYNC_TEST_FAIL_SNAPSHOT="1", SYNC_TEST_FAIL_PUSH="1")
        self.assertNotEqual(failure.returncode, 0)

    def test_unknown_ref_is_a_failure_without_implicit_main_publication(self):
        result = self.sync("push")
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(self.remote_ref("main"), self.initial)
        self.assertFalse(self.log.exists())


if __name__ == "__main__":
    unittest.main()
