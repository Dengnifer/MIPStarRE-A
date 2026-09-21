#!/usr/bin/env python3
"""The duplicate-work guard wired into ``dispatch.sh`` (issue #576).

Every case runs ``dispatch.sh --dry-run`` against a synthetic repository with a
stub ``codex`` on PATH, so no agent, no model and no network is involved.
"""

from __future__ import annotations

import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
DISPATCH = REPO_ROOT / "local" / "bin" / "dispatch.sh"
LOCAL_BIN = DISPATCH.parent
sys.path.insert(0, str(LOCAL_BIN))

import dup_check  # noqa: E402

LEMMA = """\
import Mathlib

namespace PaperLib.Core

theorem settled_already (n : Nat) : n = n := rfl

end PaperLib.Core
"""


def git(cwd: Path, *args: str) -> None:
    subprocess.run(["git", "-C", str(cwd), *args], check=True,
                   capture_output=True, text=True)


class DispatchDupCheckTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        root = Path(self.tmp.name)
        self.repo = root / "repo"
        local_bin = self.repo / "local" / "bin"
        local_bin.mkdir(parents=True)
        (self.repo / "scripts").mkdir()
        for name in ("dispatch.sh", "telemetry.py", "account_router.py",
                     "model_policy.py", "dup_check.py"):
            shutil.copy2(LOCAL_BIN / name, local_bin / name)
        shutil.copy2(REPO_ROOT / "local" / "model-policy.json",
                     self.repo / "local" / "model-policy.json")
        for name in ("blueprint_lean_sync.py", "tex_utils.py", "lean_header_utils.py",
                     "dup_scan.py", "project_config.py"):
            source = REPO_ROOT / "scripts" / name
            if source.exists():
                shutil.copy2(source, self.repo / "scripts" / name)
        (self.repo / "AGENTS.md").write_text("# fixture\n")
        lean = self.repo / "PaperLib" / "Core" / "A.lean"
        lean.parent.mkdir(parents=True)
        lean.write_text(LEMMA)

        git(self.repo, "init", "-q", "-b", "main")
        git(self.repo, "config", "user.email", "test@example.invalid")
        git(self.repo, "config", "user.name", "dispatch dup-check test")
        git(self.repo, "config", "commit.gpgsign", "false")
        git(self.repo, "add", "-A")
        git(self.repo, "commit", "-qm", "fixture")
        git(self.repo, "branch", "-f", "github/main", "main")

        self.registry = self.repo / dup_check.REGISTRY_REL
        self.home = root / "home"
        (self.home / ".codex").mkdir(parents=True)
        (self.home / ".codex" / "config.toml").write_text('model = "gpt-fixture"\n')
        self.bin = root / "bin"
        self.bin.mkdir()
        codex = self.bin / "codex"
        codex.write_text("#!/bin/sh\nexit 0\n")
        codex.chmod(0o755)
        self.addCleanup(self.tmp.cleanup)

    def claim(self, issue: int, name: str, force: bool = False) -> None:
        argv = ["claim", "--repo", str(self.repo), "--registry", str(self.registry),
                "--issue", str(issue), "--name", name]
        if force:
            argv.append("--force")
        dup_check.main(argv)

    def dispatch(self, *, role: str = "prover", issue: str = "700",
                 mode: str | None = None) -> subprocess.CompletedProcess:
        env = {
            "PATH": f"{self.bin}:/usr/bin:/bin:/usr/local/bin",
            "HOME": str(self.home),
            "MIPSTARRE_CACHE_ROOT": str(Path(self.tmp.name) / "cache"),
            "MIPSTARRE_SESSION": "test",
        }
        if mode is not None:
            env["MIPSTARRE_DUP_CHECK"] = mode
        return subprocess.run(
            ["bash", str(self.repo / "local" / "bin" / "dispatch.sh"),
             "--role", role, "--issue", issue, "--skip-hook-check", "--dry-run",
             "--", "prove the thing"],
            capture_output=True, text=True, env=env, cwd=str(self.repo),
        )

    def assert_proceeded(self, result: subprocess.CompletedProcess) -> None:
        """The guard warned but did not stop the run.

        The fixture has no codex account to reserve, so the dry run ends later
        at account routing; reaching the persona step proves the guard let the
        dispatch through rather than refusing it.
        """
        self.assertNotIn(result.returncode, (2, 3), result.stderr)
        self.assertIn("local/personas/", result.stderr)

    def test_unclaimed_issue_warns_but_dispatch_proceeds(self):
        result = self.dispatch()
        self.assert_proceeded(result)
        self.assertIn("no declaration claim registered for issue #700", result.stderr)

    def test_duplicate_claim_warns_with_the_location(self):
        self.claim(701, "PaperLib.Core.settled_already", force=True)
        result = self.dispatch(issue="701")
        self.assert_proceeded(result)
        self.assertIn("already has", result.stderr)
        self.assertIn("PaperLib/Core/A.lean:5", result.stderr)

    def test_fatal_mode_refuses_the_dispatch(self):
        self.claim(702, "PaperLib.Core.settled_already", force=True)
        result = self.dispatch(issue="702", mode="fatal")
        self.assertEqual(result.returncode, 3)
        self.assertIn("MIPSTARRE_DUP_CHECK=fatal", result.stderr)

    def test_clean_claim_reports_no_duplicate(self):
        self.claim(703, "PaperLib.Core.still_to_prove")
        result = self.dispatch(issue="703")
        self.assert_proceeded(result)
        self.assertIn("no duplicate", result.stderr)

    def test_off_skips_the_check(self):
        result = self.dispatch(mode="off")
        self.assert_proceeded(result)
        self.assertIn("duplicate-work check skipped", result.stderr)
        self.assertNotIn("no declaration claim", result.stderr)

    def test_invalid_mode_is_a_usage_error(self):
        result = self.dispatch(mode="maybe")
        self.assertEqual(result.returncode, 2)
        self.assertIn("MIPSTARRE_DUP_CHECK must be", result.stderr)

    def test_read_only_role_is_not_checked(self):
        result = self.dispatch(role="scout")
        self.assertNotIn("declaration claim", result.stderr)
        self.assertNotIn("duplicate-work check", result.stderr)

    def test_scope_word_issue_is_skipped_with_an_explanation(self):
        result = self.dispatch(issue="warmup")
        self.assert_proceeded(result)
        self.assertIn("is a scope word", result.stderr)


if __name__ == "__main__":
    unittest.main()
