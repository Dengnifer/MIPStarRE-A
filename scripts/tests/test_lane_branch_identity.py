#!/usr/bin/env python3
"""Regression tests for local/bin/lane.sh and local/bin/worktree_resolve.sh.

Three properties, each paid for on 2026-09-12:

* a lane may only exist for a real issue — the positional id, the branch and
  `gh issue view N` must agree, and a disagreement must FAIL CLOSED with a
  classified needs-attention marker (meta lanes numbered 1000+PR pushed work
  whose PR could never be adopted);
* no code path may set ``MIPSTARRE_SKIP_HOOKS`` or hand-feed the pre-push hook
  a tuple: the deleted pr_open fallback lost checked-push.sh's
  ``--force-with-lease`` and its post-preflight re-verification;
* a worktree directory holding another branch is a mismatch, never a silent
  no-op (PR 213's refresh pushed nothing for hours).
"""

from __future__ import annotations

import os
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
LANE = REPO_ROOT / "local" / "bin" / "lane.sh"
RESOLVE = REPO_ROOT / "local" / "bin" / "worktree_resolve.sh"
PR_OPEN = REPO_ROOT / "local" / "bin" / "pr_open.py"

GIT_STUB = """#!/bin/sh
for a in "$@"; do
  case "$a" in
    rev-parse) echo deadbeef; exit 0 ;;
    fetch) exit 1 ;;
  esac
done
exit 0
"""

GH_STUB = """#!/bin/sh
case "$*" in
  *"issue view 342"*)
    if [ -n "${STUB_ISSUE_OK:-}" ]; then echo "Prove the Pauli lemma"; exit 0; fi
    exit 1 ;;
esac
exit 1
"""


def _git(*args: str, cwd: Path) -> subprocess.CompletedProcess:
    return subprocess.run(
        ["git", "-c", "user.email=t@example.invalid", "-c", "user.name=test", *args],
        cwd=str(cwd), capture_output=True, text=True, check=False)


class LaneSourceTests(unittest.TestCase):
    """Properties of the script text itself."""

    def setUp(self) -> None:
        self.text = LANE.read_text(encoding="utf-8")

    def test_shell_syntax(self) -> None:
        for script in (LANE, RESOLVE):
            with self.subTest(script=script.name):
                proc = subprocess.run(["bash", "-n", str(script)], capture_output=True, text=True)
                self.assertEqual(proc.returncode, 0, proc.stderr)

    def test_no_hook_bypass_anywhere(self) -> None:
        self.assertNotIn("MIPSTARRE_SKIP_HOOKS", self.text)
        # the fallback's other half: hand-feeding .githooks/pre-push a tuple
        self.assertNotIn(".githooks/pre-push", self.text)
        self.assertNotIn("MIPStarRE pre-push: ok", self.text)

    def test_publication_only_through_pr_open(self) -> None:
        self.assertIn("local/bin/pr_open.py", self.text)
        self.assertNotIn("git -C \"$W\" push", self.text)
        self.assertNotIn("git push", self.text)
        self.assertIn("fail pr-open-failed", self.text)

    def test_no_tmp_paths(self) -> None:
        """Every tool the lane calls lives in the repo or in owner-bin."""
        code = "\n".join(line for line in self.text.splitlines()
                         if not line.lstrip().startswith("#"))
        self.assertNotIn("/tmp/", code)

    def test_one_cap_definition_reads_the_per_account_caps(self) -> None:
        self.assertIn("import account_router", self.text)
        self.assertIn("max-codex-", self.text)
        # the hard-coded fallback cap of the /tmp runner, and its dead MAXR
        self.assertNotIn("c=$((9-b))", self.text)
        self.assertNotIn("MAXR", self.text)

    def test_slot_wait_is_bounded_and_parks(self) -> None:
        self.assertIn("MIPSTARRE_LANE_SLOT_WAIT_S", self.text)
        self.assertIn("fail no-slot", self.text)
        # the six-hour wait inside the global launch lock is gone
        self.assertNotIn("seq 1 720", self.text)
        self.assertNotIn("sleep 25", self.text)

    def test_full_build_takes_the_machine_wide_lock(self) -> None:
        self.assertIn("MIPSTARRE_FULL_BUILD_LOCK", self.text)
        self.assertIn("acquire_build_lock", self.text)
        build_at = self.text.index("lake build MIPStarRE.QPBT")
        lock_at = self.text.index("acquire_build_lock || fail")
        self.assertLess(lock_at, build_at, "the build must run under the lock")

    def test_version_is_printed_and_recorded(self) -> None:
        self.assertIn('log "tool=lane.sh version=$TOOL_VERSION"', self.text)
        self.assertIn("TOOL=lane.sh VERSION=%s", self.text)
        self.assertIn("reason=%s", self.text)

    def test_gate_behaviour_of_v20_is_kept(self) -> None:
        self.assertIn("git -C \"$W\" merge -q --no-edit github/main", self.text)
        self.assertIn("issue #222", self.text)
        self.assertIn("local/bin/ci.sh", self.text)
        self.assertIn("--diff-filter=ACMR github/main HEAD", self.text)


class BranchRegexTests(unittest.TestCase):
    """lane.sh must accept exactly the branches pr_open.py accepts."""

    CORPUS = [
        "issue-42-pauli", "issue-0007-pauli-basis", "codex/issue-9-abc",
        "claude/issue-9-abc", "issue-342-games-lift", "issue-1342-meta",
        "wip/experiment", "issue--x", "issue-42-", "issue-42-Pauli",
        "issue-42-pauli_basis", "feature/issue-42-pauli", "issue-42",
    ]

    def setUp(self) -> None:
        source = PR_OPEN.read_text(encoding="utf-8")
        match = re.search(r'BRANCH_RE = re\.compile\(r"([^"]+)"\)', source)
        self.assertIsNotNone(match, "pr_open.py no longer defines BRANCH_RE as a literal")
        self.python_re = re.compile(match.group(1))
        lane = LANE.read_text(encoding="utf-8")
        match = re.search(r"^BRANCH_RE='([^']+)'", lane, re.M)
        self.assertIsNotNone(match, "lane.sh no longer defines BRANCH_RE")
        self.bash_re = match.group(1)

    def _bash_match(self, branch: str) -> tuple[bool, str, str]:
        script = (
            'if [[ "$1" =~ $2 ]]; then '
            'printf "1 %s %s\\n" "${BASH_REMATCH[2]}" "${BASH_REMATCH[3]}"; '
            'else printf "0  \\n"; fi')
        proc = subprocess.run(["bash", "-c", script, "bash", branch, self.bash_re],
                              capture_output=True, text=True, check=True)
        parts = proc.stdout.split()
        ok = parts[0] == "1"
        return ok, (parts[1] if ok else ""), (parts[2] if ok and len(parts) > 2 else "")

    def test_same_accept_reject_and_captures(self) -> None:
        for branch in self.CORPUS:
            with self.subTest(branch=branch):
                expected = self.python_re.match(branch)
                ok, number, slug = self._bash_match(branch)
                self.assertEqual(ok, expected is not None)
                if expected:
                    self.assertEqual(number, expected.group(2))
                    self.assertEqual(slug, expected.group(3))


@unittest.skipUnless(shutil.which("bash"), "bash is required")
class LaneIdentityFailClosedTests(unittest.TestCase):
    """Run lane.sh against stubbed git/gh; every disagreement must park."""

    def setUp(self) -> None:
        self.tmp = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.tmp, True)
        (self.tmp / "bin").mkdir()
        (self.tmp / "checkout" / "local" / "bin").mkdir(parents=True)
        self.lanes = self.tmp / "cache" / "watchdog" / "lanes"
        self.lanes.mkdir(parents=True)
        shutil.copy(LANE, self.tmp / "checkout" / "local" / "bin" / "lane.sh")
        for name, body in (("git", GIT_STUB), ("gh", GH_STUB)):
            path = self.tmp / "bin" / name
            path.write_text(body, encoding="utf-8")
            path.chmod(0o755)

    def _run(self, *args: str, branch: str, issue_ok: bool = False) -> subprocess.CompletedProcess:
        env = dict(os.environ)
        env.update({
            "PATH": os.pathsep.join([str(self.tmp / "bin"), os.path.dirname(sys.executable),
                                     "/usr/bin", "/bin"]),
            "HOME": str(self.tmp),
            "MIPSTARRE_CHECKOUT": str(self.tmp / "checkout"),
            "MIPSTARRE_CACHE_ROOT": str(self.tmp / "cache"),
            "LANE_BRANCH": branch,
        })
        env.pop("STUB_ISSUE_OK", None)
        if issue_ok:
            env["STUB_ISSUE_OK"] = "1"
        return subprocess.run(["bash", str(self.tmp / "checkout" / "local" / "bin" / "lane.sh"),
                               *args], capture_output=True, text=True, env=env)

    def test_lane_id_that_is_not_the_issue_number_fails_closed(self) -> None:
        proc = self._run("1342", "slug", branch="issue-342-slug", issue_ok=True)
        self.assertNotEqual(proc.returncode, 0)
        marker = (self.lanes / "1342.needs-attention").read_text(encoding="utf-8")
        self.assertIn("reason=lane-id-mismatch", marker)
        self.assertIn("version=", marker)
        self.assertNotIn("identity ok", proc.stdout)

    def test_missing_issue_fails_closed(self) -> None:
        proc = self._run("342", "slug", branch="issue-342-slug", issue_ok=False)
        self.assertNotEqual(proc.returncode, 0)
        self.assertIn("reason=issue-missing",
                      (self.lanes / "342.needs-attention").read_text(encoding="utf-8"))

    def test_off_convention_branch_warns_and_stops(self) -> None:
        proc = self._run("342", "slug", branch="wip/experiment", issue_ok=True)
        self.assertNotEqual(proc.returncode, 0)
        marker = (self.lanes / "342.needs-attention").read_text(encoding="utf-8")
        self.assertIn("reason=branch-off-convention", marker)
        # warn and stop, never silently renumber
        self.assertNotIn("identity ok", proc.stdout)

    def test_agreeing_identity_proceeds(self) -> None:
        proc = self._run("342", "slug", branch="issue-342-slug", issue_ok=True)
        self.assertIn("identity ok N=342", proc.stdout)
        # the stub makes `git fetch` fail, which parks with a different reason
        marker = (self.lanes / "342.needs-attention").read_text(encoding="utf-8")
        self.assertIn("reason=fetch-failed", marker)


@unittest.skipUnless(shutil.which("git"), "git is required")
class WorktreeResolveTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.tmp, True)
        self.root = self.tmp / "repo"
        self.root.mkdir()
        _git("init", "-q", ".", cwd=self.root)
        (self.root / "f").write_text("x\n", encoding="utf-8")
        _git("add", "f", cwd=self.root)
        _git("commit", "-qm", "init", cwd=self.root)

    def _resolve(self, branch: str, *extra: str) -> subprocess.CompletedProcess:
        return subprocess.run(["bash", str(RESOLVE), "--root", str(self.root), *extra, branch],
                              capture_output=True, text=True)

    def test_registry_first(self) -> None:
        dest = self.tmp / "elsewhere"
        _git("worktree", "add", "-q", "-b", "issue-7-a", str(dest), cwd=self.root)
        proc = self._resolve("issue-7-a")
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertEqual(Path(proc.stdout.strip()).resolve(), dest.resolve())

    def test_mismatched_convention_directory_is_refused(self) -> None:
        dest = self.root / ".worktrees" / "issue-8-b"
        dest.parent.mkdir(parents=True)
        _git("worktree", "add", "-q", "-b", "issue-9-c", str(dest), cwd=self.root)
        proc = self._resolve("issue-8-b")
        self.assertEqual(proc.returncode, 3, proc.stdout + proc.stderr)
        self.assertIn("holds", proc.stderr)

    def test_absent_worktree_without_create(self) -> None:
        proc = self._resolve("issue-10-d")
        self.assertEqual(proc.returncode, 4)
        self.assertEqual(proc.stdout.strip(), "")


if __name__ == "__main__":
    unittest.main()
