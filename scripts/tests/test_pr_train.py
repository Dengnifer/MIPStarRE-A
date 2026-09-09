"""Train acceptance and refusal tests; all Git and GitHub endpoints are fixtures."""

from __future__ import annotations

import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys
import tempfile
import unittest

from scripts.tests.test_github_workflow import FakeGitHub, LOCAL_BIN, _git


class TrainTests(unittest.TestCase):
    def setUp(self) -> None:
        holder = tempfile.TemporaryDirectory()
        self.addCleanup(holder.cleanup)
        self.tmp = Path(holder.name)
        self.repo = self.tmp / "repo"
        self.repo.mkdir()
        self.gh = FakeGitHub(self.tmp)
        self.remote = self.tmp / "remote.git"
        self.cache = self.tmp / "cache"
        self.tools = self.tmp / "tools"
        self.tools.mkdir()
        self.env = dict(os.environ, **self.gh.env(), MIPSTARRE_CACHE_ROOT=str(self.cache),
                        MIPSTARRE_CI_BUILD_LOCK_WAIT_S="0", PATH=f"{self.tools}:{os.environ['PATH']}")
        for name in list(self.env):
            if name.startswith("GIT_") or name in ("MIPSTARRE_SKIP_HOOKS", "MIPSTARRE_LAKE_ROOT",
                                                   "MIPSTARRE_FULL_BUILD_LOCK"):
                self.env.pop(name)
        _git(self.repo, "init", "-q", "--initial-branch=main", "--template=")
        _git(self.repo, "config", "user.name", "Train fixture")
        _git(self.repo, "config", "user.email", "train@example.invalid")
        _git(self.repo, "config", "commit.gpgsign", "false")
        _git(self.repo, "init", "-q", "--bare", str(self.remote))
        _git(self.repo, "remote", "add", "github", str(self.remote))
        for name in ("pr_train.py", "pr_merge.py", "gh_common.py", "wf_util.py",
                     "merge_loss_guard.py", "checked-push.sh", "ci.sh",
                     "worktree-setup.sh", "lake-root.sh"):
            target = self.repo / "local/bin" / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(LOCAL_BIN / name, target)
        self.write(".gitignore", ".lake\nblueprint/print/\n__pycache__/\n")
        self.write("shared", "base\n")
        self.write(".githooks/pre-push", "#!/bin/sh\nset -eu\n"
                   'if [ -n "${TRAIN_RACE_REF:-}" ]; then\n'
                   '  git --git-dir="$TRAIN_REMOTE" update-ref "$TRAIN_RACE_REF" "$TRAIN_RACE_SHA"\n'
                   "fi\n", executable=True)
        # Exercise real bootstrap/validation; only cache warming and hook installation are stubs.
        self.write("local/bin/warm-worktree.sh", '#!/bin/sh\nmkdir -p "$1/.lake/build"\n'
                   'ln -s "$TRAIN_PACKAGES" "$1/.lake/packages"\n', executable=True)
        self.write("scripts/install_git_hooks.sh", "#!/bin/sh\nexit 0\n", executable=True)
        pin = (LOCAL_BIN.parents[1] / "lean-toolchain").read_text()
        self.write("lean-toolchain", pin)
        self.write_tool("elan", f"#!/bin/sh\nprintf '%s' {shlex.quote(pin)}\n")
        self.write("lakefile.toml", 'name = "MIPStarRE"\ndefaultTargets = ["MIPStarRE"]\n'
                   '[[lean_lib]]\nname = "MIPStarRE"\n[[lean_exe]]\nname = "checkdecls"\n'
                   'root = "Checkdecls"\nsrcDir = "scripts"\nsupportInterpreter = true\n')
        self.write("lake-manifest.json", json.dumps({"version": "1.2.0", "name": "MIPStarRE",
                   "lakeDir": ".lake", "packagesDir": ".lake/packages", "packages": []}))
        self.write("MIPStarRE.lean", "import MIPStarRE.LDT.Test.SurfaceVsPoint\n")
        self.write("MIPStarRE/QPBT.lean", "def trainValue : Nat := 1\n")
        self.write("MIPStarRE/LDT/Test/SurfaceVsPoint.lean",
                   "import MIPStarRE.QPBT\ndef downstreamValue : Nat := trainValue\n")
        self.write("MIPStarRE/LDT/Test/AxiomAudit.lean", "import MIPStarRE.QPBT\n")
        shutil.copy2(LOCAL_BIN.parents[1] / "scripts/Checkdecls.lean", self.repo / "scripts")
        self.write("blueprint/lean_decls", "downstreamValue\n")
        packages = self.tmp / "packages"
        packages.mkdir()
        self.env.update(TRAIN_PACKAGES=str(packages), TRAIN_REMOTE=str(self.remote),
                        TRAIN_BUILD_LOG=str(self.tmp / "build.log"))
        self.write_tool("lake", '#!/bin/sh\nprintf "%s\\n" "$*" >> "$TRAIN_BUILD_LOG"\n'
                        '[ -d "$MIPSTARRE_CACHE_ROOT/.full-build-lock" ] || exit 92\n'
                        '[ "${TRAIN_FAIL_BUILD:-}" != 1 ] || exit 23\n')
        self.write_tool("leanblueprint", "#!/bin/sh\nexit 0\n")
        self.write_tool("latexmk", "#!/bin/sh\nexit 0\n")
        self.write_tool("texra-blueprint", "#!/bin/sh\nexit 0\n")
        self.write_tool("leanblueprint", '#!/bin/sh\nmkdir -p print\nprintf pdf > print/print.pdf\n')
        self.write("blueprint/.keep", "")
        for name in ("blueprint_lean_sync", "check_oversized_lean_files",
                     "audit_paper_facing_proof_debt", "audit_lean_axiom_declarations",
                     "audit_conclusion_shaped_hypotheses", "audit_unfaithful_markers",
                     "check_duplicate_private_helpers", "check_statement_paper_origin"):
            self.write(f"scripts/{name}.py", "")
        self.write("scripts/blueprint_axiom_audit_needed.py", "print('false')\n")
        self.write("scripts/comparator/check_challenge_drift.py", "")
        for name in ("audit_paper_facing_proof_debt", "check_duplicate_private_helpers",
                     "audit_conclusion_shaped_hypotheses", "audit_lean_axiom_declarations",
                     "audit_unfaithful_markers"):
            self.write(f"scripts/tests/test_{name}.py", "")
        _git(self.repo, "add", ".")
        _git(self.repo, "commit", "-qm", "base")
        self.base = _git(self.repo, "rev-parse", "HEAD")
        self.heads = {}
        for number, path, content in ((1, "shared", "accepted\n"),
                                      (2, "shared", "conflict\n"), (3, "third", "third\n")):
            _git(self.repo, "switch", "-qc", f"issue-{number}", self.base)
            self.write(path, content)
            _git(self.repo, "add", ".")
            _git(self.repo, "commit", "-qm", f"member {number}")
            self.heads[number] = _git(self.repo, "rev-parse", "HEAD")
        _git(self.repo, "switch", "-q", "main")
        _git(self.repo, "push", "-q", "github", "main", "issue-1", "issue-2", "issue-3")
        _git(self.repo, "update-ref", "refs/remotes/origin/main", self.base)
        self.arm()

    def write(self, path: str, text: str, executable: bool = False) -> None:
        target = self.repo / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text, encoding="utf-8")
        if executable:
            target.chmod(0o755)

    def write_tool(self, name: str, text: str) -> None:
        target = self.tools / name
        target.write_text(text, encoding="utf-8")
        target.chmod(0o755)

    def arm(self, bad: str = "", member: int = 3) -> None:
        self.gh.reset()
        steps = ("build", "blueprint-render", "paper-gaps", "blueprint-sync", "file-length",
                 "proof-debt", "proof-evasion", "statement-origin", "summary")
        for number, sha in self.heads.items():
            fault = bad if number == member else ""
            self.gh.route(rf"^pulls/{number}$", {
                "number": number, "state": "closed" if fault == "closed" else "open",
                "draft": fault == "draft", "merged": False, "title": f"member {number}",
                "body": "Closes #9" if fault == "dependency" else "Addresses #502",
                "head": {"sha": sha, "ref": f"issue-{number}"}, "base": {"ref": "main"}})
            statuses = [{"context": f"local-ci/{step}", "state": "success"} for step in steps]
            statuses.append({"context": "local-review/summary", "state": "success"})
            if fault == "ci":
                statuses.pop(0)
            self.gh.route(rf"^commits/{sha}/statuses", statuses)
            self.gh.route(rf"^pulls/{number}/reviews", [{
                "commit_id": self.base if fault == "review" else sha,
                "state": "CHANGES_REQUESTED" if fault == "changes" else "COMMENTED",
                "body": f"<!-- mipstarre-review pr={number} head={sha} -->\nVERDICT: APPROVED\n"}])
            self.gh.route(rf"^issues/{number}/comments", [])
            self.gh.route(rf"^issues/{number}/comments", {"id": number}, method="POST")
        self.gh.route(r"^issues/9/sub_issues", [{"number": 10, "state": "open"}])

    def train(self, *members: int) -> subprocess.CompletedProcess:
        return subprocess.run([sys.executable, str(self.repo / "local/bin/pr_train.py"),
                               *map(str, members or (1, 2, 3))], cwd=self.repo,
                              env=self.env, text=True, capture_output=True, timeout=360)

    def remote_main(self) -> str:
        return _git(self.repo, "--git-dir", str(self.remote), "rev-parse", "main")

    def test_train_drops_only_conflict_and_publishes_combined_commit(self) -> None:
        developer = self.tmp / "developer"
        _git(self.repo, "worktree", "add", str(developer), "issue-2")
        (developer / "uncommitted").write_text("preserve\n")
        result = self.train()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("dropped PR #2", result.stdout)
        head = self.remote_main()
        self.assertEqual(_git(self.repo, "rev-parse", "main"), head)
        self.assertEqual(_git(self.repo, "rev-list", "--count", "--first-parent", f"{self.base}..{head}"), "2")
        for number in (1, 3):
            _git(self.repo, "merge-base", "--is-ancestor", self.heads[number], head)
        excluded = subprocess.run(["git", "merge-base", "--is-ancestor", self.heads[2], head], cwd=self.repo)
        self.assertEqual(excluded.returncode, 1)
        self.assertEqual((developer / "uncommitted").read_text(), "preserve\n")
        self.assertEqual((self.repo / "shared").read_text(), "accepted\n")
        self.assertEqual((self.repo / "third").read_text(), "third\n")
        self.assertEqual((self.tmp / "build.log").read_text().splitlines(),
                         ["build MIPStarRE MIPStarRE.LDT.Test.AxiomAudit"])
        self.assertEqual(_git(self.repo, "branch", "--list", "train-*"), "")
        posts = [row for row in self.gh.calls() if row["method"] != "GET"]
        self.assertEqual([row["rel"] for row in posts], ["issues/1/comments", "issues/3/comments"])
        self.assertIn(head, (self.repo / "results/telemetry/events.md").read_text())

    def test_whole_train_refuses_any_bad_member(self) -> None:
        for fault in ("ci", "review", "closed", "draft", "dependency", "changes"):
            with self.subTest(fault=fault):
                self.arm(fault)
                result = self.train()
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("PR #3", result.stderr)
                self.assertEqual(self.remote_main(), self.base)
                self.assertFalse((self.cache / "trains").exists())

    def test_conflict_leaving_one_member_refuses(self) -> None:
        result = self.train(1, 2)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("fewer than two", result.stderr)
        self.assertEqual(self.remote_main(), self.base)
        self.assertFalse((self.tmp / "build.log").exists())

    def test_failed_build_refuses_and_records_failure(self) -> None:
        self.env["TRAIN_FAIL_BUILD"] = "1"
        result = self.train()
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(self.remote_main(), self.base)
        rows = (self.repo / "results/telemetry/builds.jsonl").read_text().splitlines()
        self.assertEqual(json.loads(rows[0])["outcome"], "failure")

    def test_live_build_lock_refuses_without_breaking_it(self) -> None:
        lock = self.cache / ".full-build-lock"
        lock.mkdir(parents=True)
        (lock / "owner").write_text(f"{os.getpid()}\n")
        result = self.train()
        self.assertNotEqual(result.returncode, 0)
        self.assertTrue(lock.exists())
        self.assertFalse((self.tmp / "build.log").exists())
        self.assertEqual(self.remote_main(), self.base)

    def test_dirty_primary_refuses(self) -> None:
        self.write("uncommitted", "preserve")
        result = self.train()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("dirty", result.stderr)
        self.assertEqual(self.remote_main(), self.base)

    def test_ci_cannot_certify_changed_worktree(self) -> None:
        self.write_tool("lake", '#!/bin/sh\nprintf changed > shared\n')
        result = self.train()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("became dirty", result.stdout + result.stderr)
        self.assertEqual(self.remote_main(), self.base)

    def test_changed_main_during_preflight_refuses(self) -> None:
        self.env.update(TRAIN_RACE_REF="refs/heads/main", TRAIN_RACE_SHA=self.heads[2])
        result = self.train()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("remote main changed", result.stderr)
        self.assertEqual(self.remote_main(), self.heads[2])
        self.assertEqual(_git(self.repo, "rev-parse", "main"), self.base)

    def test_changed_member_during_preflight_refuses(self) -> None:
        # GitHub's head API follows the fixture ref movement in this scenario.
        wrapper = self.tmp / "gh-moving"
        wrapper.write_text('#!/usr/bin/env python3\nimport json, os, subprocess, sys\n'
                           "if sys.argv[2].endswith('/pulls/3'):\n"
                           " p=json.load(open(os.environ['MIPSTARRE_FAKE_GH_ROUTES']))\n"
                           " row=next(r['body'] for r in p if r['path']=='^pulls/3$')\n"
                           " row['head']['sha']=subprocess.check_output(['git', '--git-dir', "
                           "os.environ['TRAIN_REMOTE'], 'rev-parse', 'issue-3'], text=True).strip()\n"
                           " print(json.dumps(row))\nelse:\n"
                           f" os.execv({str(self.gh.binary)!r}, [{str(self.gh.binary)!r}, *sys.argv[1:]])\n")
        wrapper.chmod(0o755)
        self.env.update(MIPSTARRE_GH=str(wrapper), TRAIN_RACE_REF="refs/heads/issue-3",
                        TRAIN_RACE_SHA=self.heads[2])
        result = self.train()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("PR #3", result.stderr)
        self.assertEqual(self.remote_main(), self.base)

    def test_integration_mode_rejects_skip_flags(self) -> None:
        result = subprocess.run(["bash", str(self.repo / "local/bin/ci.sh"),
                                 "--integration-head", self.base, "--base", self.base,
                                 "--worktree", str(self.repo), "--skip-build"],
                                env=self.env, text=True, capture_output=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("cannot use", result.stderr)

    def test_external_lake_root_uses_real_bootstrap(self) -> None:
        self.env["MIPSTARRE_LAKE_ROOT"] = str(self.tmp / "external-lake")
        self.env["TRAIN_FAIL_BUILD"] = "1"  # Retain the tree to inspect the bootstrap result.
        result = self.train()
        self.assertNotEqual(result.returncode, 0)
        tree = next((self.cache / "trains").glob("*/worktree"))
        branch = _git(tree, "symbolic-ref", "--short", "HEAD")
        self.assertTrue(branch.startswith("train-"))
        self.assertEqual((tree / ".lake").resolve(), self.tmp / "external-lake" / branch)
        checked = subprocess.run([str(self.repo / "local/bin/lake-root.sh"), "prepare",
                                  str(tree), "--check"], env=self.env, capture_output=True)
        self.assertEqual(checked.returncode, 0, checked.stderr)
        self.assertTrue((self.tmp / "build.log").exists(), result.stdout + result.stderr)

    def real_project(self, broken: str = "") -> None:
        lake = shutil.which("lake")
        if not lake:
            self.skipTest("real Lake is required for the cold-artifact fixture")
        # Real Lean builds share the machine lock, even though all endpoints/artifacts are private.
        self.env["MIPSTARRE_FULL_BUILD_LOCK"] = os.environ.get(
            "MIPSTARRE_FULL_BUILD_LOCK", str(Path.home() / ".cache/mipstarre-dev/.full-build-lock"))
        self.env["MIPSTARRE_CI_BUILD_LOCK_WAIT_S"] = "300"
        self.write_tool("lake", '#!/bin/sh\nset -eu\n'
                        'printf "%s\\n" "$*" >> "$TRAIN_BUILD_LOG"\n'
                        'if [ "$*" = "build MIPStarRE MIPStarRE.LDT.Test.AxiomAudit" ]; then\n'
                        ' test -d "$MIPSTARRE_FULL_BUILD_LOCK"\n'
                        ' test ! -e .lake/build/lib/lean/MIPStarRE.olean\nfi\n'
                        f'exec {shlex.quote(lake)} "$@"\n')
        # The production hook and dynamic checkdecls import run at publication.
        shutil.copy2(LOCAL_BIN.parents[1] / ".githooks/pre-push", self.repo / ".githooks")
        for name in ("check_paper_gap_note_style", "audit_new_proof_obligation_metadata",
                     "check_source_statement_changes"):
            self.write(f"scripts/{name}.py", "")
        _git(self.repo, "add", ".")
        _git(self.repo, "commit", "-qm", "publication fixture")
        self.base = _git(self.repo, "rev-parse", "HEAD")
        _git(self.repo, "push", "-q", "github", "main")
        _git(self.repo, "update-ref", "refs/remotes/origin/main", self.base)
        _git(self.repo, "switch", "-q", "issue-1")
        self.write("MIPStarRE/QPBT.lean", 'def trainValue : String := "changed"\n'
                   if broken == "downstream" else "def trainValue : Nat := 2\n")
        if broken == "audit":
            self.write("MIPStarRE/LDT/Test/AxiomAudit.lean", "example : False := by decide\n")
        _git(self.repo, "add", ".")
        _git(self.repo, "commit", "-qm", "change upstream fixture")
        self.heads[1] = _git(self.repo, "rev-parse", "HEAD")
        _git(self.repo, "switch", "-q", "main")
        _git(self.repo, "push", "-q", "github", "issue-1")
        self.arm()

    def test_cold_project_build_reaches_real_publication_checkdecls(self) -> None:
        self.real_project()
        result = self.train(1, 3)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("All 1 declarations", result.stdout)
        calls = (self.tmp / "build.log").read_text().splitlines()
        self.assertEqual(calls.count("build MIPStarRE MIPStarRE.LDT.Test.AxiomAudit"), 1)
        self.assertIn("exe checkdecls blueprint/lean_decls", calls)
        self.assertNotEqual(self.remote_main(), self.base)

    def test_cold_project_build_catches_untouched_downstream(self) -> None:
        self.real_project("downstream")
        self.assert_build_blocks_publication()

    def test_cold_project_build_catches_axiom_audit_failure(self) -> None:
        self.real_project("audit")
        self.assert_build_blocks_publication()

    def assert_build_blocks_publication(self) -> None:
        result = self.train(1, 3)
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(self.remote_main(), self.base)
        rows = (self.repo / "results/telemetry/builds.jsonl").read_text().splitlines()
        self.assertEqual(json.loads(rows[-1])["outcome"], "failure")
        self.assertNotIn("exe checkdecls", (self.tmp / "build.log").read_text())

    def ambiguous_push(self, mode: str, expected: str) -> None:
        # Real checked-push and bare Git transport; inject a lost response only after acceptance.
        git = shutil.which("git")
        self.env.update(TRAIN_GIT=str(git), TRAIN_PUSH_MODE=mode,
                        TRAIN_PUSH_MARKER=str(self.tmp / "pushed"))
        self.write_tool("git", '#!/usr/bin/env python3\nimport os, subprocess, sys\n'
                        'from pathlib import Path\na=sys.argv[1:]\ne=os.environ\n'
                        'marker=Path(e["TRAIN_PUSH_MARKER"])\nmode=e["TRAIN_PUSH_MODE"]\n'
                        'if marker.exists() and ((mode=="unreadable" and "ls-remote" in a) '
                        'or (mode=="fetch-failure" and "fetch" in a)):\n sys.exit(71)\n'
                        'rc=subprocess.call([e["TRAIN_GIT"], *a])\n'
                        'if "push" in a and rc==0:\n'
                        ' marker.touch()\n'
                        ' if mode in ("descendant", "fetch-failure"):\n'
                        '  cmd=[e["TRAIN_GIT"], "--git-dir", e["TRAIN_REMOTE"]]\n'
                        '  parent=subprocess.check_output(cmd+["rev-parse", "main"], text=True).strip()\n'
                        '  tree=subprocess.check_output(cmd+["rev-parse", "main^{tree}"], text=True).strip()\n'
                        '  child=subprocess.check_output(cmd+["-c", "user.name=Fixture", "-c", '
                        '"user.email=fixture@example.invalid", "commit-tree", tree, "-p", parent, '
                        '"-m", "remote descendant"], text=True).strip()\n'
                        '  subprocess.check_call(cmd+["update-ref", "refs/heads/main", child])\n'
                        ' sys.exit(70)\nsys.exit(rc)\n')
        result = self.train(1, 3)
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        directory = next((self.cache / "trains").iterdir())
        receipt = json.loads((directory / "publication.json").read_text())
        self.assertEqual(receipt["outcome"], expected)
        _git(self.repo, "--git-dir", str(self.remote), "merge-base", "--is-ancestor",
             receipt["head"], "main")
        self.assertIn(f"train publication {expected}", result.stderr)
        self.assertNotIn("refused", result.stderr)
        self.assertIn(f"publication {expected}", (self.repo / "results/telemetry/events.md").read_text())
        self.assertTrue((directory / "worktree").exists())
        self.assertEqual(_git(self.repo, "rev-parse", "main"), self.base)
        self.assertFalse([r for r in self.gh.calls() if r["method"] != "GET"])

    def test_accepted_push_with_lost_response_is_published(self) -> None:
        self.ambiguous_push("accepted", "published")

    def test_remote_descendant_after_lost_response_is_published(self) -> None:
        self.ambiguous_push("descendant", "published")

    def test_unreadable_remote_after_lost_response_is_unknown(self) -> None:
        self.ambiguous_push("unreadable", "unknown")

    def test_failed_descendant_fetch_after_lost_response_is_unknown(self) -> None:
        self.ambiguous_push("fetch-failure", "unknown")


if __name__ == "__main__":
    unittest.main()
