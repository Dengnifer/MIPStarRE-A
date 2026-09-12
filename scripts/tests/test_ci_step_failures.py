#!/usr/bin/env python3
"""Exercise CI step failures through the real driver with offline tool fixtures."""

from __future__ import annotations

import json
import os
import shutil
import subprocess
from pathlib import Path

from scripts.tests import test_github_workflow as workflow


FAKE_COMMAND = r'''#!/usr/bin/env python3
import os
import sys
from pathlib import Path

name = Path(sys.argv[0]).name
command = " ".join([name, *sys.argv[1:]])
cache = Path(os.environ["MIPSTARRE_CACHE_ROOT"])
assert (cache / "locks/ci-7.lock/owner").is_file()
if name == "lake":
    assert (cache / ".full-build-lock/owner").is_file()
if name == "check_oversized_lean_files.py":
    assert not (cache / ".full-build-lock").exists()
with open(os.environ["FAKE_TOOL_LOG"], "a", encoding="utf-8") as out:
    out.write(command + "\n")
failure = os.environ.get("FAKE_FAIL_COMMAND")
if failure and command.startswith(failure):
    raise SystemExit(int(os.environ["FAKE_EXIT_CODE"]))
if name == "latexmk":
    Path("../print/print.pdf").write_bytes(b"fresh pdf")
if name == "blueprint_axiom_audit_needed.py":
    print("false")
'''

FAKE_TEST = r'''import os
import unittest
from pathlib import Path

class RequiredCommandTests(unittest.TestCase):
    def test_required_command(self):
        name = Path(__file__).name
        with open(os.environ["FAKE_TOOL_LOG"], "a", encoding="utf-8") as out:
            out.write(name + "\n")
        self.assertNotEqual(os.environ.get("FAKE_FAIL_COMMAND"), name)
'''


class CiStepFailureTests(workflow.LayerTestCase):
    """Required errors survive later commands, publication, and parent cleanup."""

    def setUp(self) -> None:
        super().setUp()
        self.repo = self.tmp / "repo"
        self.repo.mkdir()
        templates = self.tmp / "no-templates"
        templates.mkdir()
        workflow._git(self.repo, "init", "-q", f"--template={templates}")
        workflow._git(self.repo, "symbolic-ref", "HEAD", "refs/heads/main")
        for key, value in (("user.name", "CI tests"), ("user.email", "ci@example.invalid"),
                           ("commit.gpgsign", "false"), ("core.hooksPath", str(templates))):
            workflow._git(self.repo, "config", key, value)
        local_bin = self.repo / "local/bin"
        local_bin.mkdir(parents=True)
        for name in ("ci.sh", "gh_common.py", "wf_util.py"):
            shutil.copy2(workflow.LOCAL_BIN / name, local_bin / name)
        for directory in ("blueprint/src", "blueprint/print", ".lake/build", ".lake/packages",
                          "scripts/tests", "scripts/comparator"):
            (self.repo / directory).mkdir(parents=True)
        for name in ("comparator/check_challenge_drift", "blueprint_lean_sync",
                     "blueprint_axiom_audit_needed", "check_oversized_lean_files",
                     "audit_paper_facing_proof_debt", "audit_lean_axiom_declarations",
                     "audit_conclusion_shaped_hypotheses", "audit_unfaithful_markers",
                     "check_duplicate_private_helpers", "check_statement_paper_origin"):
            (self.repo / f"scripts/{name}.py").write_text(FAKE_COMMAND, encoding="utf-8")
        for name in ("required", "audit_paper_facing_proof_debt", "audit_unfaithful_markers",
                     "check_duplicate_private_helpers", "audit_conclusion_shaped_hypotheses",
                     "audit_lean_axiom_declarations"):
            (self.repo / f"scripts/tests/test_{name}.py").write_text(FAKE_TEST, encoding="utf-8")
        (self.repo / ".gitignore").write_text(
            ".lake/\nresults/\nblueprint/print/\n__pycache__/\n", encoding="utf-8")
        workflow._git(self.repo, "add", "-A")
        workflow._git(self.repo, "commit", "-qm", "base")
        workflow._git(self.repo, "update-ref", "refs/remotes/origin/main", "HEAD")
        branch = "issue-504-ci-step-failure-propagation"
        workflow._git(self.repo, "checkout", "-qb", branch)
        workflow._git(self.repo, "commit", "--allow-empty", "-qm", "branch")
        self.head = workflow._git(self.repo, "rev-parse", "HEAD")
        self.gh.route(r"^pulls/7$", {
            "number": 7, "state": "open", "base": {"ref": "main"},
            "head": {"sha": self.head, "ref": branch},
        })
        self.gh.route(rf"^statuses/{self.head}$", {}, method="POST")
        self.gh.route(r"^issues/7/comments", [])
        self.gh.route(r"^issues/7/comments$", {"id": 1}, method="POST")
        self.tools = self.tmp / "tools"
        self.tools.mkdir()
        # An allowlisted PATH prevents fallback to live build or model tools.
        for name in ("bash", "python3", "git", "dirname", "basename", "date", "stat", "head",
                     "mkdir", "rm", "sleep", "mktemp", "sed", "tr", "cut", "cat", "grep",
                     "cp", "tee"):
            (self.tools / name).symlink_to(shutil.which(name))
        for name in ("lake", "leanblueprint", "texra-blueprint", "latexmk"):
            tool = self.tools / name
            tool.write_text(FAKE_COMMAND, encoding="utf-8")
            tool.chmod(0o755)
        self.cache = self.tmp / "cache"
        self.tool_log = self.tmp / "commands.log"

    def run_ci(self, failure: str = "", code: int = 7) -> tuple[dict, list[str]]:
        self.tool_log.write_text("", encoding="utf-8")
        self.gh.spool.unlink(missing_ok=True)
        env = dict(os.environ, **self.gh.env())
        env.update(PATH=str(self.tools), MIPSTARRE_CACHE_ROOT=str(self.cache),
                   MIPSTARRE_FULL_BUILD_LOCK=str(self.cache / ".full-build-lock"),
                   FAKE_TOOL_LOG=str(self.tool_log), FAKE_FAIL_COMMAND=failure,
                   FAKE_EXIT_CODE=str(code), PYTHONDONTWRITEBYTECODE="1")
        result = subprocess.run(
            ["bash", str(self.repo / "local/bin/ci.sh"), "7", "--worktree", str(self.repo),
             "--force-all"], cwd=self.repo, env=env, capture_output=True, text=True, timeout=30)
        path = self.cache / "ci-manifests" / f"pr7-{self.head}.json"
        self.assertTrue(path.is_file(), result.stdout + result.stderr)
        manifest = json.loads(path.read_text(encoding="utf-8"))
        self.assertFalse(manifest["partial"])
        self.assertEqual(result.returncode, int(manifest["conclusion"] != "success"),
                         result.stdout + result.stderr)
        statuses = {row["context"]: row["state"]
                    for row in self.gh.payloads("POST", rf"^statuses/{self.head}$")}
        for step in manifest["steps"]:
            self.assertEqual(statuses[f"local-ci/{step['step']}"], step["outcome"])
        self.assertEqual(statuses["local-ci/summary"],
                         "success" if manifest["conclusion"] == "success" else "failure")
        self.assertTrue(self.gh.payloads("POST", r"^issues/7/comments$"))
        self.assertFalse((self.cache / "locks/ci-7.lock").exists())
        self.assertFalse((self.cache / ".full-build-lock").exists())
        commands = self.tool_log.read_text(encoding="utf-8").splitlines()
        self.assertEqual(commands[-1], "check_statement_paper_origin.py --root .")
        self.assertEqual(self.step(manifest, "statement-origin")["outcome"], "success")
        return manifest, commands

    @staticmethod
    def step(manifest: dict, name: str) -> dict:
        return next(step for step in manifest["steps"] if step["step"] == name)

    def test_success_runs_all_required_commands(self) -> None:
        manifest, commands = self.run_ci()
        self.assertEqual(manifest["conclusion"], "success")
        self.assertTrue(all(step["outcome"] == "success" for step in manifest["steps"]))
        for command in ("lake build MIPStarRE.LDT.Test.AxiomAudit", "texra-blueprint web",
                        "blueprint_lean_sync.py --root . --ci"):
            self.assertIn(command, commands)

    def test_required_failures_stop_step_but_allow_later_steps(self) -> None:
        cases = (
            ("build", "lake exe cache get", "lake build"),
            ("build", "lake build", "check_challenge_drift.py --root ."),
            ("blueprint-render", "texra-blueprint bbl", "texra-blueprint web"),
            ("blueprint-render", "texra-blueprint web", None),
            ("blueprint-sync", "test_required.py",
             "blueprint_lean_sync.py --root . --update-lean-decls"),
            ("blueprint-sync", "blueprint_lean_sync.py --root . --update-lean-decls",
             "blueprint_lean_sync.py --root . --ci"),
            ("blueprint-sync", "blueprint_axiom_audit_needed.py", None),
            ("proof-evasion", "audit_lean_axiom_declarations.py",
             "audit_conclusion_shaped_hypotheses.py --root . --ci"),
        )
        for step, command, later in cases:
            with self.subTest(command=command):
                manifest, commands = self.run_ci(command)
                self.assertEqual(manifest["conclusion"], "failure")
                outcome = self.step(manifest, step)
                self.assertEqual(outcome["outcome"], "failure")
                self.assertEqual(outcome["note"], "exit 1" if command == "test_required.py"
                                 else "exit 7")
                self.assertTrue(any(call.startswith(command) for call in commands))
                if later:
                    self.assertNotIn(later, commands)

    def test_duplicate_helper_candidates_remain_advisory(self) -> None:
        manifest, _ = self.run_ci("check_duplicate_private_helpers.py", code=1)
        self.assertEqual(manifest["conclusion"], "success")
        self.assertEqual(self.step(manifest, "proof-evasion")["outcome"], "success")
        self.assertTrue(any("this audit is advisory" in note for note in manifest["warnings"]))

    def test_duplicate_helper_errors_fail(self) -> None:
        manifest, _ = self.run_ci("check_duplicate_private_helpers.py", code=2)
        self.assertEqual(manifest["conclusion"], "failure")
        self.assertEqual(self.step(manifest, "proof-evasion")["note"], "exit 2")

    def test_missing_tool_is_error_and_releases_build_lock(self) -> None:
        (self.tools / "lake").unlink()
        manifest, _ = self.run_ci()
        self.assertEqual(manifest["conclusion"], "error")
        self.assertEqual(self.step(manifest, "build")["outcome"], "error")
        self.assertIn("required tool lake", self.step(manifest, "build")["note"])
