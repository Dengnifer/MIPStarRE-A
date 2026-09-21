#!/usr/bin/env python3
"""The decision table of ``local/bin/service/gate.py``, on canned GitHub API answers.

The gate is fail-closed: it publishes ``local-review/summary`` = success ONLY for a
marked review at the exact current head, with a verdict, zero unchecked findings, every
CI context success, a complete CI manifest and no CHANGES_REQUESTED review at that head.
Every other shape must publish nothing at all — the bug this guards against is a gate
that posts a green status on stale or absent evidence, after which the merge gate has no
independent check left.

Offline: the GitHub layer, the claim tool and git are stubbed; nothing here runs gh.
"""

from __future__ import annotations

import importlib.util
import json
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
GATE_PATH = ROOT / "local" / "bin" / "service" / "gate.py"

HEAD = "a" * 40
OLD = "b" * 40
BASE = "c" * 40


def load_gate():
    spec = importlib.util.spec_from_file_location("kit_service_gate", GATE_PATH)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def review(number: int = 7, head: str = HEAD, *, body: str | None = None,
           state: str = "COMMENTED", login: str = "owner", ident: int = 91) -> dict:
    if body is None:
        body = (f"<!-- mipstarre-review pr={number} head={head} -->\n"
                "Looks fine.\n\nVERDICT: APPROVED")
    return {"id": ident, "commit_id": head, "state": state, "body": body,
            "user": {"login": login}}


class GateDecisionTests(unittest.TestCase):
    def setUp(self) -> None:
        self.gate = load_gate()
        self.tmp = tempfile.TemporaryDirectory()
        self.posted: list[tuple] = []
        self.claims: list[tuple] = []
        self.statuses = {context: {"state": "success"} for context in self.gate.CI_CONTEXTS}
        self.pull = {"state": "open", "merged": False, "draft": False,
                     "head": {"sha": HEAD, "ref": "issue-7-a-slug"},
                     "base": {"ref": "main"}, "body": ""}
        self.reviews = [review()]
        self.manifest = {"head_sha": HEAD, "conclusion": "success", "partial": False}
        self.manifest_path = Path(self.tmp.name) / "manifest.json"
        self._write_manifest()

        def api(path, **kwargs):
            if path.startswith("pulls/") and path.endswith("/reviews"):
                return list(self.reviews)
            if path.startswith("pulls/"):
                return self.pull
            if path.startswith("git/ref/heads/"):
                return {"object": {"sha": BASE}}
            raise AssertionError(f"unexpected API path {path}")

        def post_status(sha, context, state, description="", target_url=None):
            self.posted.append((sha, context, state, description))
            self.statuses[context] = {"state": state}

        def claim(action, number, note):
            self.claims.append((action, number, note))
            return subprocess.CompletedProcess([], 0, "claimed", "")

        self.patches = [
            mock.patch.object(self.gate, "api", api),
            mock.patch.object(self.gate, "latest_statuses", lambda sha: dict(self.statuses)),
            mock.patch.object(self.gate, "post_status", post_status),
            mock.patch.object(self.gate, "_claim", claim),
            mock.patch.object(self.gate.service_env, "ci_manifest", lambda n, h: self.manifest_path),
            mock.patch.object(self.gate.service_env, "slug", lambda: "owner/repo"),
            mock.patch.object(self.gate.subprocess, "run", self.fake_git),
        ]
        for patch in self.patches:
            patch.start()

    def tearDown(self) -> None:
        for patch in reversed(self.patches):
            patch.stop()
        self.tmp.cleanup()

    def _write_manifest(self) -> None:
        self.manifest_path.write_text(json.dumps(self.manifest), encoding="utf-8")

    @staticmethod
    def fake_git(cmd, **kwargs):
        if "merge-base" in cmd:
            return subprocess.CompletedProcess(cmd, 0, BASE + "\n", "")
        return subprocess.CompletedProcess(cmd, 0, "", "")

    # ----------------------------------------------------------------- green
    def test_a_clean_review_at_the_exact_head_is_gated(self) -> None:
        self.statuses.pop("local-review/summary", None)
        result = self.gate.gate(7)
        self.assertIn("GATED", result)
        self.assertEqual([(HEAD, "local-review/summary", "success")],
                         [(s, c, st) for s, c, st, _ in self.posted])
        self.assertEqual([a for a, _, _ in self.claims], ["claim", "release"])

    def test_an_already_green_summary_is_not_posted_again(self) -> None:
        self.statuses["local-review/summary"] = {"state": "success"}
        result = self.gate.gate(7)
        self.assertIn("already gated", result)
        self.assertEqual(self.posted, [])
        self.assertEqual(self.claims, [])

    # ------------------------------------------------------- nothing posted
    def test_a_review_on_an_older_head_publishes_nothing(self) -> None:
        self.reviews = [review(head=OLD)]
        result = self.gate.gate(7)
        self.assertIn("no marked review at the current head", result)
        self.assertEqual(self.posted, [])

    def test_an_unmarked_review_publishes_nothing(self) -> None:
        self.reviews = [review(body="Looks fine.\n\nVERDICT: APPROVED")]
        result = self.gate.gate(7)
        self.assertIn("no marked review", result)
        self.assertEqual(self.posted, [])

    def test_a_draft_pr_publishes_nothing(self) -> None:
        self.pull["draft"] = True
        self.assertIn("not an open non-draft PR", self.gate.gate(7))
        self.assertEqual(self.posted, [])

    def test_a_missing_ci_context_is_a_block_not_a_pass(self) -> None:
        self.statuses.pop(self.gate.CI_CONTEXTS[0])
        self.statuses.pop("local-review/summary", None)
        result = self.gate.gate(7)
        self.assertIn("NOT gated", result)
        self.assertIn("CI not all success", result)
        self.assertEqual(self.posted, [])

    def test_a_failed_ci_context_blocks(self) -> None:
        self.statuses[self.gate.CI_CONTEXTS[1]] = {"state": "failure"}
        self.statuses.pop("local-review/summary", None)
        self.assertIn("CI not all success", self.gate.gate(7))
        self.assertEqual(self.posted, [])

    def test_an_unreadable_ci_manifest_blocks(self) -> None:
        self.manifest_path.unlink()
        self.statuses.pop("local-review/summary", None)
        result = self.gate.gate(7)
        self.assertIn("CI manifest unreadable", result)
        self.assertEqual(self.posted, [])

    def test_a_partial_ci_manifest_blocks(self) -> None:
        self.manifest["partial"] = True
        self._write_manifest()
        self.statuses.pop("local-review/summary", None)
        self.assertIn("CI manifest not a complete success", self.gate.gate(7))
        self.assertEqual(self.posted, [])

    def test_a_manifest_for_another_head_blocks(self) -> None:
        self.manifest["head_sha"] = OLD
        self._write_manifest()
        self.statuses.pop("local-review/summary", None)
        self.assertIn("CI manifest not a complete success", self.gate.gate(7))
        self.assertEqual(self.posted, [])

    def test_a_missing_verdict_trailer_blocks(self) -> None:
        self.reviews = [review(body=f"<!-- mipstarre-review pr=7 head={HEAD} -->\nno verdict here")]
        self.statuses.pop("local-review/summary", None)
        result = self.gate.gate(7)
        self.assertIn("VERDICT trailer missing", result)
        self.assertEqual(self.posted, [])

    def test_a_changes_requested_review_on_this_head_blocks(self) -> None:
        self.reviews = [review(), {"id": 92, "commit_id": HEAD, "state": "CHANGES_REQUESTED",
                                   "body": "no", "user": {"login": "owner"}}]
        self.statuses.pop("local-review/summary", None)
        result = self.gate.gate(7)
        self.assertIn("CHANGES_REQUESTED", result)
        self.assertEqual(self.posted, [])

    def test_a_base_other_than_the_integration_branch_blocks(self) -> None:
        self.pull["base"]["ref"] = "some-feature"
        self.statuses.pop("local-review/summary", None)
        self.assertIn("base is some-feature", self.gate.gate(7))
        self.assertEqual(self.posted, [])

    def test_a_refused_claim_stops_before_posting(self) -> None:
        self.statuses.pop("local-review/summary", None)
        with mock.patch.object(self.gate, "_claim",
                               lambda *a: subprocess.CompletedProcess([], 3, "HELD: other", "")):
            result = self.gate.gate(7)
        self.assertIn("claim refused", result)
        self.assertEqual(self.posted, [])

    # --------------------------------------------------------------- adverse
    def test_unchecked_findings_publish_failure(self) -> None:
        self.reviews = [review(body=f"<!-- mipstarre-review pr=7 head={HEAD} -->\n"
                                    "- [ ] F1 something is wrong\n\nVERDICT: APPROVED")]
        self.statuses.pop("local-review/summary", None)
        result = self.gate.gate(7)
        self.assertIn("ADVERSE", result)
        self.assertEqual([(c, st) for _, c, st, _ in self.posted],
                         [("local-review/summary", "failure")])

    def test_a_changes_requested_verdict_publishes_failure(self) -> None:
        self.reviews = [review(body=f"<!-- mipstarre-review pr=7 head={HEAD} -->\n"
                                    "please fix\n\nVERDICT: CHANGES_REQUESTED")]
        self.statuses.pop("local-review/summary", None)
        result = self.gate.gate(7)
        self.assertIn("ADVERSE", result)
        self.assertEqual([st for _, _, st, _ in self.posted], ["failure"])

    def test_an_adverse_verdict_is_not_republished_when_already_failed(self) -> None:
        self.reviews = [review(body=f"<!-- mipstarre-review pr=7 head={HEAD} -->\n"
                                    "please fix\n\nVERDICT: CHANGES_REQUESTED")]
        self.statuses["local-review/summary"] = {"state": "failure"}
        self.gate.gate(7)
        self.assertEqual(self.posted, [])

    # ------------------------------------------------------------ read-back
    def test_a_status_that_does_not_read_back_is_reported_as_a_failure(self) -> None:
        self.statuses.pop("local-review/summary", None)

        def post_but_lose_it(sha, context, state, description="", target_url=None):
            self.posted.append((sha, context, state, description))  # never lands

        with mock.patch.object(self.gate, "post_status", post_but_lose_it):
            result = self.gate.gate(7)
        self.assertIn("did not read back", result)
        self.assertEqual([a for a, _, _ in self.claims], ["claim", "release"])

    # ------------------------------------------------- informational, not a block
    def test_a_review_by_another_account_is_noted_but_does_not_block(self) -> None:
        self.reviews = [review(login="a-colleague")]
        self.statuses.pop("local-review/summary", None)
        result = self.gate.gate(7)
        self.assertIn("GATED", result)
        self.assertIn("not the slug owner", result)


if __name__ == "__main__":
    unittest.main()
