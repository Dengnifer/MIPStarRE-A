#!/usr/bin/env python3
"""Unit tests for ``local/bin/pr_janitor.py``.

The two mechanical conditions are exercised against a real temporary git
repository — not a stub — because the whole point of the tool is that the
decision is git's, not a heuristic:

* a PR whose three-dot diff against ``github/main`` is empty AND whose head is
  reachable from ``github/main`` is closed, with one marker comment;
* either condition alone closes nothing.  In particular a branch that adds a
  commit and reverts it has an empty three-dot diff and must survive;
* the marker comment is posted at most once (a second pass updates the existing
  comment, it never posts a second one);
* no issue is ever closed: the only state-changing write is a PATCH to
  ``pulls/<n>``;
* a GitHub failure is reported, leaves the PR open, writes no closure row and
  makes the pass exit nonzero.

Run: ``python3 -m unittest scripts/tests/test_pr_janitor.py``
"""

from __future__ import annotations

import contextlib
import io
import json
import os
import re
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "local" / "bin"))

import pr_janitor  # noqa: E402
from wf_util import LayerError  # noqa: E402

GIT_ENV = dict(os.environ, GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_SYSTEM=os.devnull,
               GIT_AUTHOR_NAME="janitor test", GIT_AUTHOR_EMAIL="janitor@example.invalid",
               GIT_COMMITTER_NAME="janitor test",
               GIT_COMMITTER_EMAIL="janitor@example.invalid")


def git(repo: Path, *args: str) -> str:
    result = subprocess.run(["git", "-C", str(repo), *args], capture_output=True,
                            text=True, env=GIT_ENV)
    if result.returncode != 0:
        raise AssertionError(f"git {' '.join(args)} failed: {result.stderr}")
    return result.stdout.strip()


def commit(repo: Path, name: str, text: str, message: str) -> str:
    (repo / name).write_text(text, encoding="utf-8")
    git(repo, "add", name)
    git(repo, "commit", "-q", "-m", message)
    return git(repo, "rev-parse", "HEAD")


class FakeGitHub:
    """The REST surface pr_janitor is allowed to touch, with call recording."""

    def __init__(self, pulls: list[dict]):
        self.pulls = {int(p["number"]): dict(p, state="open") for p in pulls}
        self.comments: dict[int, dict[int, str]] = {}
        self.calls: list[tuple[str, str]] = []
        self.fail_on: set[tuple[str, str]] = set()
        self._next_comment_id = 9000

    def api(self, path, *, method=None, payload=None, paginate=False,
            mutation=False, idempotent=False, absolute=False):
        verb = method or "GET"
        self.calls.append((verb, path))
        if (verb, path) in self.fail_on:
            raise LayerError(f"gh api {path} failed: 502 Bad Gateway")

        if path.startswith("pulls?state=open"):
            return [{"number": number, "head": pull["head"]}
                    for number, pull in sorted(self.pulls.items())
                    if pull["state"] == "open"]

        match = re.fullmatch(r"pulls/(\d+)", path)
        if match and verb == "PATCH":
            number = int(match.group(1))
            assert payload == {"state": "closed"}, payload
            self.pulls[number]["state"] = "closed"
            return {"number": number, "state": "closed"}

        match = re.fullmatch(r"issues/(\d+)/comments", path)
        if match and verb == "GET":
            number = int(match.group(1))
            return [{"id": cid, "body": body}
                    for cid, body in self.comments.get(number, {}).items()]
        if match and verb == "POST":
            number = int(match.group(1))
            self._next_comment_id += 1
            self.comments.setdefault(number, {})[self._next_comment_id] = payload["body"]
            return {"id": self._next_comment_id}

        match = re.fullmatch(r"issues/comments/(\d+)", path)
        if match and verb == "PATCH":
            cid = int(match.group(1))
            for bodies in self.comments.values():
                if cid in bodies:
                    bodies[cid] = payload["body"]
                    return {"id": cid}
            raise AssertionError(f"patching an unknown comment {cid}")

        raise AssertionError(f"pr_janitor made an unexpected API call: {verb} {path}")

    # --- assertions the tests read ---

    def marker_comments(self, number: int) -> list[str]:
        return [body for body in self.comments.get(number, {}).values()
                if pr_janitor.MARKER in body]

    def state_changing_calls(self) -> list[tuple[str, str]]:
        return [call for call in self.calls if call[0] in ("PATCH", "POST", "PUT", "DELETE")]


class PrJanitorTestCase(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self._tmp.cleanup)
        self.root = Path(self._tmp.name)
        self.repo = self.root / "checkout"
        (self.repo / "local" / "bin").mkdir(parents=True)
        git(self.repo, "init", "-q")
        git(self.repo, "config", "user.email", "janitor@example.invalid")
        git(self.repo, "config", "user.name", "janitor test")

        self.sha_a = commit(self.repo, "a.txt", "a\n", "A")
        git(self.repo, "branch", "-M", "main")

        # (1) work that landed on main: head is reachable, three-dot diff empty
        git(self.repo, "checkout", "-q", "-b", "issue-329-landed")
        self.sha_landed = commit(self.repo, "b.txt", "b\n", "B")
        git(self.repo, "checkout", "-q", "main")
        git(self.repo, "merge", "-q", "--no-ff", "-m", "merge issue-329", "issue-329-landed")
        self.sha_carrier = git(self.repo, "rev-parse", "HEAD")

        # (2) live work: nonempty diff, not reachable
        git(self.repo, "checkout", "-q", "-b", "issue-342-live", "main")
        self.sha_live = commit(self.repo, "c.txt", "c\n", "C")

        # (3) empty net diff but never merged: condition 1 alone
        git(self.repo, "checkout", "-q", "-b", "issue-400-noop", "main")
        commit(self.repo, "d.txt", "d\n", "add d")
        git(self.repo, "rm", "-q", "d.txt")
        git(self.repo, "commit", "-q", "-m", "remove d again")
        self.sha_noop = git(self.repo, "rev-parse", "HEAD")

        git(self.repo, "checkout", "-q", "main")
        git(self.repo, "update-ref", "refs/remotes/github/main", "main")
        self.sha_main = git(self.repo, "rev-parse", "main")

        self.ledger = self.root / "closures.jsonl"
        patcher = mock.patch.object(pr_janitor, "ledger_path", lambda: self.ledger)
        patcher.start()
        self.addCleanup(patcher.stop)

    def run_pass(self, fake: FakeGitHub, *extra: str) -> int:
        self.stdout = io.StringIO()
        with mock.patch.object(pr_janitor.gh_common, "api", fake.api), \
                contextlib.redirect_stdout(self.stdout):
            return pr_janitor.main(["--repo-root", str(self.repo), "--no-fetch",
                                    "--no-event", *extra])

    def ledger_rows(self) -> list[dict]:
        if not self.ledger.exists():
            return []
        return [json.loads(line) for line in
                self.ledger.read_text(encoding="utf-8").splitlines() if line.strip()]

    def pulls(self) -> list[dict]:
        return [
            {"number": 329, "head": {"sha": self.sha_landed, "ref": "issue-329-landed"}},
            {"number": 342, "head": {"sha": self.sha_live, "ref": "issue-342-live"}},
            {"number": 400, "head": {"sha": self.sha_noop, "ref": "issue-400-noop"}},
        ]


class TestDecision(PrJanitorTestCase):
    def test_should_close_requires_both_conditions(self) -> None:
        self.assertTrue(pr_janitor.should_close(True, True))
        self.assertFalse(pr_janitor.should_close(True, False))
        self.assertFalse(pr_janitor.should_close(False, True))
        self.assertFalse(pr_janitor.should_close(False, False))

    def test_git_conditions_on_a_real_repository(self) -> None:
        base = "github/main"
        self.assertTrue(pr_janitor.diff_is_empty(self.repo, base, self.sha_landed))
        self.assertTrue(pr_janitor.head_is_reachable(self.repo, base, self.sha_landed))

        self.assertFalse(pr_janitor.diff_is_empty(self.repo, base, self.sha_live))
        self.assertFalse(pr_janitor.head_is_reachable(self.repo, base, self.sha_live))

        # Empty three-dot diff, never merged: condition 1 alone must not close.
        self.assertTrue(pr_janitor.diff_is_empty(self.repo, base, self.sha_noop))
        self.assertFalse(pr_janitor.head_is_reachable(self.repo, base, self.sha_noop))

    def test_carrier_is_the_commit_on_main_that_took_the_work(self) -> None:
        self.assertEqual(
            pr_janitor.carrier_commit(self.repo, "github/main", self.sha_landed),
            self.sha_carrier)

    def test_a_git_failure_is_raised_not_read_as_empty(self) -> None:
        with self.assertRaises(LayerError):
            pr_janitor.diff_is_empty(self.repo, "github/main", "0" * 40)


class TestPass(PrJanitorTestCase):
    def test_only_the_superseded_pr_is_closed(self) -> None:
        fake = FakeGitHub(self.pulls())
        self.assertEqual(self.run_pass(fake), 0)
        self.assertEqual(fake.pulls[329]["state"], "closed")
        self.assertEqual(fake.pulls[342]["state"], "open")
        self.assertEqual(fake.pulls[400]["state"], "open",
                         "an empty diff alone must never close a PR")

    def test_the_marker_comment_is_posted_once(self) -> None:
        fake = FakeGitHub(self.pulls())
        self.run_pass(fake)
        self.assertEqual(len(fake.marker_comments(329)), 1)
        body = fake.marker_comments(329)[0]
        self.assertIn(self.sha_landed, body)
        self.assertIn(self.sha_main, body)
        self.assertIn(self.sha_carrier, body)
        self.assertIn("git diff --quiet", body)
        self.assertIn("merge-base --is-ancestor", body)
        self.assertEqual(fake.marker_comments(342), [])

        # A second pass over the same (still open) PR updates, never re-posts.
        fake.pulls[329]["state"] = "open"
        posts = [call for call in fake.calls if call == ("POST", "issues/329/comments")]
        self.run_pass(fake)
        posts_after = [call for call in fake.calls if call == ("POST", "issues/329/comments")]
        self.assertEqual(len(posts), len(posts_after), "the marker comment was re-posted")
        self.assertEqual(len(fake.marker_comments(329)), 1)

    def test_the_only_state_change_is_a_patch_on_the_pulls_endpoint(self) -> None:
        fake = FakeGitHub(self.pulls())
        self.run_pass(fake)
        patches = [call for call in fake.state_changing_calls() if call[0] == "PATCH"]
        self.assertIn(("PATCH", "pulls/329"), patches)
        for verb, path in fake.calls:
            self.assertFalse(re.fullmatch(r"issues/\d+", path) and verb == "PATCH",
                             f"pr_janitor must never PATCH an issue ({verb} {path})")

    def test_closures_are_recorded_in_the_ledger(self) -> None:
        fake = FakeGitHub(self.pulls())
        self.run_pass(fake)
        rows = self.ledger_rows()
        self.assertEqual([row["pr"] for row in rows], [329])
        row = rows[0]
        self.assertEqual(row["action"], "closed-superseded")
        self.assertTrue(row["diff_empty"])
        self.assertTrue(row["reachable"])
        self.assertEqual(row["head"], self.sha_landed)
        self.assertEqual(row["carrier"], self.sha_carrier)

    def test_dry_run_changes_nothing(self) -> None:
        fake = FakeGitHub(self.pulls())
        self.assertEqual(self.run_pass(fake, "--dry-run"), 0)
        self.assertEqual(fake.pulls[329]["state"], "open")
        self.assertEqual(fake.state_changing_calls(), [])
        self.assertEqual(self.ledger_rows(), [])

    def test_a_github_failure_is_reported_not_converted_into_success(self) -> None:
        fake = FakeGitHub(self.pulls())
        fake.fail_on.add(("PATCH", "pulls/329"))
        self.assertEqual(self.run_pass(fake), 1, "a failed closure must exit nonzero")
        self.assertEqual(fake.pulls[329]["state"], "open")
        self.assertEqual(self.ledger_rows(), [],
                         "a PR that did not close must not be recorded as closed")

    def test_a_head_missing_from_the_object_store_is_an_error_not_a_closure(self) -> None:
        fake = FakeGitHub([{"number": 501, "head": {"sha": "0" * 40, "ref": "gone"}}])
        self.assertEqual(self.run_pass(fake), 1)
        self.assertEqual(fake.state_changing_calls(), [])

    def test_pr_filter_limits_the_pass(self) -> None:
        fake = FakeGitHub(self.pulls())
        self.assertEqual(self.run_pass(fake, "--pr", "342"), 0)
        self.assertEqual(fake.pulls[329]["state"], "open")
        self.assertEqual(fake.state_changing_calls(), [])

    def test_report_names_every_examined_pr(self) -> None:
        fake = FakeGitHub(self.pulls())
        report = self.root / "report.txt"
        self.run_pass(fake, "--report", str(report))
        text = report.read_text(encoding="utf-8")
        self.assertIn("3 open PR(s) examined, 1 superseded", text)
        self.assertIn("PR 329 closed", text)


if __name__ == "__main__":
    unittest.main()
