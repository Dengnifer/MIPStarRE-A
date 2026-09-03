#!/usr/bin/env python3
"""Regression tests for the GitHub-native workflow layer under ``local/bin``.

Issue 0007 replaced the ``issues/`` and ``prs/`` registries with GitHub records:
commit statuses on the exact head SHA, marker-keyed PR comments, one COMMENT
review per head, and a REST merge behind the exact-SHA guard
(``local/bin/gh_common.py:1-25``).  Those paths used to be untestable because
they were file writes; now they are ``gh api`` calls, so the suite pins them by
standing a fake ``gh`` in front of the layer.

The fake is a small Python script this file writes into a tempdir and points
``MIPSTARRE_GH`` at (the override read at ``gh_common.py:57-67``).  It logs
argv+stdin to a spool and answers from a canned route table, so every test here
runs offline, needs no ``gh`` installed, and asserts on the *wire* contract —
the route, the method and the JSON payload — rather than on a mock's call list.
An unmatched route fails the call: a test that forgets to declare one sees it.

Coverage mirrors the layer's failure modes, one test each: status reduction and
posting, comment/review idempotency and post-failure adoption, the merge
topology check, label validation and key-marker adoption, the ``pr_merge.py``
gate ladder (fail-closed on missing CI evidence and on an adverse verdict), the
audit snapshot, and a hygiene check that no live tool still reaches for the
retired registry trees.
"""

from __future__ import annotations

import ast
import io
import json
import os
import re
import subprocess
import sys
import tempfile
import tokenize
import unittest
from pathlib import Path
from unittest import mock

REPO_ROOT = Path(__file__).resolve().parents[2]
LOCAL_BIN = REPO_ROOT / "local" / "bin"
sys.path.insert(0, str(LOCAL_BIN))

import gh_common  # noqa: E402
import pr_merge  # noqa: E402
from wf_util import LayerError  # noqa: E402

#: Fixed slug so no test depends on the machine's git remotes (gh_common.py:70-86).
REPO = "Dengnifer/MIPStarRE-A"
HEAD = "a" * 40
BASE_SHA = "b" * 40
MERGE_SHA = "c" * 40

#: The fake ``gh``.  Kept as source text rather than a checked-in helper script:
#: it exists only for this suite, and writing it per test keeps the spool, the
#: route table and the binary in one disposable tempdir.
FAKE_GH = '''#!/usr/bin/env python3
"""Stand-in for the gh CLI: log every call, answer from a canned route table."""
import json
import os
import re
import sys

argv = sys.argv[1:]
method = argv[argv.index("-X") + 1] if "-X" in argv else "GET"
path = argv[1] if len(argv) > 1 else ""
rel = re.sub(r"^repos/[^/]+/[^/]+/", "", path)
stdin = sys.stdin.read() if "--input" in argv else ""
spool = os.environ["MIPSTARRE_FAKE_GH_SPOOL"]
with open(spool, "a", encoding="utf-8") as handle:
    handle.write(json.dumps({"argv": argv, "method": method, "path": path,
                             "rel": rel, "stdin": stdin}) + "\\n")

with open(os.environ["MIPSTARRE_FAKE_GH_ROUTES"], encoding="utf-8") as handle:
    routes = json.load(handle)
state_path = spool + ".state"
used = {}
if os.path.exists(state_path):
    with open(state_path, encoding="utf-8") as handle:
        used = json.load(handle)

for index, rule in enumerate(routes):
    key = str(index)
    if rule.get("method", "GET") != method or not re.search(rule["path"], rel):
        continue
    if rule.get("once") and used.get(key):
        continue
    used[key] = used.get(key, 0) + 1
    with open(state_path, "w", encoding="utf-8") as handle:
        json.dump(used, handle)
    if rule.get("fail"):
        sys.stderr.write(rule.get("stderr") or "fake gh: canned refusal\\n")
        raise SystemExit(1)
    if "body" in rule:
        sys.stdout.write(json.dumps(rule["body"]))
    raise SystemExit(0)

sys.stderr.write("fake gh: no route for %s %s\\n" % (method, rel))
raise SystemExit(1)
'''


class FakeGitHub:
    """A fake ``gh`` binary plus its route table, all inside one tempdir."""

    def __init__(self, tmp: Path) -> None:
        self.tmp = tmp
        self.binary = tmp / "gh"
        self.binary.write_text(FAKE_GH, encoding="utf-8")
        self.binary.chmod(0o755)
        self.spool = tmp / "gh-calls.jsonl"
        self.routes_path = tmp / "gh-routes.json"
        self.routes: list[dict] = []
        self._flush()

    def route(self, path: str, body=None, *, method: str = "GET",
              fail: bool = False, once: bool = False) -> "FakeGitHub":
        """Declare one reply.  *path* is a regex against the repo-relative route.

        Rules match in declaration order, so a ``once=True`` rule in front of a
        broader one models "state changed between two reads" — exactly the
        adoption paths at ``gh_common.py:216-224`` and ``:336-343``.
        """
        rule: dict = {"path": path, "method": method}
        if body is not None:
            rule["body"] = body
        if fail:
            rule["fail"] = True
        if once:
            rule["once"] = True
        self.routes.append(rule)
        self._flush()
        return self

    def reset(self) -> None:
        """Forget the routes and the call log; used between gate scenarios."""
        self.routes = []
        self._flush()
        for path in (self.spool, Path(str(self.spool) + ".state")):
            if path.exists():
                path.unlink()

    def env(self) -> dict[str, str]:
        return {"MIPSTARRE_GH": str(self.binary),
                "MIPSTARRE_GITHUB_REPO": REPO,
                "MIPSTARRE_FAKE_GH_SPOOL": str(self.spool),
                "MIPSTARRE_FAKE_GH_ROUTES": str(self.routes_path)}

    def calls(self) -> list[dict]:
        if not self.spool.exists():
            return []
        return [json.loads(line) for line in
                self.spool.read_text(encoding="utf-8").splitlines() if line]

    def payloads(self, method: str, pattern: str) -> list[dict]:
        """Decoded request bodies of the calls matching *method* and *pattern*."""
        return [json.loads(call["stdin"]) for call in self.calls()
                if call["method"] == method and re.search(pattern, call["rel"])
                and call["stdin"]]

    def _flush(self) -> None:
        self.routes_path.write_text(json.dumps(self.routes), encoding="utf-8")


class LayerTestCase(unittest.TestCase):
    """Every test gets a fresh tempdir, a fresh fake ``gh`` and a clean spool."""

    def setUp(self) -> None:
        holder = tempfile.TemporaryDirectory()
        self.addCleanup(holder.cleanup)
        self.tmp = Path(holder.name)
        self.gh = FakeGitHub(self.tmp)
        patcher = mock.patch.dict(os.environ, self.gh.env())
        patcher.start()
        self.addCleanup(patcher.stop)


class GitHubLayerTests(LayerTestCase):
    """``gh_common`` against the wire: routes, payloads, idempotency, adoption."""

    def test_latest_statuses_keeps_the_newest_row_per_context(self) -> None:
        self.gh.route(r"^commits/[0-9a-f]+/statuses", [
            {"context": "local-ci/build", "state": "success",
             "description": "newest", "created_at": "2026-01-02T00:00:00Z"},
            {"context": "local-ci/build", "state": "failure",
             "description": "older", "created_at": "2026-01-01T00:00:00Z"},
            {"context": "local-review/summary", "state": "failure",
             "description": "adverse", "created_at": "2026-01-01T12:00:00Z"},
        ])
        latest = gh_common.latest_statuses(HEAD)
        self.assertEqual(sorted(latest), ["local-ci/build", "local-review/summary"])
        self.assertEqual(latest["local-ci/build"]["state"], "success")
        self.assertEqual(latest["local-ci/build"]["description"], "newest")
        self.assertEqual(latest["local-review/summary"]["state"], "failure")
        self.assertIn(f"commits/{HEAD}/statuses", self.gh.calls()[0]["rel"])

    def test_post_status_validates_state_and_binds_to_the_exact_sha(self) -> None:
        with self.assertRaises(LayerError):
            gh_common.post_status(HEAD, "local-ci/build", "green")
        self.assertEqual(self.gh.calls(), [], "an invalid state must not reach gh")
        self.gh.route(r"^statuses/", {"id": 1}, method="POST")
        gh_common.post_status(HEAD, "local-ci/build", "success", description="x" * 300)
        call = self.gh.calls()[0]
        self.assertEqual(call["path"], f"repos/{REPO}/statuses/{HEAD}")
        payload = json.loads(call["stdin"])
        self.assertEqual(payload["state"], "success")
        self.assertEqual(payload["context"], "local-ci/build")
        self.assertEqual(len(payload["description"]), 140)

    def test_ensure_pr_comment_patches_posts_and_adopts(self) -> None:
        marker = "<!-- mipstarre-ci-manifest pr=7 -->"
        with self.subTest("marker present -> PATCH in place"):
            self.gh.route(r"^issues/7/comments", [{"id": 11, "body": marker + "\nold"}])
            self.gh.route(r"^issues/comments/11", {"id": 11}, method="PATCH")
            self.assertEqual(gh_common.ensure_pr_comment(7, marker, "new"), 11)
            self.assertEqual(len(self.gh.payloads("PATCH", r"^issues/comments/11")), 1)
            self.assertEqual(self.gh.payloads("POST", r"^issues/7/comments"), [])
        with self.subTest("marker absent -> POST once"):
            self.gh.reset()
            self.gh.route(r"^issues/7/comments", [])
            self.gh.route(r"^issues/7/comments", {"id": 22}, method="POST")
            self.assertEqual(gh_common.ensure_pr_comment(7, marker, "body"), 22)
            posted = self.gh.payloads("POST", r"^issues/7/comments")
            self.assertEqual(len(posted), 1)
            self.assertTrue(posted[0]["body"].startswith(marker))
        with self.subTest("ambiguous POST -> adopt, never re-post"):
            self.gh.reset()
            self.gh.route(r"^issues/7/comments", [], once=True)
            self.gh.route(r"^issues/7/comments", fail=True, method="POST")
            self.gh.route(r"^issues/7/comments", [{"id": 33, "body": marker}])
            self.assertEqual(gh_common.ensure_pr_comment(7, marker, "body"), 33)
            self.assertEqual(len(self.gh.payloads("POST", r"^issues/7/comments")), 1)

    def test_post_review_is_marker_idempotent_and_posts_a_comment_review(self) -> None:
        marker = f"<!-- mipstarre-review pr=7 head={HEAD} -->"
        with self.subTest("same commit id and marker -> skip"):
            self.gh.route(r"^pulls/7/reviews",
                          [{"id": 5, "commit_id": HEAD, "body": marker + "\nVERDICT: APPROVED"}])
            self.assertEqual(gh_common.post_review(7, HEAD, marker, "again"), "exists")
            self.assertEqual(self.gh.payloads("POST", r"^pulls/7/reviews"), [])
        with self.subTest("absent -> one COMMENT review bound to the commit"):
            self.gh.reset()
            # A review of an earlier head must not satisfy the marker check.
            self.gh.route(r"^pulls/7/reviews", [{"id": 4, "commit_id": BASE_SHA, "body": marker}])
            self.gh.route(r"^pulls/7/reviews", {"id": 99}, method="POST")
            self.assertEqual(gh_common.post_review(7, HEAD, marker, "VERDICT: APPROVED"), "99")
            payload = self.gh.payloads("POST", r"^pulls/7/reviews")[0]
            self.assertEqual(payload["event"], "COMMENT")
            self.assertEqual(payload["commit_id"], HEAD)
            self.assertTrue(payload["body"].startswith(marker))

    def test_merge_pr_requires_a_merged_pr_and_the_frozen_head_as_second_parent(self) -> None:
        def arm(pr: dict, parents: list[str]) -> None:
            self.gh.route(r"^pulls/7/merge", {"merged": True}, method="PUT")
            self.gh.route(r"^pulls/7$", pr)
            self.gh.route(r"^commits/", {"parents": [{"sha": sha} for sha in parents]})

        merged = {"number": 7, "state": "closed", "merged": True,
                  "merge_commit_sha": MERGE_SHA, "head": {"sha": HEAD}}
        with self.subTest("read-back says unmerged"):
            arm({"number": 7, "state": "open", "merged": False, "head": {"sha": HEAD}}, [])
            with self.assertRaisesRegex(LayerError, "did not merge"):
                gh_common.merge_pr(7, HEAD)
        with self.subTest("merge commit does not carry the frozen head"):
            self.gh.reset()
            arm(merged, [BASE_SHA, "d" * 40])
            with self.assertRaisesRegex(LayerError, "someone else merged"):
                gh_common.merge_pr(7, HEAD)
        with self.subTest("correct topology"):
            self.gh.reset()
            arm(merged, [BASE_SHA, HEAD])
            self.assertEqual(gh_common.merge_pr(7, HEAD), MERGE_SHA)
            self.assertEqual(self.gh.payloads("PUT", r"^pulls/7/merge"),
                             [{"sha": HEAD, "merge_method": "merge"}])

    def test_issue_create_rejects_unknown_labels_and_adopts_by_key(self) -> None:
        with self.subTest("unknown label is named, nothing is created"):
            self.gh.route(r"^labels", [{"name": "formalization"}])
            with self.assertRaisesRegex(LayerError, "no-such-label"):
                gh_common.issue_create("Title", "body", labels=("no-such-label",))
            self.assertEqual(self.gh.payloads("POST", r"^issues$"), [])
        with self.subTest("ambiguous create -> adopt the keyed issue"):
            self.gh.reset()
            marker = "<!-- mipstarre-issue-key: qpbt-pauli -->"
            self.gh.route(r"^labels", [{"name": "formalization"}])
            self.gh.route(r"^issues\?state=all", [], once=True)
            self.gh.route(r"^issues$", fail=True, method="POST")
            self.gh.route(r"^issues\?state=all", [
                {"number": 9, "body": marker, "pull_request": {"url": "x"}},
                {"number": 42, "body": marker + "\nbody"},
            ])
            number = gh_common.issue_create("Title", "body", labels=("formalization",),
                                            key="qpbt-pauli")
            self.assertEqual(number, 42, "a pull request row must never be adopted")
            self.assertEqual(len(self.gh.payloads("POST", r"^issues$")), 1)

    def test_snapshot_writes_three_files_and_drops_pull_requests(self) -> None:
        self.gh.route(r"^issues\?state=open", [
            {"number": 3, "title": "open issue"},
            {"number": 4, "title": "a PR", "pull_request": {"url": "x"}},
        ])
        self.gh.route(r"^pulls\?state=open", [{"number": 7, "title": "the PR"}])
        out = self.tmp / "snapshot"
        gh_common.snapshot(out)
        issues = json.loads((out / "open-issues.json").read_text(encoding="utf-8"))
        pulls = json.loads((out / "open-pulls.json").read_text(encoding="utf-8"))
        meta = json.loads((out / "metadata.json").read_text(encoding="utf-8"))
        self.assertEqual([row["number"] for row in issues], [3])
        self.assertEqual([row["number"] for row in pulls], [7])
        self.assertEqual((meta["repo"], meta["open_issues"], meta["open_pulls"]), (REPO, 1, 1))
        # atomic_write leaves no ".<name>.*.tmp" droppings behind (wf_util.py:180-204).
        self.assertEqual(sorted(p.name for p in out.iterdir()),
                         ["metadata.json", "open-issues.json", "open-pulls.json"])


# --------------------------------------------------------------------------
# pr_merge.py — the gate ladder that stands in for branch protection
# --------------------------------------------------------------------------

def _git(repo: Path, *args: str) -> str:
    proc = subprocess.run(["git", *args], cwd=str(repo), capture_output=True, text=True)
    if proc.returncode != 0:
        raise AssertionError(f"git {' '.join(args)} failed: {proc.stderr.strip()}")
    return proc.stdout.strip()


class MergeGateTests(LayerTestCase):
    """``pr_merge.py --check-only`` must refuse on thin evidence and pass on full.

    Gate 2 reads a real worktree (pr_merge.py:112-135), so the scenarios run
    against a throwaway repository whose branch tip *is* the PR head SHA; the
    other gates read GitHub through the fake.  ``--check-only`` stops before the
    merge, which the assertions confirm by the absence of a PUT.
    """

    BRANCH = "issue-0007-lean"
    REVIEW_BODY = ("VERDICT: APPROVED (code=clean, prose=clean)\n\n"
                   "## Findings\n\n- [x] nothing outstanding\n")

    def setUp(self) -> None:
        super().setUp()
        self.repo = self.tmp / "repo"
        self.repo.mkdir()
        templates = self.tmp / "no-templates"
        templates.mkdir()
        _git(self.repo, "init", "-q", f"--template={templates}")
        _git(self.repo, "symbolic-ref", "HEAD", "refs/heads/main")
        _git(self.repo, "config", "user.email", "tests@example.invalid")
        _git(self.repo, "config", "user.name", "MIPStarRE tests")
        _git(self.repo, "config", "commit.gpgsign", "false")
        (self.repo / "README.md").write_text("base\n", encoding="utf-8")
        _git(self.repo, "add", "-A")
        _git(self.repo, "commit", "-q", "--no-verify", "-m", "base commit")
        _git(self.repo, "checkout", "-q", "-b", self.BRANCH)
        (self.repo / "README.md").write_text("work\n", encoding="utf-8")
        _git(self.repo, "commit", "-q", "--no-verify", "-am", "port the workflow layer")
        self.head = _git(self.repo, "rev-parse", "HEAD")
        _git(self.repo, "checkout", "-q", "main")
        # Gate 2b fetches github/<base> and requires the head to contain its
        # tip; a self-remote satisfies both without any network.
        _git(self.repo, "remote", "add", "github", str(self.repo))
        _git(self.repo, "fetch", "-q", "github", "main")

    def _arm(self, *, missing: tuple[str, ...] = (), review_state: str = "success") -> None:
        """Route the PR, its statuses and its one marker review for a gate run."""
        rows = [{"context": context, "state": "success", "description": "ok",
                 "created_at": "2026-01-01T00:00:00Z"}
                for context in pr_merge.CI_CONTEXTS if context not in missing]
        rows.append({"context": pr_merge.REVIEW_CONTEXT, "state": review_state,
                     "description": "review", "created_at": "2026-01-01T01:00:00Z"})
        marker = f"<!-- mipstarre-review pr=7 head={self.head} -->"
        self.gh.route(r"^pulls/7$", {
            "number": 7, "state": "open", "draft": False, "merged": False,
            "title": "GitHub-native records", "body": "No auto-closing footer here.",
            "head": {"sha": self.head, "ref": self.BRANCH}, "base": {"ref": "main"}})
        self.gh.route(r"^commits/[0-9a-f]+/statuses", rows)
        self.gh.route(r"^pulls/7/reviews", [
            {"id": 5, "state": "COMMENTED", "commit_id": self.head,
             "body": marker + "\n" + self.REVIEW_BODY, "user": {"login": "Dengnifer"}}])

    def _check_only(self) -> subprocess.CompletedProcess:
        env = dict(os.environ, MIPSTARRE_CACHE_ROOT=str(self.tmp / "cache"))
        return subprocess.run(
            [sys.executable, str(LOCAL_BIN / "pr_merge.py"), "7", "--check-only",
             "--repo-root", str(self.repo)],
            capture_output=True, text=True, env=env)

    def test_gate_ladder_blocks_on_thin_evidence_and_passes_on_full(self) -> None:
        with self.subTest("a missing local-ci context is a block, never a pass"):
            self._arm(missing=("local-ci/statement-origin",))
            result = self._check_only()
            self.assertEqual(result.returncode, 1, result.stderr)
            self.assertIn("gate 3 (CI)", result.stderr)
            self.assertIn("local-ci/statement-origin: MISSING", result.stderr)
        with self.subTest("adverse local-review/summary without adjudication"):
            self.gh.reset()
            self._arm(review_state="failure")
            result = self._check_only()
            self.assertEqual(result.returncode, 1, result.stderr)
            self.assertIn("gate 4 (review)", result.stderr)
            self.assertEqual(self.gh.payloads("GET", r"^issues/7/comments"), [],
                             "the adjudication path is only read under --adjudicated")
        with self.subTest("all statuses green plus a clean marker review"):
            self.gh.reset()
            self._arm()
            result = self._check_only()
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn("gate passed: PR #7", result.stdout)
            self.assertIn("gate 5 no CHANGES_REQUESTED review", result.stdout)
            self.assertEqual([c for c in self.gh.calls() if c["method"] == "PUT"], [],
                             "--check-only must stop before the merge")
        with self.subTest("fix-prefixed commits are reported, never a gate"):
            os.environ["MIPSTARRE_FIX_CAP"] = "5"  # the retired knob must be inert
            self.addCleanup(os.environ.pop, "MIPSTARRE_FIX_CAP", None)
            _git(self.repo, "checkout", "-q", self.BRANCH)
            for number in range(6):
                _git(self.repo, "commit", "-q", "--no-verify", "--allow-empty",
                     "-m", f"[codex-review-fix] repair {number}")
            self.head = _git(self.repo, "rev-parse", "HEAD")
            _git(self.repo, "checkout", "-q", "main")
            self.gh.reset()
            self._arm()
            result = self._check_only()
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn("6 fix-prefixed commit(s)", result.stdout)

    def test_adjudication_validates_round_head_dispositions_and_issues(self) -> None:
        marker = f"<!-- mipstarre-review pr=7 head={self.head} -->"
        current = marker + "\nVERDICT: COMMENTED\n- [ ] F1 (changes) `x:1` — fix\n"
        reviews = [{"commit_id": self.head, "body": current}]
        for digit in "1234":
            sha = digit * 40
            reviews.append({"commit_id": sha,
                            "body": f"<!-- mipstarre-review pr=7 head={sha} -->"})
        statuses = {pr_merge.REVIEW_CONTEXT: {"state": "failure"}}
        comment = {"id": 9, "body": ("ADJUDICATION\nhead=" + self.head
                                      + "\n- [x] F1 — deferred to issue #24: follow-up")}

        with mock.patch.object(pr_merge.gh_common, "api",
                               side_effect=lambda path, **_: [comment] if path.endswith("comments")
                               else {"number": 24, "state": "open"}):
            deferred = pr_merge.check_review(7, self.head, reviews, statuses, adjudicated=True)
        self.assertEqual(deferred, {24})

        merge_base = _git(self.repo, "merge-base", "main", self.head)
        with mock.patch.object(pr_merge.gh_common, "open_sub_issues", return_value=[]):
            pr_merge.check_dependencies(self.repo, 7, "Closes #23", merge_base, self.head,
                                        deferred)
        with self.assertRaisesRegex(LayerError, "also closes deferred"):
            pr_merge.check_dependencies(self.repo, 7, "Closes #23", merge_base, self.head,
                                        {23})

        for bad_body in (comment["body"].replace("head=", "head ="),
                         "ADJUDICATION\nhead=" + self.head):
            with self.subTest(bad_body=bad_body), \
                    mock.patch.object(pr_merge.gh_common, "api",
                                      return_value=[dict(comment, body=bad_body)]):
                with self.assertRaisesRegex(LayerError, "exactly head="):
                    pr_merge.check_review(7, self.head, reviews, statuses, adjudicated=True)

        with mock.patch.object(pr_merge.gh_common, "api",
                               side_effect=([comment], {"number": 24, "state": "closed"})):
            with self.assertRaisesRegex(LayerError, "open tracked issue"):
                pr_merge.check_review(7, self.head, reviews, statuses, adjudicated=True)

        with self.assertRaisesRegex(LayerError, "round 5"):
            pr_merge.check_review(7, self.head, reviews[:-1], statuses, adjudicated=True)


# --------------------------------------------------------------------------
# Repository hygiene — the retired trees stay retired
# --------------------------------------------------------------------------

#: A path segment into the archived registries.  The REST API also speaks
#: ``issues/...``, so the two are told apart by what follows: a route always
#: continues with an f-string field (``issues/{number}/comments``) or with
#: ``comments/{id}`` (gh_common.py:213), while a tree reference continues with a
#: literal id, glob or filename.
_TREE_PATH_RE = re.compile(r"(?<![\w.-])(?:issues|prs)/")
_REST_ROUTE_RE = re.compile(r"^issues/(?:\{|comments/\{)")

#: The other shape a tree reference takes: a join onto the repository root.
_TREE_JOIN_RE = re.compile(
    r"""(?:\$\{?ROOT\}?|\$\{?REPO_ROOT\}?|repo_root|REPO_ROOT)\s*/\s*["']?(?:issues|prs)\b""")


def _active_source(path: Path) -> str:
    """The file's live code: comments and docstrings blanked, line numbers kept.

    Every surviving mention of the registries is historical narration ("Pre-0007
    this wrote ``prs/<id>-<slug>/pr.md``", issue_new.py:2-5), so a grep over raw
    text cannot express the rule.  Python comments come from ``tokenize`` (a
    ``#`` inside a string is not a comment token) and docstrings from ``ast``;
    shell keeps only its non-comment lines.
    """
    text = path.read_text(encoding="utf-8")
    if path.suffix == ".sh":
        return "\n".join("" if line.lstrip().startswith("#") else line
                         for line in text.splitlines())
    lines = text.splitlines()
    docstring_lines: set[int] = set()
    for node in ast.walk(ast.parse(text)):
        if isinstance(node, (ast.Module, ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef)):
            if ast.get_docstring(node, clean=False) is not None:
                first = node.body[0]
                docstring_lines.update(range(first.lineno, (first.end_lineno or first.lineno) + 1))
    for token in tokenize.generate_tokens(io.StringIO(text).readline):
        if token.type == tokenize.COMMENT:
            row, column = token.start
            lines[row - 1] = lines[row - 1][:column]
    return "\n".join("" if number + 1 in docstring_lines else line
                     for number, line in enumerate(lines))


class RegistryHygieneTests(unittest.TestCase):
    def test_no_live_tool_reaches_for_the_retired_issue_or_pr_trees(self) -> None:
        """The registries are archived read-only; nothing in ``local/bin`` reads them.

        A single surviving path join is enough to reintroduce the split brain
        issue 0007 removed — a tool that consults a stale local record instead of
        GitHub fails open rather than closed.
        """
        offenders: list[str] = []
        tools = sorted(p for p in LOCAL_BIN.iterdir() if p.suffix in (".py", ".sh"))
        self.assertGreater(len(tools), 10, "the local/bin tool set did not load")
        for tool in tools:
            source = _active_source(tool)
            for number, line in enumerate(source.splitlines(), start=1):
                for hit in _TREE_PATH_RE.finditer(line):
                    if not _REST_ROUTE_RE.match(line[hit.start():]):
                        offenders.append(f"{tool.name}:{number}: {line.strip()}")
                if _TREE_JOIN_RE.search(line):
                    offenders.append(f"{tool.name}:{number}: {line.strip()}")
        self.assertEqual(offenders, [], "live registry-tree references:\n" + "\n".join(offenders))


if __name__ == "__main__":
    unittest.main()
