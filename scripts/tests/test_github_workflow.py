#!/usr/bin/env python3
"""Deterministic regression tests for the GitHub-authoritative local workflow."""

from __future__ import annotations

import argparse
import contextlib
import io
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


REPO_ROOT = Path(__file__).resolve().parents[2]
BIN_DIR = REPO_ROOT / "local" / "bin"
sys.path.insert(0, str(BIN_DIR))

import github_api  # noqa: E402
import issue_close  # noqa: E402
import issue_new  # noqa: E402
import pr_merge  # noqa: E402
import pr_open  # noqa: E402


FAKE_GH = r'''#!/usr/bin/env python3
import json
import os
import sys
import time
import urllib.parse

state_path = os.environ["FAKE_GH_STATE"]
with open(state_path, encoding="utf-8") as stream:
    state = json.load(stream)
args = sys.argv[1:]
stdin = sys.stdin.read() if "--input" in args else ""
payload = json.loads(stdin) if stdin.strip() else None
state.setdefault("calls", []).append({"args": args, "input": payload})


def save():
    temporary = state_path + ".tmp"
    with open(temporary, "w", encoding="utf-8") as stream:
        json.dump(state, stream)
    os.replace(temporary, state_path)


def emit(value):
    if value is not None:
        sys.stdout.write(json.dumps(value))
    save()
    raise SystemExit(0)


def fail(message, stdout=""):
    if stdout:
        os.write(1, stdout.encode("utf-8", errors="surrogatepass"))
    sys.stderr.write(message + "\n")
    save()
    raise SystemExit(1)


def option(name, default=""):
    try:
        return args[args.index(name) + 1]
    except (ValueError, IndexError):
        return default


def page(rows, query):
    values = urllib.parse.parse_qs(query)
    number = int(values.get("page", ["1"])[0])
    size = int(values.get("per_page", ["100"])[0])
    return rows[(number - 1) * size:number * size]


def next_number(key):
    rows = state.get(key, {})
    return max([int(value) for value in rows] + [0]) + 1


if args[:3] == ["pr", "merge", "--help"]:
    sys.stdout.write("usage: gh pr merge --merge --match-head-commit SHA\n")
    save()
    raise SystemExit(0)

if args[:2] == ["issue", "create"]:
    number = next_number("issues")
    body = option("--body")
    labels = []
    for index, value in enumerate(args):
        if value == "--label" and index + 1 < len(args):
            labels.append({"name": args[index + 1]})
    row = {
        "id": 1000 + number,
        "number": number,
        "title": option("--title"),
        "body": body,
        "state": "open",
        "state_reason": None,
        "labels": labels,
        "html_url": f"https://github.com/o/r/issues/{number}",
    }
    state.setdefault("issues", {})[str(number)] = row
    if state.pop("ambiguous_issue_create_once", False):
        fail("HTTP 503 Service Unavailable")
    save()
    sys.stdout.write(row["html_url"] + "\n")
    raise SystemExit(0)

if args[:2] == ["pr", "create"]:
    number = next_number("pulls")
    row = {
        "id": 2000 + number,
        "number": number,
        "title": option("--title"),
        "body": option("--body"),
        "state": "open",
        "draft": False,
        "mergeable": True,
        "head": {"ref": option("--head"), "sha": state.get("local_head", "a" * 40)},
        "base": {"ref": option("--base")},
        "labels": [],
        "commits": 1,
        "html_url": f"https://github.com/o/r/pull/{number}",
    }
    state.setdefault("pulls", {})[str(number)] = row
    state.setdefault("issues", {})[str(number)] = {
        **row,
        "pull_request": {"url": row["html_url"]},
    }
    if state.pop("ambiguous_pr_create_once", False):
        fail("HTTP 503 Service Unavailable")
    save()
    sys.stdout.write(row["html_url"] + "\n")
    raise SystemExit(0)

if args[:2] == ["pr", "merge"]:
    number = str(int(args[2]))
    row = state.setdefault("pulls", {}).get(number)
    if row is None:
        fail("HTTP 404 Not Found")
    row["merged"] = True
    row["state"] = "closed"
    row["merge_commit_sha"] = state.get("merge_sha", "b" * 40)
    emit({"merged": True})

if not args or args[0] != "api":
    fail("unsupported fake gh command")

method = option("--method", "GET").upper()
endpoint = args[3] if len(args) > 3 else ""
parsed = urllib.parse.urlsplit(endpoint)
path = parsed.path.strip("/")
parts = path.split("/")
if parts[:3] != ["repos", "o", "r"]:
    fail("HTTP 404 Not Found")
tail = parts[3:]
key = method + " " + "/".join(tail)

failure = state.setdefault("failures", {}).get(key)
if failure and int(failure.get("remaining", 0)) > 0:
    failure["remaining"] = int(failure["remaining"]) - 1
    stdout = str(failure.get("stdout", ""))
    fail(str(failure.get("message", "HTTP 500 Internal Server Error")), stdout)

if tail == ["slow"]:
    os.write(1, b"\xffpartial-output")
    sys.stdout.flush()
    time.sleep(5)
    emit({})

if not tail and method == "GET":
    emit(state.get("repo", {"id": 1, "full_name": "o/r"}))

if tail == ["labels"] and method == "GET":
    emit(page(state.get("labels", []), parsed.query))

if tail == ["issues"] and method == "GET":
    rows = list(state.get("issues", {}).values())
    wanted = urllib.parse.parse_qs(parsed.query).get("state", ["all"])[0]
    if wanted != "all":
        rows = [row for row in rows if row.get("state") == wanted]
    emit(page(rows, parsed.query))

if tail == ["pulls"] and method == "GET":
    rows = list(state.get("pulls", {}).values())
    values = urllib.parse.parse_qs(parsed.query)
    wanted = values.get("state", ["all"])[0]
    if wanted != "all":
        rows = [row for row in rows if row.get("state") == wanted]
    head = values.get("head", [""])[0].split(":", 1)[-1]
    if head:
        rows = [row for row in rows if row.get("head", {}).get("ref") == head]
    emit(page(rows, parsed.query))

if len(tail) == 2 and tail[0] == "issues":
    number = tail[1]
    row = state.setdefault("issues", {}).get(number)
    if row is None:
        fail("HTTP 404 Not Found")
    if method == "GET":
        emit(row)
    if method == "PATCH":
        row.update(payload or {})
        emit(row)

if len(tail) == 2 and tail[0] == "pulls":
    number = tail[1]
    row = state.setdefault("pulls", {}).get(number)
    if row is None:
        fail("HTTP 404 Not Found")
    if method == "GET":
        sequence = state.get("pull_head_sequence", [])
        count = int(state.get("pull_read_count", 0))
        if sequence:
            row["head"]["sha"] = sequence[min(count, len(sequence) - 1)]
            state["pull_read_count"] = count + 1
        emit(row)
    if method == "PATCH":
        row.update({key: value for key, value in (payload or {}).items() if key != "base"})
        if payload and "base" in payload:
            row["base"] = {"ref": payload["base"]}
        emit(row)

if len(tail) == 3 and tail[0] == "issues" and tail[2] == "comments":
    number = tail[1]
    comments = state.setdefault("comments", {}).setdefault(number, [])
    if method == "GET":
        emit(page(comments, parsed.query))
    if method == "POST":
        row = {
            "id": len(comments) + 1,
            "body": str((payload or {}).get("body", "")),
            "created_at": f"2026-01-01T00:00:{len(comments):02d}Z",
        }
        comments.append(row)
        if state.pop("corrupt_comment_response", False):
            emit({**row, "body": "corrupt response"})
        emit(row)

if len(tail) == 3 and tail[0] == "issues" and tail[2] == "sub_issues":
    number = tail[1]
    rows = state.setdefault("sub_issues", {}).setdefault(number, [])
    if method == "GET":
        emit(page(rows, parsed.query))
    if method == "POST":
        child_id = int((payload or {}).get("sub_issue_id"))
        child = next(
            row for row in state.get("issues", {}).values() if row.get("id") == child_id
        )
        rows.append(child)
        emit(child)

if len(tail) == 4 and tail[0] == "issues" and tail[2] == "labels":
    number, label = tail[1], urllib.parse.unquote(tail[3])
    row = state.setdefault("issues", {}).get(number)
    if row is None:
        fail("HTTP 404 Not Found")
    if method == "DELETE":
        row["labels"] = [
            item for item in row.get("labels", []) if item.get("name") != label
        ]
        emit(None)

if len(tail) == 3 and tail[0] == "issues" and tail[2] == "labels":
    number = tail[1]
    row = state.setdefault("pulls", {}).get(number)
    if row is None:
        fail("HTTP 404 Not Found")
    if method == "PUT":
        row["labels"] = [{"name": name} for name in (payload or {}).get("labels", [])]
        issue = state.setdefault("issues", {}).get(number)
        if issue is not None:
            issue["labels"] = row["labels"]
        emit(row["labels"])

if len(tail) == 3 and tail[0] == "pulls" and tail[2] == "commits":
    emit(page(state.setdefault("commits", {}).get(tail[1], []), parsed.query))

if len(tail) == 3 and tail[0] == "pulls" and tail[2] == "reviews":
    number = tail[1]
    reviews = state.setdefault("reviews", {}).setdefault(number, [])
    if method == "GET":
        emit(page(reviews, parsed.query))
    if method == "POST":
        event = str((payload or {}).get("event", ""))
        rejection = state.get("review_422")
        if event == "REQUEST_CHANGES" and rejection:
            state["review_422"] = ""
            fail("HTTP 422 " + rejection)
        row = {
            "id": len(reviews) + 1,
            "body": str((payload or {}).get("body", "")),
            "commit_id": str((payload or {}).get("commit_id", "")),
            "state": "CHANGES_REQUESTED" if event == "REQUEST_CHANGES" else "COMMENTED",
            "submitted_at": f"2026-01-01T00:00:{len(reviews):02d}Z",
        }
        reviews.append(row)
        if state.pop("corrupt_review_response", False):
            emit({**row, "commit_id": "0" * 40})
        emit(row)

if len(tail) == 3 and tail[0] == "commits" and tail[2] == "statuses":
    sha = tail[1]
    emit(page(state.setdefault("statuses", {}).get(sha, []), parsed.query))

if len(tail) == 2 and tail[0] == "statuses" and method == "POST":
    sha = tail[1]
    rows = state.setdefault("statuses", {}).setdefault(sha, [])
    row = {
        "id": len(rows) + 1,
        "sha": sha,
        "context": str((payload or {}).get("context", "")),
        "state": str((payload or {}).get("state", "")),
        "description": str((payload or {}).get("description", "")),
        "created_at": f"2026-01-01T00:00:{len(rows):02d}Z",
    }
    rows.append(row)
    if state.pop("ambiguous_status_once", False):
        fail("HTTP 503 Service Unavailable")
    if state.pop("corrupt_status_response", False):
        emit({**row, "context": "different/context"})
    emit(row)

fail("HTTP 404 unsupported fake endpoint " + key)
'''


def run_git(root: Path, *args: str) -> str:
    result = subprocess.run(
        ["git", "-C", str(root), *args],
        text=True,
        capture_output=True,
        check=False,
    )
    if result.returncode:
        raise AssertionError(result.stderr or result.stdout)
    return result.stdout.strip()


def issue_row(number: int, *, title: str = "Issue", body: str = "") -> dict:
    return {
        "id": 1000 + number,
        "number": number,
        "title": title,
        "body": body,
        "state": "open",
        "state_reason": None,
        "labels": [],
        "html_url": f"https://github.com/o/r/issues/{number}",
    }


def pull_row(number: int, sha: str, branch: str = "issue-7-test") -> dict:
    return {
        "id": 2000 + number,
        "number": number,
        "title": "Feature",
        "body": "Body",
        "state": "open",
        "draft": False,
        "mergeable": True,
        "mergeable_state": "clean",
        "head": {"ref": branch, "sha": sha},
        "base": {"ref": "main"},
        "labels": [],
        "commits": 1,
        "merged": False,
        "html_url": f"https://github.com/o/r/pull/{number}",
    }


class FakeGhCase(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.state_path = self.root / "fake-gh-state.json"
        self.gh_path = self.root / "gh"
        self.gh_path.write_text(FAKE_GH, encoding="utf-8")
        self.gh_path.chmod(0o755)
        self.write_state()
        self.environment = mock.patch.dict(
            os.environ,
            {
                "MIPSTARRE_GH": str(self.gh_path),
                "MIPSTARRE_GITHUB_REPO": "o/r",
                "MIPSTARRE_GH_RETRIES": "2",
                "MIPSTARRE_GH_RETRY_DELAY": "0",
                "FAKE_GH_STATE": str(self.state_path),
            },
        )
        self.environment.start()
        self.addCleanup(self.environment.stop)

    def write_state(self, **updates: object) -> None:
        state = {
            "repo": {"id": 1, "full_name": "o/r"},
            "labels": [],
            "issues": {},
            "pulls": {},
            "comments": {},
            "reviews": {},
            "statuses": {},
            "commits": {},
            "sub_issues": {},
            "calls": [],
            "failures": {},
        }
        if self.state_path.exists():
            state.update(json.loads(self.state_path.read_text(encoding="utf-8")))
        state.update(updates)
        self.state_path.write_text(json.dumps(state), encoding="utf-8")

    def state(self) -> dict:
        return json.loads(self.state_path.read_text(encoding="utf-8"))

    def client(self, root: Path | None = None) -> github_api.GitHub:
        return github_api.GitHub(repo_root=root or self.root)

    def make_repository(self) -> tuple[Path, Path, str, str]:
        repository = self.root / "repository"
        remote = self.root / "github.git"
        repository.mkdir()
        run_git(repository, "init", "-b", "main")
        run_git(repository, "config", "user.name", "Workflow Test")
        run_git(repository, "config", "user.email", "workflow@example.invalid")
        (repository / "README.md").write_text("base\n", encoding="utf-8")
        run_git(repository, "add", "README.md")
        run_git(repository, "commit", "-m", "Initial")
        base_sha = run_git(repository, "rev-parse", "HEAD")
        subprocess.run(
            ["git", "clone", "--bare", str(repository), str(remote)],
            check=True,
            capture_output=True,
            text=True,
        )
        run_git(repository, "remote", "add", "github", str(remote))
        run_git(
            repository,
            "fetch",
            "github",
            "refs/heads/main:refs/remotes/github/main",
        )
        run_git(repository, "checkout", "-b", "issue-7-test")
        (repository / "README.md").write_text("base\nfeature\n", encoding="utf-8")
        run_git(repository, "add", "README.md")
        run_git(repository, "commit", "-m", "Feature")
        head_sha = run_git(repository, "rev-parse", "HEAD")
        return repository, remote, base_sha, head_sha


class IssueLifecycleTests(FakeGhCase):
    """Group 1: create/recover, labels, sub-issues, and close reasons."""

    def test_issue_create_recovery_parent_and_close_are_idempotent(self) -> None:
        self.write_state(
            labels=[{"name": "formalization"}],
            issues={"1": issue_row(1, title="Parent")},
        )
        arguments = [
            "--title",
            "Prove the basis lemma",
            "--body",
            "Paper statement and target.",
            "--label",
            "formalization",
            "--parent",
            "1",
            "--repo-root",
            str(self.root),
        ]
        self.assertEqual(issue_new.main(arguments), 0)
        self.assertEqual(issue_new.main(arguments), 0)
        state = self.state()
        self.assertEqual(len(state["issues"]), 2)
        created = state["issues"]["2"]
        self.assertEqual(created["body"].count("mipstarre:issue-create"), 1)
        self.assertEqual([row["number"] for row in state["sub_issues"]["1"]], [2])

        close = [
            "2",
            "--reason",
            "not-planned",
            "--comment",
            "Superseded by the source correction.",
            "--repo-root",
            str(self.root),
        ]
        self.assertEqual(issue_close.main(close), 0)
        self.assertEqual(issue_close.main(close), 0)
        state = self.state()
        self.assertEqual(state["issues"]["2"]["state_reason"], "not_planned")
        self.assertEqual(len(state["comments"]["2"]), 1)

    def test_ambiguous_create_is_recovered_and_missing_label_fails(self) -> None:
        self.write_state(
            labels=[{"name": "formalization"}],
            ambiguous_issue_create_once=True,
        )
        args = [
            "--title",
            "Ambiguous create",
            "--body",
            "body",
            "--label",
            "formalization",
            "--repo-root",
            str(self.root),
        ]
        self.assertEqual(issue_new.main(args), 0)
        self.assertEqual(len(self.state()["issues"]), 1)
        bad = ["--title", "Bad label", "--label", "missing", "--repo-root", str(self.root)]
        self.assertEqual(issue_new.main(bad), 2)
        self.assertEqual(len(self.state()["issues"]), 1)


class PullRequestLifecycleTests(FakeGhCase):
    """Group 2: explicit ref push, create/adopt, footer, and empty diff."""

    def test_explicit_feature_ref_create_and_adopt(self) -> None:
        repository, remote, base_sha, head_sha = self.make_repository()
        self.write_state(
            labels=[{"name": "formalization"}],
            issues={"7": issue_row(7)},
            local_head=head_sha,
        )
        args = [
            "--branch",
            "issue-7-test",
            "--base",
            "main",
            "--title",
            "feat(local): test PR publication",
            "--body",
            "### Motivation\n\nTest.\n",
            "--label",
            "formalization",
            "--issue",
            "7",
            "--repo-root",
            str(repository),
        ]
        self.assertEqual(pr_open.main(args), 0)
        self.assertEqual(pr_open.main(args), 0)
        state = self.state()
        self.assertEqual(len(state["pulls"]), 1)
        body = state["pulls"]["1"]["body"]
        self.assertIn("Closes #7", body)
        self.assertEqual(body.count("mipstarre:pr-create"), 1)
        self.assertEqual(run_git(remote, "rev-parse", "refs/heads/main"), base_sha)
        self.assertEqual(
            run_git(remote, "rev-parse", "refs/heads/issue-7-test"), head_sha
        )
        self.assertNotIn("--all", (BIN_DIR / "pr_open.py").read_text(encoding="utf-8"))

    def test_ambiguous_pr_create_and_empty_diff_refusal(self) -> None:
        repository, _remote, _base_sha, head_sha = self.make_repository()
        self.write_state(ambiguous_pr_create_once=True, local_head=head_sha)
        args = [
            "--branch",
            "issue-7-test",
            "--title",
            "Ambiguous PR",
            "--body",
            "body",
            "--repo-root",
            str(repository),
        ]
        self.assertEqual(pr_open.main(args), 0)
        self.assertEqual(len(self.state()["pulls"]), 1)
        run_git(repository, "checkout", "main")
        run_git(repository, "checkout", "-b", "issue-8-empty")
        empty = [
            "--branch",
            "issue-8-empty",
            "--title",
            "Empty",
            "--repo-root",
            str(repository),
        ]
        self.assertEqual(pr_open.main(empty), 2)

        run_git(repository, "checkout", "issue-7-test")
        run_git(repository, "update-ref", "-d", "refs/remotes/github/main")
        self.assertEqual(pr_open.main(args), 2)


class SharedGitHubLayerTests(FakeGhCase):
    """Group 3: discovery, retries, timeout bytes, status read-back, and SHAs."""

    def test_pagination_headers_rate_limit_and_permanent_failure(self) -> None:
        labels = [{"name": f"label-{index}"} for index in range(101)]
        self.write_state(
            labels=labels,
            failures={
                "GET ": {"remaining": 1, "message": "HTTP 403 secondary rate limit"}
            },
        )
        client = self.client()
        client.probe_authentication()
        self.assertEqual(len(client.labels()), 101)
        self.write_state(
            failures={
                "GET labels": {"remaining": 1, "message": "HTTP 429 rate limit exceeded"}
            }
        )
        self.assertEqual(len(client.labels()), 101)
        calls = self.state()["calls"]
        self.assertTrue(any("X-GitHub-Api-Version" in " ".join(row["args"]) for row in calls))
        self.assertGreaterEqual(sum(row["args"][0] == "api" for row in calls), 4)

        self.write_state(
            failures={"GET ": {"remaining": 3, "message": "HTTP 404 Not Found"}}
        )
        before = len(self.state()["calls"])
        with self.assertRaises(github_api.GitHubError):
            client.probe_authentication()
        self.assertEqual(len(self.state()["calls"]) - before, 1)

    def test_cli_and_repository_discovery_precedence(self) -> None:
        self.assertEqual(github_api.discover_gh(), self.gh_path.resolve())
        with mock.patch.dict(
            os.environ,
            {"MIPSTARRE_GH": str(self.root / "missing-gh")},
        ):
            with self.assertRaises(github_api.GitHubError):
                github_api.discover_gh()

        repository = self.root / "discovery"
        repository.mkdir()
        run_git(repository, "init", "-b", "main")
        run_git(
            repository,
            "remote",
            "add",
            "github",
            "https://github.com/example/project.git",
        )
        with mock.patch.dict(os.environ, {}, clear=False):
            os.environ.pop("MIPSTARRE_GITHUB_REPO", None)
            self.assertEqual(
                github_api.discover_repository(repository), "example/project"
            )

    def test_timeout_bytes_and_sanitized_retained_stdout(self) -> None:
        os.environ["MIPSTARRE_GH_TIMEOUT"] = "0.05"
        client = self.client()
        with self.assertRaises(github_api.GitHubError) as caught:
            client.api("/repos/o/r/slow")
        self.assertIn("timed out", str(caught.exception))
        self.assertIn("partial-output", caught.exception.stdout)

        secret = "workflow-secret-value"
        os.environ["WORKFLOW_TOKEN"] = secret
        self.write_state(
            failures={
                "GET ": {
                    "remaining": 3,
                    "message": "HTTP 500 failed",
                    "stdout": secret + "\u0001 retained",
                }
            }
        )
        with self.assertRaises(github_api.GitHubError) as failed:
            client.probe_authentication()
        self.assertNotIn(secret, failed.exception.stdout)
        self.assertNotIn("\u0001", failed.exception.stdout)
        self.assertNotIn(secret, json.dumps(self.state()["calls"]))

    def test_ambiguous_status_reconciles_and_contexts_casefold(self) -> None:
        sha = "a" * 40
        self.write_state(ambiguous_status_once=True)
        client = self.client()
        client.post_status(sha, "Local-CI/Build", "success", "passed")
        state = self.state()
        self.assertEqual(len(state["statuses"][sha]), 1)
        self.assertIn("local-ci/build", client.latest_statuses(sha))
        state["statuses"][sha].append(
            {
                "id": 99,
                "sha": "c" * 40,
                "context": "LOCAL-CI/BUILD",
                "state": "failure",
                "description": "wrong SHA",
                "created_at": "2099-01-01T00:00:00Z",
            }
        )
        self.write_state(statuses=state["statuses"])
        self.assertEqual(
            client.latest_statuses(sha)["local-ci/build"]["state"], "success"
        )
        posts = [
            row for row in state["calls"]
            if row["args"][:2] == ["api", "--method"]
            and row["args"][2] == "POST"
            and "statuses/" in row["args"][3]
        ]
        self.assertEqual(len(posts), 1)
        for value in ("a" * 39, "g" * 40, "a" * 41, "deadbeef"):
            with self.assertRaises(github_api.GitHubError):
                github_api.normalize_sha(value)
        self.assertEqual(github_api.normalize_sha("A" * 64), "a" * 64)

    def test_successful_publications_validate_exact_return_values(self) -> None:
        sha = "b" * 40
        client = self.client()
        self.write_state(corrupt_status_response=True)
        with self.assertRaises(github_api.GitHubError):
            client.post_status(sha, "local-ci/build", "success", "passed")

        marker = github_api.stable_marker("test-comment", id="one")
        body = "body\n\n" + marker
        self.write_state(corrupt_comment_response=True)
        with self.assertRaises(github_api.GitHubError):
            client.comment_once(1, body, marker)

        review_marker = github_api.stable_marker(
            "test-review", head=sha, event="COMMENT", fallback="none"
        )
        review_body = "ledger\n" + review_marker
        self.write_state(corrupt_review_response=True)
        with self.assertRaises(github_api.GitHubError):
            client.review_once(1, sha, review_body, "COMMENT", review_marker)


class CIPublicationTests(FakeGhCase):
    """Group 4: exact-head statuses, partial refusal, manifest, and races."""

    def prepare_ci(self) -> tuple[Path, str]:
        repository, _remote, _base_sha, head_sha = self.make_repository()
        local_bin = repository / "local" / "bin"
        local_bin.mkdir(parents=True)
        shutil.copy2(BIN_DIR / "ci.sh", local_bin / "ci.sh")
        shutil.copy2(BIN_DIR / "github_api.py", local_bin / "github_api.py")
        pull = pull_row(1, head_sha)
        self.write_state(
            pulls={"1": pull},
            issues={"1": {**pull, "pull_request": {"url": pull["html_url"]}}},
            commits={"1": [{"sha": head_sha, "commit": {"message": "Feature"}}]},
        )
        return repository, head_sha

    def run_ci(self, repository: Path, *extra: str) -> subprocess.CompletedProcess[str]:
        environment = os.environ.copy()
        environment["MIPSTARRE_CACHE_ROOT"] = str(self.root / "cache")
        return subprocess.run(
            ["bash", str(repository / "local/bin/ci.sh"), "1", "--worktree", str(repository), *extra],
            cwd=repository,
            env=environment,
            text=True,
            capture_output=True,
            check=False,
        )

    def test_complete_skipped_lane_publishes_all_contexts_and_manifest(self) -> None:
        repository, head_sha = self.prepare_ci()
        result = self.run_ci(repository)
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        state = self.state()
        rows = state["statuses"][head_sha]
        contexts = {row["context"].casefold() for row in rows}
        self.assertEqual(contexts, set(github_api.CANONICAL_CI_CONTEXTS))
        latest = self.client().latest_statuses(head_sha)
        self.assertTrue(all(row["state"] == "success" for row in latest.values()))
        self.assertTrue(all("skipped" in row["description"] for row in latest.values()))
        comments = state["comments"]["1"]
        self.assertEqual(len(comments), 1)
        self.assertIn("mipstarre:ci-manifest", comments[0]["body"])
        self.client().ci_manifest(1, head_sha)

    def test_partial_run_publishes_nothing_and_remote_race_has_no_success(self) -> None:
        repository, head_sha = self.prepare_ci()
        partial = self.run_ci(repository, "--only", "build")
        self.assertEqual(partial.returncode, 0, partial.stderr + partial.stdout)
        self.assertEqual(self.state()["statuses"], {})
        self.assertEqual(self.state()["comments"], {})

        self.write_state(pull_head_sequence=[head_sha, "c" * 40], pull_read_count=0)
        moved = self.run_ci(repository)
        self.assertNotEqual(moved.returncode, 0)
        rows = self.state()["statuses"][head_sha]
        self.assertFalse(any(row["state"] == "success" for row in rows))
        source = (BIN_DIR / "ci.sh").read_text(encoding="utf-8")
        self.assertIn('REMOTE_FINAL_SHA" != "$HEAD_SHA', source)
        self.assertIn('LOCAL_FINAL_SHA" != "$HEAD_SHA', source)


class ReviewPublicationTests(FakeGhCase):
    """Group 5: exact-commit review events, fallback, ledger, and head checks."""

    def test_review_events_idempotency_and_self_review_fallback(self) -> None:
        sha = "d" * 40
        client = self.client()
        clean_marker = github_api.stable_marker(
            "test-review", head=sha, event="COMMENT", fallback="none"
        )
        clean_body = "## Findings\n\nNone.\n\n" + clean_marker
        row, event = client.review_once(1, sha, clean_body, "COMMENT", clean_marker)
        self.assertEqual((row["commit_id"], event), (sha, "COMMENT"))
        client.review_once(1, sha, clean_body, "COMMENT", clean_marker)
        self.assertEqual(len(self.state()["reviews"]["1"]), 1)

        self.write_state(
            review_422="Cannot request changes on your own pull request"
        )
        marker = github_api.stable_marker(
            "test-review", head=sha, event="REQUEST_CHANGES", fallback="COMMENT"
        )
        body = "## Findings\n\n- [ ] F1 defect\n\n" + marker
        _row, used = client.review_once(1, sha, body, "REQUEST_CHANGES", marker)
        self.assertEqual(used, "COMMENT")
        client.post_status(sha, github_api.REVIEW_CONTEXT, "failure", "findings")

    def test_unrelated_422_fails_and_wrapper_contains_moved_head_recheck(self) -> None:
        sha = "e" * 40
        self.write_state(review_422="Validation Failed: commit is not part of pull")
        marker = github_api.stable_marker(
            "test-review", head=sha, event="REQUEST_CHANGES", fallback="COMMENT"
        )
        body = "ledger\n" + marker
        with self.assertRaises(github_api.GitHubError):
            self.client().review_once(1, sha, body, "REQUEST_CHANGES", marker)
        source = (BIN_DIR / "review.sh").read_text(encoding="utf-8")
        self.assertIn("head moved during review", source)
        self.assertIn('REMOTE_FINAL_SHA" != "$HEAD_SHA', source)
        self.assertIn('LOCAL_FINAL_SHA" != "$HEAD_SHA', source)
        self.assertLess(source.index("head moved during review"), source.index("review-once"))
        self.assertIn("latest-review-ledger", source)
        self.assertIn('"$REVIEW_CONTEXT"', source)

    def test_marker_collision_and_event_mismatch_fail_closed(self) -> None:
        sha = "9" * 40
        client = self.client()
        marker = github_api.stable_marker(
            "test-review", head=sha, event="COMMENT", fallback="none"
        )
        body = "ledger\n" + marker
        self.write_state(
            reviews={
                "1": [
                    {
                        "id": 1,
                        "body": "different\n" + marker,
                        "commit_id": sha,
                        "state": "COMMENTED",
                    }
                ]
            }
        )
        with self.assertRaises(github_api.GitHubError):
            client.review_once(1, sha, body, "COMMENT", marker)
        with self.assertRaises(github_api.GitHubError):
            client.review_once(1, sha, body, "REQUEST_CHANGES", marker)
        legacy = (
            f"<!-- mipstarre:review-ledger pr=1 head={sha} run=legacy -->"
        )
        self.write_state(
            reviews={
                "1": [
                    {
                        "id": 2,
                        "body": "legacy ledger\n" + legacy,
                        "commit_id": sha,
                        "state": "COMMENTED",
                    }
                ]
            }
        )
        with self.assertRaises(github_api.GitHubError):
            client.review_ledger(1, sha)


class AutoFixTests(FakeGhCase):
    """Auto-fix: opt-in, exact-head evidence, complete count, and cap action."""

    def prepare_autofix(self) -> tuple[Path, str, dict]:
        repository, _remote, _base_sha, head_sha = self.make_repository()
        local_bin = repository / "local" / "bin"
        local_bin.mkdir(parents=True)
        shutil.copy2(BIN_DIR / "autofix.sh", local_bin / "autofix.sh")
        shutil.copy2(BIN_DIR / "github_api.py", local_bin / "github_api.py")
        pull = pull_row(1, head_sha)
        issue = {**pull, "pull_request": {"url": pull["html_url"]}}
        self.write_state(
            pulls={"1": pull},
            issues={"1": issue},
            commits={"1": [{"sha": head_sha, "commit": {"message": "Feature"}}]},
        )
        return repository, head_sha, pull

    def run_autofix(self, repository: Path) -> subprocess.CompletedProcess[str]:
        environment = os.environ.copy()
        environment["MIPSTARRE_CACHE_ROOT"] = str(self.root / "cache")
        return subprocess.run(
            ["bash", str(repository / "local/bin/autofix.sh"), "1", "--mode", "ci"],
            cwd=repository,
            env=environment,
            text=True,
            capture_output=True,
            check=False,
        )

    def test_opt_in_and_missing_evidence_fail_closed(self) -> None:
        repository, _head_sha, pull = self.prepare_autofix()
        absent = self.run_autofix(repository)
        self.assertEqual(absent.returncode, 0, absent.stderr)
        self.assertIn("no automatic fix is authorized", absent.stderr)

        pull["labels"] = [{"name": github_api.AUTO_FIX_LABEL}]
        self.write_state(
            pulls={"1": pull},
            issues={"1": {**pull, "pull_request": {"url": pull["html_url"]}}},
        )
        missing = self.run_autofix(repository)
        self.assertNotEqual(missing.returncode, 0)
        self.assertIn("requires a valid marker-bound exact-head CI manifest", missing.stderr)

    def test_cap_removes_opt_in_and_posts_one_marker_comment(self) -> None:
        repository, head_sha, pull = self.prepare_autofix()
        pull["labels"] = [{"name": github_api.AUTO_FIX_LABEL}]
        manifest = {
            "pr": "1",
            "head_sha": head_sha,
            "partial": False,
            "steps": [
                {
                    "step": step,
                    "outcome": "failure" if step == "build" else "success",
                    "log_path": "",
                }
                for step in github_api.CANONICAL_CI_STEPS
            ],
        }
        marker = f"<!-- mipstarre:ci-manifest pr=1 head={head_sha} run=cap -->"
        body = "```json\n" + json.dumps(manifest) + "\n```\n\n" + marker
        commits = [
            {
                "sha": f"{index + 1:040x}",
                "commit": {"message": "[codex-auto-fix] repair"},
            }
            for index in range(5)
        ]
        pull["commits"] = len(commits)
        issue = {**pull, "pull_request": {"url": pull["html_url"]}}
        self.write_state(
            pulls={"1": pull},
            issues={"1": issue},
            comments={"1": [{"id": 1, "body": body, "created_at": "2026-01-01Z"}]},
            commits={"1": commits},
        )
        result = self.run_autofix(repository)
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        state = self.state()
        labels = [row["name"] for row in state["issues"]["1"]["labels"]]
        self.assertNotIn(github_api.AUTO_FIX_LABEL, labels)
        cap_comments = [
            row for row in state["comments"]["1"] if "mipstarre:autofix-cap" in row["body"]
        ]
        self.assertEqual(len(cap_comments), 1)


class MergeGateTests(FakeGhCase):
    """Group 6: status/review/lock/cap/adjudication gate refusals."""

    def green_state(self, sha: str) -> dict:
        statuses = [
            {
                "id": index + 1,
                "sha": sha,
                "context": context,
                "state": "success",
                "description": "ok",
                "created_at": f"2026-01-01T00:00:{index:02d}Z",
            }
            for index, context in enumerate(github_api.CANONICAL_CI_CONTEXTS)
        ]
        statuses.append(
            {
                "id": 50,
                "sha": sha,
                "context": github_api.REVIEW_CONTEXT,
                "state": "success",
                "description": "clean",
                "created_at": "2026-01-01T00:01:00Z",
            }
        )
        marker = (
            f"<!-- mipstarre:review-ledger pr=1 head={sha} run=test "
            "event=COMMENT fallback=none -->"
        )
        review = {
            "id": 1,
            "body": "## Findings\n\nNo unresolved findings.\n\n" + marker,
            "commit_id": sha,
            "state": "COMMENTED",
            "submitted_at": "2026-01-01T00:01:00Z",
        }
        return {"statuses": {sha: statuses}, "reviews": {"1": [review]}}

    def test_missing_failing_stale_and_adverse_review_refuse(self) -> None:
        sha = "f" * 40
        client = self.client()
        with self.assertRaises(pr_merge.GateFailure):
            pr_merge.require_statuses(client, sha)
        state = self.green_state(sha)
        state["statuses"][sha][0]["state"] = "failure"
        self.write_state(**state)
        with self.assertRaises(pr_merge.GateFailure):
            pr_merge.require_statuses(client, sha)

        state = self.green_state(sha)
        state["reviews"]["1"].append(
            {
                "id": 2,
                "body": "later",
                "commit_id": sha,
                "state": "CHANGES_REQUESTED",
                "submitted_at": "2026-01-01T00:02:00Z",
            }
        )
        self.write_state(**state)
        with self.assertRaises(pr_merge.GateFailure):
            pr_merge.require_review(client, 1, sha)

    def test_live_lock_history_cap_and_adjudication_are_fail_closed(self) -> None:
        cache = self.root / "cache"
        lock = cache / "locks" / "fix-issue-7-test.lock"
        lock.mkdir(parents=True)
        (lock / "pid").write_text(str(os.getpid()), encoding="utf-8")
        with self.assertRaises(pr_merge.GateFailure):
            pr_merge.require_no_live_fix(cache, "issue-7-test")

        sha = "1" * 40
        pull = pull_row(1, sha)
        pull["commits"] = 251
        self.write_state(pulls={"1": pull})
        with self.assertRaises(github_api.GitHubError):
            self.client().pull_commits(1)
        commits = [
            {"commit": {"message": "[codex-auto-fix] fix\nbody"}},
            {"commit": {"message": "ordinary"}},
            {"commit": {"message": "[codex-review-fix] fix"}},
        ]
        self.assertEqual(github_api.fix_iteration_count(commits), 2)

        pull["labels"] = [{"name": github_api.ADJUDICATION_LABEL}]
        self.write_state(pulls={"1": pull}, comments={"1": []})
        with self.assertRaises(pr_merge.GateFailure):
            pr_merge.require_adjudication(self.client(), pull, 1, sha)


class GuardedMergeTests(FakeGhCase):
    """Group 7: one exact-head guarded gh merge and no direct main push."""

    def test_valid_gate_invokes_only_guarded_gh_merge(self) -> None:
        repository, _remote, _base_sha, head_sha = self.make_repository()
        pull = pull_row(1, head_sha)
        manifest = {
            "pr": "1",
            "head_sha": head_sha,
            "partial": False,
            "steps": [
                {"step": step, "outcome": "success"}
                for step in github_api.CANONICAL_CI_STEPS
            ],
        }
        ci_marker = f"<!-- mipstarre:ci-manifest pr=1 head={head_sha} run=test -->"
        ci_body = "```json\n" + json.dumps(manifest) + "\n```\n\n" + ci_marker
        review_marker = (
            f"<!-- mipstarre:review-ledger pr=1 head={head_sha} run=test "
            "event=COMMENT fallback=none -->"
        )
        statuses = []
        for index, context in enumerate(
            (*github_api.CANONICAL_CI_CONTEXTS, github_api.REVIEW_CONTEXT)
        ):
            statuses.append(
                {
                    "id": index + 1,
                    "sha": head_sha,
                    "context": context,
                    "state": "success",
                    "description": "ok",
                    "created_at": f"2026-01-01T00:00:{index:02d}Z",
                }
            )
        self.write_state(
            pulls={"1": pull},
            issues={"1": {**pull, "pull_request": {"url": pull["html_url"]}}},
            statuses={head_sha: statuses},
            comments={"1": [{"id": 1, "body": ci_body, "created_at": "2026-01-01Z"}]},
            reviews={
                "1": [
                    {
                        "id": 1,
                        "body": "## Findings\n\nClean.\n\n" + review_marker,
                        "commit_id": head_sha,
                        "state": "COMMENTED",
                        "submitted_at": "2026-01-01Z",
                    }
                ]
            },
            commits={"1": [{"sha": head_sha, "commit": {"message": "Feature"}}]},
            merge_sha="2" * 40,
        )
        args = argparse.Namespace(
            number="1",
            adjudicated=False,
            dry_run=False,
            fix_cap=5,
            repo_root=repository,
        )
        with mock.patch.object(pr_merge, "fast_forward_base"), mock.patch.object(
            pr_merge, "cleanup_feature"
        ):
            self.assertEqual(pr_merge.run(args), 0)
        calls = self.state()["calls"]
        merge_calls = [row["args"] for row in calls if row["args"][:2] == ["pr", "merge"]]
        self.assertIn(
            [
                "pr",
                "merge",
                "1",
                "--repo",
                "o/r",
                "--merge",
                "--match-head-commit",
                head_sha,
            ],
            merge_calls,
        )
        source = (BIN_DIR / "pr_merge.py").read_text(encoding="utf-8")
        self.assertNotIn('"push", "github"', source)
        self.assertNotIn("--admin", source)


class SnapshotTests(FakeGhCase):
    """Group 8: pagination, filtering, atomic generations, failure injection."""

    def test_snapshot_is_coherent_and_failed_generation_preserves_previous(self) -> None:
        issues = {str(index): issue_row(index) for index in range(1, 102)}
        issues["500"] = {
            **issue_row(500),
            "pull_request": {"url": "https://github.com/o/r/pull/500"},
        }
        pulls = {
            str(index): pull_row(index, f"{index:040x}", branch=f"issue-{index}-x")
            for index in range(1, 102)
        }
        self.write_state(issues=issues, pulls=pulls)
        destination = self.root / "snapshot"
        metadata = github_api.write_snapshot(self.client(), destination)
        self.assertTrue(destination.is_symlink())
        first_target = os.readlink(destination)
        self.assertEqual(
            len(json.loads((destination / "open-issues.json").read_text())), 101
        )
        self.assertEqual(
            len(json.loads((destination / "open-pulls.json").read_text())), 101
        )
        self.assertEqual(
            json.loads((destination / "metadata.json").read_text())["generation"],
            metadata["generation"],
        )

        os.environ["MIPSTARRE_SNAPSHOT_FAIL_AFTER"] = "pulls"
        issues["102"] = issue_row(102)
        self.write_state(issues=issues)
        with self.assertRaises(github_api.GitHubError):
            github_api.write_snapshot(self.client(), destination)
        self.assertEqual(os.readlink(destination), first_target)
        self.assertEqual(
            len(json.loads((destination / "open-issues.json").read_text())), 101
        )


class RepositoryGuardTests(FakeGhCase):
    """Group 9: static/runtime no-registry guard and hook coverage."""

    def test_active_surfaces_do_not_recreate_retired_root_registries(self) -> None:
        self.assertFalse((REPO_ROOT / "issues").exists())
        self.assertFalse((REPO_ROOT / "prs").exists())
        self.assertFalse((REPO_ROOT / "local/labels.yml").exists())

        active = [
            REPO_ROOT / "AGENTS.md",
            REPO_ROOT / "README.md",
            *(REPO_ROOT / "local/bin").glob("*"),
            *(REPO_ROOT / "local/personas").glob("*.md"),
            *(REPO_ROOT / "local/protocols").glob("*.md"),
            *(REPO_ROOT / "docs").glob("*.md"),
            *(REPO_ROOT / "scripts").glob("*.py"),
            *(REPO_ROOT / ".githooks").glob("*"),
        ]
        forbidden = ("issues/.seq", "prs/.seq", "local/labels.yml", "prs/<")
        for path in active:
            if not path.is_file() or path.name == "EVOLUTION.md":
                continue
            text = path.read_text(encoding="utf-8", errors="replace")
            for token in forbidden:
                self.assertNotIn(token, text, f"{path.relative_to(REPO_ROOT)}: {token}")

        production = [
            *(REPO_ROOT / "local/bin").glob("*"),
            *(REPO_ROOT / "scripts").glob("*.py"),
        ]
        root_access = (
            re.compile(r"\$(?:ROOT|REPO_ROOT)/(?:issues|prs)(?:/|\b)"),
            re.compile(
                r"\b(?:root|repo_root|REPO_ROOT|ROOT)\s*/\s*"
                r"[\"'](?:issues|prs)[\"']"
            ),
            re.compile(r"\bmkdir(?:\s+-p)?\s+(?:issues|prs)(?:/|\s|$)"),
        )
        for path in production:
            if not path.is_file():
                continue
            text = path.read_text(encoding="utf-8", errors="replace")
            for pattern in root_access:
                self.assertIsNone(
                    pattern.search(text),
                    f"{path.relative_to(REPO_ROOT)}: {pattern.pattern}",
                )

        hooks = (
            (REPO_ROOT / ".githooks/pre-commit").read_text(encoding="utf-8")
            + (REPO_ROOT / ".githooks/pre-push").read_text(encoding="utf-8")
        )
        self.assertIn("scripts.tests.test_github_workflow", hooks)
        self.assertIn("github_api", hooks)
        self.assertIn("refs/remotes/github/main", hooks)
        for name in ("worktree-setup", "cache-warmer", "blueprint_lean_sync"):
            self.assertIn(name, hooks)

        self.write_state(failures={"GET ": {"remaining": 1, "message": "HTTP 401"}})
        result = issue_new.main(
            ["--title", "Must fail closed", "--repo-root", str(self.root)]
        )
        self.assertEqual(result, 2)
        self.assertFalse((self.root / "issues").exists())
        self.assertFalse((self.root / "prs").exists())

    def test_archive_and_frozen_precedent_are_unmodified(self) -> None:
        for path in ("results/telemetry/registry-archive", ".github"):
            result = subprocess.run(
                ["git", "-C", str(REPO_ROOT), "diff", "--quiet", "--", path],
                check=False,
            )
            self.assertEqual(result.returncode, 0, path)


if __name__ == "__main__":
    unittest.main()
