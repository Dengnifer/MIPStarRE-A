#!/usr/bin/env python3
"""Deterministic regression tests for the GitHub-authoritative local workflow."""

from __future__ import annotations

import argparse
import contextlib
import hashlib
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
    if state.pop("fail_issue_create_before_once", False):
        fail("HTTP 503 Service Unavailable")
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
    if state.pop("fail_pr_create_before_once", False):
        fail("HTTP 503 Service Unavailable")
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
        "base": {
            "ref": option("--base"),
            "sha": state.get("base_sha", "b" * 40),
        },
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
        base_sequence = state.get("pull_base_sequence", [])
        count = int(state.get("pull_read_count", 0))
        if sequence:
            row["head"]["sha"] = sequence[min(count, len(sequence) - 1)]
        if base_sequence:
            row["base"]["sha"] = base_sequence[
                min(count, len(base_sequence) - 1)
            ]
        if sequence or base_sequence:
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
        read_count = int(state.get("review_read_count", 0))
        if state.get("inject_adverse_review_at") == read_count:
            pull = state.setdefault("pulls", {}).get(number, {})
            reviews.append(
                {
                    "id": 9000 + read_count,
                    "body": "same-head race",
                    "commit_id": str((pull.get("head") or {}).get("sha") or ""),
                    "state": "CHANGES_REQUESTED",
                    "submitted_at": "2099-01-01T00:00:00Z",
                }
            )
            state["inject_adverse_review_at"] = None
        state["review_read_count"] = read_count + 1
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


def pull_row(
    number: int,
    sha: str,
    branch: str = "issue-7-test",
    *,
    base_sha: str = "0" * 40,
) -> dict:
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
        "base": {"ref": "main", "sha": base_sha},
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

    def append_sessions(self, root: Path, rows: list[dict]) -> None:
        path = root / "results" / "telemetry" / "sessions.jsonl"
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open("a", encoding="utf-8") as stream:
            for row in rows:
                stream.write(json.dumps(row) + "\n")

    def ci_bundle(
        self,
        head_sha: str,
        base_sha: str,
        *,
        run_id: str = "ci-test",
        outcomes: dict[str, str] | None = None,
        comment_id: int = 1,
        created_at: str = "2026-01-01T00:01:00Z",
    ) -> tuple[dict, list[dict]]:
        outcomes = outcomes or {}
        steps = []
        statuses = []
        for index, step_name in enumerate(github_api.CANONICAL_CI_STEPS):
            outcome = outcomes.get(step_name, "success")
            step = {"step": step_name, "outcome": outcome, "note": ""}
            steps.append(step)
            state, description = github_api.ci_status_description(run_id, step)
            context = f"local-ci/{step_name}"
            statuses.append(
                {
                    "id": index + 1,
                    "sha": head_sha,
                    "context": context,
                    "state": state,
                    "description": github_api.render_status_description(
                        head_sha, context, state, description
                    ),
                    "created_at": created_at,
                }
            )
        conclusion = "success"
        if any(step["outcome"] == "failure" for step in steps):
            conclusion = "failure"
        elif any(step["outcome"] == "error" for step in steps):
            conclusion = "error"
        manifest = {
            "schema": 1,
            "pr": "1",
            "base_sha": base_sha,
            "head_sha": head_sha,
            "run_id": run_id,
            "partial": False,
            "conclusion": conclusion,
            "steps": steps,
        }
        marker = (
            f"<!-- mipstarre:ci-manifest pr=1 head={head_sha} "
            f"run={run_id} -->"
        )
        body = "```json\n" + json.dumps(manifest) + "\n```\n\n" + marker + "\n"
        comment = {"id": comment_id, "body": body, "created_at": created_at}
        return comment, statuses

    def review_bundle(
        self,
        root: Path,
        head_sha: str,
        base_sha: str,
        *,
        run_id: str = "review-test",
        worktree: Path | None = None,
        findings: int = 0,
        review_id: int = 1,
        status_id: int = 100,
        submitted_at: str = "2026-01-01T00:02:00Z",
        thread_id: str | None = None,
        session_name: str | None = None,
    ) -> tuple[dict, dict, list[dict], str, str]:
        worktree_text = str((worktree or root).resolve())
        safe_run = re.sub(r"[^A-Za-z0-9._-]", "-", run_id)
        session_name = session_name or f"reviewer-pr1-{safe_run}"
        thread_id = thread_id or f"thread-{safe_run}-code"
        lane = {
            "lane": "code",
            "name": session_name,
            "thread_id": thread_id,
            "exit": 0,
            "worktree": worktree_text,
            "start": "2026-01-01T00:00:00+00:00",
            "end": "2026-01-01T00:01:00+00:00",
        }
        finding_lines = [
            f"- [ ] F{index} (changes) `path.py:{index}` - defect {index}"
            for index in range(1, findings + 1)
        ]
        ledger = "\n".join(finding_lines) if finding_lines else "<!-- no findings -->"
        event = "COMMENT" if findings == 0 else "REQUEST_CHANGES"
        attestation = {
            "schema": 1,
            "pr": 1,
            "head_sha": head_sha,
            "base_sha": base_sha,
            "run_id": run_id,
            "canonical_findings": findings,
            "event": event,
            "fallback": "none",
            "lanes": [lane],
        }
        prefix = (
            "# Local review ledger\n\n"
            "## Code review lane\n\n"
            "<!-- findings:begin -->\n"
            f"{ledger}\n"
            "<!-- findings:end -->\n\n"
            "## Review attestation\n\n"
            "```json\n"
            + json.dumps(attestation, indent=2, sort_keys=True)
            + "\n```\n\n"
        )
        digest = hashlib.sha256(prefix.encode("utf-8")).hexdigest()
        marker = (
            f"<!-- mipstarre:review-attestation pr=1 head={head_sha} "
            f"base={base_sha} run={run_id} findings={findings} event={event} "
            f"fallback=none digest={digest} -->"
        )
        body = prefix + marker + "\n"
        state = "COMMENTED" if findings == 0 else "CHANGES_REQUESTED"
        review = {
            "id": review_id,
            "body": body,
            "commit_id": head_sha,
            "state": state,
            "submitted_at": submitted_at,
        }
        status_state = "success" if findings == 0 else "failure"
        verdict = "clean" if findings == 0 else f"findings={findings}"
        description = f"local review digest={digest} run={run_id} {verdict}"
        status = {
            "id": status_id,
            "sha": head_sha,
            "context": github_api.REVIEW_CONTEXT,
            "state": status_state,
            "description": github_api.render_status_description(
                head_sha,
                github_api.REVIEW_CONTEXT,
                status_state,
                description,
            ),
            "created_at": submitted_at,
        }
        session = {
            "name": session_name,
            "role": "reviewer",
            "issue": "pr1",
            "pr": "1",
            "thread_id": thread_id,
            "start": lane["start"],
            "end": lane["end"],
            "wall_s": 60,
            "usage": {},
            "turns": 1,
            "exit": 0,
            "dispatcher": "test",
            "worktree": worktree_text,
            "status": "done",
        }
        return review, status, [session], body, marker


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
        repository, _remote, base_sha, head_sha = self.make_repository()
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

    def test_ambiguous_absent_mutations_never_issue_a_second_write(self) -> None:
        sha = "6" * 40
        self.write_state(
            failures={
                f"POST statuses/{sha}": {
                    "remaining": 1,
                    "message": "HTTP 503 Service Unavailable",
                }
            }
        )
        with self.assertRaises(github_api.GitHubError) as caught:
            self.client().post_status(sha, "local-ci/build", "success", "passed")
        self.assertIn("refusing to issue a second mutation", str(caught.exception))
        posts = [
            call
            for call in self.state()["calls"]
            if call["args"][:3] == ["api", "--method", "POST"]
            and call["args"][3].endswith(f"statuses/{sha}")
        ]
        self.assertEqual(len(posts), 1)
        self.assertEqual(self.state()["statuses"].get(sha, []), [])

        self.write_state(fail_issue_create_before_once=True)
        with contextlib.redirect_stderr(io.StringIO()):
            result = issue_new.main(
                ["--title", "Ambiguous absent", "--repo-root", str(self.root)]
            )
        self.assertEqual(result, 2)
        creates = [
            call for call in self.state()["calls"]
            if call["args"][:2] == ["issue", "create"]
        ]
        self.assertEqual(len(creates), 1)
        self.assertEqual(self.state()["issues"], {})

        issue = issue_row(1)
        self.write_state(
            issues={"1": issue},
            failures={
                "PATCH issues/1": {
                    "remaining": 1,
                    "message": "HTTP 503 Service Unavailable",
                }
            },
        )
        with contextlib.redirect_stderr(io.StringIO()):
            result = issue_close.main(
                ["1", "--reason", "completed", "--repo-root", str(self.root)]
            )
        self.assertEqual(result, 2)
        patches = [
            call
            for call in self.state()["calls"]
            if call["args"][:3] == ["api", "--method", "PATCH"]
            and call["args"][3].endswith("issues/1")
        ]
        self.assertEqual(len(patches), 1)
        self.assertEqual(self.state()["issues"]["1"]["state"], "open")

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

        _review, _status, _sessions, review_body, review_marker = self.review_bundle(
            self.root, sha, "a" * 40
        )
        self.write_state(corrupt_review_response=True)
        with self.assertRaises(github_api.GitHubError):
            client.review_once(1, sha, review_body, "COMMENT", review_marker)


class CIPublicationTests(FakeGhCase):
    """Group 4: exact-head statuses, partial refusal, manifest, and races."""

    def prepare_ci(self) -> tuple[Path, str, str]:
        repository, _remote, base_sha, head_sha = self.make_repository()
        local_bin = repository / "local" / "bin"
        local_bin.mkdir(parents=True)
        shutil.copy2(BIN_DIR / "ci.sh", local_bin / "ci.sh")
        shutil.copy2(BIN_DIR / "github_api.py", local_bin / "github_api.py")
        pull = pull_row(1, head_sha, base_sha=base_sha)
        self.write_state(
            pulls={"1": pull},
            issues={"1": {**pull, "pull_request": {"url": pull["html_url"]}}},
            commits={"1": [{"sha": head_sha, "commit": {"message": "Feature"}}]},
        )
        return repository, base_sha, head_sha

    def run_ci(self, repository: Path, *extra: str) -> subprocess.CompletedProcess[str]:
        environment = os.environ.copy()
        environment["MIPSTARRE_CACHE_ROOT"] = str(self.root / "cache")
        return subprocess.run(
            [
                "bash",
                str(repository / "local/bin/ci.sh"),
                "1",
                "--worktree",
                str(repository),
                *extra,
            ],
            cwd=repository,
            env=environment,
            text=True,
            capture_output=True,
            check=False,
        )

    def test_complete_skipped_lane_publishes_all_contexts_and_manifest(self) -> None:
        repository, _base_sha, head_sha = self.prepare_ci()
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
        repository, base_sha, head_sha = self.prepare_ci()
        partial = self.run_ci(repository, "--only", "build")
        self.assertEqual(partial.returncode, 0, partial.stderr + partial.stdout)
        self.assertEqual(self.state()["statuses"], {})
        self.assertEqual(self.state()["comments"], {})

        self.write_state(
            pull_head_sequence=[head_sha, "c" * 40],
            pull_base_sequence=[base_sha, base_sha],
            pull_read_count=0,
        )
        moved = self.run_ci(repository)
        self.assertNotEqual(moved.returncode, 0)
        rows = self.state()["statuses"][head_sha]
        self.assertFalse(any(row["state"] == "success" for row in rows))
        source = (BIN_DIR / "ci.sh").read_text(encoding="utf-8")
        self.assertIn('REMOTE_FINAL_SHA" != "$HEAD_SHA', source)
        self.assertIn('LOCAL_FINAL_SHA" != "$HEAD_SHA', source)

    def test_remote_base_race_has_no_success_or_manifest(self) -> None:
        repository, base_sha, head_sha = self.prepare_ci()
        self.write_state(
            pull_head_sequence=[head_sha, head_sha],
            pull_base_sequence=[base_sha, "c" * 40],
            pull_read_count=0,
        )
        moved = self.run_ci(repository)
        self.assertNotEqual(moved.returncode, 0)
        rows = self.state()["statuses"][head_sha]
        self.assertFalse(any(row["state"] == "success" for row in rows))
        self.assertEqual(self.state()["comments"], {})


class ReviewPublicationTests(FakeGhCase):
    """Group 5: exact-commit review events, fallback, ledger, and head checks."""

    def test_clean_comment_attestation_is_idempotent_without_approval(self) -> None:
        sha, base_sha = "d" * 40, "a" * 40
        client = self.client()
        review, status, sessions, body, marker = self.review_bundle(
            self.root, sha, base_sha
        )
        row, event = client.review_once(1, sha, body, "COMMENT", marker)
        self.assertEqual((row["commit_id"], event), (sha, "COMMENT"))
        client.review_once(1, sha, body, "COMMENT", marker)
        self.assertEqual(len(self.state()["reviews"]["1"]), 1)
        self.assertNotEqual(row["state"], "APPROVED")
        self.write_state(statuses={sha: [status]})
        self.append_sessions(self.root, sessions)
        evidence = client.review_evidence(1, sha, base_sha)
        self.assertEqual(evidence.attestation.event, "COMMENT")
        self.assertEqual(evidence.attestation.findings, 0)

    def test_request_changes_rejection_is_not_retried_as_comment(self) -> None:
        sha, base_sha = "e" * 40, "b" * 40
        _review, _status, _sessions, body, marker = self.review_bundle(
            self.root, sha, base_sha, findings=1
        )
        self.write_state(review_422="Validation Failed: commit is not part of pull")
        with self.assertRaises(github_api.GitHubError):
            self.client().review_once(1, sha, body, "REQUEST_CHANGES", marker)
        posts = [
            call
            for call in self.state()["calls"]
            if call["args"][:3] == ["api", "--method", "POST"]
            and call["args"][3].endswith("pulls/1/reviews")
        ]
        self.assertEqual(len(posts), 1)
        source = (BIN_DIR / "review.sh").read_text(encoding="utf-8")
        self.assertIn("head/base moved during review", source)
        self.assertIn('"$remote_head" = "$HEAD_SHA"', source)
        self.assertIn('"$local_head" = "$HEAD_SHA"', source)
        self.assertIn('"$remote_base" = "$BASE_SHA"', source)
        self.assertIn('"$local_base" = "$BASE_SHA"', source)
        self.assertLess(
            source.index("head/base moved during review"),
            source.index("review-once"),
        )
        self.assertIn("latest-review-ledger", source)
        self.assertIn('"$REVIEW_CONTEXT"', source)

    def test_marker_collision_and_event_mismatch_fail_closed(self) -> None:
        sha, base_sha = "9" * 40, "8" * 40
        client = self.client()
        _review, _status, _sessions, body, marker = self.review_bundle(
            self.root, sha, base_sha
        )
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

    def test_digest_run_base_commit_findings_and_status_mismatches_fail(self) -> None:
        sha, base_sha = "7" * 40, "6" * 40
        review, status, sessions, _body, _marker = self.review_bundle(
            self.root, sha, base_sha
        )
        self.append_sessions(self.root, sessions)
        client = self.client()

        tampered = {**review, "body": review["body"].replace("# Local", "# Altered", 1)}
        self.write_state(reviews={"1": [tampered]}, statuses={sha: [status]})
        with self.assertRaises(github_api.GitHubError):
            client.review_evidence(1, sha, base_sha)

        wrong_commit = {**review, "commit_id": "5" * 40}
        self.write_state(reviews={"1": [wrong_commit]}, statuses={sha: [status]})
        with self.assertRaises(github_api.GitHubError):
            client.review_evidence(1, sha, base_sha)

        self.write_state(reviews={"1": [review]}, statuses={sha: [status]})
        with self.assertRaises(github_api.GitHubError):
            client.review_evidence(1, sha, "4" * 40)

        wrong_status = {**status, "description": "different run and digest"}
        self.write_state(reviews={"1": [review]}, statuses={sha: [wrong_status]})
        with self.assertRaises(github_api.GitHubError):
            client.review_evidence(1, sha, base_sha)

        wrong_findings = {
            **review,
            "body": review["body"].replace("findings=0 event=", "findings=1 event="),
        }
        self.write_state(reviews={"1": [wrong_findings]}, statuses={sha: [status]})
        with self.assertRaises(github_api.GitHubError):
            client.review_evidence(1, sha, base_sha)

    def test_invalid_reused_and_nonzero_reviewer_sessions_fail(self) -> None:
        sha, base_sha = "3" * 40, "2" * 40
        review, status, sessions, _body, _marker = self.review_bundle(
            self.root, sha, base_sha
        )
        self.write_state(reviews={"1": [review]}, statuses={sha: [status]})
        telemetry = self.root / "results/telemetry/sessions.jsonl"

        invalid = {**sessions[0], "role": "prover"}
        self.append_sessions(self.root, [invalid])
        with self.assertRaises(github_api.GitHubError):
            self.client().review_evidence(1, sha, base_sha)

        telemetry.write_text("", encoding="utf-8")
        reused = {
            **sessions[0],
            "name": "reviewer-pr1-reused",
            "issue": "pr1",
        }
        self.append_sessions(self.root, [sessions[0], reused])
        with self.assertRaises(github_api.GitHubError):
            self.client().review_evidence(1, sha, base_sha)

        telemetry.write_text("", encoding="utf-8")
        self.append_sessions(self.root, [sessions[0], sessions[0]])
        with self.assertRaises(github_api.GitHubError):
            self.client().review_evidence(1, sha, base_sha)

        telemetry.write_text("", encoding="utf-8")
        failed = {**sessions[0], "exit": 7, "status": "failed"}
        self.append_sessions(self.root, [failed])
        dispatch_log = self.root / "dispatch.log"
        dispatch_log.write_text(
            f"name: {failed['name']}\n"
            f"thread_id: {failed['thread_id']}\n"
            "last_message: output.md\n"
            "exit: 7\n",
            encoding="utf-8",
        )
        (self.root / "output.md").write_text("usable-looking output\n", encoding="utf-8")
        with self.assertRaises(github_api.GitHubError):
            github_api.validate_reviewer_session(
                dispatch_log,
                telemetry,
                lane="code",
                number=1,
                worktree=self.root,
                expected_exit=7,
            )
        source = (BIN_DIR / "review.sh").read_text(encoding="utf-8")
        self.assertLess(
            source.index('if [ "$CODE_RC" -ne 0 ]'),
            source.index('CODE_RESULT=""'),
        )
        self.assertNotIn("retrying once", source)
        self.assertNotIn("for attempt in 1 2", source)
        self.assertEqual(source.count("comparison_matches_attestation \"$RUN_TMP/"), 2)

    def test_same_head_reruns_select_matching_latest_run(self) -> None:
        sha, base_sha = "1" * 40, "a" * 40
        old_review, old_status, old_sessions, _body, _marker = self.review_bundle(
            self.root,
            sha,
            base_sha,
            run_id="review-old",
            review_id=1,
            status_id=101,
            submitted_at="2026-01-01T00:01:00Z",
        )
        new_review, new_status, new_sessions, _body, _marker = self.review_bundle(
            self.root,
            sha,
            base_sha,
            run_id="review-new",
            review_id=2,
            status_id=102,
            submitted_at="2026-01-01T00:02:00Z",
        )
        old_comment, old_ci_statuses = self.ci_bundle(
            sha,
            base_sha,
            run_id="ci-old",
            comment_id=1,
            created_at="2026-01-01T00:01:00Z",
        )
        new_comment, new_ci_statuses = self.ci_bundle(
            sha,
            base_sha,
            run_id="ci-new",
            comment_id=2,
            created_at="2026-01-01T00:02:00Z",
        )
        self.append_sessions(self.root, [*old_sessions, *new_sessions])
        self.write_state(
            reviews={"1": [old_review, new_review]},
            comments={"1": [old_comment, new_comment]},
            statuses={
                sha: [
                    *old_ci_statuses,
                    old_status,
                    *new_ci_statuses,
                    new_status,
                ]
            },
        )
        self.assertEqual(
            self.client().review_evidence(1, sha, base_sha).attestation.run_id,
            "review-new",
        )
        self.assertEqual(
            self.client().ci_evidence(1, sha, base_sha).run_id,
            "ci-new",
        )

        self.write_state(
            statuses={sha: [*new_ci_statuses, old_status]},
        )
        with self.assertRaises(github_api.GitHubError):
            self.client().review_evidence(1, sha, base_sha)


class AutoFixTests(FakeGhCase):
    """Auto-fix: opt-in, exact-head evidence, complete count, and cap action."""

    def prepare_autofix(self) -> tuple[Path, str, dict]:
        repository, _remote, base_sha, head_sha = self.make_repository()
        local_bin = repository / "local" / "bin"
        local_bin.mkdir(parents=True)
        shutil.copy2(BIN_DIR / "autofix.sh", local_bin / "autofix.sh")
        shutil.copy2(BIN_DIR / "github_api.py", local_bin / "github_api.py")
        pull = pull_row(1, head_sha, base_sha=base_sha)
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
        comment, statuses = self.ci_bundle(
            head_sha,
            pull["base"]["sha"],
            run_id="cap",
            outcomes={"build": "failure"},
        )
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
            comments={"1": [comment]},
            statuses={head_sha: statuses},
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

    def green_state(
        self, sha: str, base_sha: str = "e" * 40, *, root: Path | None = None
    ) -> dict:
        root = root or self.root
        comment, statuses = self.ci_bundle(sha, base_sha)
        review, review_status, sessions, _body, _marker = self.review_bundle(
            root, sha, base_sha, worktree=root
        )
        self.append_sessions(root, sessions)
        return {
            "statuses": {sha: [*statuses, review_status]},
            "comments": {"1": [comment]},
            "reviews": {"1": [review]},
        }

    def test_missing_failing_stale_and_adverse_review_refuse(self) -> None:
        sha = "f" * 40
        base_sha = "e" * 40
        client = self.client()
        with self.assertRaises(pr_merge.GateFailure):
            pr_merge.require_ci(client, 1, sha, base_sha)
        comment, statuses = self.ci_bundle(
            sha, base_sha, outcomes={"build": "failure"}
        )
        state = {"comments": {"1": [comment]}, "statuses": {sha: statuses}}
        self.write_state(**state)
        with self.assertRaises(pr_merge.GateFailure):
            pr_merge.require_ci(client, 1, sha, base_sha)

        state = self.green_state(sha, base_sha)
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
            pr_merge.require_review(client, 1, sha, base_sha)

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

    def prepare_valid_merge(
        self,
    ) -> tuple[Path, str, str, argparse.Namespace]:
        repository, _remote, base_sha, head_sha = self.make_repository()
        pull = pull_row(1, head_sha, base_sha=base_sha)
        ci_comment, statuses = self.ci_bundle(head_sha, base_sha)
        review, review_status, sessions, _body, _marker = self.review_bundle(
            repository, head_sha, base_sha, worktree=repository
        )
        statuses.append(review_status)
        self.append_sessions(repository, sessions)
        self.write_state(
            pulls={"1": pull},
            issues={"1": {**pull, "pull_request": {"url": pull["html_url"]}}},
            statuses={head_sha: statuses},
            comments={"1": [ci_comment]},
            reviews={"1": [review]},
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
        return repository, base_sha, head_sha, args

    def test_valid_gate_invokes_only_guarded_gh_merge(self) -> None:
        repository, _base_sha, head_sha, args = self.prepare_valid_merge()
        with mock.patch.dict(
            os.environ, {"MIPSTARRE_CACHE_ROOT": str(self.root / "cache")}
        ), mock.patch.object(pr_merge, "fast_forward_base"), mock.patch.object(
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

    def test_base_movement_between_evaluations_blocks_merge(self) -> None:
        _repository, base_sha, head_sha, args = self.prepare_valid_merge()
        self.write_state(
            pull_head_sequence=[head_sha] * 6,
            pull_base_sequence=[base_sha] * 4 + ["f" * 40],
            pull_read_count=0,
        )
        with mock.patch.dict(
            os.environ, {"MIPSTARRE_CACHE_ROOT": str(self.root / "cache")}
        ), mock.patch.object(pr_merge, "fast_forward_base"), mock.patch.object(
            pr_merge, "cleanup_feature"
        ):
            with self.assertRaises(pr_merge.GateFailure):
                pr_merge.run(args)
        merge_calls = [
            call for call in self.state()["calls"]
            if call["args"][:2] == ["pr", "merge"] and "--help" not in call["args"]
        ]
        self.assertEqual(merge_calls, [])

    def test_final_same_head_adverse_review_race_blocks_merge(self) -> None:
        _repository, _base_sha, _head_sha, args = self.prepare_valid_merge()
        self.write_state(inject_adverse_review_at=2, review_read_count=0)
        with mock.patch.dict(
            os.environ, {"MIPSTARRE_CACHE_ROOT": str(self.root / "cache")}
        ), mock.patch.object(pr_merge, "fast_forward_base"), mock.patch.object(
            pr_merge, "cleanup_feature"
        ):
            with self.assertRaisesRegex(
                pr_merge.GateFailure, "later exact-head CHANGES_REQUESTED"
            ):
                pr_merge.run(args)
        merge_calls = [
            call for call in self.state()["calls"]
            if call["args"][:2] == ["pr", "merge"] and "--help" not in call["args"]
        ]
        self.assertEqual(merge_calls, [])
        locks = self.root / "cache" / "locks"
        self.assertFalse((locks / "review-1.lock").exists())
        self.assertFalse((locks / "fix-issue-7-test.lock").exists())


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
