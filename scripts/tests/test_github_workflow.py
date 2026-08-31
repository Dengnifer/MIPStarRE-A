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
        dirty = state.get("dirty_worktree_on_pull_read") or {}
        if int(dirty.get("at", -1)) == count:
            target = str(dirty.get("path", ""))
            if target:
                os.makedirs(os.path.dirname(target), exist_ok=True)
                with open(target, "w", encoding="utf-8") as stream:
                    stream.write(str(dirty.get("content", "dirty\n")))
            state["dirty_worktree_on_pull_read"] = {}
        status_injection = state.get("inject_review_status_on_pull_read") or {}
        if int(status_injection.get("at", -1)) == count:
            injected = dict(status_injection.get("row") or {})
            sha = str((row.get("head") or {}).get("sha") or "")
            if injected and sha:
                state.setdefault("statuses", {}).setdefault(sha, []).append(injected)
            state["inject_review_status_on_pull_read"] = {}
        cancellation = state.get("cancel_lock_on_pull_read") or {}
        if int(cancellation.get("at", -1)) == count:
            target = str(cancellation.get("path", ""))
            if target:
                os.makedirs(os.path.dirname(target), exist_ok=True)
                with open(target, "w", encoding="utf-8") as stream:
                    stream.write("test late supersession\n")
            state["cancel_lock_on_pull_read"] = {}
            state["cancel_lock_on_pull_read_fired"] = count
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
        read_count = int(state.get("comment_read_count", 0))
        dirty = state.get("dirty_worktree_on_comment_read") or {}
        if int(dirty.get("at", -1)) == read_count:
            target = str(dirty.get("path", ""))
            if target:
                os.makedirs(os.path.dirname(target), exist_ok=True)
                with open(target, "w", encoding="utf-8") as stream:
                    stream.write(str(dirty.get("content", "dirty\n")))
            state["dirty_worktree_on_comment_read"] = {}
        state["comment_read_count"] = read_count + 1
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
        review_injection = state.get("inject_review_on_review_read") or {}
        if int(review_injection.get("at", -1)) == read_count:
            injected = dict(review_injection.get("row") or {})
            if injected:
                reviews.append(injected)
            state["inject_review_on_review_read"] = {}
        movement = state.get("move_pull_base_on_review_read") or {}
        if int(movement.get("at", -1)) == read_count:
            pull = state.setdefault("pulls", {}).get(number, {})
            pull.setdefault("base", {})["sha"] = str(movement.get("sha", ""))
            state["move_pull_base_on_review_read"] = {}
        cancellation = state.get("cancel_lock_on_review_read") or {}
        if int(cancellation.get("at", -1)) == read_count:
            target = str(cancellation.get("path", ""))
            if target:
                os.makedirs(os.path.dirname(target), exist_ok=True)
                with open(target, "w", encoding="utf-8") as stream:
                    stream.write("test publication cancellation\n")
            state["cancel_lock_on_review_read"] = {}
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
        if state.pop("ambiguous_review_once", False):
            fail("HTTP 503 Service Unavailable")
        if state.pop("corrupt_review_response", False):
            emit({**row, "commit_id": "0" * 40})
        emit(row)

if len(tail) == 3 and tail[0] == "commits" and tail[2] == "statuses":
    sha = tail[1]
    read_count = int(state.get("status_read_count", 0))
    movement = state.get("move_pull_base_on_status_read") or {}
    if int(movement.get("at", -1)) == read_count:
        for pull in state.setdefault("pulls", {}).values():
            if str((pull.get("head") or {}).get("sha") or "") == sha:
                pull.setdefault("base", {})["sha"] = str(movement.get("sha", ""))
        state["move_pull_base_on_status_read"] = {}
    status_injection = state.get("inject_review_status_on_status_read") or {}
    if int(status_injection.get("at", -1)) == read_count:
        injected = dict(status_injection.get("row") or {})
        if injected:
            state.setdefault("statuses", {}).setdefault(sha, []).append(injected)
        state["inject_review_status_on_status_read"] = {}
    cancellation = state.get("cancel_lock_on_status_read") or {}
    if int(cancellation.get("at", -1)) == read_count:
        target = str(cancellation.get("path", ""))
        if target:
            os.makedirs(os.path.dirname(target), exist_ok=True)
            with open(target, "w", encoding="utf-8") as stream:
                stream.write("test publication cancellation\n")
        state["cancel_lock_on_status_read"] = {}
    state["status_read_count"] = read_count + 1
    emit(page(state.setdefault("statuses", {}).get(sha, []), parsed.query))

if len(tail) == 2 and tail[0] == "statuses" and method == "POST":
    sha = tail[1]
    if (
        state.get("fail_review_summary_final_once")
        and str((payload or {}).get("context", "")).casefold()
        == "local-review/summary"
        and str((payload or {}).get("state", "")).casefold() in {"success", "failure"}
    ):
        state["fail_review_summary_final_once"] = False
        fail("HTTP 503 injected final review status failure")
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


FAKE_DISPATCH = r'''#!/usr/bin/env python3
import json
import os
import pathlib
import signal
import subprocess
import sys


def option(name, default=""):
    try:
        return sys.argv[sys.argv.index(name) + 1]
    except (ValueError, IndexError):
        return default


cache = pathlib.Path(os.environ["MIPSTARRE_CACHE_ROOT"])
cache.mkdir(parents=True, exist_ok=True)
counter_path = cache / "fake-dispatch-count"
count = int(counter_path.read_text(encoding="utf-8") if counter_path.exists() else "0") + 1
counter_path.write_text(str(count), encoding="utf-8")
(cache / "fake-dispatch-observed").write_text(str(count), encoding="utf-8")
if "--" in sys.argv and sys.argv.index("--") + 1 < len(sys.argv):
    task = sys.argv[sys.argv.index("--") + 1]
    (cache / ("fake-dispatch-task-%d.md" % count)).write_text(
        task, encoding="utf-8"
    )

role = option("--role")
issue = option("--issue")
pr = option("--pr")
worktree = pathlib.Path(option("--worktree")).resolve()
branch = os.environ.get("MIPSTARRE_TEST_BRANCH", "issue-7-test").replace("/", "-")
fix_lock = cache / "locks" / ("fix-" + branch + ".lock")
if fix_lock.is_dir() and (fix_lock / "pid").exists() and (fix_lock / "owner").exists():
    (cache / "fake-fix-lock-observed").write_text("yes", encoding="utf-8")

action = os.environ.get("MIPSTARRE_TEST_LOCK_ACTION", "")
if action == "cancel":
    (fix_lock / "cancel").write_text("test supersession\n", encoding="utf-8")
elif action == "steal":
    (fix_lock / "owner").write_text("different-owner\n", encoding="utf-8")
signal_target = os.environ.get("MIPSTARRE_TEST_SIGNAL_PARENT")
if signal_target == "TERM":
    os.kill(os.getppid(), signal.SIGTERM)
elif signal_target == "TERM_REVIEW_WRAPPER":
    parent = os.getppid()
    with open("/proc/%d/status" % parent, encoding="utf-8") as stream:
        grandparent = next(
            int(line.split()[1])
            for line in stream
            if line.startswith("PPid:")
        )
    os.kill(grandparent, signal.SIGTERM)

if role == "reviewer":
    guard_action = os.environ.get("MIPSTARRE_TEST_GUARD_ACTION", "")
    state_path = os.environ.get("FAKE_GH_STATE")
    if state_path and guard_action in {
        "cancel-review-post",
        "cancel-status-post",
        "move-base-review-post",
        "move-base-status-post",
    }:
        with open(state_path, encoding="utf-8") as stream:
            state = json.load(stream)
        if guard_action == "cancel-review-post":
            counter_key = "review_read_count"
            injection_key = "cancel_lock_on_review_read"
            injection = {
                "at": int(state.get(counter_key, 0)) + 1,
                "path": str(fix_lock / "cancel"),
            }
        elif guard_action == "cancel-status-post":
            counter_key = "status_read_count"
            injection_key = "cancel_lock_on_status_read"
            injection = {
                "at": int(state.get(counter_key, 0)) + 1,
                "path": str(fix_lock / "cancel"),
            }
        elif guard_action == "move-base-review-post":
            counter_key = "review_read_count"
            injection_key = "move_pull_base_on_review_read"
            injection = {
                "at": int(state.get(counter_key, 0)) + 2,
                "sha": "f" * 40,
            }
        else:
            counter_key = "status_read_count"
            injection_key = "move_pull_base_on_status_read"
            injection = {
                "at": int(state.get(counter_key, 0)) + 2,
                "sha": "f" * 40,
            }
        state[injection_key] = injection
        temporary = state_path + ".tmp"
        with open(temporary, "w", encoding="utf-8") as stream:
            json.dump(state, stream)
        os.replace(temporary, state_path)
    output = os.environ.get(
        "MIPSTARRE_TEST_REVIEW_OUTPUT",
        "## Findings\n\n- none\n\n## Review\n\nNo findings.\n\nVERDICT: APPROVED\n",
    )
    message = cache / ("review-message-%d.md" % count)
    message.write_text(output, encoding="utf-8")
    name = "reviewer-pr%s-test-%d" % (pr, count)
    thread = "thread-review-test-%08d" % count
    start = "2026-01-01T00:00:%02d+00:00" % min(count, 59)
    end = "2026-01-01T00:01:%02d+00:00" % min(count, 59)
    telemetry = worktree / "results" / "telemetry" / "sessions.jsonl"
    telemetry.parent.mkdir(parents=True, exist_ok=True)
    row = {
        "name": name,
        "role": "reviewer",
        "issue": issue,
        "pr": pr,
        "thread_id": thread,
        "start": start,
        "end": end,
        "wall_s": 60,
        "usage": {},
        "turns": 1,
        "exit": 0,
        "dispatcher": "fake",
        "worktree": str(worktree),
        "status": "done",
    }
    with telemetry.open("a", encoding="utf-8") as stream:
        stream.write(json.dumps(row) + "\n")
    print("name: " + name)
    print("thread_id: " + thread)
    print("last_message: " + str(message))
    print("exit: 0")
else:
    relative = os.environ.get("MIPSTARRE_TEST_FIX_FILE", "README.md")
    target = worktree / relative
    with target.open("a", encoding="utf-8") as stream:
        stream.write(os.environ.get("MIPSTARRE_TEST_FIX_TEXT", "fixed\n"))
    state_path = os.environ.get("FAKE_GH_STATE")
    if state_path and os.environ.get("MIPSTARRE_TEST_CANCEL_DURING_PRE_PUSH"):
        with open(state_path, encoding="utf-8") as stream:
            state = json.load(stream)
        state["cancel_lock_on_pull_read"] = {
            "at": int(state.get("pull_read_count", 0)) + 2,
            "path": str(fix_lock / "cancel"),
        }
        temporary = state_path + ".tmp"
        with open(temporary, "w", encoding="utf-8") as stream:
            json.dump(state, stream)
        os.replace(temporary, state_path)
    moved_base = os.environ.get("MIPSTARRE_TEST_MOVE_BASE_AFTER_DISPATCH")
    if state_path and moved_base:
        with open(state_path, encoding="utf-8") as stream:
            state = json.load(stream)
        state["pulls"][pr]["base"]["sha"] = moved_base
        temporary = state_path + ".tmp"
        with open(temporary, "w", encoding="utf-8") as stream:
            json.dump(state, stream)
        os.replace(temporary, state_path)
    moved_local_base = os.environ.get("MIPSTARRE_TEST_MOVE_LOCAL_BASE_AFTER_DISPATCH")
    if moved_local_base:
        subprocess.run(
            [
                "git",
                "-C",
                str(worktree),
                "update-ref",
                "refs/remotes/github/main",
                moved_local_base,
            ],
            check=True,
        )
    message = cache / ("fix-message-%d.md" % count)
    message.write_text("fix complete\n", encoding="utf-8")
    print("name: prover-pr%s-test-%d" % (pr, count))
    print("thread_id: thread-prover-test-%08d" % count)
    print("last_message: " + str(message))
    print("exit: 0")
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

    def make_repository(
        self,
        *,
        name: str = "repository",
        base_sources: dict[str, Path] | None = None,
        base_text: dict[str, str] | None = None,
    ) -> tuple[Path, Path, str, str]:
        repository = self.root / name
        remote = self.root / f"{name}-github.git"
        repository.mkdir()
        run_git(repository, "init", "-b", "main")
        run_git(repository, "config", "user.name", "Workflow Test")
        run_git(repository, "config", "user.email", "workflow@example.invalid")
        (repository / "README.md").write_text("base\n", encoding="utf-8")
        (repository / ".gitignore").write_text(
            "results/telemetry/sessions.jsonl\n", encoding="utf-8"
        )
        for relative, source in (base_sources or {}).items():
            destination = repository / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, destination)
        for relative, content in (base_text or {}).items():
            destination = repository / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_text(content, encoding="utf-8")
            if destination.suffix == ".sh":
                destination.chmod(0o755)
        run_git(repository, "add", "-A")
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
        comment_fallback: bool = False,
        extra_prose: str = "",
        ledger_override: str | None = None,
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
            f"- [ ] F{index} (changes) `path.py:{index}` — defect {index}"
            for index in range(1, findings + 1)
        ]
        ledger = (
            ledger_override
            if ledger_override is not None
            else "\n".join(finding_lines) if finding_lines else "- none"
        )
        event = "COMMENT" if findings == 0 else "REQUEST_CHANGES"
        fallback = "none" if findings == 0 else "COMMENT"
        attestation = {
            "schema": 1,
            "pr": 1,
            "head_sha": head_sha,
            "base_sha": base_sha,
            "run_id": run_id,
            "canonical_findings": findings,
            "event": event,
            "fallback": fallback,
            "lanes": [lane],
        }
        prefix = (
            "# Local review ledger\n\n"
            + (extra_prose.rstrip() + "\n\n" if extra_prose else "")
            + "## Code review lane\n\n"
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
            f"fallback={fallback} digest={digest} -->"
        )
        body = prefix + marker + "\n"
        state = "COMMENTED" if findings == 0 or comment_fallback else "CHANGES_REQUESTED"
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

    def prepare_ci(self, *, name: str = "repository") -> tuple[Path, str, str]:
        repository, _remote, base_sha, head_sha = self.make_repository(
            name=name,
            base_sources={
                "local/bin/ci.sh": BIN_DIR / "ci.sh",
                "local/bin/github_api.py": BIN_DIR / "github_api.py",
            }
        )
        pull = pull_row(1, head_sha, base_sha=base_sha)
        self.write_state(
            pulls={"1": pull},
            issues={"1": {**pull, "pull_request": {"url": pull["html_url"]}}},
            commits={"1": [{"sha": head_sha, "commit": {"message": "Feature"}}]},
            comments={},
            reviews={},
            statuses={},
            calls=[],
            pull_read_count=0,
            pull_head_sequence=[],
            pull_base_sequence=[],
            dirty_worktree_on_pull_read={},
            comment_read_count=0,
            dirty_worktree_on_comment_read={},
            status_read_count=0,
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

    def test_dirty_tracked_staged_and_untracked_trees_publish_nothing(self) -> None:
        for index, kind in enumerate(("tracked", "staged", "untracked"), start=1):
            with self.subTest(kind=kind):
                repository, _base_sha, head_sha = self.prepare_ci(
                    name=f"ci-dirty-{index}"
                )
                if kind == "untracked":
                    (repository / "untracked.txt").write_text("dirty\n", encoding="utf-8")
                else:
                    (repository / "README.md").write_text(
                        "base\nfeature\ndirty\n", encoding="utf-8"
                    )
                    if kind == "staged":
                        run_git(repository, "add", "README.md")
                result = self.run_ci(repository)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("worktree", result.stderr)
                self.assertEqual(self.state()["statuses"].get(head_sha), None)
                self.assertEqual(self.state()["comments"], {})

    def test_tree_dirtied_at_final_recheck_invalidates_all_statuses(self) -> None:
        repository, _base_sha, head_sha = self.prepare_ci(name="ci-final-dirty")
        dirty_path = repository / "late-untracked.txt"
        self.write_state(
            dirty_worktree_on_pull_read={
                "at": 1,
                "path": str(dirty_path),
                "content": "late dirt\n",
            }
        )
        result = self.run_ci(repository)
        self.assertNotEqual(result.returncode, 0)
        latest = self.client().latest_statuses(head_sha)
        self.assertEqual(set(latest), set(github_api.CANONICAL_CI_CONTEXTS))
        self.assertTrue(all(row["state"] == "error" for row in latest.values()))
        self.assertEqual(self.state()["comments"], {})

    def test_tree_dirtied_during_comment_lookup_blocks_manifest(self) -> None:
        repository, _base_sha, head_sha = self.prepare_ci(name="ci-comment-dirty")
        dirty_path = repository / "comment-window-untracked.txt"
        self.write_state(
            dirty_worktree_on_comment_read={
                "at": 0,
                "path": str(dirty_path),
                "content": "dirty during comment lookup\n",
            }
        )
        result = self.run_ci(repository)
        self.assertNotEqual(result.returncode, 0)
        self.assertTrue(dirty_path.exists())
        latest = self.client().latest_statuses(head_sha)
        self.assertEqual(set(latest), set(github_api.CANONICAL_CI_CONTEXTS))
        self.assertTrue(all(row["state"] == "error" for row in latest.values()))
        self.assertEqual(self.state()["comments"].get("1", []), [])


class ReviewPublicationTests(FakeGhCase):
    """Group 5: exact-commit review events, fallback, ledger, and head checks."""

    def prepare_review_shell(
        self,
        *,
        name: str = "review-shell",
        outcomes: dict[str, str] | None = None,
    ) -> tuple[Path, str, str, dict]:
        repository, _remote, base_sha, head_sha = self.make_repository(
            name=name,
            base_sources={
                "local/bin/review.sh": BIN_DIR / "review.sh",
                "local/bin/github_api.py": BIN_DIR / "github_api.py",
            },
            base_text={
                "local/bin/dispatch.sh": FAKE_DISPATCH,
                ".github/prompts/claude-code-review-system-prompt.md": (
                    "Review committed workflow changes.\n"
                ),
                ".github/prompts/claude-code-review-prompt.md": (
                    "Report canonical findings and a final verdict.\n"
                ),
            },
        )
        pull = pull_row(1, head_sha, base_sha=base_sha)
        comment, statuses = self.ci_bundle(
            head_sha,
            base_sha,
            outcomes=outcomes,
        )
        self.write_state(
            pulls={"1": pull},
            issues={"1": {**pull, "pull_request": {"url": pull["html_url"]}}},
            comments={"1": [comment]},
            reviews={},
            statuses={head_sha: statuses},
            commits={"1": [{"sha": head_sha, "commit": {"message": "Feature"}}]},
            calls=[],
            pull_read_count=0,
            pull_head_sequence=[],
            pull_base_sequence=[],
            dirty_worktree_on_pull_read={},
            review_read_count=0,
            status_read_count=0,
            cancel_lock_on_review_read={},
            cancel_lock_on_status_read={},
            move_pull_base_on_review_read={},
            move_pull_base_on_status_read={},
            inject_review_status_on_status_read={},
            fail_review_summary_final_once=False,
            inject_review_status_on_pull_read={},
        )
        return repository, base_sha, head_sha, pull

    def review_cache(self, repository: Path) -> Path:
        return self.root / f"cache-{repository.name}"

    def run_review(
        self,
        repository: Path,
        *,
        output: str | None = None,
        trusted_ref: str | None = None,
        extra_env: dict[str, str] | None = None,
    ) -> subprocess.CompletedProcess[str]:
        environment = os.environ.copy()
        environment.update(
            {
                "MIPSTARRE_CACHE_ROOT": str(self.review_cache(repository)),
                "MIPSTARRE_REVIEW_LOCK_WAIT": "0",
                "MIPSTARRE_TEST_BRANCH": "issue-7-test",
            }
        )
        if output is not None:
            environment["MIPSTARRE_TEST_REVIEW_OUTPUT"] = output
        if trusted_ref is not None:
            environment["MIPSTARRE_TRUSTED_REF"] = trusted_ref
        environment.update(extra_env or {})
        return subprocess.run(
            ["bash", str(repository / "local/bin/review.sh"), "1"],
            cwd=repository,
            env=environment,
            text=True,
            capture_output=True,
            check=False,
        )

    def dispatch_count(self, repository: Path) -> int:
        path = self.review_cache(repository) / "fake-dispatch-count"
        return int(path.read_text(encoding="utf-8")) if path.exists() else 0

    def review_posts(self) -> list[dict]:
        return [
            call
            for call in self.state()["calls"]
            if call["args"][:3] == ["api", "--method", "POST"]
            and call["args"][3].endswith("pulls/1/reviews")
        ]

    def test_review_refuses_failed_ci_before_dispatch(self) -> None:
        repository, _base_sha, _head_sha, _pull = self.prepare_review_shell(
            outcomes={"build": "failure"}
        )
        result = self.run_review(repository)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("not one successful exact-head/base run", result.stderr)
        self.assertEqual(self.dispatch_count(repository), 0)
        self.assertEqual(self.review_posts(), [])

    def test_review_refuses_dirty_tracked_staged_and_untracked_trees(self) -> None:
        for index, kind in enumerate(("tracked", "staged", "untracked"), start=1):
            with self.subTest(kind=kind):
                repository, _base_sha, _head_sha, _pull = self.prepare_review_shell(
                    name=f"review-dirty-{index}"
                )
                if kind == "untracked":
                    (repository / "untracked.txt").write_text(
                        "dirty\n", encoding="utf-8"
                    )
                else:
                    (repository / "README.md").write_text(
                        "base\nfeature\ndirty\n", encoding="utf-8"
                    )
                    if kind == "staged":
                        run_git(repository, "add", "README.md")
                result = self.run_review(repository)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("dirty", result.stderr)
                self.assertEqual(self.dispatch_count(repository), 0)
                self.assertEqual(self.review_posts(), [])

    def test_reviewer_output_parser_rejects_every_noncanonical_shape(self) -> None:
        finding = "- [ ] F1 (changes) `README.md:2` — defect"
        malformed = {
            "missing-findings": "## Review\n\nText.\n\nVERDICT: APPROVED\n",
            "duplicate-findings": (
                "## Findings\n\n- none\n\n## Findings\n\n- none\n\n"
                "VERDICT: APPROVED\n"
            ),
            "malformed-duplicate-findings": (
                "## Findings\n\n- none\n\n### findings\n\n- none\n\n"
                "VERDICT: APPROVED\n"
            ),
            "punctuated-duplicate-findings": (
                "## Findings\n\n- none\n\n## Findings:\n\n"
                "- [ ] F1 (changes) `README.md:2` — hidden defect\n\n"
                "VERDICT: APPROVED\n"
            ),
            "word-character-duplicate-findings": (
                "## Findings\n\n- none\n\n## Findings_hidden\n\n"
                "- [ ] F1 (changes) `README.md:2` — hidden defect\n\n"
                "VERDICT: APPROVED\n"
            ),
            "malformed-finding": (
                "## Findings\n\n- [ ] F1 (changes) `README.md:2` - defect\n\n"
                "VERDICT: CHANGES_REQUESTED\n"
            ),
            "missing-location-line": (
                "## Findings\n\n- [ ] F1 (changes) `README.md` — defect\n\n"
                "VERDICT: CHANGES_REQUESTED\n"
            ),
            "location-with-spaces": (
                "## Findings\n\n"
                "- [ ] F1 (changes) `anything with spaces:2` — defect\n\n"
                "VERDICT: CHANGES_REQUESTED\n"
            ),
            "location-outside-repository": (
                "## Findings\n\n"
                "- [ ] F1 (changes) `../README.md:2` — defect\n\n"
                "VERDICT: CHANGES_REQUESTED\n"
            ),
            "mixed-none": (
                f"## Findings\n\n- none\n{finding}\n\n"
                "VERDICT: CHANGES_REQUESTED\n"
            ),
            "missing-verdict": "## Findings\n\n- none\n",
            "duplicate-verdict": (
                "## Findings\n\n- none\n\nVERDICT: APPROVED\n"
                "VERDICT: APPROVED\n"
            ),
            "nonfinal-verdict": (
                "## Findings\n\n- none\n\nVERDICT: APPROVED\ntrailing text\n"
            ),
            "malformed-verdict": (
                "## Findings\n\n- none\n\nVerdict: APPROVED\n"
            ),
            "malformed-extra-verdict": (
                "## Findings\n\n- none\n\nVerdict: COMMENTED\n\n"
                "VERDICT: APPROVED\n"
            ),
            "word-character-extra-verdict": (
                "## Findings\n\n- none\n\nVERDICT_COMMENTED\n\n"
                "VERDICT: APPROVED\n"
            ),
        }
        for index, (case, output) in enumerate(malformed.items(), start=1):
            with self.subTest(case=case):
                repository, _base_sha, head_sha, _pull = self.prepare_review_shell(
                    name=f"review-parser-{index}"
                )
                result = self.run_review(repository, output=output)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(self.dispatch_count(repository), 1)
                self.assertEqual(self.review_posts(), [])
                latest = self.client().latest_statuses(head_sha).get(
                    github_api.REVIEW_CONTEXT.casefold(), {}
                )
                self.assertNotEqual(latest.get("state"), "success")

    def test_reviewer_output_preserves_all_canonical_checkbox_states(self) -> None:
        repository, base_sha, head_sha, _pull = self.prepare_review_shell()
        lines = [
            "- [ ] F1 (changes) `README.md:2` — unresolved defect",
            "- [x] F2 (advisory) `README.md:1` — resolved note",
            "- [-] F3 (blocker) `README.md:3` — outdated location",
        ]
        output = (
            "## Findings\n\n"
            + "\n".join(lines)
            + "\n\n## Review\n\nOne finding remains.\n\nVERDICT: COMMENTED\n"
        )
        result = self.run_review(repository, output=output)
        self.assertEqual(result.returncode, 1, result.stderr + result.stdout)
        self.assertEqual(self.dispatch_count(repository), 1)
        self.assertTrue(
            (self.review_cache(repository) / "fake-fix-lock-observed").exists()
        )
        reviews = self.state()["reviews"]["1"]
        self.assertEqual(len(reviews), 1)
        for line in lines:
            self.assertIn(line, reviews[0]["body"])
        dispatched_task = (
            self.review_cache(repository) / "fake-dispatch-task-1.md"
        ).read_text(encoding="utf-8")
        self.assertIn("`[ ]` unresolved", dispatched_task)
        self.assertIn("`[x]` resolved", dispatched_task)
        self.assertIn("`[-]` outdated", dispatched_task)
        attestation = self.client(repository).review_attestation(
            1, head_sha, base_sha
        )
        self.assertEqual(attestation.findings, 1)

    def test_attestation_rejects_noncanonical_finding_location(self) -> None:
        sha, base_sha = "b" * 40, "a" * 40
        review, _status, sessions, _body, _marker = self.review_bundle(
            self.root,
            sha,
            base_sha,
            findings=1,
            ledger_override=(
                "- [ ] F1 (changes) `anything with spaces:2` — defect"
            ),
        )
        self.append_sessions(self.root, sessions)
        self.write_state(reviews={"1": [review]}, statuses={})
        with self.assertRaisesRegex(github_api.GitHubError, "malformed"):
            self.client().review_attestation(1, sha, base_sha)

    def test_review_recovers_matching_missing_summary_without_reposting(self) -> None:
        repository, base_sha, head_sha, _pull = self.prepare_review_shell()
        self.write_state(fail_review_summary_final_once=True)
        first = self.run_review(repository)
        self.assertNotEqual(first.returncode, 0)
        self.assertEqual(self.dispatch_count(repository), 1)
        self.assertEqual(len(self.review_posts()), 1)
        state = self.client(repository).review_publication_state(
            1, head_sha, base_sha
        )
        self.assertEqual(state["state"], "recoverable")

        second = self.run_review(repository)
        self.assertEqual(second.returncode, 0, second.stderr + second.stdout)
        self.assertEqual(self.dispatch_count(repository), 1)
        self.assertEqual(len(self.review_posts()), 1)
        self.client(repository).review_evidence(1, head_sha, base_sha)

    def test_review_does_not_recover_unrelated_pending_run(self) -> None:
        repository, base_sha, head_sha, _pull = self.prepare_review_shell()
        first = self.run_review(repository)
        self.assertEqual(first.returncode, 0, first.stderr + first.stdout)
        self.client(repository).post_status(
            head_sha,
            github_api.REVIEW_CONTEXT,
            "pending",
            github_api.review_pending_description("unrelated-run"),
        )
        before_dispatch = self.dispatch_count(repository)
        before_posts = len(self.review_posts())
        second = self.run_review(repository)
        self.assertNotEqual(second.returncode, 0)
        self.assertEqual(self.dispatch_count(repository), before_dispatch)
        self.assertEqual(len(self.review_posts()), before_posts)

    def test_recovery_reclassifies_status_after_its_final_boundary(self) -> None:
        repository, _base_sha, head_sha, _pull = self.prepare_review_shell(
            name="review-recovery-race"
        )
        self.write_state(fail_review_summary_final_once=True)
        first = self.run_review(repository)
        self.assertNotEqual(first.returncode, 0)
        before_dispatch = self.dispatch_count(repository)
        before_posts = len(self.review_posts())
        unrelated = {
            "id": 999,
            "sha": head_sha,
            "context": github_api.REVIEW_CONTEXT,
            "state": "pending",
            "description": github_api.render_status_description(
                head_sha,
                github_api.REVIEW_CONTEXT,
                "pending",
                github_api.review_pending_description("race-run"),
            ),
            "created_at": "2099-01-01T00:00:00Z",
        }
        self.write_state(
            status_read_count=0,
            inject_review_status_on_status_read={"at": 3, "row": unrelated},
        )
        second = self.run_review(repository)
        self.assertNotEqual(second.returncode, 0)
        self.assertEqual(self.dispatch_count(repository), before_dispatch)
        self.assertEqual(len(self.review_posts()), before_posts)
        latest = self.client(repository).latest_statuses(head_sha)[
            github_api.REVIEW_CONTEXT.casefold()
        ]
        self.assertEqual(latest["description"], unrelated["description"])

    def test_same_head_stale_base_attestation_is_not_recovered(self) -> None:
        repository, base_sha, head_sha, pull = self.prepare_review_shell()
        first = self.run_review(repository)
        self.assertEqual(first.returncode, 0, first.stderr + first.stdout)
        new_base = run_git(
            repository,
            "commit-tree",
            f"{base_sha}^{{tree}}",
            "-p",
            base_sha,
            "-m",
            "Moved base",
        )
        run_git(repository, "update-ref", "refs/remotes/github/main", new_base)
        pull["base"]["sha"] = new_base
        comment, ci_statuses = self.ci_bundle(
            head_sha, new_base, run_id="ci-moved-base", comment_id=2
        )
        old_review_status = {
            **self.client(repository).latest_statuses(head_sha)[
                github_api.REVIEW_CONTEXT.casefold()
            ],
            "id": 0,
            "created_at": "2025-01-01T00:00:00Z",
        }
        self.write_state(
            pulls={"1": pull},
            issues={"1": {**pull, "pull_request": {"url": pull["html_url"]}}},
            comments={"1": [comment]},
            statuses={head_sha: [*ci_statuses, old_review_status]},
            pull_read_count=0,
            calls=[],
        )
        second = self.run_review(repository)
        self.assertEqual(second.returncode, 0, second.stderr + second.stdout)
        self.assertEqual(self.dispatch_count(repository), 2)
        self.assertEqual(len(self.review_posts()), 1)
        reviews = self.state()["reviews"]["1"]
        self.assertEqual(len(reviews), 2)
        self.assertIn(f'"base_sha": "{new_base}"', reviews[-1]["body"])

    def test_trusted_ref_resolving_to_reviewed_head_is_rejected(self) -> None:
        repository, _base_sha, _head_sha, _pull = self.prepare_review_shell()
        result = self.run_review(repository, trusted_ref="HEAD")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("reviewed head is the trusted prompt commit", result.stderr)
        self.assertEqual(self.dispatch_count(repository), 0)
        self.assertEqual(self.review_posts(), [])

    def test_review_aborts_when_branch_reservation_is_cancelled_or_stolen(self) -> None:
        for action in ("cancel", "steal"):
            with self.subTest(action=action):
                repository, _base_sha, head_sha, _pull = self.prepare_review_shell(
                    name=f"review-lock-{action}"
                )
                result = self.run_review(
                    repository,
                    extra_env={"MIPSTARRE_TEST_LOCK_ACTION": action},
                )
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(self.dispatch_count(repository), 1)
                self.assertTrue(
                    (self.review_cache(repository) / "fake-fix-lock-observed").exists()
                )
                self.assertEqual(self.review_posts(), [])
                latest = self.client().latest_statuses(head_sha)[
                    github_api.REVIEW_CONTEXT.casefold()
                ]
                self.assertNotEqual(latest["state"], "success")

    def test_review_term_signal_exits_nonzero_and_releases_owned_locks(self) -> None:
        repository, _base_sha, head_sha, _pull = self.prepare_review_shell(
            name="review-term-signal"
        )
        result = self.run_review(
            repository,
            extra_env={"MIPSTARRE_TEST_SIGNAL_PARENT": "TERM_REVIEW_WRAPPER"},
        )
        self.assertEqual(result.returncode, 143, result.stderr + result.stdout)
        cache = self.review_cache(repository)
        self.assertFalse((cache / "locks/review-1.lock").exists())
        self.assertFalse((cache / "locks/fix-issue-7-test.lock").exists())
        self.assertEqual(self.review_posts(), [])
        latest = self.client().latest_statuses(head_sha)[
            github_api.REVIEW_CONTEXT.casefold()
        ]
        self.assertEqual(latest["state"], "pending")

    def test_review_cancel_during_idempotency_lookup_blocks_review_post(self) -> None:
        repository, _base_sha, head_sha, _pull = self.prepare_review_shell(
            name="review-cancel-before-post"
        )
        result = self.run_review(
            repository,
            extra_env={"MIPSTARRE_TEST_GUARD_ACTION": "cancel-review-post"},
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(self.dispatch_count(repository), 1)
        self.assertEqual(self.review_posts(), [])
        latest = self.client().latest_statuses(head_sha)[
            github_api.REVIEW_CONTEXT.casefold()
        ]
        self.assertEqual(latest["state"], "pending")

    def test_review_cancel_during_status_lookup_blocks_final_status(self) -> None:
        repository, _base_sha, head_sha, _pull = self.prepare_review_shell(
            name="review-cancel-before-status"
        )
        result = self.run_review(
            repository,
            extra_env={"MIPSTARRE_TEST_GUARD_ACTION": "cancel-status-post"},
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(self.dispatch_count(repository), 1)
        self.assertEqual(len(self.review_posts()), 1)
        latest = self.client().latest_statuses(head_sha)[
            github_api.REVIEW_CONTEXT.casefold()
        ]
        self.assertEqual(latest["state"], "pending")

    def test_review_base_move_during_identity_lookup_blocks_review_post(self) -> None:
        repository, _base_sha, _head_sha, _pull = self.prepare_review_shell(
            name="review-base-before-post"
        )
        result = self.run_review(
            repository,
            extra_env={"MIPSTARRE_TEST_GUARD_ACTION": "move-base-review-post"},
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(self.dispatch_count(repository), 1)
        self.assertEqual(self.review_posts(), [])

    def test_review_base_move_during_reclassification_blocks_final_status(self) -> None:
        repository, _base_sha, head_sha, _pull = self.prepare_review_shell(
            name="review-base-before-status"
        )
        result = self.run_review(
            repository,
            extra_env={"MIPSTARRE_TEST_GUARD_ACTION": "move-base-status-post"},
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(self.dispatch_count(repository), 1)
        self.assertEqual(len(self.review_posts()), 1)
        latest = self.client().latest_statuses(head_sha)[
            github_api.REVIEW_CONTEXT.casefold()
        ]
        self.assertEqual(latest["state"], "pending")

    def test_statusless_attestation_is_valid_but_not_merge_evidence(self) -> None:
        sha, base_sha = "b" * 40, "a" * 40
        review, _status, sessions, body, _marker = self.review_bundle(
            self.root, sha, base_sha
        )
        self.append_sessions(self.root, sessions)
        self.write_state(reviews={"1": [review]}, statuses={})
        self.assertEqual(self.client().review_ledger(1, sha, base_sha)["body"], body)
        with self.assertRaises(github_api.GitHubError):
            self.client().review_evidence(1, sha, base_sha)

    def test_reviewer_session_and_thread_cannot_cross_attestations(self) -> None:
        sha, base_sha = "c" * 40, "a" * 40
        original, _status, sessions, _body, _marker = self.review_bundle(
            self.root, sha, base_sha, run_id="original"
        )
        self.append_sessions(self.root, sessions)

        duplicate = {**original, "id": 2, "submitted_at": "2026-01-01T00:03:00Z"}
        self.write_state(reviews={"1": [original, duplicate]})
        self.assertEqual(
            self.client().latest_review_attestation(1).run_id, "original"
        )

        reused_name, _status, _sessions, _body, _marker = self.review_bundle(
            self.root,
            sha,
            base_sha,
            run_id="reused-name",
            review_id=3,
            submitted_at="2026-01-01T00:04:00Z",
            session_name=sessions[0]["name"],
            thread_id="thread-reused-name",
        )
        self.write_state(reviews={"1": [original, reused_name]})
        with self.assertRaisesRegex(github_api.GitHubError, "reviewer session"):
            self.client().latest_review_attestation(1)

        reused_thread, _status, _sessions, _body, _marker = self.review_bundle(
            self.root,
            sha,
            base_sha,
            run_id="reused-thread",
            review_id=4,
            submitted_at="2026-01-01T00:05:00Z",
            session_name="reviewer-pr1-reused-thread",
            thread_id=sessions[0]["thread_id"],
        )
        self.write_state(reviews={"1": [original, reused_thread]})
        with self.assertRaisesRegex(github_api.GitHubError, "thread"):
            self.client().latest_review_attestation(1)

    def test_review_run_id_cannot_cross_attestations_or_bases(self) -> None:
        sha, old_base, new_base = "c" * 40, "a" * 40, "b" * 40
        original, _status, original_sessions, _body, _marker = self.review_bundle(
            self.root, sha, old_base, run_id="shared-run"
        )
        replay, _status, replay_sessions, replay_body, replay_marker = (
            self.review_bundle(
                self.root,
                sha,
                new_base,
                run_id="shared-run",
                review_id=2,
                submitted_at="2026-01-01T00:03:00Z",
                session_name="reviewer-pr1-shared-run-new-base",
                thread_id="thread-shared-run-new-base",
            )
        )
        self.write_state(reviews={"1": [original]}, calls=[])
        with self.assertRaisesRegex(github_api.GitHubError, "review run id"):
            self.client().review_once(
                1, sha, replay_body, "COMMENT", replay_marker
            )
        self.assertEqual(self.review_posts(), [])

        self.append_sessions(self.root, [*original_sessions, *replay_sessions])
        self.write_state(reviews={"1": [original, replay]})
        with self.assertRaisesRegex(github_api.GitHubError, "review run"):
            self.client().review_publication_state(1, sha, new_base)

    def test_review_publication_rejects_identity_replay_before_post(self) -> None:
        sha, base_sha = "d" * 40, "a" * 40
        original, _status, sessions, _body, _marker = self.review_bundle(
            self.root, sha, base_sha, run_id="published"
        )
        reused_name, _status, _sessions, name_body, name_marker = self.review_bundle(
            self.root,
            sha,
            base_sha,
            run_id="new-name-replay",
            session_name=sessions[0]["name"],
            thread_id="thread-new-name",
        )
        self.write_state(reviews={"1": [original]}, calls=[])
        with self.assertRaisesRegex(github_api.GitHubError, "session name"):
            self.client().review_once(1, sha, name_body, "COMMENT", name_marker)
        self.assertEqual(self.review_posts(), [])

        reused_thread, _status, _sessions, thread_body, thread_marker = (
            self.review_bundle(
                self.root,
                sha,
                base_sha,
                run_id="new-thread-replay",
                session_name="reviewer-pr1-new-thread",
                thread_id=sessions[0]["thread_id"],
            )
        )
        self.write_state(reviews={"1": [original]}, calls=[])
        with self.assertRaisesRegex(github_api.GitHubError, "thread id"):
            self.client().review_once(
                1, sha, thread_body, "COMMENT", thread_marker
            )
        self.assertEqual(self.review_posts(), [])

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

    def test_exact_self_review_422_falls_back_once_with_adverse_evidence(self) -> None:
        sha, base_sha = "e" * 40, "b" * 40
        client = self.client()
        _review, status, sessions, body, marker = self.review_bundle(
            self.root, sha, base_sha, findings=1
        )
        self.write_state(
            review_422="Review Can not request changes on your own pull request."
        )
        row, used_event = client.review_once(
            1, sha, body, "REQUEST_CHANGES", marker
        )
        self.assertEqual((used_event, row["state"]), ("COMMENT", "COMMENTED"))
        posts = [
            call
            for call in self.state()["calls"]
            if call["args"][:3] == ["api", "--method", "POST"]
            and call["args"][3].endswith("pulls/1/reviews")
        ]
        self.assertEqual(
            [call["input"]["event"] for call in posts],
            ["REQUEST_CHANGES", "COMMENT"],
        )
        self.assertIn(
            "findings=1 event=REQUEST_CHANGES fallback=COMMENT", row["body"]
        )

        self.write_state(statuses={sha: [status]})
        self.append_sessions(self.root, sessions)
        evidence = client.review_evidence(1, sha, base_sha)
        self.assertEqual(
            (
                evidence.attestation.event,
                evidence.attestation.fallback,
                evidence.attestation.findings,
                evidence.status["state"],
            ),
            ("REQUEST_CHANGES", "COMMENT", 1, "failure"),
        )
        self.assertEqual(evidence.attestation.head_sha, sha)
        self.assertEqual(evidence.attestation.base_sha, base_sha)
        self.assertEqual(evidence.attestation.run_id, "review-test")
        self.assertEqual(evidence.attestation.lanes[0].name, sessions[0]["name"])
        self.assertEqual(client.latest_review_ledger(1)["body"], body)

        adopted, adopted_event = client.review_once(
            1, sha, body, "REQUEST_CHANGES", marker
        )
        self.assertEqual((adopted["id"], adopted_event), (row["id"], "COMMENT"))
        posts = [
            call
            for call in self.state()["calls"]
            if call["args"][:3] == ["api", "--method", "POST"]
            and call["args"][3].endswith("pulls/1/reviews")
        ]
        self.assertEqual(len(posts), 2)

    def test_unrelated_request_changes_422_is_one_post_refusal(self) -> None:
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
        self.assertEqual(posts[0]["input"]["event"], "REQUEST_CHANGES")

    def test_ambiguous_and_transient_review_writes_never_fall_back(self) -> None:
        sha, base_sha = "c" * 40, "a" * 40
        _review, _status, _sessions, body, marker = self.review_bundle(
            self.root, sha, base_sha, findings=1
        )
        self.write_state(ambiguous_review_once=True)
        row, used_event = self.client().review_once(
            1, sha, body, "REQUEST_CHANGES", marker
        )
        self.assertEqual((row["state"], used_event), ("CHANGES_REQUESTED", "REQUEST_CHANGES"))
        posts = [
            call
            for call in self.state()["calls"]
            if call["args"][:3] == ["api", "--method", "POST"]
            and call["args"][3].endswith("pulls/1/reviews")
        ]
        self.assertEqual([call["input"]["event"] for call in posts], ["REQUEST_CHANGES"])

        other_sha = "d" * 40
        _review, _status, _sessions, other_body, other_marker = self.review_bundle(
            self.root, other_sha, base_sha, findings=1, run_id="review-transient"
        )
        self.write_state(
            reviews={},
            calls=[],
            failures={
                "POST pulls/1/reviews": {
                    "remaining": 1,
                    "message": (
                        "HTTP 503 Cannot request changes on your own pull request"
                    ),
                }
            },
        )
        with self.assertRaisesRegex(
            github_api.GitHubError, "refusing to issue a second mutation"
        ):
            self.client().review_once(
                1, other_sha, other_body, "REQUEST_CHANGES", other_marker
            )
        posts = [
            call
            for call in self.state()["calls"]
            if call["args"][:3] == ["api", "--method", "POST"]
            and call["args"][3].endswith("pulls/1/reviews")
        ]
        self.assertEqual([call["input"]["event"] for call in posts], ["REQUEST_CHANGES"])

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

    def prepare_autofix(
        self,
        *,
        name: str = "repository",
        with_review_prompts: bool = False,
    ) -> tuple[Path, str, dict]:
        base_text = {
            "local/bin/dispatch.sh": FAKE_DISPATCH,
            ".github/prompts/auto-fix-ci-system-prompt.md": (
                "Repair the committed CI failure.\n"
            ),
            ".github/prompts/auto-fix-ci-prompt.md": (
                "Make the smallest validated repair.\n"
            ),
        }
        if with_review_prompts:
            base_text.update({
                ".github/prompts/auto-fix-review-system-prompt.md": (
                    "Trusted review fixer persona.\n"
                ),
                ".github/prompts/auto-fix-review-prompt.md": (
                    "Address the attached findings.\n"
                ),
            })
        repository, _remote, base_sha, head_sha = self.make_repository(
            name=name,
            base_sources={
                "local/bin/autofix.sh": BIN_DIR / "autofix.sh",
                "local/bin/github_api.py": BIN_DIR / "github_api.py",
            },
            base_text=base_text,
        )
        run_git(
            repository,
            "push",
            "github",
            f"{head_sha}:refs/heads/issue-7-test",
        )
        pull = pull_row(1, head_sha, base_sha=base_sha)
        issue = {**pull, "pull_request": {"url": pull["html_url"]}}
        self.write_state(
            pulls={"1": pull},
            issues={"1": issue},
            commits={"1": [{"sha": head_sha, "commit": {"message": "Feature"}}]},
        )
        return repository, head_sha, pull

    def run_autofix(
        self,
        repository: Path,
        *,
        mode: str = "ci",
        dry_run: bool = False,
        trusted_ref: str | None = None,
        extra_env: dict[str, str] | None = None,
    ) -> subprocess.CompletedProcess[str]:
        environment = os.environ.copy()
        environment.update(
            {
                "MIPSTARRE_CACHE_ROOT": str(
                    self.root / f"cache-{repository.name}"
                ),
                "MIPSTARRE_TEST_BRANCH": "issue-7-test",
            }
        )
        if trusted_ref is not None:
            environment["MIPSTARRE_TRUSTED_REF"] = trusted_ref
        environment.update(extra_env or {})
        command = [
            "bash",
            str(repository / "local/bin/autofix.sh"),
            "1",
            "--mode",
            mode,
        ]
        if dry_run:
            command.append("--dry-run")
        return subprocess.run(
            command,
            cwd=repository,
            env=environment,
            text=True,
            capture_output=True,
            check=False,
        )

    def autofix_dispatch_count(self, repository: Path) -> int:
        path = self.root / f"cache-{repository.name}" / "fake-dispatch-count"
        return int(path.read_text(encoding="utf-8")) if path.exists() else 0

    def configure_failed_ci(self, repository: Path, head_sha: str, pull: dict) -> None:
        pull["labels"] = [{"name": github_api.AUTO_FIX_LABEL}]
        comment, statuses = self.ci_bundle(
            head_sha,
            pull["base"]["sha"],
            outcomes={"build": "failure"},
        )
        self.write_state(
            pulls={"1": pull},
            issues={"1": {**pull, "pull_request": {"url": pull["html_url"]}}},
            comments={"1": [comment]},
            reviews={},
            statuses={head_sha: statuses},
            commits={"1": [{"sha": head_sha, "commit": {"message": "Feature"}}]},
            calls=[],
            pull_read_count=0,
            pull_head_sequence=[],
            pull_base_sequence=[],
        )

    def test_adverse_comment_fallback_is_consumed_by_review_autofix(self) -> None:
        repository, head_sha, pull = self.prepare_autofix(with_review_prompts=True)
        pull["labels"] = [{"name": github_api.AUTO_FIX_LABEL}]
        review, _status, sessions, _body, _marker = self.review_bundle(
            repository,
            head_sha,
            pull["base"]["sha"],
            findings=1,
            comment_fallback=True,
        )
        self.append_sessions(repository, sessions)
        self.write_state(
            pulls={"1": pull},
            issues={"1": {**pull, "pull_request": {"url": pull["html_url"]}}},
            reviews={"1": [review]},
            statuses={},
            commits={"1": [{"sha": head_sha, "commit": {"message": "Feature"}}]},
        )
        result = self.run_autofix(
            repository,
            mode="review",
            dry_run=True,
        )
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        self.assertIn("dry run: the review fix prompt", result.stderr)
        self.assertNotIn("requires a valid marker-bound exact-head review ledger", result.stderr)

    def test_review_autofix_uses_structured_canonical_finding_count(self) -> None:
        repository, head_sha, pull = self.prepare_autofix(
            name="autofix-structured-findings",
            with_review_prompts=True,
        )
        pull["labels"] = [{"name": github_api.AUTO_FIX_LABEL}]
        review, _status, sessions, _body, _marker = self.review_bundle(
            repository,
            head_sha,
            pull["base"]["sha"],
            findings=0,
            extra_prose=(
                "Historical example outside the canonical ledger:\n"
                "- [ ] F99 (changes) `old.py:1` — no longer a finding"
            ),
        )
        self.append_sessions(repository, sessions)
        self.write_state(
            pulls={"1": pull},
            issues={"1": {**pull, "pull_request": {"url": pull["html_url"]}}},
            reviews={"1": [review]},
            statuses={},
            commits={"1": [{"sha": head_sha, "commit": {"message": "Feature"}}]},
        )
        result = self.run_autofix(repository, mode="review", dry_run=True)
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        self.assertIn("nothing to fix", result.stderr)
        self.assertEqual(self.autofix_dispatch_count(repository), 0)

    def test_review_autofix_reads_count_and_body_from_one_snapshot(self) -> None:
        repository, head_sha, pull = self.prepare_autofix(
            name="autofix-review-snapshot",
            with_review_prompts=True,
        )
        pull["labels"] = [{"name": github_api.AUTO_FIX_LABEL}]
        old_review, _status, old_sessions, _body, _marker = self.review_bundle(
            repository,
            head_sha,
            pull["base"]["sha"],
            run_id="review-old-findings",
            findings=1,
            comment_fallback=True,
            submitted_at="2026-01-01T00:01:00Z",
        )
        new_review, _status, new_sessions, _body, _marker = self.review_bundle(
            repository,
            head_sha,
            pull["base"]["sha"],
            run_id="review-new-clean",
            review_id=2,
            submitted_at="2026-01-01T00:02:00Z",
        )
        self.append_sessions(repository, [*old_sessions, *new_sessions])
        self.write_state(
            pulls={"1": pull},
            issues={"1": {**pull, "pull_request": {"url": pull["html_url"]}}},
            reviews={"1": [old_review]},
            statuses={},
            commits={"1": [{"sha": head_sha, "commit": {"message": "Feature"}}]},
            review_read_count=0,
            inject_review_on_review_read={"at": 0, "row": new_review},
        )
        result = self.run_autofix(repository, mode="review", dry_run=True)
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        self.assertIn("nothing to fix", result.stderr)
        self.assertEqual(self.state()["review_read_count"], 1)
        self.assertEqual(self.autofix_dispatch_count(repository), 0)

    def test_error_ci_manifest_is_readable_but_never_dispatches_autofix(self) -> None:
        repository, head_sha, pull = self.prepare_autofix(
            name="autofix-ci-error"
        )
        pull["labels"] = [{"name": github_api.AUTO_FIX_LABEL}]
        comment, statuses = self.ci_bundle(
            head_sha,
            pull["base"]["sha"],
            outcomes={"build": "error"},
        )
        self.write_state(
            pulls={"1": pull},
            issues={"1": {**pull, "pull_request": {"url": pull["html_url"]}}},
            comments={"1": [comment]},
            statuses={head_sha: statuses},
            commits={"1": [{"sha": head_sha, "commit": {"message": "Feature"}}]},
        )
        client = self.client(repository)
        _row, manifest = client.ci_manifest(
            1, head_sha, pull["base"]["sha"]
        )
        self.assertEqual(manifest["conclusion"], "error")
        with self.assertRaisesRegex(github_api.GitHubError, "not success"):
            client.ci_success_evidence(1, head_sha, pull["base"]["sha"])

        result = self.run_autofix(repository)
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        self.assertIn("infrastructure failures, not code failures", result.stderr)
        self.assertIn("nothing to fix", result.stderr)
        self.assertEqual(self.autofix_dispatch_count(repository), 0)

    def test_ci_autofix_rejects_same_head_manifest_for_other_base(self) -> None:
        repository, head_sha, pull = self.prepare_autofix()
        pull["labels"] = [{"name": github_api.AUTO_FIX_LABEL}]
        comment, statuses = self.ci_bundle(
            head_sha,
            "f" * 40,
            outcomes={"build": "failure"},
        )
        self.write_state(
            pulls={"1": pull},
            issues={"1": {**pull, "pull_request": {"url": pull["html_url"]}}},
            comments={"1": [comment]},
            statuses={head_sha: statuses},
            commits={"1": [{"sha": head_sha, "commit": {"message": "Feature"}}]},
        )
        result = self.run_autofix(repository, dry_run=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("requires a valid marker-bound exact-head CI manifest", result.stderr)
        self.assertEqual(self.autofix_dispatch_count(repository), 0)

    def test_same_head_base_movement_stops_before_autofix_dispatch(self) -> None:
        repository, head_sha, pull = self.prepare_autofix(name="autofix-pre-dispatch")
        self.configure_failed_ci(repository, head_sha, pull)
        base_sha = pull["base"]["sha"]
        self.write_state(
            pull_base_sequence=[base_sha, base_sha, base_sha, "f" * 40],
            pull_read_count=0,
        )
        result = self.run_autofix(repository)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("before the ci dispatch", result.stderr)
        self.assertEqual(self.autofix_dispatch_count(repository), 0)
        self.assertEqual(run_git(repository, "rev-parse", "HEAD"), head_sha)

    def test_base_movement_after_dispatch_stops_before_commit(self) -> None:
        repository, head_sha, pull = self.prepare_autofix(name="autofix-post-dispatch")
        self.configure_failed_ci(repository, head_sha, pull)
        result = self.run_autofix(
            repository,
            extra_env={"MIPSTARRE_TEST_MOVE_BASE_AFTER_DISPATCH": "e" * 40},
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("after the ci dispatch", result.stderr)
        self.assertEqual(self.autofix_dispatch_count(repository), 1)
        self.assertEqual(run_git(repository, "rev-parse", "HEAD"), head_sha)

    def test_fetched_base_movement_after_dispatch_stops_before_commit(self) -> None:
        repository, head_sha, pull = self.prepare_autofix(name="autofix-local-base")
        self.configure_failed_ci(repository, head_sha, pull)
        result = self.run_autofix(
            repository,
            extra_env={
                "MIPSTARRE_TEST_MOVE_LOCAL_BASE_AFTER_DISPATCH": head_sha,
            },
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("after the ci dispatch", result.stderr)
        self.assertEqual(self.autofix_dispatch_count(repository), 1)
        self.assertEqual(run_git(repository, "rev-parse", "HEAD"), head_sha)

    def test_autofix_cancel_and_owner_theft_abort_before_commit(self) -> None:
        for action in ("cancel", "steal"):
            with self.subTest(action=action):
                repository, head_sha, pull = self.prepare_autofix(
                    name=f"autofix-lock-{action}"
                )
                self.configure_failed_ci(repository, head_sha, pull)
                result = self.run_autofix(
                    repository,
                    extra_env={"MIPSTARRE_TEST_LOCK_ACTION": action},
                )
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("ownership was lost or superseded", result.stderr)
                self.assertEqual(self.autofix_dispatch_count(repository), 1)
                self.assertEqual(run_git(repository, "rev-parse", "HEAD"), head_sha)
                remote_head = run_git(
                    repository,
                    "ls-remote",
                    "github",
                    "refs/heads/issue-7-test",
                ).split()[0]
                self.assertEqual(remote_head, head_sha)
                lock = (
                    self.root
                    / f"cache-{repository.name}"
                    / "locks/fix-issue-7-test.lock"
                )
                if action == "steal":
                    self.assertTrue(lock.is_dir())
                    self.assertEqual(
                        (lock / "owner").read_text(encoding="utf-8").strip(),
                        "different-owner",
                    )
                else:
                    self.assertFalse(lock.exists())

    def test_base_movement_at_commit_boundary_prevents_commit(self) -> None:
        repository, head_sha, pull = self.prepare_autofix(name="autofix-pre-commit")
        self.configure_failed_ci(repository, head_sha, pull)
        base_sha = pull["base"]["sha"]
        self.write_state(
            pull_base_sequence=[base_sha] * 6 + ["d" * 40],
            pull_read_count=0,
        )
        result = self.run_autofix(repository)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("immediately before the ci commit", result.stderr)
        self.assertEqual(self.autofix_dispatch_count(repository), 1)
        self.assertEqual(run_git(repository, "rev-parse", "HEAD"), head_sha)

    def test_base_movement_at_push_boundary_leaves_bot_commit_unpushed(self) -> None:
        repository, head_sha, pull = self.prepare_autofix(name="autofix-pre-push")
        self.configure_failed_ci(repository, head_sha, pull)
        base_sha = pull["base"]["sha"]
        self.write_state(
            pull_base_sequence=[base_sha] * 7 + ["c" * 40],
            pull_read_count=0,
        )
        result = self.run_autofix(repository)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("immediately before push", result.stderr)
        local_head = run_git(repository, "rev-parse", "HEAD")
        remote_head = run_git(
            repository, "rev-parse", "refs/remotes/github/issue-7-test"
        )
        self.assertNotEqual(local_head, head_sha)
        self.assertEqual(remote_head, head_sha)

    def test_successful_autofix_push_uses_original_comparison_identity(self) -> None:
        repository, head_sha, pull = self.prepare_autofix(name="autofix-success")
        self.configure_failed_ci(repository, head_sha, pull)
        base_sha = pull["base"]["sha"]
        result = self.run_autofix(repository)
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        local_head = run_git(repository, "rev-parse", "HEAD")
        remote_head = run_git(
            repository, "ls-remote", "github", "refs/heads/issue-7-test"
        ).split()[0]
        self.assertNotEqual(local_head, head_sha)
        self.assertEqual(remote_head, local_head)
        message = run_git(repository, "show", "-s", "--format=%B", local_head)
        self.assertIn("[codex-auto-fix] fix Lean build errors", message)
        self.assertIn(f"Evidence head SHA: {head_sha}", message)
        self.assertIn(f"PR base SHA: {base_sha}", message)
        self.assertIn(f"Parent feature tip: {head_sha}", message)

    def test_post_commit_cancel_hands_off_only_the_committed_tip(self) -> None:
        repository, head_sha, pull = self.prepare_autofix(name="autofix-handoff")
        self.configure_failed_ci(repository, head_sha, pull)
        hook = repository / ".git/hooks/post-commit"
        hook.write_text(
            "#!/bin/sh\n"
            'lock="$MIPSTARRE_CACHE_ROOT/locks/fix-issue-7-test.lock"\n'
            'printf "test supersession\\n" >"$lock/cancel"\n',
            encoding="utf-8",
        )
        hook.chmod(0o755)
        result = self.run_autofix(repository)
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        self.assertIn("publishing only the already committed tip", result.stderr)
        local_head = run_git(repository, "rev-parse", "HEAD")
        remote_head = run_git(
            repository, "ls-remote", "github", "refs/heads/issue-7-test"
        ).split()[0]
        self.assertNotEqual(local_head, head_sha)
        self.assertEqual(remote_head, local_head)

    def test_late_post_commit_cancel_does_not_strand_the_committed_tip(self) -> None:
        repository, head_sha, pull = self.prepare_autofix(
            name="autofix-late-handoff"
        )
        self.configure_failed_ci(repository, head_sha, pull)
        result = self.run_autofix(
            repository,
            extra_env={"MIPSTARRE_TEST_CANCEL_DURING_PRE_PUSH": "1"},
        )
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        self.assertIsInstance(
            self.state().get("cancel_lock_on_pull_read_fired"), int
        )
        local_head = run_git(repository, "rev-parse", "HEAD")
        remote_head = run_git(
            repository, "ls-remote", "github", "refs/heads/issue-7-test"
        ).split()[0]
        self.assertNotEqual(local_head, head_sha)
        self.assertEqual(remote_head, local_head)

    def test_staging_failure_is_not_converted_to_success(self) -> None:
        repository, head_sha, pull = self.prepare_autofix(
            name="autofix-stage-failure"
        )
        self.configure_failed_ci(repository, head_sha, pull)
        index_lock = repository / ".git/index.lock"
        index_lock.write_text("test lock\n", encoding="utf-8")
        result = self.run_autofix(repository)
        self.assertEqual(result.returncode, 2, result.stderr + result.stdout)
        self.assertIn("could not stage the ci fix", result.stderr)
        self.assertEqual(run_git(repository, "rev-parse", "HEAD"), head_sha)
        remote_head = run_git(
            repository, "ls-remote", "github", "refs/heads/issue-7-test"
        ).split()[0]
        self.assertEqual(remote_head, head_sha)

    def test_term_signal_exits_nonzero_and_releases_owned_lock(self) -> None:
        repository, head_sha, pull = self.prepare_autofix(
            name="autofix-term-signal"
        )
        self.configure_failed_ci(repository, head_sha, pull)
        result = self.run_autofix(
            repository,
            extra_env={"MIPSTARRE_TEST_SIGNAL_PARENT": "TERM"},
        )
        self.assertEqual(result.returncode, 143, result.stderr + result.stdout)
        lock = (
            self.root
            / f"cache-{repository.name}"
            / "locks/fix-issue-7-test.lock"
        )
        self.assertFalse(lock.exists())
        self.assertEqual(run_git(repository, "rev-parse", "HEAD"), head_sha)

    def test_exact_push_lease_rejects_a_stale_remote_feature_ref(self) -> None:
        repository, head_sha, pull = self.prepare_autofix(name="autofix-lease")
        self.configure_failed_ci(repository, head_sha, pull)
        base_sha = pull["base"]["sha"]
        remote = self.root / f"{repository.name}-github.git"
        run_git(remote, "update-ref", "refs/heads/issue-7-test", base_sha)
        result = self.run_autofix(repository)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("could not push the explicit feature ref", result.stderr)
        local_head = run_git(repository, "rev-parse", "HEAD")
        remote_head = run_git(
            repository, "ls-remote", "github", "refs/heads/issue-7-test"
        ).split()[0]
        self.assertNotEqual(local_head, head_sha)
        self.assertEqual(remote_head, base_sha)

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

    def test_adverse_comment_fallback_is_valid_evidence_but_blocks_merge(self) -> None:
        sha, base_sha = "a" * 40, "b" * 40
        review, status, sessions, _body, _marker = self.review_bundle(
            self.root,
            sha,
            base_sha,
            findings=1,
            comment_fallback=True,
        )
        self.append_sessions(self.root, sessions)
        self.write_state(reviews={"1": [review]}, statuses={sha: [status]})
        evidence = self.client().review_evidence(1, sha, base_sha)
        self.assertEqual(evidence.attestation.event, "REQUEST_CHANGES")
        self.assertEqual(evidence.attestation.fallback, "COMMENT")
        self.assertEqual(evidence.attestation.row["state"], "COMMENTED")
        with self.assertRaisesRegex(pr_merge.GateFailure, "not a clean COMMENT"):
            pr_merge.require_review(self.client(), 1, sha, base_sha)

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
