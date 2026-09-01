#!/usr/bin/env python3
"""Deterministic regression tests for the GitHub-authoritative local workflow."""

from __future__ import annotations

import argparse
import copy
import contextlib
import hashlib
import io
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import threading
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
import runtime_lock  # noqa: E402


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


def require_runtime_locks(key, observed_key):
    paths = [str(value) for value in state.get(key, [])]
    for path in paths:
        required = ("pid", "token", "identity", "owner")
        if not os.path.isdir(path) or not all(
            os.path.isfile(os.path.join(path, name)) for name in required
        ):
            fail("HTTP 409 required workflow lock is not held: " + path)
        try:
            with open(os.path.join(path, "owner"), encoding="utf-8") as stream:
                owner = json.load(stream)
            if set(owner) != {
                "schema", "pid", "token", "identity", "owner", "host", "created_at"
            }:
                raise ValueError("noncanonical owner metadata")
        except (OSError, ValueError, TypeError, json.JSONDecodeError):
            fail("HTTP 409 required workflow lock is malformed: " + path)
    if paths:
        state[observed_key] = paths


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
    state["merge_call_count"] = int(state.get("merge_call_count", 0)) + 1
    if state.pop("fail_merge_before_once", False):
        fail("HTTP 503 Service Unavailable before merge")
    race = state.pop("merge_race", {}) or {}
    if race.get("head_sha"):
        row.setdefault("head", {})["sha"] = str(race["head_sha"])
    if race.get("base_sha"):
        row.setdefault("base", {})["sha"] = str(race["base_sha"])
    if race.get("base_tip"):
        base_name = str((row.get("base") or {}).get("ref") or "")
        state.setdefault("branch_tips", {})[base_name] = str(race["base_tip"])
    if race.get("status"):
        head = str((row.get("head") or {}).get("sha") or "")
        state.setdefault("statuses", {}).setdefault(head, []).append(race["status"])
    if "--merge" not in args or "--admin" in args or "--auto" in args:
        fail("HTTP 422 merge invocation bypassed strict server gates")
    matched_head = option("--match-head-commit")
    current_head = str((row.get("head") or {}).get("sha") or "")
    if matched_head != current_head:
        fail("HTTP 409 head commit no longer matches")
    base = str((row.get("base") or {}).get("ref") or "")
    base_sha = str((row.get("base") or {}).get("sha") or "")
    protection = state.setdefault("branch_protections", {}).get(base, {})
    required = protection.get("required_status_checks") or {}
    if required.get("strict") is not True:
        fail("HTTP 409 base does not use strict required checks")
    contexts = {str(item).casefold() for item in required.get("contexts", [])}
    expected_contexts = {"local-ci/summary", "local-review/summary"}
    if contexts != expected_contexts:
        fail("HTTP 409 required summary contexts are not exact")
    if state.setdefault("branch_tips", {}).get(base, base_sha) != base_sha:
        fail("HTTP 409 pull request is not current with the protected base")
    latest = {}
    status_rows = list(state.setdefault("statuses", {}).get(current_head, []))
    status_rows.sort(
        key=lambda item: (str(item.get("created_at", "")), int(item.get("id", 0))),
        reverse=True,
    )
    for status in status_rows:
        context = str(status.get("context") or "").casefold()
        if context and context not in latest:
            latest[context] = status
    if any(str((latest.get(name) or {}).get("state") or "").casefold() != "success"
           for name in expected_contexts):
        fail("HTTP 409 required summary status is not successful")
    require_runtime_locks("required_merge_locks", "merge_locks_observed")
    merge_sha = state.get("merge_sha", "b" * 40)
    parents = state.get("merge_commit_parents")
    if parents is None:
        parents = [base_sha, current_head]
    state.setdefault("git_commits", {}).setdefault(
        merge_sha,
        {
            "sha": merge_sha,
            "parents": [{"sha": str(parent)} for parent in parents],
        },
    )
    row["merged"] = True
    row["state"] = "closed"
    row["merge_commit_sha"] = merge_sha
    if state.get("post_merge_base_sha"):
        row.setdefault("base", {})["sha"] = str(state["post_merge_base_sha"])
    if state.get("post_merge_head_ref"):
        row.setdefault("head", {})["ref"] = str(state["post_merge_head_ref"])
    if state.pop("ambiguous_merge_success_once", False):
        fail("HTTP 503 Service Unavailable after merge")
    emit({"merged": True})

if not args or args[0] != "api":
    fail("unsupported fake gh command")

method = option("--method", "GET").upper()
endpoint = args[3] if len(args) > 3 else ""
parsed = urllib.parse.urlsplit(endpoint)
path = parsed.path.strip("/")
if path == "user" and method == "GET":
    emit(state.get("user", {"login": "o"}))
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
    emit(
        state.get(
            "repo", {"id": 1, "full_name": "o/r", "allow_merge_commit": True}
        )
    )

if len(tail) == 3 and tail[:2] == ["git", "commits"] and method == "GET":
    commit = state.setdefault("git_commits", {}).get(tail[2])
    if commit is None:
        fail("HTTP 404 Git commit not found")
    emit(commit)

if len(tail) >= 3 and tail[0] == "branches" and tail[-1] == "protection":
    branch = urllib.parse.unquote("/".join(tail[1:-1]))
    protection = state.setdefault("branch_protections", {}).get(branch)
    if protection is None:
        fail("HTTP 404 Branch not protected")
    emit(protection)

if len(tail) >= 3 and tail[:2] == ["rules", "branches"] and method == "GET":
    branch = urllib.parse.unquote("/".join(tail[2:]))
    emit(state.setdefault("branch_rules", {}).get(branch, []))

if len(tail) == 2 and tail[0] == "rulesets" and method == "GET":
    ruleset = state.setdefault("rulesets", {}).get(tail[1])
    if ruleset is None:
        fail("HTTP 404 Ruleset not found")
    emit(ruleset)

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
                    stream.write(
                        str(cancellation.get("content", "test late supersession\n"))
                    )
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
            "updated_at": f"2026-01-01T00:00:{len(comments):02d}Z",
            "user": dict(state.get("user", {"login": "o"})),
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
        if state.pop("fail_label_put_before_once", False):
            fail("HTTP 503 Service Unavailable")
        row["labels"] = [{"name": name} for name in (payload or {}).get("labels", [])]
        issue = state.setdefault("issues", {}).get(number)
        if issue is not None:
            issue["labels"] = row["labels"]
        if state.pop("ambiguous_label_put_once", False):
            fail("HTTP 503 Service Unavailable")
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
                    stream.write(
                        str(cancellation.get("content", "test publication cancellation\n"))
                    )
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
        if event != "COMMENT":
            fail("HTTP 422 local review attestations must use COMMENT")
        row = {
            "id": len(reviews) + 1,
            "body": str((payload or {}).get("body", "")),
            "commit_id": str((payload or {}).get("commit_id", "")),
            "state": "COMMENTED",
            "submitted_at": f"2026-01-01T00:00:{len(reviews):02d}Z",
            "user": dict(state.get("user", {"login": "o"})),
        }
        reviews.append(row)
        readback_failures = int(
            state.pop("ambiguous_review_readback_failures_once", 0)
        )
        if readback_failures > 0:
            state.setdefault("failures", {})["GET pulls/1/reviews"] = {
                "remaining": readback_failures,
                "message": "HTTP 503 injected review readback outage",
            }
            fail("HTTP 503 Service Unavailable")
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
                stream.write(
                    str(cancellation.get("content", "test publication cancellation\n"))
                )
        state["cancel_lock_on_status_read"] = {}
    state["status_read_count"] = read_count + 1
    response_rows = state.setdefault("statuses", {}).get(sha, [])
    hidden_reads = int(state.get("hide_status_reads", 0))
    if hidden_reads > 0:
        state["hide_status_reads"] = hidden_reads - 1
        response_rows = []
    if "status_read_sha_override" in state:
        response_rows = [
            {**row, "sha": state["status_read_sha_override"]}
            for row in response_rows
        ]
    elif state.get("status_responses_omit_sha"):
        response_rows = [
            {key: value for key, value in row.items() if key != "sha"}
            for row in response_rows
        ]
    emit(page(response_rows, parsed.query))

if len(tail) == 2 and tail[0] == "statuses" and method == "POST":
    sha = tail[1]
    if (
        str((payload or {}).get("context", "")).casefold()
        == "local-review/summary"
        and str((payload or {}).get("state", "")).casefold() == "success"
    ):
        require_runtime_locks(
            "required_adjudication_locks", "adjudication_locks_observed"
        )
    if (
        state.get("fail_review_aborted_status_once")
        and str((payload or {}).get("context", "")).casefold()
        == "local-review/summary"
        and str((payload or {}).get("state", "")).casefold() == "error"
        and "state=aborted" in str((payload or {}).get("description", ""))
    ):
        state["fail_review_aborted_status_once"] = False
        fail("HTTP 503 injected aborted review status failure")
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
        "created_at": f"2098-01-01T00:00:{len(rows):02d}Z",
        "creator": dict(state.get("user", {"login": "o"})),
    }
    rows.append(row)
    response_row = row
    if "status_post_sha_override" in state:
        response_row = {**row, "sha": state["status_post_sha_override"]}
    elif state.get("status_responses_omit_sha"):
        response_row = {key: value for key, value in row.items() if key != "sha"}
    readback_failures = int(state.pop("status_readback_failures_once", 0))
    if readback_failures > 0:
        state.setdefault("failures", {})[f"GET commits/{sha}/statuses"] = {
            "remaining": readback_failures,
            "message": "HTTP 503 injected status readback outage",
        }
    if state.pop("ambiguous_status_once", False):
        fail("HTTP 503 Service Unavailable")
    if state.pop("corrupt_status_response", False):
        emit({**response_row, "context": "different/context"})
    emit(response_row)

fail("HTTP 404 unsupported fake endpoint " + key)
'''


FAKE_DISPATCH = r'''#!/usr/bin/env python3
import json
import os
import pathlib
import signal
import subprocess
import sys

sys.dont_write_bytecode = True


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

sys.path.insert(0, str(worktree / "local" / "bin"))
import runtime_lock


def cancellation_content():
    observed = runtime_lock.inspect_lock(fix_lock)
    if observed.record is None:
        raise RuntimeError("test cancellation needs a complete lock claim")
    claim = observed.record.claim
    return json.dumps(
        {
            "schema": 1,
            "identity": claim.identity.render(),
            "pid": claim.pid,
            "token": claim.token,
            "owner_digest": claim.owner_digest,
            "requester": "workflow regression test",
            "requested_at": "2026-01-01T00:00:00Z",
        },
        sort_keys=True,
        separators=(",", ":"),
    ) + "\n"


def request_valid_cancellation():
    observed = runtime_lock.inspect_lock(fix_lock)
    if observed.record is None:
        raise RuntimeError("test cancellation needs a complete lock claim")
    result = runtime_lock.request_cancellation(
        fix_lock,
        observed.record.claim,
        "workflow regression test",
        required_owner_prefix="autofix ",
    )
    if result.state != "cancel-requested":
        raise RuntimeError("could not request test cancellation: " + result.state)


def install_replacement_claim():
    observed = runtime_lock.inspect_lock(fix_lock)
    if observed.record is None:
        raise RuntimeError("test replacement needs a complete lock claim")
    released = runtime_lock.release_owned_lock(fix_lock, observed.record.claim)
    if released.state != "released":
        raise RuntimeError("could not release test claim: " + released.state)
    acquired = runtime_lock.acquire_lock(
        fix_lock,
        os.getpid(),
        runtime_lock.new_token(),
        "autofix replacement-test",
    )
    if acquired.state != "acquired":
        raise RuntimeError("could not install replacement claim: " + acquired.state)


action = os.environ.get("MIPSTARRE_TEST_LOCK_ACTION", "")
if action == "cancel":
    request_valid_cancellation()
elif action == "malformed-cancel":
    (fix_lock / "cancel").write_text("test supersession\n", encoding="utf-8")
elif action == "steal":
    install_replacement_claim()
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
    if os.environ.get("MIPSTARRE_TEST_REVIEW_DISPATCH_FAIL") == "1":
        raise SystemExit(17)
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
                "content": cancellation_content(),
            }
        elif guard_action == "cancel-status-post":
            counter_key = "status_read_count"
            injection_key = "cancel_lock_on_status_read"
            injection = {
                "at": int(state.get(counter_key, 0)) + 1,
                "path": str(fix_lock / "cancel"),
                "content": cancellation_content(),
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
            "content": cancellation_content(),
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


def classic_protection() -> dict:
    """Return the exact classic-protection contract required by the merge gate."""
    contexts = [github_api.CI_SUMMARY_CONTEXT, github_api.REVIEW_CONTEXT]
    return {
        "required_status_checks": {
            "strict": True,
            "contexts": contexts,
            "checks": [
                {"context": context, "app_id": None} for context in contexts
            ],
        },
        "enforce_admins": {"enabled": True},
        "required_pull_request_reviews": {
            "required_approving_review_count": 0,
            "require_code_owner_reviews": False,
            "require_last_push_approval": False,
            "bypass_pull_request_allowances": {
                "users": [],
                "teams": [],
                "apps": [],
            },
        },
        "allow_force_pushes": {"enabled": False},
        "allow_deletions": {"enabled": False},
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
            "repo": {"id": 1, "full_name": "o/r", "allow_merge_commit": True},
            "user": {"login": "o"},
            "labels": [],
            "issues": {},
            "pulls": {},
            "comments": {},
            "reviews": {},
            "statuses": {},
            "commits": {},
            "git_commits": {},
            "sub_issues": {},
            "branch_protections": {"main": classic_protection()},
            "branch_rules": {"main": []},
            "rulesets": {},
            "branch_tips": {},
            "merge_call_count": 0,
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
                    "creator": {"login": "o"},
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
        comment = {
            "id": comment_id,
            "body": body,
            "created_at": created_at,
            "user": {"login": "o"},
        }
        digest = github_api.ci_manifest_digest(manifest)
        summary_state = conclusion
        verdict = {
            "success": "passed",
            "failure": "failed",
            "error": "could not run",
        }[conclusion]
        summary_description = (
            f"local CI digest={digest} run={run_id} {verdict}"
        )
        statuses.append(
            {
                "id": len(statuses) + 1,
                "sha": head_sha,
                "context": github_api.CI_SUMMARY_CONTEXT,
                "state": summary_state,
                "description": github_api.render_status_description(
                    head_sha,
                    github_api.CI_SUMMARY_CONTEXT,
                    summary_state,
                    summary_description,
                ),
                "created_at": created_at,
                "creator": {"login": "o"},
            }
        )
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
        event = "COMMENT"
        fallback = "none"
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
        review = {
            "id": review_id,
            "body": body,
            "commit_id": head_sha,
            "state": "COMMENTED",
            "submitted_at": submitted_at,
            "user": {"login": "o"},
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
            "creator": {"login": "o"},
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

    def adjudication_bundle(
        self,
        root: Path,
        head_sha: str,
        base_sha: str,
        *,
        round_count: int = 4,
        first_review_id: int = 1,
        first_round_head_sha: str | None = None,
        dispositions: list[dict] | None = None,
    ) -> tuple[list[dict], list[dict], list[dict], dict, dict]:
        """Build canonical, independently attested rounds and one adjudication."""
        reviews: list[dict] = []
        statuses: list[dict] = []
        sessions: list[dict] = []
        rounds: list[dict] = []
        for offset in range(round_count):
            index = offset + 1
            review_id = first_review_id + offset
            run_id = f"adjudication-round-{review_id}"
            review, status, round_sessions, _body, marker = self.review_bundle(
                root,
                first_round_head_sha if offset == 0 and first_round_head_sha else head_sha,
                base_sha,
                run_id=run_id,
                worktree=root,
                findings=1,
                review_id=review_id,
                status_id=200 + review_id,
                submitted_at=f"2026-01-01T00:03:{index:02d}Z",
            )
            digest_match = re.search(r"digest=([0-9a-f]{64})", marker)
            assert digest_match is not None
            rounds.append(
                {
                    "review_id": review_id,
                    "run_id": run_id,
                    "digest": digest_match.group(1),
                }
            )
            reviews.append(review)
            statuses.append(status)
            sessions.extend(round_sessions)

        source = rounds[-1]
        payload = {
            "schema": 1,
            "pr": 1,
            "head_sha": head_sha,
            "base_sha": base_sha,
            "source_review": dict(source),
            "rounds": rounds,
            "dispositions": dispositions
            if dispositions is not None
            else [
                {
                    "finding": "code:F1",
                    "outcome": "fixed",
                    "reason": "The source finding was repaired in the exact head.",
                    "evidence": "Focused regression coverage exercises the repair.",
                }
            ],
        }
        prefix = (
            "ADJUDICATION\n\n```json\n"
            + json.dumps(payload, indent=2, sort_keys=True)
            + "\n```\n\n"
        )
        body_digest = hashlib.sha256(prefix.encode("utf-8")).hexdigest()
        marker = (
            f"<!-- mipstarre:adjudication pr=1 head={head_sha} base={base_sha} "
            f"review={source['review_id']} run={source['run_id']} "
            f"digest={source['digest']} body={body_digest} -->"
        )
        comment = {
            "id": 500,
            "body": prefix + marker + "\n",
            "created_at": "2026-01-01T00:10:00Z",
            "updated_at": "2026-01-01T00:10:00Z",
            "user": {"login": "o"},
        }
        return reviews, statuses, sessions, comment, payload


class RuntimeLockTests(FakeGhCase):
    """Stable transition mutexes preserve replacements and serialize breakers."""

    def acquire_record(
        self, path: Path, pid: int, owner: str
    ) -> runtime_lock.LockRecord:
        result = runtime_lock.acquire_lock(
            path,
            pid,
            runtime_lock.new_token(),
            owner,
        )
        self.assertEqual(result.state, "acquired", result.detail)
        self.assertIsNotNone(result.record)
        return result.record  # type: ignore[return-value]

    def test_blocked_breaker_revalidates_replacement_before_rename(self) -> None:
        lock = self.root / "locks" / "ci-1.lock"
        stale = self.acquire_record(lock, 999_999_999, "stale ci owner")
        replacement_source = self.root / "locks" / "replacement-source.lock"
        replacement_record = self.acquire_record(
            replacement_source, os.getpid(), "live replacement"
        )
        started = threading.Event()
        result: list[runtime_lock.TransitionResult] = []

        with runtime_lock.transition_mutex(lock):
            worker = threading.Thread(
                target=lambda: result.append(
                    runtime_lock.break_stale_lock(
                        lock, stale.claim, before_mutex=started.set
                    )
                )
            )
            worker.start()
            self.assertTrue(started.wait(timeout=2))
            displaced = lock.with_name("ci-1.lock.displaced")
            lock.rename(displaced)
            replacement_source.rename(lock)
            replacement = replacement_record.identity
        worker.join(timeout=2)

        self.assertFalse(worker.is_alive())
        self.assertEqual([item.state for item in result], ["changed"])
        self.assertEqual(runtime_lock.directory_identity(lock), replacement)
        with self.assertRaises(pr_merge.GateFailure):
            with pr_merge.reserve_runtime_lock(lock, "contender"):
                self.fail(
                    "a contender acquired a replacement owned by a live process"
                )

    def test_acquire_requires_explicit_recovery_for_every_complete_record(
        self,
    ) -> None:
        lock = self.root / "locks" / "complete-dead.lock"
        owner = self.acquire_record(lock, 999_999_999, "completed parent")

        contender = runtime_lock.acquire_lock(
            lock,
            os.getpid(),
            runtime_lock.new_token(),
            "contender",
        )

        self.assertEqual(contender.state, "busy")
        self.assertIn("descendants may survive", contender.detail)
        self.assertEqual(runtime_lock.directory_identity(lock), owner.identity)
        self.assertEqual(
            runtime_lock.break_stale_lock(lock, owner.claim).state,
            "broken",
        )

    def test_oversized_complete_owner_pid_is_nonthrowing_and_fail_closed(
        self,
    ) -> None:
        lock = self.root / "locks" / "oversized-pid.lock"
        owner = self.acquire_record(lock, 10**50, "oversized owner")

        contender = runtime_lock.acquire_lock(
            lock,
            os.getpid(),
            runtime_lock.new_token(),
            "contender",
        )

        self.assertEqual(contender.state, "busy")
        self.assertEqual(runtime_lock.directory_identity(lock), owner.identity)

    def test_two_breakers_serialize_and_only_one_contender_enters(self) -> None:
        lock = self.root / "locks" / "ci-2.lock"
        stale = self.acquire_record(lock, 999_999_999, "stale ci owner")
        barrier = threading.Barrier(3)
        results: list[str] = []

        def breaker() -> None:
            result = runtime_lock.break_stale_lock(
                lock,
                stale.claim,
                before_mutex=barrier.wait,
            )
            results.append(result.state)

        breakers = [threading.Thread(target=breaker) for _ in range(2)]
        for worker in breakers:
            worker.start()
        barrier.wait(timeout=2)
        for worker in breakers:
            worker.join(timeout=2)
        self.assertEqual(results.count("broken"), 1)
        self.assertEqual(len(results), 2)

        entered: list[str] = []
        holder_entered = threading.Event()
        release_holder = threading.Event()

        def contender(name: str) -> None:
            try:
                with pr_merge.reserve_runtime_lock(lock, name):
                    entered.append(name)
                    holder_entered.set()
                    release_holder.wait(timeout=2)
            except pr_merge.GateFailure:
                pass

        first = threading.Thread(target=contender, args=("first",))
        second = threading.Thread(target=contender, args=("second",))
        first.start()
        self.assertTrue(holder_entered.wait(timeout=2))
        second.start()
        second.join(timeout=2)
        release_holder.set()
        first.join(timeout=2)
        self.assertEqual(entered, ["first"])

    def test_merge_cleanup_never_renames_whole_directory_replacement(self) -> None:
        lock = self.root / "locks" / "review-1.lock"
        displaced = lock.with_name("review-1.lock.displaced")
        replacement_source = self.root / "locks" / "replacement-source.lock"
        replacement_record = self.acquire_record(
            replacement_source, os.getpid(), "replacement owner"
        )
        with pr_merge.reserve_runtime_lock(lock, "merge cleanup") as held:
            lock.rename(displaced)
            replacement_source.rename(lock)
            self.assertNotEqual(replacement_record.identity, held.identity)

        self.assertEqual(
            runtime_lock.directory_identity(lock), replacement_record.identity
        )
        self.assertTrue(displaced.is_dir())
        self.assertEqual(list(lock.parent.glob("review-1.lock.release.*")), [])

    def test_blocked_cancellation_preserves_replacement(self) -> None:
        lock = self.root / "locks" / "fix-branch.lock"
        original = self.acquire_record(lock, os.getpid(), "original autofix")
        replacement_source = self.root / "locks" / "cancel-replacement.lock"
        replacement = self.acquire_record(
            replacement_source, os.getpid(), "replacement autofix"
        )
        started = threading.Event()
        results: list[runtime_lock.TransitionResult] = []

        with runtime_lock.transition_mutex(lock):
            worker = threading.Thread(
                target=lambda: results.append(
                    runtime_lock.request_cancellation(
                        lock,
                        original.claim,
                        "new autofix",
                        before_mutex=started.set,
                    )
                )
            )
            worker.start()
            self.assertTrue(started.wait(timeout=2))
            lock.rename(lock.with_name("fix-branch.lock.displaced"))
            replacement_source.rename(lock)
        worker.join(timeout=2)

        self.assertFalse(worker.is_alive())
        self.assertEqual([item.state for item in results], ["changed"])
        self.assertEqual(
            runtime_lock.directory_identity(lock), replacement.identity
        )
        self.assertFalse((lock / "cancel").exists())

    def test_cancellation_is_bound_to_the_complete_owner_claim(self) -> None:
        lock = self.root / "locks" / "fix-cancel.lock"
        owner = self.acquire_record(lock, os.getpid(), "autofix pr=1")

        requested = runtime_lock.request_cancellation(
            lock,
            owner.claim,
            "superseding autofix",
            required_owner_prefix="autofix ",
        )
        self.assertEqual(requested.state, "cancel-requested")
        self.assertEqual(
            runtime_lock.validate_owned_lock(lock, owner.claim).state, "owned"
        )
        self.assertEqual(
            runtime_lock.validate_owned_lock(
                lock, owner.claim, reject_cancel=True
            ).state,
            "cancelled",
        )
        self.assertEqual(
            runtime_lock.release_owned_lock(lock, owner.claim).state, "released"
        )

        agent_lock = self.root / "locks" / "fix-agent.lock"
        agent = self.acquire_record(
            agent_lock,
            os.getpid(),
            "agent.sh target=pr#1 branch=issue-7-test",
        )
        refused = runtime_lock.request_cancellation(
            agent_lock,
            agent.claim,
            "superseding autofix",
            required_owner_prefix="autofix ",
        )
        self.assertEqual(refused.state, "not-cancellable")
        self.assertFalse((agent_lock / "cancel").exists())

    def test_signal_traps_exit_conventionally_and_release_exact_claims(
        self,
    ) -> None:
        for name in ("housekeeping.sh", "cache-warmer.sh", "warm-worktree.sh"):
            with self.subTest(script=name):
                source = (BIN_DIR / name).read_text(encoding="utf-8")
                self.assertIn("trap cleanup EXIT", source)
                self.assertIn("trap 'exit 130' INT", source)
                self.assertIn("trap 'exit 143' TERM", source)
                self.assertNotIn("trap cleanup EXIT INT TERM", source)
                self.assertIn("runtime_lock.py\" release-owned", source)

    def test_partial_owner_records_fail_closed(self) -> None:
        fields = ("pid", "token", "identity", "owner")
        for count in range(len(fields)):
            with self.subTest(files=fields[:count]):
                lock = self.root / "partial" / f"lock-{count}"
                lock.mkdir(parents=True)
                identity = runtime_lock.directory_identity(lock)
                self.assertIsNotNone(identity)
                values = {
                    "pid": f"{os.getpid()}\n",
                    "token": f"{runtime_lock.new_token()}\n",
                    "identity": f"{identity.render()}\n",  # type: ignore[union-attr]
                    "owner": "{}\n",
                }
                for field in fields[:count]:
                    (lock / field).write_text(values[field], encoding="utf-8")
                result = runtime_lock.acquire_lock(
                    lock,
                    os.getpid(),
                    runtime_lock.new_token(),
                    "contender",
                )
                self.assertEqual(result.state, "unsafe")
                self.assertTrue(lock.is_dir())

    def test_full_build_participants_use_one_compatible_lock_contract(self) -> None:
        participants = {
            "ci.sh": ("ci.sh pr=", "ci.sh pr=1"),
            "warm-worktree.sh": (
                "warm-worktree.sh $WORKTREE",
                "warm-worktree.sh test",
            ),
            "cache-warmer.sh": (
                "cache-warmer.sh $purpose",
                "cache-warmer.sh full-lake-build",
            ),
            "housekeeping.sh": (
                "housekeeping.sh linter-sweep",
                "housekeeping.sh linter-sweep",
            ),
        }
        shared_path = "MIPSTARRE_FULL_BUILD_LOCK:-$CACHE_ROOT/.full-build-lock"
        forbidden_mutations = (
            'mkdir "$FULL_BUILD_LOCK"',
            'mv "$FULL_BUILD_LOCK"',
            'rm -rf "$FULL_BUILD_LOCK"',
        )
        for script, (source_owner, _record_owner) in participants.items():
            source = (BIN_DIR / script).read_text(encoding="utf-8")
            self.assertIn("runtime_lock.py", source)
            self.assertIn(shared_path, source)
            self.assertIn(source_owner, source)
            for mutation in forbidden_mutations:
                self.assertNotIn(mutation, source)

        lock = self.root / "cache" / ".full-build-lock"
        record_owners = [value[1] for value in participants.values()]
        held = self.acquire_record(lock, os.getpid(), record_owners[0])
        for owner in record_owners[1:]:
            result = runtime_lock.acquire_lock(
                lock,
                os.getpid(),
                runtime_lock.new_token(),
                owner,
            )
            self.assertEqual(result.state, "busy")
            self.assertEqual(result.record.claim, held.claim)  # type: ignore[union-attr]
        released = runtime_lock.release_owned_lock(lock, held.claim)
        self.assertEqual(released.state, "released")
        replacement = self.acquire_record(
            lock, os.getpid(), participants["cache-warmer.sh"][1]
        )
        self.assertNotEqual(replacement.claim, held.claim)


class DispatchShellTests(FakeGhCase):
    """Dispatcher argv preserves parent-option placement for fresh and resumed runs."""

    def test_resume_places_exec_only_options_before_subcommand(self) -> None:
        repository, _remote, _base_sha, _head_sha = self.make_repository(
            name="dispatch-shell",
            base_sources={
                "local/bin/dispatch.sh": BIN_DIR / "dispatch.sh",
                "local/bin/runtime_lock.py": BIN_DIR / "runtime_lock.py",
                "local/bin/telemetry.py": BIN_DIR / "telemetry.py",
            },
            base_text={"AGENTS.md": "# Test agent instructions\n"},
        )
        fake_bin = self.root / "fake-bin"
        fake_bin.mkdir()
        fake_codex = fake_bin / "codex"
        fake_codex.write_text("#!/bin/sh\nexit 99\n", encoding="utf-8")
        fake_codex.chmod(0o755)
        environment = os.environ.copy()
        environment.update(
            {
                "MIPSTARRE_CACHE_ROOT": str(self.root / "dispatch-cache"),
                "PATH": str(fake_bin) + os.pathsep + environment.get("PATH", ""),
            }
        )

        def dry_run(*extra: str) -> list[str]:
            result = subprocess.run(
                [
                    "bash",
                    str(repository / "local/bin/dispatch.sh"),
                    "--role",
                    "scout",
                    "--issue",
                    "dispatch-argv-test",
                    "--worktree",
                    str(repository),
                    "--sandbox",
                    "read-only",
                    "--no-persona",
                    "--skip-hook-check",
                    "--dry-run",
                    *extra,
                    "--",
                    "Inspect only.",
                ],
                cwd=repository,
                env=environment,
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
            command = next(
                line.removeprefix("command:").strip()
                for line in result.stdout.splitlines()
                if line.startswith("command:")
            )
            return shlex.split(command)

        prefix = [
            "codex",
            "exec",
            "-C",
            str(repository.resolve()),
            "--sandbox",
            "read-only",
        ]
        fresh = dry_run()
        self.assertEqual(fresh[: len(prefix)], prefix)
        self.assertNotIn("resume", fresh)
        self.assertEqual(fresh[-2:], ["--", "<prompt>"])

        thread_id = "01a05b58-ff5d-7302-b38d-1d61f575a435"
        resumed = dry_run("--resume", thread_id)
        self.assertEqual(resumed[: len(prefix) + 1], [*prefix, "resume"])
        self.assertEqual(resumed[-3:], ["--", thread_id, "<prompt>"])


class AgentShellTests(FakeGhCase):
    """Human write sessions reserve the branch; read-only sessions only observe it."""

    def prepare_agent(self) -> tuple[Path, str]:
        repository, _remote, base_sha, head_sha = self.make_repository(
            name="agent-shell",
            base_sources={
                "local/bin/agent.sh": BIN_DIR / "agent.sh",
                "local/bin/github_api.py": BIN_DIR / "github_api.py",
                "local/bin/runtime_lock.py": BIN_DIR / "runtime_lock.py",
            },
            base_text={
                "local/bin/dispatch.sh": FAKE_DISPATCH,
                ".github/prompts/claude-code-system-prompt.md": (
                    "Trusted human-directed session persona.\n"
                ),
            },
        )
        pull = pull_row(1, head_sha, base_sha=base_sha)
        self.write_state(
            pulls={"1": pull},
            issues={
                "1": {**pull, "pull_request": {"url": pull["html_url"]}}
            },
        )
        return repository, head_sha

    def run_agent(
        self, repository: Path, cache: Path, *, read_only: bool = False
    ) -> subprocess.CompletedProcess[str]:
        command = [
            "bash",
            str(repository / "local/bin/agent.sh"),
            "1",
            "Inspect the workflow boundary.",
        ]
        if read_only:
            command.append("--read-only")
        environment = os.environ.copy()
        environment.update(
            {
                "MIPSTARRE_CACHE_ROOT": str(cache),
                "MIPSTARRE_TEST_BRANCH": "issue-7-test",
            }
        )
        return subprocess.run(
            command,
            cwd=repository,
            env=environment,
            text=True,
            capture_output=True,
            check=False,
        )

    def test_workspace_write_holds_branch_lease_through_dispatch(self) -> None:
        repository, _head_sha = self.prepare_agent()
        cache = self.root / "cache-agent-write"
        result = self.run_agent(repository, cache)

        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        self.assertTrue((cache / "fake-fix-lock-observed").is_file())
        self.assertFalse((cache / "locks/fix-issue-7-test.lock").exists())

    def test_read_only_does_not_reserve_or_cancel_branch_lease(self) -> None:
        repository, _head_sha = self.prepare_agent()
        cache = self.root / "cache-agent-read"
        lock = cache / "locks/fix-issue-7-test.lock"
        held = runtime_lock.acquire_lock(
            lock,
            os.getpid(),
            runtime_lock.new_token(),
            "autofix pr=1 branch=issue-7-test mode=ci",
        )
        self.assertEqual(held.state, "acquired")

        result = self.run_agent(repository, cache, read_only=True)

        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        self.assertIsNotNone(held.record)
        claim = held.record.claim  # type: ignore[union-attr]
        self.assertEqual(
            runtime_lock.validate_owned_lock(lock, claim).state,
            "owned",
        )
        self.assertFalse((lock / "cancel").exists())


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
        label_puts = [
            call
            for call in state["calls"]
            if call["args"][:3] == ["api", "--method", "PUT"]
            and call["args"][3].endswith("issues/1/labels")
        ]
        self.assertEqual(len(label_puts), 1)

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

    def test_ambiguous_label_replace_is_adopted_without_a_second_put(self) -> None:
        repository, _remote, _base_sha, head_sha = self.make_repository(
            name="ambiguous-labels"
        )
        self.write_state(
            labels=[{"name": "formalization"}],
            issues={"7": issue_row(7)},
            local_head=head_sha,
            ambiguous_label_put_once=True,
        )
        result = pr_open.main(
            [
                "--branch",
                "issue-7-test",
                "--title",
                "feat(local): reconcile labels",
                "--label",
                "formalization",
                "--issue",
                "7",
                "--repo-root",
                str(repository),
            ]
        )
        self.assertEqual(result, 0)
        puts = [
            call
            for call in self.state()["calls"]
            if call["args"][:3] == ["api", "--method", "PUT"]
            and call["args"][3].endswith("issues/1/labels")
        ]
        self.assertEqual(len(puts), 1)
        self.assertEqual(
            self.state()["issues"]["1"]["labels"],
            [{"name": "formalization"}],
        )

    def test_absent_label_replace_outcome_is_not_retried(self) -> None:
        repository, _remote, _base_sha, head_sha = self.make_repository(
            name="failed-labels"
        )
        self.write_state(
            labels=[{"name": "formalization"}],
            issues={"7": issue_row(7)},
            local_head=head_sha,
            fail_label_put_before_once=True,
        )
        result = pr_open.main(
            [
                "--branch",
                "issue-7-test",
                "--title",
                "feat(local): refuse label replay",
                "--label",
                "formalization",
                "--issue",
                "7",
                "--repo-root",
                str(repository),
            ]
        )
        self.assertEqual(result, 2)
        puts = [
            call
            for call in self.state()["calls"]
            if call["args"][:3] == ["api", "--method", "PUT"]
            and call["args"][3].endswith("issues/1/labels")
        ]
        self.assertEqual(len(puts), 1)
        self.assertEqual(self.state()["issues"]["1"]["labels"], [])


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
        self.assertEqual(len(self.state()["calls"]) - before, 2)

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

    def test_trusted_actor_defaults_to_owner_and_rejects_auth_mismatch(self) -> None:
        client = self.client()
        self.assertEqual(client.trusted_actor, "o")
        self.assertEqual(client.verify_authenticated_actor()["login"], "o")

        self.write_state(user={"login": "Mallory"}, statuses={})
        mismatched = self.client()
        with self.assertRaisesRegex(github_api.GitHubError, "does not match"):
            mismatched.probe_authentication()
        with self.assertRaisesRegex(github_api.GitHubError, "does not match"):
            mismatched.post_status("a" * 40, "local-ci/build", "success", "ok")
        with self.assertRaisesRegex(github_api.GitHubError, "does not match"):
            mismatched.ci_evidence(1, "a" * 40, "b" * 40)
        self.assertEqual(self.state()["statuses"], {})

        self.write_state(user={"login": "Dengnifer"})
        with mock.patch.dict(
            os.environ, {"MIPSTARRE_GITHUB_ACTOR": "Dengnifer"}
        ):
            configured = self.client()
            self.assertEqual(configured.trusted_actor, "Dengnifer")
            configured.probe_authentication()
        with mock.patch.dict(
            os.environ, {"MIPSTARRE_GITHUB_ACTOR": "invalid_actor"}
        ):
            with self.assertRaisesRegex(github_api.GitHubError, "valid GitHub"):
                self.client()

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

    def test_status_endpoint_binds_real_github_rows_without_sha(self) -> None:
        sha = "d" * 40
        self.write_state(status_responses_omit_sha=True)
        row = self.client().post_status(
            sha, "local-ci/build", "success", "passed"
        )
        self.assertEqual(row["sha"], sha)
        self.assertEqual(
            self.client().latest_statuses(sha)["local-ci/build"]["sha"], sha
        )
        posts = [
            call for call in self.state()["calls"]
            if call["args"][:3] == ["api", "--method", "POST"]
            and call["args"][3].endswith(f"statuses/{sha}")
        ]
        self.assertEqual(len(posts), 1)

    def test_status_readback_retries_without_reposting(self) -> None:
        delayed_sha = "7" * 40
        self.write_state(hide_status_reads=2)
        delayed = self.client().post_status(
            delayed_sha, "local-ci/build", "success", "delayed"
        )
        self.assertEqual(delayed["sha"], delayed_sha)

        transient_sha = "8" * 40
        self.write_state(status_readback_failures_once=3)
        transient = self.client().post_status(
            transient_sha, "local-ci/build", "success", "transient"
        )
        self.assertEqual(transient["sha"], transient_sha)

        calls = self.state()["calls"]
        for sha in (delayed_sha, transient_sha):
            posts = [
                call for call in calls
                if call["args"][:3] == ["api", "--method", "POST"]
                and call["args"][3].endswith(f"statuses/{sha}")
            ]
            self.assertEqual(len(posts), 1)

    def test_status_readback_absence_fails_closed_without_reposting(self) -> None:
        sha = "9" * 40
        self.write_state(hide_status_reads=99)
        client = self.client()
        with self.assertRaisesRegex(
            github_api.GitHubError, "not visible after authoritative read-back"
        ):
            client.post_status(sha, "local-ci/build", "success", "hidden")
        calls = self.state()["calls"]
        posts = [
            call for call in calls
            if call["args"][:3] == ["api", "--method", "POST"]
            and call["args"][3].endswith(f"statuses/{sha}")
        ]
        self.assertEqual(len(posts), 1)

        self.write_state(hide_status_reads=0)
        client.post_status(sha, "local-ci/build", "success", "hidden")
        posts = [
            call for call in self.state()["calls"]
            if call["args"][:3] == ["api", "--method", "POST"]
            and call["args"][3].endswith(f"statuses/{sha}")
        ]
        self.assertEqual(len(posts), 1)

    def test_explicit_status_sha_values_never_inherit_endpoint_identity(self) -> None:
        context = "local-ci/build"
        for index, value in enumerate((None, "", "deadbeef", "f" * 40), start=1):
            sha = str(index) * 40
            self.write_state(
                calls=[],
                statuses={},
                status_post_sha_override=value,
            )
            with self.assertRaisesRegex(
                github_api.GitHubError, "does not match its exact SHA"
            ):
                self.client().post_status(sha, context, "success", "invalid")
            posts = [
                call for call in self.state()["calls"]
                if call["args"][:3] == ["api", "--method", "POST"]
            ]
            self.assertEqual(len(posts), 1)

            stored = self.state()["statuses"][sha][0]
            self.write_state(
                statuses={sha: [{**stored, "sha": value}]},
                status_post_sha_override=value,
            )
            self.assertNotIn(context, self.client().latest_statuses(sha))

        sha = "5" * 40
        self.write_state(
            calls=[],
            statuses={},
            status_post_sha_override=sha,
            status_read_sha_override="e" * 40,
        )
        with self.assertRaisesRegex(
            github_api.GitHubError, "not visible after authoritative read-back"
        ):
            self.client().post_status(sha, context, "success", "conflicting read")
        posts = [
            call for call in self.state()["calls"]
            if call["args"][:3] == ["api", "--method", "POST"]
        ]
        self.assertEqual(len(posts), 1)

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

    def test_publication_guards_run_after_write_response_and_adoption(self) -> None:
        sha = "c" * 40
        base_sha = "a" * 40
        client = self.client()

        status_observations: list[int] = []

        def status_guard() -> None:
            status_observations.append(
                len(self.state().get("statuses", {}).get(sha, []))
            )

        client.post_status(
            sha,
            "local-ci/build",
            "success",
            "passed",
            before_mutation=status_guard,
        )
        client.post_status(
            sha,
            "local-ci/build",
            "success",
            "passed",
            before_mutation=status_guard,
        )
        self.assertEqual(status_observations, [0, 1, 1, 1])

        marker = github_api.stable_marker("guarded-comment", id="one")
        body = "guarded body\n\n" + marker
        comment_observations: list[int] = []

        def comment_guard() -> None:
            comment_observations.append(
                len(self.state().get("comments", {}).get("1", []))
            )

        client.comment_once(1, body, marker, before_mutation=comment_guard)
        client.comment_once(1, body, marker, before_mutation=comment_guard)
        self.assertEqual(comment_observations, [0, 1, 1])

        _review, _status, _sessions, review_body, review_marker = (
            self.review_bundle(self.root, sha, base_sha)
        )
        review_observations: list[int] = []
        local_observations: list[int] = []

        def review_guard() -> None:
            review_observations.append(
                len(self.state().get("reviews", {}).get("1", []))
            )

        def local_guard() -> None:
            local_observations.append(
                len(self.state().get("reviews", {}).get("1", []))
            )

        client.review_once(
            1,
            sha,
            review_body,
            "COMMENT",
            review_marker,
            before_mutation=review_guard,
            before_write=local_guard,
        )
        client.review_once(
            1,
            sha,
            review_body,
            "COMMENT",
            review_marker,
            before_mutation=review_guard,
            before_write=local_guard,
        )
        self.assertEqual(review_observations, [0, 0, 1, 1])
        self.assertEqual(local_observations, [0, 1, 1])


class CIPublicationTests(FakeGhCase):
    """Group 4: exact-head statuses, partial refusal, manifest, and races."""

    def prepare_ci(self, *, name: str = "repository") -> tuple[Path, str, str]:
        repository, _remote, base_sha, head_sha = self.make_repository(
            name=name,
            base_sources={
                "local/bin/ci.sh": BIN_DIR / "ci.sh",
                "local/bin/github_api.py": BIN_DIR / "github_api.py",
                "local/bin/runtime_lock.py": BIN_DIR / "runtime_lock.py",
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
        expected_contexts = {
            *github_api.CANONICAL_CI_CONTEXTS,
            github_api.CI_SUMMARY_CONTEXT,
        }
        self.assertEqual(contexts, expected_contexts)
        latest = self.client().latest_statuses(head_sha)
        self.assertTrue(all(row["state"] == "success" for row in latest.values()))
        self.assertTrue(
            all(
                "skipped" in latest[context.casefold()]["description"]
                for context in github_api.CANONICAL_CI_CONTEXTS
            )
        )
        self.assertIn(
            "digest=", latest[github_api.CI_SUMMARY_CONTEXT.casefold()]["description"]
        )
        comments = state["comments"]["1"]
        self.assertEqual(len(comments), 1)
        self.assertIn("mipstarre:ci-manifest", comments[0]["body"])
        self.client().ci_manifest(1, head_sha)
        calls = state["calls"]
        pending_index = next(
            index
            for index, call in enumerate(calls)
            if call["args"][:3] == ["api", "--method", "POST"]
            and call["args"][3].endswith(f"statuses/{head_sha}")
            and call["input"].get("context") == github_api.CI_SUMMARY_CONTEXT
            and call["input"].get("state") == "pending"
        )
        comment_index = next(
            index
            for index, call in enumerate(calls)
            if call["args"][:3] == ["api", "--method", "POST"]
            and call["args"][3].endswith("issues/1/comments")
            and "mipstarre:ci-manifest" in call["input"].get("body", "")
        )
        success_index = next(
            index
            for index, call in enumerate(calls)
            if call["args"][:3] == ["api", "--method", "POST"]
            and call["args"][3].endswith(f"statuses/{head_sha}")
            and call["input"].get("context") == github_api.CI_SUMMARY_CONTEXT
            and call["input"].get("state") == "success"
        )
        first_step_index = next(
            index
            for index, call in enumerate(calls)
            if call["args"][:3] == ["api", "--method", "POST"]
            and call["args"][3].endswith(f"statuses/{head_sha}")
            and call["input"].get("context") == "local-ci/build"
            and call["input"].get("state") == "pending"
        )
        self.assertLess(pending_index, first_step_index)
        self.assertLess(pending_index, comment_index)
        self.assertLess(comment_index, success_index)
        between = calls[comment_index + 1 : success_index]
        self.assertTrue(
            any(
                call["args"][:3] == ["api", "--method", "GET"]
                and call["args"][3].startswith("repos/o/r/issues/1/comments")
                for call in between
            )
        )
        self.assertTrue(
            any(
                call["args"][:3] == ["api", "--method", "GET"]
                and call["args"][3].startswith(
                    f"repos/o/r/commits/{head_sha}/statuses"
                )
                for call in between
            )
        )

    def test_ci_preserves_partial_and_requires_explicit_dead_owner_recovery(self) -> None:
        repository, _base_sha, _head_sha = self.prepare_ci(name="ci-lock-race")
        lock = self.root / "cache" / "locks" / "ci-1.lock"
        lock.mkdir(parents=True)

        nascent = self.run_ci(repository)
        self.assertNotEqual(nascent.returncode, 0)
        self.assertTrue(lock.is_dir())

        os.utime(lock, (1, 1))
        old_partial = self.run_ci(repository)
        self.assertNotEqual(old_partial.returncode, 0)
        self.assertTrue(lock.is_dir())

        lock.rmdir()
        stale = runtime_lock.acquire_lock(
            lock,
            999_999_999,
            runtime_lock.new_token(),
            "stale ci test",
        )
        self.assertEqual(stale.state, "acquired")
        blocked = self.run_ci(repository)
        self.assertNotEqual(blocked.returncode, 0)
        self.assertTrue(lock.is_dir())
        self.assertIsNotNone(stale.record)
        broken = runtime_lock.break_stale_lock(
            lock,
            stale.record.claim,  # type: ignore[union-attr]
        )
        self.assertEqual(broken.state, "broken")

        recovered = self.run_ci(repository)
        self.assertEqual(recovered.returncode, 0, recovered.stderr + recovered.stdout)
        self.assertFalse(lock.exists())

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
        rows = self.state()["statuses"].get(head_sha, [])
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
        rows = self.state()["statuses"].get(head_sha, [])
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

    def test_tree_dirtied_at_publication_boundary_never_leaves_success(self) -> None:
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
        self.assertFalse(any(row["state"] == "success" for row in latest.values()))
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
        self.assertEqual(
            set(latest),
            {*github_api.CANONICAL_CI_CONTEXTS, github_api.CI_SUMMARY_CONTEXT},
        )
        self.assertTrue(all(row["state"] == "error" for row in latest.values()))
        self.assertEqual(self.state()["comments"].get("1", []), [])


class ReviewPublicationTests(FakeGhCase):
    """Group 5: exact-commit COMMENT attestations, ledger, and head checks."""

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
                "local/bin/runtime_lock.py": BIN_DIR / "runtime_lock.py",
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
        options: tuple[str, ...] = (),
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
            ["bash", str(repository / "local/bin/review.sh"), "1", *options],
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
        self.assertEqual(reviews[0]["state"], "COMMENTED")
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
        self.assertEqual((attestation.event, attestation.fallback), ("COMMENT", "none"))
        latest = self.client(repository).latest_statuses(head_sha)[
            github_api.REVIEW_CONTEXT.casefold()
        ]
        self.assertEqual(latest["state"], "failure")
        calls = self.state()["calls"]
        pending_index = next(
            index
            for index, call in enumerate(calls)
            if call["args"][:3] == ["api", "--method", "POST"]
            and call["args"][3].endswith(f"statuses/{head_sha}")
            and call["input"].get("context") == github_api.REVIEW_CONTEXT
            and call["input"].get("state") == "pending"
        )
        review_index = next(
            index
            for index, call in enumerate(calls)
            if call["args"][:3] == ["api", "--method", "POST"]
            and call["args"][3].endswith("pulls/1/reviews")
        )
        failure_index = next(
            index
            for index, call in enumerate(calls)
            if call["args"][:3] == ["api", "--method", "POST"]
            and call["args"][3].endswith(f"statuses/{head_sha}")
            and call["input"].get("context") == github_api.REVIEW_CONTEXT
            and call["input"].get("state") == "failure"
        )
        self.assertLess(pending_index, review_index)
        self.assertLess(review_index, failure_index)
        self.assertEqual(calls[review_index]["input"]["event"], "COMMENT")

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

        second = self.run_review(repository, options=("--new-round",))
        self.assertEqual(second.returncode, 0, second.stderr + second.stdout)
        self.assertEqual(self.dispatch_count(repository), 1)
        self.assertEqual(len(self.review_posts()), 1)
        self.client(repository).review_evidence(1, head_sha, base_sha)

    def test_review_new_round_cli_produces_four_exact_comparison_rounds(self) -> None:
        repository, base_sha, head_sha, _pull = self.prepare_review_shell(
            name="review-four-rounds"
        )
        first = self.run_review(repository)
        self.assertEqual(first.returncode, 0, first.stderr + first.stdout)

        ordinary = self.run_review(repository)
        self.assertEqual(ordinary.returncode, 0, ordinary.stderr + ordinary.stdout)
        self.assertEqual(self.dispatch_count(repository), 1)

        for _ in range(3):
            result = self.run_review(repository, options=("--new-round",))
            self.assertEqual(result.returncode, 0, result.stderr + result.stdout)

        self.assertEqual(self.dispatch_count(repository), 4)
        attestations = self.client(repository).review_attestations(1)
        self.assertEqual(len(attestations), 4)
        self.assertTrue(
            all(
                item.head_sha == head_sha and item.base_sha == base_sha
                for item in attestations
            )
        )
        self.assertEqual(len({item.run_id for item in attestations}), 4)
        self.assertEqual(len(self.review_posts()), 4)

    def test_failed_dispatch_round_requires_explicit_new_round(self) -> None:
        for publication_fails in (False, True):
            with self.subTest(publication_fails=publication_fails):
                repository, base_sha, head_sha, _pull = self.prepare_review_shell(
                    name=f"review-dispatch-retry-{publication_fails}"
                )
                initial = self.run_review(repository)
                self.assertEqual(initial.returncode, 0, initial.stderr + initial.stdout)
                if publication_fails:
                    self.write_state(fail_review_aborted_status_once=True)
                failed = self.run_review(
                    repository,
                    options=("--new-round",),
                    extra_env={"MIPSTARRE_TEST_REVIEW_DISPATCH_FAIL": "1"},
                )
                self.assertNotEqual(failed.returncode, 0)
                self.assertEqual(self.dispatch_count(repository), 2)
                self.assertEqual(len(self.review_posts()), 1)
                latest = self.client(repository).latest_statuses(head_sha)[
                    github_api.REVIEW_CONTEXT.casefold()
                ]
                self.assertEqual(
                    latest["state"], "pending" if publication_fails else "error"
                )
                attempt = github_api.parse_review_attempt_status(latest, head_sha)
                self.assertIsNotNone(attempt)
                self.assertEqual(
                    attempt["base_fingerprint"],
                    github_api.stable_digest({"base_sha": base_sha}, length=32),
                )

                ordinary = self.run_review(repository)
                self.assertNotEqual(ordinary.returncode, 0)
                self.assertEqual(self.dispatch_count(repository), 2)

                recovered = self.run_review(repository, options=("--new-round",))
                self.assertEqual(
                    recovered.returncode, 0, recovered.stderr + recovered.stdout
                )
                self.assertEqual(self.dispatch_count(repository), 3)
                self.assertEqual(len(self.review_posts()), 2)
                adopted = self.run_review(repository)
                self.assertEqual(adopted.returncode, 0, adopted.stderr + adopted.stdout)
                self.assertEqual(self.dispatch_count(repository), 3)

    def test_failed_parser_round_requires_explicit_new_round(self) -> None:
        malformed = "review output without the canonical findings grammar\n"
        for publication_fails in (False, True):
            with self.subTest(publication_fails=publication_fails):
                repository, _base_sha, _head_sha, _pull = self.prepare_review_shell(
                    name=f"review-parser-retry-{publication_fails}"
                )
                initial = self.run_review(repository)
                self.assertEqual(initial.returncode, 0, initial.stderr + initial.stdout)
                if publication_fails:
                    self.write_state(fail_review_aborted_status_once=True)
                failed = self.run_review(
                    repository,
                    output=malformed,
                    options=("--new-round",),
                )
                self.assertEqual(failed.returncode, 4)
                self.assertEqual(self.dispatch_count(repository), 2)
                self.assertEqual(len(self.review_posts()), 1)

                ordinary = self.run_review(repository)
                self.assertNotEqual(ordinary.returncode, 0)
                self.assertEqual(self.dispatch_count(repository), 2)
                recovered = self.run_review(repository, options=("--new-round",))
                self.assertEqual(
                    recovered.returncode, 0, recovered.stderr + recovered.stdout
                )
                self.assertEqual(self.dispatch_count(repository), 3)
                self.assertEqual(len(self.review_posts()), 2)

    def test_review_recovers_untrusted_summary_but_rejects_trusted_conflict(self) -> None:
        for index, creator in enumerate(({"login": "Mallory"}, None), start=1):
            with self.subTest(creator=creator):
                repository, base_sha, head_sha, _pull = self.prepare_review_shell(
                    name=f"review-untrusted-summary-{index}"
                )
                first = self.run_review(repository)
                self.assertEqual(first.returncode, 0, first.stderr + first.stdout)
                before_dispatch = self.dispatch_count(repository)
                state = self.state()
                poisoned = {
                    "id": 999,
                    "sha": head_sha,
                    "context": github_api.REVIEW_CONTEXT,
                    "state": "failure",
                    "description": "untrusted summary poison",
                    "created_at": "2098-01-01T00:00:11Z",
                }
                if creator is not None:
                    poisoned["creator"] = creator
                state["statuses"][head_sha].append(poisoned)
                self.write_state(**state)

                recovered = self.run_review(repository)
                self.assertEqual(
                    recovered.returncode, 0, recovered.stderr + recovered.stdout
                )
                self.assertEqual(self.dispatch_count(repository), before_dispatch)
                evidence = self.client(repository).review_evidence(
                    1, head_sha, base_sha
                )
                self.assertEqual(evidence.status["creator"]["login"], "o")

        repository, _base_sha, head_sha, _pull = self.prepare_review_shell(
            name="review-trusted-summary-conflict"
        )
        first = self.run_review(repository)
        self.assertEqual(first.returncode, 0, first.stderr + first.stdout)
        self.client(repository).post_status(
            head_sha,
            github_api.REVIEW_CONTEXT,
            "pending",
            "trusted summary conflict without canonical attempt binding",
        )
        before_dispatch = self.dispatch_count(repository)
        conflict = self.run_review(repository, options=("--new-round",))
        self.assertNotEqual(conflict.returncode, 0)
        self.assertEqual(self.dispatch_count(repository), before_dispatch)

    def test_review_does_not_recover_unrelated_pending_run(self) -> None:
        repository, base_sha, head_sha, _pull = self.prepare_review_shell()
        first = self.run_review(repository)
        self.assertEqual(first.returncode, 0, first.stderr + first.stdout)
        self.client(repository).post_status(
            head_sha,
            github_api.REVIEW_CONTEXT,
            "pending",
            github_api.review_pending_description(base_sha, "unrelated-run"),
        )
        before_dispatch = self.dispatch_count(repository)
        before_posts = len(self.review_posts())
        second = self.run_review(repository)
        self.assertNotEqual(second.returncode, 0)
        self.assertEqual(self.dispatch_count(repository), before_dispatch)
        self.assertEqual(len(self.review_posts()), before_posts)

    def test_review_rejects_wrong_base_attempt_even_with_new_round(self) -> None:
        repository, base_sha, head_sha, _pull = self.prepare_review_shell(
            name="review-wrong-base-attempt"
        )
        first = self.run_review(repository)
        self.assertEqual(first.returncode, 0, first.stderr + first.stdout)
        wrong_base = "f" * 40
        self.client(repository).post_status(
            head_sha,
            github_api.REVIEW_CONTEXT,
            "error",
            github_api.review_aborted_description(wrong_base, "wrong-base"),
        )
        before_dispatch = self.dispatch_count(repository)
        rejected = self.run_review(repository, options=("--new-round",))
        self.assertNotEqual(rejected.returncode, 0)
        self.assertEqual(self.dispatch_count(repository), before_dispatch)
        self.assertNotEqual(base_sha, wrong_base)

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
                github_api.review_pending_description(_base_sha, "race-run"),
            ),
            "created_at": "2099-01-01T00:00:00Z",
            "creator": {"login": "o"},
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

    def test_accepted_review_readback_outage_is_adopted_on_rerun(self) -> None:
        repository, _base_sha, head_sha, _pull = self.prepare_review_shell(
            name="review-accepted-readback-outage"
        )
        self.write_state(ambiguous_review_readback_failures_once=9)

        first = self.run_review(repository)

        self.assertNotEqual(first.returncode, 0)
        self.assertEqual(self.dispatch_count(repository), 1)
        self.assertEqual(len(self.review_posts()), 1)
        latest = self.client(repository).latest_statuses(head_sha)[
            github_api.REVIEW_CONTEXT.casefold()
        ]
        self.assertEqual(latest["state"], "pending")
        self.assertNotIn("state=aborted", latest["description"])

        second = self.run_review(repository)

        self.assertEqual(second.returncode, 0, second.stderr + second.stdout)
        self.assertEqual(self.dispatch_count(repository), 1)
        self.assertEqual(len(self.review_posts()), 1)
        final = self.client(repository).latest_statuses(head_sha)[
            github_api.REVIEW_CONTEXT.casefold()
        ]
        self.assertEqual(final["state"], "success")

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
        self.assertEqual(latest["state"], "error")
        attempt = github_api.parse_review_attempt_status(latest, head_sha)
        self.assertIsNotNone(attempt)
        self.assertEqual(attempt["attempt_state"], "aborted")

    def test_invoked_review_post_guard_failure_retains_pending_attempt(self) -> None:
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
        attempt = github_api.parse_review_attempt_status(latest, head_sha)
        self.assertIsNotNone(attempt)
        self.assertEqual(attempt["attempt_state"], "pending")

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

    def test_adverse_findings_publish_one_comment_and_failure_summary(self) -> None:
        sha, base_sha = "e" * 40, "b" * 40
        client = self.client()
        _review, status, sessions, body, marker = self.review_bundle(
            self.root, sha, base_sha, findings=1
        )
        row, used_event = client.review_once(1, sha, body, "COMMENT", marker)
        self.assertEqual((used_event, row["state"]), ("COMMENT", "COMMENTED"))
        posts = [
            call
            for call in self.state()["calls"]
            if call["args"][:3] == ["api", "--method", "POST"]
            and call["args"][3].endswith("pulls/1/reviews")
        ]
        self.assertEqual(
            [call["input"]["event"] for call in posts],
            ["COMMENT"],
        )
        self.assertIn("findings=1 event=COMMENT fallback=none", row["body"])

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
            ("COMMENT", "none", 1, "failure"),
        )
        self.assertEqual(evidence.attestation.head_sha, sha)
        self.assertEqual(evidence.attestation.base_sha, base_sha)
        self.assertEqual(evidence.attestation.run_id, "review-test")
        self.assertEqual(evidence.attestation.lanes[0].name, sessions[0]["name"])
        self.assertEqual(client.latest_review_ledger(1)["body"], body)

        adopted, adopted_event = client.review_once(1, sha, body, "COMMENT", marker)
        self.assertEqual((adopted["id"], adopted_event), (row["id"], "COMMENT"))
        posts = [
            call
            for call in self.state()["calls"]
            if call["args"][:3] == ["api", "--method", "POST"]
            and call["args"][3].endswith("pulls/1/reviews")
        ]
        self.assertEqual(len(posts), 1)

    def test_request_changes_publication_is_rejected_before_post(self) -> None:
        sha, base_sha = "e" * 40, "b" * 40
        _review, _status, _sessions, body, marker = self.review_bundle(
            self.root, sha, base_sha, findings=1
        )
        with self.assertRaisesRegex(github_api.GitHubError, "only COMMENT"):
            self.client().review_once(1, sha, body, "REQUEST_CHANGES", marker)
        posts = [
            call
            for call in self.state()["calls"]
            if call["args"][:3] == ["api", "--method", "POST"]
            and call["args"][3].endswith("pulls/1/reviews")
        ]
        self.assertEqual(posts, [])

    def test_ambiguous_and_transient_comment_writes_never_repeat(self) -> None:
        sha, base_sha = "c" * 40, "a" * 40
        _review, _status, _sessions, body, marker = self.review_bundle(
            self.root, sha, base_sha, findings=1
        )
        self.write_state(ambiguous_review_once=True)
        row, used_event = self.client().review_once(1, sha, body, "COMMENT", marker)
        self.assertEqual((row["state"], used_event), ("COMMENTED", "COMMENT"))
        posts = [
            call
            for call in self.state()["calls"]
            if call["args"][:3] == ["api", "--method", "POST"]
            and call["args"][3].endswith("pulls/1/reviews")
        ]
        self.assertEqual([call["input"]["event"] for call in posts], ["COMMENT"])

        reconciled_sha = "f" * 40
        _review, _status, _sessions, reconciled_body, reconciled_marker = (
            self.review_bundle(
                self.root,
                reconciled_sha,
                base_sha,
                findings=1,
                run_id="review-reconciled",
            )
        )
        self.write_state(
            reviews={},
            calls=[],
            failures={},
            ambiguous_review_readback_failures_once=3,
        )
        reconciled, reconciled_event = self.client().review_once(
            1,
            reconciled_sha,
            reconciled_body,
            "COMMENT",
            reconciled_marker,
        )
        self.assertEqual(
            (reconciled["state"], reconciled_event),
            ("COMMENTED", "COMMENT"),
        )
        posts = [
            call
            for call in self.state()["calls"]
            if call["args"][:3] == ["api", "--method", "POST"]
            and call["args"][3].endswith("pulls/1/reviews")
        ]
        self.assertEqual(len(posts), 1)

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
            self.client().review_once(1, other_sha, other_body, "COMMENT", other_marker)
        posts = [
            call
            for call in self.state()["calls"]
            if call["args"][:3] == ["api", "--method", "POST"]
            and call["args"][3].endswith("pulls/1/reviews")
        ]
        self.assertEqual([call["input"]["event"] for call in posts], ["COMMENT"])

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
                        "user": {"login": "o"},
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

    def test_archived_reviewer_session_keeps_exact_attestation_valid(self) -> None:
        sha, base_sha = "b" * 40, "a" * 40
        review, status, sessions, _body, _marker = self.review_bundle(
            self.root, sha, base_sha
        )
        self.write_state(reviews={"1": [review]}, statuses={sha: [status]})
        completion = sessions[0]
        archived = {
            **completion,
            "status": "archived",
            "status_ts": "2026-01-01T00:03:00+00:00",
            "note": "review retained",
        }
        telemetry = self.root / "results/telemetry/sessions.jsonl"
        self.append_sessions(self.root, [completion, archived])
        evidence = self.client().review_evidence(1, sha, base_sha)
        self.assertEqual(evidence.attestation.run_id, "review-test")

        telemetry.write_text("", encoding="utf-8")
        changed_identity = {**archived, "worktree": str(self.root / "other")}
        self.append_sessions(self.root, [completion, changed_identity])
        with self.assertRaises(github_api.GitHubError):
            self.client().review_evidence(1, sha, base_sha)

        telemetry.write_text("", encoding="utf-8")
        self.append_sessions(self.root, [archived, completion])
        with self.assertRaises(github_api.GitHubError):
            self.client().review_evidence(1, sha, base_sha)

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
                "local/bin/runtime_lock.py": BIN_DIR / "runtime_lock.py",
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

    def test_autofix_never_cancels_a_human_agent_branch_lease(self) -> None:
        repository, head_sha, pull = self.prepare_autofix(
            name="autofix-agent-owner"
        )
        self.configure_failed_ci(repository, head_sha, pull)
        cache = self.root / f"cache-{repository.name}"
        lock = cache / "locks/fix-issue-7-test.lock"
        lock.parent.mkdir(parents=True)
        held = runtime_lock.acquire_lock(
            lock,
            os.getpid(),
            runtime_lock.new_token(),
            "agent.sh target=pr#1 branch=issue-7-test",
        )
        self.assertEqual(held.state, "acquired")

        result = self.run_autofix(
            repository,
            extra_env={"MIPSTARRE_FIX_LOCK_WAIT": "0"},
        )

        self.assertNotEqual(result.returncode, 0)
        self.assertIn("non-autofix writer", result.stderr)
        self.assertFalse((lock / "cancel").exists())
        self.assertIsNotNone(held.record)
        claim = held.record.claim  # type: ignore[union-attr]
        self.assertEqual(
            runtime_lock.validate_owned_lock(lock, claim).state,
            "owned",
        )

    def test_adverse_comment_attestation_is_consumed_by_review_autofix(self) -> None:
        repository, head_sha, pull = self.prepare_autofix(with_review_prompts=True)
        pull["labels"] = [{"name": github_api.AUTO_FIX_LABEL}]
        review, _status, sessions, _body, _marker = self.review_bundle(
            repository,
            head_sha,
            pull["base"]["sha"],
            findings=1,
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

    def test_cancel_during_running_autofix_commits_and_pushes_cleanly(self) -> None:
        repository, head_sha, pull = self.prepare_autofix(
            name="autofix-lock-cancel"
        )
        self.configure_failed_ci(repository, head_sha, pull)
        result = self.run_autofix(
            repository,
            extra_env={"MIPSTARRE_TEST_LOCK_ACTION": "cancel"},
        )
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        self.assertIn("publishing only the already committed tip", result.stderr)
        self.assertEqual(self.autofix_dispatch_count(repository), 1)
        local_head = run_git(repository, "rev-parse", "HEAD")
        remote_head = run_git(
            repository, "ls-remote", "github", "refs/heads/issue-7-test"
        ).split()[0]
        self.assertNotEqual(local_head, head_sha)
        self.assertEqual(remote_head, local_head)
        self.assertIn(
            "[codex-auto-fix]",
            run_git(repository, "show", "-s", "--format=%s", local_head),
        )
        self.assertEqual(
            run_git(repository, "status", "--porcelain=v1", "--untracked-files=all"),
            "",
        )
        lock = (
            self.root
            / f"cache-{repository.name}"
            / "locks/fix-issue-7-test.lock"
        )
        self.assertFalse(lock.exists())

    def test_autofix_owner_theft_aborts_and_preserves_replacement(self) -> None:
        repository, head_sha, pull = self.prepare_autofix(
            name="autofix-lock-steal"
        )
        self.configure_failed_ci(repository, head_sha, pull)
        result = self.run_autofix(
            repository,
            extra_env={"MIPSTARRE_TEST_LOCK_ACTION": "steal"},
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("fix-lock ownership was lost", result.stderr)
        self.assertEqual(self.autofix_dispatch_count(repository), 1)
        self.assertEqual(run_git(repository, "rev-parse", "HEAD"), head_sha)
        remote_head = run_git(
            repository, "ls-remote", "github", "refs/heads/issue-7-test"
        ).split()[0]
        self.assertEqual(remote_head, head_sha)
        lock = (
            self.root
            / f"cache-{repository.name}"
            / "locks/fix-issue-7-test.lock"
        )
        self.assertTrue(lock.is_dir())
        replacement = runtime_lock.inspect_lock(lock)
        self.assertEqual(replacement.state, "held")
        self.assertIsNotNone(replacement.record)
        self.assertEqual(replacement.record.owner, "autofix replacement-test")

    def test_malformed_autofix_cancellation_fails_closed(self) -> None:
        repository, head_sha, pull = self.prepare_autofix(
            name="autofix-lock-malformed"
        )
        self.configure_failed_ci(repository, head_sha, pull)
        result = self.run_autofix(
            repository,
            extra_env={"MIPSTARRE_TEST_LOCK_ACTION": "malformed-cancel"},
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("unsafe fix-lock state", result.stderr)
        self.assertEqual(run_git(repository, "rev-parse", "HEAD"), head_sha)
        remote_head = run_git(
            repository, "ls-remote", "github", "refs/heads/issue-7-test"
        ).split()[0]
        self.assertEqual(remote_head, head_sha)
        self.assertEqual(
            run_git(repository, "status", "--porcelain=v1", "--untracked-files=all"),
            "M README.md",
        )

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
            'helper="$PWD/local/bin/runtime_lock.py"\n'
            'claim="$(python3 "$helper" inspect "$lock")" || exit 1\n'
            'identity="$(printf "%s\\n" "$claim" | cut -d "|" -f 2)"\n'
            'pid="$(printf "%s\\n" "$claim" | cut -d "|" -f 3)"\n'
            'token="$(printf "%s\\n" "$claim" | cut -d "|" -f 4)"\n'
            'digest="$(printf "%s\\n" "$claim" | cut -d "|" -f 5)"\n'
            'python3 "$helper" request-cancel "$lock" "$identity" "$pid" '
            '"$token" "$digest" "post-commit test" --owner-prefix "autofix "\n',
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

    def test_merge_preflight_requires_draft_to_be_exactly_false(self) -> None:
        sha = "d" * 40
        base_sha = "b" * 40
        accepted = pull_row(1, sha, base_sha=base_sha)
        self.assertEqual(
            pr_merge.require_open_mergeable(accepted, 1).head_sha,
            sha,
        )
        for value in (None, 0, "false", True):
            with self.subTest(draft=value):
                rejected = {**accepted, "draft": value}
                with self.assertRaisesRegex(
                    pr_merge.GateFailure,
                    "draft state is not exactly false",
                ):
                    pr_merge.require_open_mergeable(rejected, 1)
        missing = dict(accepted)
        missing.pop("draft")
        with self.assertRaisesRegex(
            pr_merge.GateFailure,
            "draft state is not exactly false",
        ):
            pr_merge.require_open_mergeable(missing, 1)

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
        green_comment, green_statuses = self.ci_bundle(sha, base_sha)
        step_only = [
            status
            for status in green_statuses
            if status["context"] != github_api.CI_SUMMARY_CONTEXT
        ]
        self.write_state(
            comments={"1": [green_comment]}, statuses={sha: step_only}
        )
        with self.assertRaises(pr_merge.GateFailure):
            pr_merge.require_ci(client, 1, sha, base_sha)
        with self.assertRaises(github_api.GitHubError):
            github_api.require_ci_success(client, 1, sha, base_sha)
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

    def test_adverse_comment_is_valid_evidence_but_blocks_merge(self) -> None:
        sha, base_sha = "a" * 40, "b" * 40
        review, status, sessions, _body, _marker = self.review_bundle(
            self.root,
            sha,
            base_sha,
            findings=1,
        )
        self.append_sessions(self.root, sessions)
        self.write_state(reviews={"1": [review]}, statuses={sha: [status]})
        evidence = self.client().review_evidence(1, sha, base_sha)
        self.assertEqual(evidence.attestation.event, "COMMENT")
        self.assertEqual(evidence.attestation.fallback, "none")
        self.assertEqual(evidence.attestation.row["state"], "COMMENTED")
        with self.assertRaisesRegex(pr_merge.GateFailure, "not a clean COMMENT"):
            pr_merge.require_review(self.client(), 1, sha, base_sha)

    def test_evidence_is_bound_to_trusted_comment_review_and_status_actors(self) -> None:
        sha, base_sha = "7" * 40, "8" * 40
        state = self.green_state(sha, base_sha)
        trusted_comment = state["comments"]["1"][0]
        trusted_review = state["reviews"]["1"][0]
        statuses = state["statuses"][sha]

        copied_comment = {
            **trusted_comment,
            "id": 900,
            "created_at": "2099-01-01T00:00:00Z",
            "user": {"login": "Mallory"},
        }
        copied_review = {
            **trusted_review,
            "id": 901,
            "submitted_at": "2099-01-01T00:00:01Z",
            "user": {"login": "Mallory"},
        }
        self.write_state(
            comments={"1": [trusted_comment, copied_comment]},
            reviews={"1": [trusted_review, copied_review]},
            statuses={sha: statuses},
        )
        pr_merge.require_ci(self.client(), 1, sha, base_sha)
        pr_merge.require_review(self.client(), 1, sha, base_sha)

        for field, row, collection, requirement in (
            ("user", trusted_comment, "comments", pr_merge.require_ci),
            ("user", trusted_review, "reviews", pr_merge.require_review),
        ):
            for identity in ({"login": "Mallory"}, None):
                with self.subTest(collection=collection, identity=identity):
                    candidate = copy.deepcopy(row)
                    if identity is None:
                        candidate.pop(field, None)
                    else:
                        candidate[field] = identity
                    self.write_state(
                        comments={
                            "1": [candidate]
                            if collection == "comments"
                            else [trusted_comment]
                        },
                        reviews={"1": [candidate] if collection == "reviews" else [trusted_review]},
                        statuses={sha: statuses},
                    )
                    with self.assertRaises(pr_merge.GateFailure):
                        requirement(self.client(), 1, sha, base_sha)

        for context in (
            "local-ci/build",
            github_api.CI_SUMMARY_CONTEXT,
            github_api.REVIEW_CONTEXT,
        ):
            trusted = next(
                item for item in statuses if item["context"].casefold() == context.casefold()
            )
            for creator in ({"login": "Mallory"}, None):
                with self.subTest(context=context, creator=creator):
                    poisoned = {**trusted, "id": 999, "created_at": "2099-01-01T00:00:02Z"}
                    if creator is None:
                        poisoned.pop("creator", None)
                    else:
                        poisoned["creator"] = creator
                    self.write_state(
                        comments={"1": [trusted_comment]},
                        reviews={"1": [trusted_review]},
                        statuses={sha: [*statuses, poisoned]},
                    )
                    requirement = (
                        pr_merge.require_review
                        if context == github_api.REVIEW_CONTEXT
                        else pr_merge.require_ci
                    )
                    with self.assertRaises(pr_merge.GateFailure):
                        requirement(self.client(), 1, sha, base_sha)

    def test_server_policy_requires_exact_zero_approval_classic_protection(self) -> None:
        client = self.client()
        pr_merge.require_server_policy(client, "main")

        for allowance in ("absent", None):
            with self.subTest(valid_bypass=allowance):
                protection = classic_protection()
                reviews = protection["required_pull_request_reviews"]
                if allowance == "absent":
                    reviews.pop("bypass_pull_request_allowances")
                else:
                    reviews["bypass_pull_request_allowances"] = None
                self.write_state(branch_protections={"main": protection})
                pr_merge.require_server_policy(client, "main")

        protection = classic_protection()
        for check in protection["required_status_checks"]["checks"]:
            check["app_id"] = -1
        self.write_state(branch_protections={"main": protection})
        pr_merge.require_server_policy(client, "main")

        protection = classic_protection()
        protection["required_linear_history"] = {"enabled": False}
        self.write_state(branch_protections={"main": protection})
        pr_merge.require_server_policy(client, "main")

        invalid: list[tuple[str, dict]] = []
        protection = classic_protection()
        protection["required_status_checks"]["strict"] = False
        invalid.append(("nonstrict", protection))
        protection = classic_protection()
        protection["required_status_checks"]["contexts"].append("legacy/check")
        protection["required_status_checks"]["checks"].append(
            {"context": "legacy/check", "app_id": None}
        )
        invalid.append(("extra-check", protection))
        protection = classic_protection()
        protection["enforce_admins"]["enabled"] = False
        invalid.append(("admins", protection))
        protection = classic_protection()
        protection["required_pull_request_reviews"][
            "required_approving_review_count"
        ] = 1
        invalid.append(("approval", protection))
        protection = classic_protection()
        protection["required_pull_request_reviews"][
            "require_code_owner_reviews"
        ] = True
        invalid.append(("code-owner", protection))
        protection = classic_protection()
        protection["required_pull_request_reviews"][
            "require_last_push_approval"
        ] = True
        invalid.append(("last-push", protection))
        protection = classic_protection()
        protection["required_pull_request_reviews"][
            "bypass_pull_request_allowances"
        ]["users"] = [{"login": "owner"}]
        invalid.append(("bypass-user", protection))
        for actor_kind in ("teams", "apps"):
            protection = classic_protection()
            protection["required_pull_request_reviews"][
                "bypass_pull_request_allowances"
            ][actor_kind] = [{"slug": "bypass"}]
            invalid.append((f"bypass-{actor_kind}", protection))
        for malformed in ([], {"users": [], "teams": []}):
            protection = classic_protection()
            protection["required_pull_request_reviews"][
                "bypass_pull_request_allowances"
            ] = malformed
            invalid.append(("bypass-malformed", protection))
        for producer in (1, "-1", "missing"):
            protection = classic_protection()
            check = protection["required_status_checks"]["checks"][0]
            if producer == "missing":
                check.pop("app_id")
            else:
                check["app_id"] = producer
            invalid.append((f"classic-producer-{producer}", protection))
        protection = classic_protection()
        protection["allow_force_pushes"]["enabled"] = True
        invalid.append(("force-push", protection))
        protection = classic_protection()
        protection["allow_deletions"]["enabled"] = True
        invalid.append(("deletion", protection))
        protection = classic_protection()
        protection["required_linear_history"] = {"enabled": True}
        invalid.append(("linear-history", protection))
        for malformed in (None, [], {}, {"enabled": None}):
            protection = classic_protection()
            protection["required_linear_history"] = malformed
            invalid.append((f"linear-history-malformed-{malformed!r}", protection))

        for name, candidate in invalid:
            with self.subTest(name=name):
                self.write_state(
                    branch_protections={"main": candidate},
                    branch_rules={"main": []},
                    rulesets={},
                )
                with self.assertRaises(pr_merge.GateFailure):
                    pr_merge.require_server_policy(client, "main")

    def test_server_policy_rejects_weak_effective_rules_and_bypasses(self) -> None:
        client = self.client()
        status_rule = {
            "type": "required_status_checks",
            "ruleset_id": 7,
            "parameters": {
                "strict_required_status_checks_policy": True,
                "required_status_checks": [
                    {
                        "context": github_api.CI_SUMMARY_CONTEXT,
                        "integration_id": None,
                    },
                    {
                        "context": github_api.REVIEW_CONTEXT,
                        "integration_id": None,
                    },
                ],
            },
        }
        review_rule = {
            "type": "pull_request",
            "ruleset_id": 7,
            "parameters": {
                "required_approving_review_count": 0,
                "require_code_owner_review": False,
                "require_last_push_approval": False,
                "allowed_merge_methods": ["merge"],
            },
        }
        active = {"enforcement": "active", "bypass_actors": []}
        self.write_state(
            branch_protections={"main": classic_protection()},
            branch_rules={"main": [status_rule, review_rule]},
            rulesets={"7": active},
        )
        pr_merge.require_server_policy(client, "main")

        pat_status_rule = copy.deepcopy(status_rule)
        for check in pat_status_rule["parameters"]["required_status_checks"]:
            check["integration_id"] = -1
        self.write_state(branch_rules={"main": [pat_status_rule, review_rule]})
        pr_merge.require_server_policy(client, "main")

        candidates = {
            "merge-queue": [{"type": "merge_queue", "parameters": {}}],
            "linear-history": [
                {"type": "required_linear_history", "parameters": {}}
            ],
            "nonstrict-status": [
                {
                    **status_rule,
                    "parameters": {
                        **status_rule["parameters"],
                        "strict_required_status_checks_policy": False,
                    },
                }
            ],
            "positive-approval": [
                {
                    **review_rule,
                    "parameters": {
                        **review_rule["parameters"],
                        "required_approving_review_count": 1,
                    },
                }
            ],
        }
        for producer in (7, "-1", "missing"):
            candidate = copy.deepcopy(status_rule)
            check = candidate["parameters"]["required_status_checks"][0]
            if producer == "missing":
                check.pop("integration_id")
            else:
                check["integration_id"] = producer
            candidates[f"effective-producer-{producer}"] = [candidate]
        for name, rules in candidates.items():
            with self.subTest(name=name):
                self.write_state(
                    branch_rules={"main": rules},
                    rulesets={"7": active},
                )
                with self.assertRaises(pr_merge.GateFailure):
                    pr_merge.require_server_policy(client, "main")

        self.write_state(
            branch_rules={"main": [status_rule]},
            rulesets={
                "7": {
                    "enforcement": "active",
                    "bypass_actors": [{"actor_type": "OrganizationAdmin"}],
                }
            },
        )
        with self.assertRaisesRegex(pr_merge.GateFailure, "bypass actors"):
            pr_merge.require_server_policy(client, "main")

    def test_adjudication_accepts_exact_fixed_and_open_tracked_dispositions(self) -> None:
        sha, base_sha = "2" * 40, "3" * 40
        pull = pull_row(1, sha, base_sha=base_sha)
        pull["labels"] = [{"name": github_api.ADJUDICATION_LABEL}]
        reviews, _statuses, sessions, comment, _payload = (
            self.adjudication_bundle(self.root, sha, base_sha)
        )
        self.append_sessions(self.root, sessions)
        self.write_state(pulls={"1": pull}, reviews={"1": reviews}, comments={"1": [comment]})
        evidence = pr_merge.require_adjudication(
            self.client(), pull, 1, sha, base_sha, require_status=False
        )
        self.assertEqual(evidence.source.finding_rows[0].key, "code:F1")

        tracked = [{"finding": "code:F1", "outcome": "tracked", "issue": 7}]
        reviews, _statuses, sessions, comment, _payload = self.adjudication_bundle(
            self.root,
            sha,
            base_sha,
            first_review_id=10,
            dispositions=tracked,
        )
        self.append_sessions(self.root, sessions)
        self.write_state(
            pulls={"1": pull},
            reviews={"1": reviews},
            comments={"1": [comment]},
            issues={"7": issue_row(7)},
        )
        pr_merge.require_adjudication(
            self.client(), pull, 1, sha, base_sha, require_status=False
        )

    def test_adjudication_ignores_prefix_poison_and_requires_trusted_later_row(self) -> None:
        sha, base_sha = "a" * 40, "b" * 40
        pull = pull_row(1, sha, base_sha=base_sha)
        pull["labels"] = [{"name": github_api.ADJUDICATION_LABEL}]
        reviews, _statuses, sessions, comment, _payload = self.adjudication_bundle(
            self.root, sha, base_sha, first_review_id=30
        )
        self.append_sessions(self.root, sessions)
        prefix_poison = {
            "id": 600,
            "body": "ADJUDICATION\nthis is unrelated prose",
            "created_at": "2099-01-01T00:00:00Z",
            "updated_at": "2099-01-01T00:00:00Z",
            "user": {"login": "o"},
        }
        untrusted_copy = {
            **comment,
            "id": 601,
            "user": {"login": "Mallory"},
        }
        self.write_state(
            pulls={"1": pull},
            reviews={"1": reviews},
            comments={"1": [prefix_poison, untrusted_copy, comment]},
        )
        pr_merge.require_adjudication(
            self.client(), pull, 1, sha, base_sha, require_status=False
        )

        for author in ({"login": "Mallory"}, None):
            with self.subTest(author=author):
                wrong_author = copy.deepcopy(comment)
                if author is None:
                    wrong_author.pop("user")
                else:
                    wrong_author["user"] = author
                self.write_state(comments={"1": [wrong_author]})
                with self.assertRaisesRegex(
                    pr_merge.GateFailure, "structurally valid"
                ):
                    pr_merge.require_adjudication(
                        self.client(), pull, 1, sha, base_sha, require_status=False
                    )

        pre_source = {
            **comment,
            "created_at": "2026-01-01T00:03:03Z",
            "updated_at": "2026-01-01T00:03:03Z",
        }
        self.write_state(comments={"1": [pre_source]})
        with self.assertRaisesRegex(pr_merge.GateFailure, "strictly later"):
            pr_merge.require_adjudication(
                self.client(), pull, 1, sha, base_sha, require_status=False
            )

        equal_source = {
            **comment,
            "id": 9999,
            "created_at": "2026-01-01T00:03:04Z",
            "updated_at": "2026-01-01T00:03:04Z",
        }
        self.write_state(comments={"1": [equal_source]})
        with self.assertRaisesRegex(pr_merge.GateFailure, "strictly later"):
            pr_merge.require_adjudication(
                self.client(), pull, 1, sha, base_sha, require_status=False
            )

    def test_adjudication_rejects_edited_duplicate_short_and_inexact_records(self) -> None:
        sha, base_sha = "4" * 40, "5" * 40
        pull = pull_row(1, sha, base_sha=base_sha)
        pull["labels"] = [{"name": github_api.ADJUDICATION_LABEL}]

        for index, case in enumerate(
            (
                "edited",
                "duplicate",
                "short",
                "stale-round",
                "missing",
                "bad-fixed",
                "closed-tracked",
            ),
            start=1,
        ):
            with self.subTest(case=case):
                dispositions = None
                round_count = 4
                issues: dict[str, dict] = {}
                if case == "short":
                    round_count = 3
                elif case == "missing":
                    dispositions = []
                elif case == "bad-fixed":
                    dispositions = [
                        {
                            "finding": "code:F1",
                            "outcome": "fixed",
                            "reason": "No evidence is provided.",
                        }
                    ]
                elif case == "closed-tracked":
                    dispositions = [
                        {"finding": "code:F1", "outcome": "tracked", "issue": 9}
                    ]
                    issues = {"9": {**issue_row(9), "state": "closed"}}
                reviews, _statuses, sessions, comment, _payload = (
                    self.adjudication_bundle(
                        self.root,
                        sha,
                        base_sha,
                        round_count=round_count,
                        first_review_id=100 + index * 10,
                        first_round_head_sha=("6" * 40 if case == "stale-round" else None),
                        dispositions=dispositions,
                    )
                )
                self.append_sessions(self.root, sessions)
                comments = [comment]
                if case == "edited":
                    comment = {**comment, "updated_at": "2026-01-01T00:11:00Z"}
                    comments = [comment]
                elif case == "duplicate":
                    comments = [comment, {**comment, "id": 501}]
                self.write_state(
                    pulls={"1": pull},
                    reviews={"1": reviews},
                    comments={"1": comments},
                    issues=issues,
                )
                with self.assertRaises(pr_merge.GateFailure):
                    pr_merge.require_adjudication(
                        self.client(), pull, 1, sha, base_sha, require_status=False
                    )

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
            pr_merge.require_adjudication(
                self.client(), pull, 1, sha, pull["base"]["sha"], require_status=False
            )

    def test_partial_runtime_lock_fails_closed_with_explicit_recovery(self) -> None:
        lock = self.root / "cache" / "locks" / "review-1.lock"
        lock.mkdir(parents=True)
        with self.assertRaisesRegex(
            pr_merge.GateFailure, "remove .* explicitly and retry"
        ):
            with pr_merge.reserve_runtime_lock(lock, "test partial"):
                self.fail("a partial lock must never be adopted")
        self.assertTrue(lock.is_dir())

        lock.rmdir()
        with pr_merge.reserve_runtime_lock(lock, "test live") as held:
            held.require_owned()
            with self.assertRaisesRegex(
                pr_merge.GateFailure, "owner pid .*not proven dead"
            ):
                with pr_merge.reserve_runtime_lock(lock, "test contender"):
                    self.fail("a live lock must exclude a contender")
        self.assertFalse(lock.exists())

        with pr_merge.reserve_runtime_lock(lock, "test replacement") as held:
            (lock / "token").write_text("replacement-owner\n", encoding="utf-8")
            with self.assertRaisesRegex(pr_merge.GateFailure, "no longer owned"):
                held.require_owned()
        self.assertTrue(lock.is_dir())
        self.assertEqual(
            (lock / "token").read_text(encoding="utf-8"),
            "replacement-owner\n",
        )
        shutil.rmtree(lock)


class GuardedMergeTests(FakeGhCase):
    """Group 7: one exact-head guarded gh merge and no direct main push."""

    def prepare_valid_merge(
        self, *, name: str = "repository"
    ) -> tuple[Path, str, str, argparse.Namespace]:
        repository, _remote, base_sha, head_sha = self.make_repository(name=name)
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
            branch_tips={"main": base_sha},
            required_merge_locks=[
                str(self.root / "cache/locks/review-1.lock"),
                str(self.root / "cache/locks/fix-issue-7-test.lock"),
                str(self.root / "cache/locks/ci-1.lock"),
            ],
            calls=[],
            merge_call_count=0,
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
        merge_calls = [
            row["args"]
            for row in calls
            if row["args"][:2] == ["pr", "merge"] and "--help" not in row["args"]
        ]
        self.assertEqual(
            merge_calls,
            [
            [
                "pr",
                "merge",
                "1",
                "--repo",
                "o/r",
                "--merge",
                "--match-head-commit",
                head_sha,
            ]
            ],
        )
        self.assertEqual(self.state()["merge_call_count"], 1)
        self.assertEqual(len(self.state()["merge_locks_observed"]), 3)
        self.assertNotIn("--admin", merge_calls[0])
        self.assertNotIn("--auto", merge_calls[0])
        source = (BIN_DIR / "pr_merge.py").read_text(encoding="utf-8")
        self.assertNotIn('"push", "github"', source)
        self.assertNotIn("--admin", source)

    def test_local_post_merge_failures_warn_and_defer_after_remote_success(self) -> None:
        _repository, _base_sha, _head_sha, args = self.prepare_valid_merge(
            name="merge-local-cleanup-deferred"
        )
        stderr = io.StringIO()
        stdout = io.StringIO()
        with mock.patch.dict(
            os.environ, {"MIPSTARRE_CACHE_ROOT": str(self.root / "cache")}
        ), mock.patch.object(
            pr_merge,
            "fast_forward_base",
            side_effect=pr_merge.GateFailure("dirty local telemetry"),
        ) as refresh, mock.patch.object(
            pr_merge,
            "cleanup_feature",
            side_effect=OSError("worktree cleanup unavailable"),
        ) as cleanup, contextlib.redirect_stderr(stderr), contextlib.redirect_stdout(
            stdout
        ):
            self.assertEqual(pr_merge.run(args), 0)

        refresh.assert_called_once()
        cleanup.assert_called_once()
        self.assertTrue(self.state()["pulls"]["1"]["merged"])
        self.assertIn("local base refresh is deferred", stderr.getvalue())
        self.assertIn("local feature cleanup is deferred", stderr.getvalue())
        self.assertIn("merged GitHub PR #1", stdout.getvalue())

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

    def test_repository_merge_method_preflight_blocks_the_mutation(self) -> None:
        _repository, _base_sha, _head_sha, args = self.prepare_valid_merge(
            name="merge-method-disabled"
        )
        self.write_state(
            repo={"id": 1, "full_name": "o/r", "allow_merge_commit": False}
        )
        with mock.patch.dict(
            os.environ, {"MIPSTARRE_CACHE_ROOT": str(self.root / "cache")}
        ), mock.patch.object(pr_merge, "fast_forward_base"), mock.patch.object(
            pr_merge, "cleanup_feature"
        ):
            with self.assertRaisesRegex(pr_merge.GateFailure, "allow merge commits"):
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
        self.assertFalse((locks / "ci-1.lock").exists())

    def test_merge_mutation_rejects_head_base_and_required_status_races_once(self) -> None:
        cases = {
            "head": {"head_sha": "8" * 40},
            "base": {"base_tip": "9" * 40},
            "status": {
                "status": {
                    "id": 999,
                    "sha": "unused",
                    "context": github_api.REVIEW_CONTEXT,
                    "state": "failure",
                    "description": "injected race",
                    "created_at": "2099-01-01T00:00:00Z",
                }
            },
        }
        for name, race in cases.items():
            with self.subTest(name=name):
                _repository, _base_sha, _head_sha, args = self.prepare_valid_merge(
                    name=f"merge-race-{name}"
                )
                self.write_state(merge_race=race)
                with mock.patch.dict(
                    os.environ,
                    {"MIPSTARRE_CACHE_ROOT": str(self.root / "cache")},
                ), mock.patch.object(pr_merge, "fast_forward_base"), mock.patch.object(
                    pr_merge, "cleanup_feature"
                ):
                    with self.assertRaises((github_api.GitHubError, pr_merge.GateFailure)):
                        pr_merge.run(args)
                self.assertEqual(self.state()["merge_call_count"], 1)
                merge_calls = [
                    call
                    for call in self.state()["calls"]
                    if call["args"][:2] == ["pr", "merge"]
                    and "--help" not in call["args"]
                ]
                self.assertEqual(len(merge_calls), 1)

    def test_ambiguous_merge_success_is_read_back_without_retry(self) -> None:
        _repository, _base_sha, _head_sha, args = self.prepare_valid_merge(
            name="merge-ambiguous-success"
        )
        self.write_state(ambiguous_merge_success_once=True)
        with mock.patch.dict(
            os.environ, {"MIPSTARRE_CACHE_ROOT": str(self.root / "cache")}
        ), mock.patch.object(pr_merge, "fast_forward_base"), mock.patch.object(
            pr_merge, "cleanup_feature"
        ):
            self.assertEqual(pr_merge.run(args), 0)
        self.assertEqual(self.state()["merge_call_count"], 1)
        self.assertTrue(self.state()["pulls"]["1"]["merged"])

    def test_merge_readback_accepts_advanced_base_and_verifies_parent_order(self) -> None:
        _repository, base_sha, head_sha, args = self.prepare_valid_merge(
            name="merge-readback-base-advanced"
        )
        self.write_state(post_merge_base_sha="3" * 40)
        with mock.patch.dict(
            os.environ, {"MIPSTARRE_CACHE_ROOT": str(self.root / "cache")}
        ), mock.patch.object(pr_merge, "fast_forward_base"), mock.patch.object(
            pr_merge, "cleanup_feature"
        ):
            self.assertEqual(pr_merge.run(args), 0)
        commit = self.state()["git_commits"]["2" * 40]
        self.assertEqual(
            [parent["sha"] for parent in commit["parents"]],
            [base_sha, head_sha],
        )
        self.assertEqual(self.state()["pulls"]["1"]["base"]["sha"], "3" * 40)

    def test_nonconforming_merge_commit_is_external_and_never_retried(self) -> None:
        for name, parents in (
            ("one-parent", ["0" * 40]),
            ("reversed", ["1" * 40, "0" * 40]),
            ("wrong-first", ["9" * 40, "1" * 40]),
        ):
            with self.subTest(name=name):
                _repository, base_sha, head_sha, args = self.prepare_valid_merge(
                    name=f"merge-nonconforming-{name}"
                )
                resolved = [
                    base_sha if parent == "0" * 40 else
                    head_sha if parent == "1" * 40 else parent
                    for parent in parents
                ]
                self.write_state(merge_commit_parents=resolved)
                with mock.patch.dict(
                    os.environ,
                    {"MIPSTARRE_CACHE_ROOT": str(self.root / "cache")},
                ), mock.patch.object(
                    pr_merge, "fast_forward_base"
                ), mock.patch.object(pr_merge, "cleanup_feature"):
                    with self.assertRaisesRegex(
                        pr_merge.NonconformingMerge, "external/nonconforming"
                    ):
                        pr_merge.run(args)
                self.assertEqual(self.state()["merge_call_count"], 1)

    def test_post_merge_ref_drift_is_external_and_never_retried(self) -> None:
        _repository, _base_sha, _head_sha, args = self.prepare_valid_merge(
            name="merge-nonconforming-ref"
        )
        self.write_state(post_merge_head_ref="foreign-feature")
        with mock.patch.dict(
            os.environ, {"MIPSTARRE_CACHE_ROOT": str(self.root / "cache")}
        ), mock.patch.object(pr_merge, "fast_forward_base"), mock.patch.object(
            pr_merge, "cleanup_feature"
        ):
            with self.assertRaisesRegex(
                pr_merge.NonconformingMerge, "head/ref/base-ref"
            ):
                pr_merge.run(args)
        self.assertEqual(self.state()["merge_call_count"], 1)

    def test_ambiguous_unmerged_outcome_is_not_retried(self) -> None:
        _repository, _base_sha, _head_sha, args = self.prepare_valid_merge(
            name="merge-ambiguous-absent"
        )
        self.write_state(fail_merge_before_once=True)
        with mock.patch.dict(
            os.environ, {"MIPSTARRE_CACHE_ROOT": str(self.root / "cache")}
        ), mock.patch.object(pr_merge, "fast_forward_base"), mock.patch.object(
            pr_merge, "cleanup_feature"
        ):
            with self.assertRaisesRegex(pr_merge.GateFailure, "not retried"):
                pr_merge.run(args)
        self.assertEqual(self.state()["merge_call_count"], 1)
        self.assertFalse(self.state()["pulls"]["1"]["merged"])

    def test_adjudicated_merge_publishes_exact_success_under_all_locks(self) -> None:
        repository, base_sha, head_sha, args = self.prepare_valid_merge(
            name="merge-adjudicated"
        )
        state = self.state()
        pull = state["pulls"]["1"]
        pull["labels"] = [{"name": github_api.ADJUDICATION_LABEL}]
        reviews, statuses, sessions, comment, payload = self.adjudication_bundle(
            repository,
            head_sha,
            base_sha,
            first_review_id=10,
        )
        self.append_sessions(repository, sessions)
        state["pulls"]["1"] = pull
        state["issues"]["1"] = {
            **pull,
            "pull_request": {"url": pull["html_url"]},
        }
        state["comments"]["1"].append(comment)
        state["reviews"]["1"].extend(reviews)
        state["statuses"][head_sha].extend(statuses)
        state["required_adjudication_locks"] = state["required_merge_locks"]
        self.write_state(**state)
        args.adjudicated = True
        with mock.patch.dict(
            os.environ, {"MIPSTARRE_CACHE_ROOT": str(self.root / "cache")}
        ), mock.patch.object(pr_merge, "fast_forward_base"), mock.patch.object(
            pr_merge, "cleanup_feature"
        ):
            self.assertEqual(pr_merge.run(args), 0)
        final_state = self.state()
        self.assertEqual(final_state["merge_call_count"], 1)
        self.assertEqual(len(final_state["adjudication_locks_observed"]), 3)
        latest = self.client(repository).latest_statuses(head_sha)[
            github_api.REVIEW_CONTEXT.casefold()
        ]
        self.assertEqual(latest["state"], "success")
        self.assertIn(
            f"review={payload['source_review']['review_id']}",
            latest["description"],
        )


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

        hook_sources = [
            (REPO_ROOT / ".githooks/pre-commit").read_text(encoding="utf-8"),
            (REPO_ROOT / ".githooks/pre-push").read_text(encoding="utf-8"),
        ]
        for hook_source in hook_sources:
            self.assertIn(".github/", hook_source)
            self.assertIn("results/telemetry/registry-archive/", hook_source)
            self.assertIn("--no-renames", hook_source)
            self.assertNotIn("--diff-filter=ACMR", hook_source)
        hooks = "".join(hook_sources)
        self.assertIn("scripts.tests.test_github_workflow", hooks)
        self.assertIn("github_api", hooks)
        self.assertIn("refs/remotes/github/main", hooks)
        for name in (
            "worktree-setup",
            "cache-warmer",
            "runtime_lock",
            "warm-worktree",
            "blueprint_lean_sync",
        ):
            self.assertIn(name, hooks)
        ci_source = (REPO_ROOT / "local/bin/ci.sh").read_text(encoding="utf-8")
        self.assertIn("local/bin/runtime_lock.py", ci_source)
        self.assertIn("local/bin/warm-worktree.sh", ci_source)
        self.assertIn("'.github/*'", ci_source)
        self.assertIn("'results/telemetry/registry-archive/*'", ci_source)
        dispatch_source = (REPO_ROOT / "local/bin/dispatch.sh").read_text(
            encoding="utf-8"
        )
        self.assertIn("runtime_lock.py", dispatch_source)
        self.assertIn("release-owned", dispatch_source)
        self.assertNotIn('kill -0 "$owner"', dispatch_source)
        self.assertNotIn('rm -rf "$dir"', dispatch_source)

        self.write_state(failures={"GET ": {"remaining": 1, "message": "HTTP 401"}})
        result = issue_new.main(
            ["--title", "Must fail closed", "--repo-root", str(self.root)]
        )
        self.assertEqual(result, 2)
        self.assertFalse((self.root / "issues").exists())
        self.assertFalse((self.root / "prs").exists())

    def test_archive_and_frozen_precedent_are_unmodified(self) -> None:
        archival_commit = "c8f1999"
        resolved = subprocess.run(
            [
                "git",
                "-C",
                str(REPO_ROOT),
                "rev-parse",
                "--verify",
                f"{archival_commit}^{{commit}}",
            ],
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertEqual(resolved.returncode, 0, resolved.stderr)
        for path in ("results/telemetry/registry-archive", ".github"):
            result = subprocess.run(
                [
                    "git",
                    "-C",
                    str(REPO_ROOT),
                    "diff",
                    "--quiet",
                    archival_commit,
                    "--",
                    path,
                ],
                check=False,
            )
            self.assertEqual(result.returncode, 0, path)
            dirty = subprocess.run(
                [
                    "git",
                    "-C",
                    str(REPO_ROOT),
                    "status",
                    "--porcelain=v1",
                    "--untracked-files=all",
                    "--ignored=matching",
                    "--",
                    path,
                ],
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertEqual(dirty.returncode, 0, dirty.stderr)
            self.assertEqual(dirty.stdout, "", f"dirty or untracked: {path}")


if __name__ == "__main__":
    unittest.main()
