#!/usr/bin/env python3
"""Merge a GitHub pull request after all exact-head local gates pass."""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Sequence

sys.path.insert(0, str(Path(__file__).resolve().parent))
from github_api import (  # noqa: E402
    ADJUDICATION_LABEL,
    CANONICAL_CI_CONTEXTS,
    REVIEW_CONTEXT,
    GitHub,
    GitHubError,
    fix_iteration_count,
    normalize_number,
    normalize_sha,
    pull_head,
)


DEFAULT_FIX_CAP = 5
UNRESOLVED_RE = re.compile(r"^\s*[-*]\s*\[ \]\s+F\d+", re.MULTILINE)
DISPOSITION_RE = re.compile(r"^Disposition:\s*\S.*$", re.MULTILINE)


class GateFailure(RuntimeError):
    """A merge-gate refusal with an operator-facing explanation."""


def git(root: Path, *arguments: str, check: bool = True) -> str:
    result = subprocess.run(
        ["git", "-C", str(root), *arguments],
        text=True,
        capture_output=True,
        check=False,
    )
    if check and result.returncode != 0:
        raise GateFailure(
            result.stderr.strip() or f"git {' '.join(arguments)} failed"
        )
    return result.stdout.strip()


def primary_root(value: Path | None) -> Path:
    root = (value or Path.cwd()).resolve()
    common = git(root, "rev-parse", "--path-format=absolute", "--git-common-dir")
    common_path = Path(common)
    return common_path.parent if common_path.name == ".git" else root


def branch_worktree(root: Path, branch: str) -> Path | None:
    current: Path | None = None
    for line in git(root, "worktree", "list", "--porcelain").splitlines():
        if line.startswith("worktree "):
            current = Path(line.removeprefix("worktree "))
        elif line == f"branch refs/heads/{branch}" and current is not None:
            return current
    return None


def exact_local_head(root: Path, branch: str) -> tuple[str, Path]:
    if any(ch in branch for ch in "[]~^:?*\\ \t\r\n"):
        raise GateFailure(f"unsafe GitHub head branch {branch!r}")
    worktree = branch_worktree(root, branch)
    if worktree is None or not worktree.is_dir():
        raise GateFailure(f"no local worktree is registered for PR branch {branch!r}")
    symbolic = git(worktree, "symbolic-ref", "--quiet", "--short", "HEAD")
    if symbolic != branch:
        raise GateFailure(
            f"worktree {worktree} is on {symbolic!r}, expected {branch!r}"
        )
    return normalize_sha(git(worktree, "rev-parse", "HEAD")), worktree


def require_open_mergeable(pull: dict[str, Any], number: int) -> tuple[str, str, str]:
    if str(pull.get("state") or "").casefold() != "open":
        raise GateFailure(f"PR #{number} is not open")
    if bool(pull.get("draft")):
        raise GateFailure(f"PR #{number} is a draft")
    if pull.get("mergeable") is not True:
        state = pull.get("mergeable_state") or "unknown"
        raise GateFailure(f"PR #{number} is not proven mergeable (state={state})")
    return pull_head(pull)


def require_statuses(client: GitHub, sha: str) -> dict[str, dict[str, Any]]:
    latest = client.latest_statuses(sha)
    failures: list[str] = []
    for context in CANONICAL_CI_CONTEXTS:
        state = str(
            (latest.get(context.casefold()) or {}).get("state") or "missing"
        ).casefold()
        if state != "success":
            failures.append(f"{context}={state}")
    if failures:
        raise GateFailure("exact-head CI gate failed: " + ", ".join(failures))
    return latest


def row_order(row: dict[str, Any]) -> tuple[str, int]:
    return (
        str(row.get("submitted_at") or row.get("created_at") or ""),
        int(row.get("id") or 0),
    )


def require_review(client: GitHub, number: int, sha: str) -> None:
    latest = client.latest_statuses(sha)
    summary = latest.get(REVIEW_CONTEXT.casefold()) or {}
    if str(summary.get("state") or "").casefold() != "success":
        raise GateFailure(
            f"{REVIEW_CONTEXT} is not successful on exact head {sha}"
        )
    try:
        ledger = client.review_ledger(number, sha)
    except GitHubError as exc:
        raise GateFailure(f"no valid exact-head review ledger: {exc}") from exc
    body = str(ledger.get("body") or "")
    if str(ledger.get("state") or "").upper() != "COMMENTED":
        raise GateFailure("the clean exact-head review ledger is not a COMMENT review")
    if UNRESOLVED_RE.search(body):
        raise GateFailure("the latest exact-head review ledger has unresolved findings")
    ledger_order = row_order(ledger)
    for review in client.reviews(number):
        if str(review.get("commit_id") or "").lower() != sha:
            continue
        if str(review.get("state") or "").upper() != "CHANGES_REQUESTED":
            continue
        if row_order(review) > ledger_order:
            raise GateFailure("a later exact-head CHANGES_REQUESTED review is unresolved")


def require_adjudication(
    client: GitHub, pull: dict[str, Any], number: int, sha: str
) -> None:
    labels = {
        str(item.get("name") if isinstance(item, dict) else item)
        for item in (pull.get("labels") or [])
    }
    if ADJUDICATION_LABEL not in labels:
        raise GateFailure(f"adjudicated merge requires label {ADJUDICATION_LABEL!r}")
    marker = f"<!-- mipstarre:adjudication pr={number} head={sha} -->"
    matches: list[dict[str, Any]] = []
    for row in client.comments(number):
        body = str(row.get("body") or "")
        if body.startswith("ADJUDICATION") and marker in body:
            matches.append(row)
    if not matches:
        raise GateFailure("no current-head ADJUDICATION comment with a stable marker")
    matches.sort(key=row_order, reverse=True)
    body = str(matches[0].get("body") or "")
    if body.count(marker) != 1 or not DISPOSITION_RE.search(body):
        raise GateFailure(
            "the adjudication comment must contain one exact-head marker and a "
            "nonempty 'Disposition:' line"
        )


def require_no_live_fix(cache: Path, branch: str) -> None:
    lock = cache / "locks" / f"fix-{branch.replace('/', '-')}.lock"
    if not lock.is_dir():
        return
    try:
        pid = int((lock / "pid").read_text(encoding="utf-8").strip())
    except (OSError, ValueError):
        return
    try:
        os.kill(pid, 0)
    except OSError:
        return
    raise GateFailure(f"live auto-fix lock {lock} is held by pid {pid}")


def require_merge_capability(client: GitHub) -> None:
    result = client.run(["pr", "merge", "--help"], retry=False)
    if "--match-head-commit" not in result.stdout:
        raise GateFailure(
            "installed gh lacks 'pr merge --match-head-commit'; upgrade before merging"
        )


def recheck_head(
    client: GitHub, number: int, expected: str, root: Path, branch: str
) -> dict[str, Any]:
    pull = client.get_pull(number)
    _, _, remote = pull_head(pull)
    local, _ = exact_local_head(root, branch)
    if remote != expected or local != expected:
        raise GateFailure(
            f"head moved during gate evaluation (expected={expected}, "
            f"remote={remote}, local={local})"
        )
    return pull


def fast_forward_base(root: Path, base: str) -> None:
    git(
        root,
        "fetch",
        "--no-tags",
        "github",
        f"refs/heads/{base}:refs/remotes/github/{base}",
    )
    worktree = branch_worktree(root, base)
    if worktree is None:
        raise GateFailure(
            f"GitHub merged the PR, but no local checkout of base branch {base!r} exists"
        )
    if git(worktree, "status", "--porcelain"):
        raise GateFailure(
            f"GitHub merged the PR, but base worktree {worktree} is dirty; "
            "it was not advanced"
        )
    git(worktree, "merge", "--ff-only", f"refs/remotes/github/{base}")


def cleanup_feature(root: Path, branch: str, worktree: Path, merge_sha: str) -> None:
    if git(worktree, "status", "--porcelain"):
        raise GateFailure(
            f"PR merged, but feature worktree {worktree} is dirty; cleanup was skipped"
        )
    ancestor = subprocess.run(
        ["git", "-C", str(root), "merge-base", "--is-ancestor", branch, merge_sha],
        check=False,
    )
    if ancestor.returncode != 0:
        raise GateFailure(
            f"PR merged, but local branch {branch!r} is not contained in {merge_sha}; "
            "cleanup was skipped"
        )
    git(root, "worktree", "remove", str(worktree))
    git(root, "branch", "-d", branch)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("number", help="GitHub pull-request number")
    parser.add_argument("--adjudicated", action="store_true")
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--fix-cap", type=int, default=None)
    parser.add_argument("--repo-root", type=Path)
    return parser


def run(args: argparse.Namespace) -> int:
    number = normalize_number(args.number, kind="PR number")
    root = primary_root(args.repo_root)
    cache = Path(
        os.environ.get("MIPSTARRE_CACHE_ROOT", Path.home() / ".cache/mipstarre-dev")
    )
    cap = args.fix_cap
    if cap is None:
        cap = int(os.environ.get("MIPSTARRE_FIX_CAP", str(DEFAULT_FIX_CAP)))
    if cap < 0:
        raise GateFailure("fix cap must be nonnegative")

    client = GitHub(repo_root=root)
    client.probe_authentication()
    pull = client.get_pull(number)
    branch, base, sha = require_open_mergeable(pull, number)
    local_sha, feature_worktree = exact_local_head(root, branch)
    if local_sha != sha:
        raise GateFailure(f"local branch tip {local_sha} does not equal GitHub head {sha}")

    require_statuses(client, sha)
    try:
        client.ci_manifest(number, sha)
        client.review_ledger(number, sha)
    except GitHubError as exc:
        raise GateFailure(str(exc)) from exc
    if args.adjudicated:
        require_adjudication(client, pull, number, sha)
    else:
        require_review(client, number, sha)

    require_no_live_fix(cache, branch)
    commits = client.pull_commits(number)
    iterations = fix_iteration_count(commits)
    if iterations > cap:
        raise GateFailure(
            f"fix iteration count {iterations} exceeds configured cap {cap}"
        )
    require_merge_capability(client)
    pull = recheck_head(client, number, sha, root, branch)
    require_open_mergeable(pull, number)

    command = [
        "pr",
        "merge",
        str(number),
        "--repo",
        client.repo,
        "--merge",
        "--match-head-commit",
        sha,
    ]
    if args.dry_run:
        print("gate passed; would run: gh " + " ".join(command))
        return 0

    client.run(command, retry=False)
    merged = client.get_pull(number)
    if not merged.get("merged"):
        raise GateFailure("gh returned success but GitHub does not report the PR merged")
    merge_sha = normalize_sha(
        str(merged.get("merge_commit_sha") or ""), kind="merge commit SHA"
    )
    fast_forward_base(root, base)
    cleanup_feature(root, branch, feature_worktree, merge_sha)
    print(f"merged GitHub PR #{number} at {merge_sha}")
    return 0


def main(argv: Sequence[str] | None = None) -> int:
    try:
        return run(build_parser().parse_args(argv))
    except (GateFailure, GitHubError, OSError, ValueError) as exc:
        sys.stderr.write(f"pr_merge.py: merge refused: {exc}\n")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
