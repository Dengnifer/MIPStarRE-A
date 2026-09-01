#!/usr/bin/env python3
"""Push one feature ref and create or update its GitHub pull request."""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import time
import urllib.parse
from pathlib import Path
from typing import Any, Sequence

sys.path.insert(0, str(Path(__file__).resolve().parent))
from github_api import (  # noqa: E402
    GitHub,
    GitHubError,
    create_marker,
    normalize_number,
)


DEFAULT_BODY = """### Motivation

- Explain why this change is needed and cite the GitHub issue and source.

### Description

- State precisely what changed.

### Testing

- List the checks that were run.
"""
FORBIDDEN_BRANCH = re.compile(r"[][~^:?*\\\s]")


def _root(value: Path | None) -> Path:
    if value:
        return value.resolve()
    override = os.environ.get("MIPSTARRE_REPO_ROOT")
    return Path(override).resolve() if override else Path.cwd().resolve()


def _git(root: Path, *arguments: str, check: bool = True) -> str:
    result = subprocess.run(
        ["git", "-C", str(root), *arguments],
        text=True,
        capture_output=True,
        check=False,
    )
    if check and result.returncode != 0:
        raise GitHubError(result.stderr.strip() or f"git {' '.join(arguments)} failed")
    return result.stdout.strip()


def _base_ref(root: Path, base: str) -> str:
    candidate = f"refs/remotes/github/{base}"
    if _git(root, "rev-parse", "--verify", "--quiet", f"{candidate}^{{commit}}", check=False):
        return candidate
    raise GitHubError(
        f"fetched GitHub base {candidate!r} does not resolve locally; fetch it first"
    )


def _open_pulls(client: GitHub, branch: str) -> list[dict[str, Any]]:
    head = urllib.parse.quote(f"{client.owner}:{branch}", safe=":")
    return client.paginate(f"/repos/{client.repo}/pulls?state=open&head={head}")


def _parse_created_pull(client: GitHub, output: str) -> dict[str, Any]:
    match = re.search(r"https://github\.com/[^/]+/[^/]+/pull/(\d+)", output)
    if not match:
        raise GitHubError("gh pr create succeeded but returned no recognizable PR URL")
    return client.get_pull(int(match.group(1)))


def _create_pull(
    client: GitHub,
    branch: str,
    base: str,
    title: str,
    body: str,
) -> tuple[dict[str, Any], bool]:
    def exact(row: dict[str, Any]) -> dict[str, Any] | None:
        number = row.get("number")
        if not isinstance(number, int):
            raise GitHubError("adopted PR lacks a numeric GitHub number")
        pull = client.get_pull(number)
        head = pull.get("head") if isinstance(pull.get("head"), dict) else {}
        target = pull.get("base") if isinstance(pull.get("base"), dict) else {}
        if str(head.get("ref") or "") != branch or str(target.get("ref") or "") != base:
            raise GitHubError("adopted PR has a different head or base branch")
        if str(pull.get("title") or "") != title or str(pull.get("body") or "") != body:
            return None
        return pull

    existing = _open_pulls(client, branch)
    if len(existing) > 1:
        raise GitHubError(f"more than one open PR has head branch {branch!r}")
    if existing:
        number = int(existing[0]["number"])
        found = exact(existing[0])
        if found is not None:
            return found, True

        def lookup() -> dict[str, Any] | None:
            return exact({"number": number})

        def mutate() -> dict[str, Any]:
            payload = client.api(
                f"/repos/{client.repo}/pulls/{number}",
                method="PATCH",
                data={"title": title, "body": body, "base": base},
                retry=False,
            )
            if not isinstance(payload, dict):
                raise GitHubError("PR update returned a non-object response")
            return payload

        client._idempotent_mutation(lookup=lookup, mutate=mutate)
        updated = lookup()
        if updated is None:
            raise GitHubError("GitHub did not retain the requested PR title/body/base")
        return updated, True

    arguments = [
        "pr",
        "create",
        "--repo",
        client.repo,
        "--head",
        branch,
        "--base",
        base,
        "--title",
        title,
        "--body",
        body,
    ]
    try:
        result = client.run(arguments, retry=False)
        created = exact(_parse_created_pull(client, result.stdout))
        if created is None:
            raise GitHubError(
                "created PR does not retain its marker-bound title, body, head, and base"
            )
        return created, False
    except GitHubError as exc:
        if not exc.transient:
            raise
        for attempt in range(client.retries + 1):
            existing = _open_pulls(client, branch)
            if len(existing) == 1:
                adopted = exact(existing[0])
                if adopted is None:
                    raise GitHubError(
                        "ambiguous PR create found the branch but its marker-bound "
                        "title or body does not match"
                    )
                return adopted, True
            if len(existing) > 1:
                raise GitHubError(
                    f"more than one open PR has head branch {branch!r}"
                )
            if attempt < client.retries:
                time.sleep(client.retry_delay * (2**attempt))
        raise GitHubError(
            "PR creation outcome is ambiguous after authoritative read-back; "
            "refusing to create a second PR",
            status=exc.status,
            transient=True,
        ) from exc


def _split(values: Sequence[str]) -> list[str]:
    return [item.strip() for value in values for item in value.split(",") if item.strip()]


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--branch", required=True)
    parser.add_argument("--base", default="main")
    parser.add_argument("--title", required=True)
    body = parser.add_mutually_exclusive_group()
    body.add_argument("--body")
    body.add_argument("--body-file", type=Path)
    parser.add_argument("--label", "--labels", action="append", default=[])
    parser.add_argument(
        "--issue",
        "--closing-issue",
        dest="issue",
        help="GitHub issue number closed by the PR footer",
    )
    parser.add_argument("--repo-root", type=Path)
    return parser


def run(args: argparse.Namespace) -> int:
    root = _root(args.repo_root)
    branch = args.branch.strip()
    base = args.base.strip()
    title = args.title.strip()
    if not branch or FORBIDDEN_BRANCH.search(branch):
        raise GitHubError(f"unsafe branch name {branch!r}")
    if branch == base:
        raise GitHubError("feature branch and base branch must differ")
    _git(root, "check-ref-format", "--branch", branch)
    branch_ref = f"refs/heads/{branch}"
    if not _git(root, "rev-parse", "--verify", "--quiet", f"{branch_ref}^{{commit}}", check=False):
        raise GitHubError(f"local branch {branch!r} does not exist")
    base_ref = _base_ref(root, base)
    ahead = int(_git(root, "rev-list", "--count", f"{base_ref}..{branch_ref}"))
    if ahead == 0:
        raise GitHubError(
            f"branch {branch!r} has no commits ahead of {base!r}; refusing a placeholder PR"
        )

    issue = normalize_number(args.issue, kind="closing issue number") if args.issue else None
    source_body = (
        args.body_file.read_text(encoding="utf-8")
        if args.body_file
        else (args.body if args.body is not None else DEFAULT_BODY)
    )
    if issue is not None:
        source_body = source_body.rstrip() + f"\n\n---\nCloses #{issue}\n"
    labels = _split(args.label)

    client = GitHub(repo_root=root)
    client.probe_authentication()
    labels = client.validate_labels(labels)
    if issue is not None:
        client.get_issue(issue)
    marker = create_marker(
        "pr",
        {
            "repository": client.repo,
            "branch": branch,
            "base": base,
            "title": title,
            "body": source_body,
            "labels": sorted(labels),
            "issue": issue,
        },
    )
    full_body = source_body.rstrip() + "\n\n" + marker + "\n"

    # Publish exactly one explicit feature ref. Never push all refs or main.
    _git(root, "push", "github", f"{branch_ref}:{branch_ref}")
    pull, adopted = _create_pull(client, branch, base, title, full_body)
    number = int(pull["number"])
    if labels:
        authoritative = client.replace_labels_once(number, labels)
        adopted_labels = {
            str(row.get("name") or "")
            for row in authoritative.get("labels", [])
            if isinstance(row, dict)
        }
        if adopted_labels != set(labels):
            raise GitHubError("GitHub did not retain the requested PR labels exactly")
    action = "adopted/updated" if adopted else "created"
    url = pull.get("html_url") or pull.get("url")
    print(f"{action} GitHub PR #{number}: {url}")
    return 0


def main(argv: Sequence[str] | None = None) -> int:
    try:
        return run(build_parser().parse_args(argv))
    except (GitHubError, OSError, ValueError) as exc:
        sys.stderr.write(f"pr_open.py: {exc}\n")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
