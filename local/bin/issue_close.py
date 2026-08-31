#!/usr/bin/env python3
"""Close a GitHub issue with an explicit state reason."""

from __future__ import annotations

import argparse
import os
import sys
from pathlib import Path
from typing import Sequence

sys.path.insert(0, str(Path(__file__).resolve().parent))
from github_api import (  # noqa: E402
    GitHub,
    GitHubError,
    normalize_number,
    stable_digest,
    stable_marker,
)


REASONS = {
    "completed": "completed",
    "not-planned": "not_planned",
    "not_planned": "not_planned",
}


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("number", help="GitHub issue number")
    parser.add_argument("--reason", required=True, choices=tuple(REASONS))
    parser.add_argument("--comment", help="explanatory comment posted before closing")
    parser.add_argument("--repo-root", type=Path)
    return parser


def run(args: argparse.Namespace) -> int:
    number = normalize_number(args.number, kind="issue number")
    root = args.repo_root or Path(os.environ.get("MIPSTARRE_REPO_ROOT", Path.cwd()))
    client = GitHub(repo_root=root.resolve())
    client.probe_authentication()
    client.get_issue(number)
    if args.comment:
        marker = stable_marker(
            "issue-close-comment",
            issue=number,
            id=stable_digest({"reason": args.reason, "comment": args.comment}),
        )
        client.comment_once(number, f"{args.comment.rstrip()}\n\n{marker}\n", marker)
    expected_reason = REASONS[args.reason]

    def lookup() -> dict | None:
        issue = client.get_issue(number)
        if (
            str(issue.get("state") or "").casefold() == "closed"
            and str(issue.get("state_reason") or "").casefold() == expected_reason
        ):
            return issue
        return None

    def mutate() -> dict:
        result = client.api(
            f"/repos/{client.repo}/issues/{number}",
            method="PATCH",
            data={"state": "closed", "state_reason": expected_reason},
            retry=False,
        )
        if not isinstance(result, dict):
            raise GitHubError("issue close returned a non-object response")
        return result

    client._idempotent_mutation(lookup=lookup, mutate=mutate)
    payload = lookup()
    if payload is None:
        raise GitHubError("GitHub did not retain the requested close state and reason")
    url = payload.get("html_url") or payload.get("url")
    print(f"closed GitHub issue #{number} as {args.reason}: {url}")
    return 0


def main(argv: Sequence[str] | None = None) -> int:
    try:
        return run(build_parser().parse_args(argv))
    except (GitHubError, OSError, ValueError) as exc:
        sys.stderr.write(f"issue_close.py: {exc}\n")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
