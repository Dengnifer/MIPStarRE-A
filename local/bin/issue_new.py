#!/usr/bin/env python3
"""Create or recover a GitHub issue without a local registry."""

from __future__ import annotations

import argparse
import os
import re
import sys
import time
from pathlib import Path
from typing import Any, Sequence

sys.path.insert(0, str(Path(__file__).resolve().parent))
from github_api import (  # noqa: E402
    GitHub,
    GitHubError,
    create_marker,
    normalize_number,
)


TEMPLATES = {
    "formalization": """### Precise mathematical statement

### Mathematical source

- Paper: `references/<paper-mirror>/<section>.tex:NNN`, label `thm:...`.
- Blueprint: `blueprint/src/chapter/<chapter>.tex:NN`, label `thm:...`.

### Target Lean declaration

### Mathematical dependencies

### Proof plan

### Statement integrity
""",
    "bug": """### File(s) affected

### Description

### Mathematical source, if relevant

### Expected behavior

### Lean toolchain
""",
    "tracking": """### Mathematical area

### Mathematical objective

### Sub-issues to attach

### Mathematical notes
""",
}


def _repo_root(value: Path | None) -> Path:
    if value is not None:
        return value.resolve()
    override = os.environ.get("MIPSTARRE_REPO_ROOT")
    return Path(override).resolve() if override else Path.cwd().resolve()


def _split(values: Sequence[str]) -> list[str]:
    return [item.strip() for value in values for item in value.split(",") if item.strip()]


def _find_by_marker(
    client: GitHub,
    marker: str,
    *,
    title: str,
    body: str,
) -> dict[str, Any] | None:
    matches = [
        row
        for row in client.paginate(f"/repos/{client.repo}/issues?state=all")
        if "pull_request" not in row and marker in str(row.get("body") or "")
    ]
    if len(matches) > 1:
        numbers = ", ".join(f"#{row.get('number')}" for row in matches)
        raise GitHubError(f"issue create marker is not unique; found {numbers}")
    if not matches:
        return None
    return _validate_issue(client, matches[0], marker=marker, title=title, body=body)


def _validate_issue(
    client: GitHub,
    row: dict[str, Any],
    *,
    marker: str,
    title: str,
    body: str,
) -> dict[str, Any]:
    """Read back and validate one marker-bound issue."""
    number = row.get("number")
    if not isinstance(number, int):
        raise GitHubError("adopted issue lacks a numeric GitHub number")
    issue = client.get_issue(number)
    adopted_body = str(issue.get("body") or "")
    if adopted_body.count(marker) != 1 or adopted_body != body:
        raise GitHubError(
            "issue marker collision: authoritative body differs from the request"
        )
    if str(issue.get("title") or "") != title:
        raise GitHubError(
            "issue marker collision: authoritative title differs from the request"
        )
    return issue


def _parse_created_issue(client: GitHub, output: str) -> dict[str, Any]:
    match = re.search(r"https://github\.com/[^/]+/[^/]+/issues/(\d+)", output)
    if not match:
        raise GitHubError(
            "gh issue create succeeded but returned no recognizable issue URL"
        )
    return client.get_issue(int(match.group(1)))


def _create_or_recover(
    client: GitHub,
    *,
    title: str,
    body: str,
    labels: Sequence[str],
    assignees: Sequence[str],
    marker: str,
) -> tuple[dict[str, Any], bool]:
    existing = _find_by_marker(client, marker, title=title, body=body)
    if existing is not None:
        return existing, True

    arguments = [
        "issue",
        "create",
        "--repo",
        client.repo,
        "--title",
        title,
        "--body",
        body,
    ]
    for label in labels:
        arguments.extend(["--label", label])
    for assignee in assignees:
        arguments.extend(["--assignee", assignee])

    last: GitHubError | None = None
    for attempt in range(client.retries + 1):
        try:
            result = client.run(arguments, retry=False)
            created = _parse_created_issue(client, result.stdout)
            return (
                _validate_issue(
                    client,
                    created,
                    marker=marker,
                    title=title,
                    body=body,
                ),
                False,
            )
        except GitHubError as exc:
            last = exc
            if not exc.transient:
                raise
            existing = _find_by_marker(client, marker, title=title, body=body)
            if existing is not None:
                return existing, True
            if attempt >= client.retries:
                break
            time.sleep(client.retry_delay * (2**attempt))
    raise last or GitHubError("issue creation failed")


def _attach_parent(client: GitHub, parent: int, child: dict[str, Any]) -> None:
    child_id = child.get("id")
    child_number = child.get("number")
    if not isinstance(child_id, int) or not isinstance(child_number, int):
        raise GitHubError(
            "created issue response lacks numeric id/number for sub-issue attachment"
        )
    client.get_issue(parent)

    def lookup() -> dict[str, Any] | None:
        rows = client.paginate(f"/repos/{client.repo}/issues/{parent}/sub_issues")
        return next(
            (
                row
                for row in rows
                if row.get("id") == child_id or row.get("number") == child_number
            ),
            None,
        )

    def mutate() -> dict[str, Any]:
        payload = client.api(
            f"/repos/{client.repo}/issues/{parent}/sub_issues",
            method="POST",
            data={"sub_issue_id": child_id},
            retry=False,
        )
        if not isinstance(payload, dict):
            raise GitHubError("sub-issue attachment returned a non-object response")
        return payload

    attached = client._idempotent_mutation(lookup=lookup, mutate=mutate)
    if attached.get("id") != child_id or attached.get("number") != child_number:
        raise GitHubError("sub-issue attachment returned a different child issue")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--title", required=True)
    body = parser.add_mutually_exclusive_group()
    body.add_argument("--body")
    body.add_argument("--body-file", type=Path)
    parser.add_argument("--template", choices=tuple(TEMPLATES))
    parser.add_argument("--label", "--labels", action="append", default=[])
    parser.add_argument("--assignee", "--assignees", action="append", default=[])
    parser.add_argument("--parent", help="GitHub parent issue number")
    parser.add_argument("--repo-root", type=Path)
    return parser


def run(args: argparse.Namespace) -> int:
    title = args.title.strip()
    if not title:
        raise GitHubError("--title must not be empty")
    if "[" in title or "]" in title:
        raise GitHubError("issue titles must be bracket-free")
    if args.body_file:
        source_body = args.body_file.read_text(encoding="utf-8")
    elif args.body is not None:
        source_body = args.body
    elif args.template:
        source_body = TEMPLATES[args.template]
    else:
        source_body = ""
    labels = _split(args.label)
    assignees = _split(args.assignee)
    parent = (
        normalize_number(args.parent, kind="parent issue number")
        if args.parent
        else None
    )

    client = GitHub(repo_root=_repo_root(args.repo_root))
    client.probe_authentication()
    labels = client.validate_labels(labels)
    marker_payload = {
        "repository": client.repo,
        "title": title,
        "body": source_body,
        "labels": sorted(labels),
        "assignees": sorted(assignees),
        "parent": parent,
    }
    marker = create_marker("issue", marker_payload)
    body = source_body.rstrip() + ("\n\n" if source_body.strip() else "") + marker + "\n"
    issue, adopted = _create_or_recover(
        client,
        title=title,
        body=body,
        labels=labels,
        assignees=assignees,
        marker=marker,
    )
    if parent is not None:
        _attach_parent(client, parent, issue)
    number = issue.get("number")
    url = issue.get("html_url") or issue.get("url")
    action = "adopted" if adopted else "created"
    print(f"{action} GitHub issue #{number}: {url}")
    return 0


def main(argv: Sequence[str] | None = None) -> int:
    try:
        return run(build_parser().parse_args(argv))
    except (GitHubError, OSError, ValueError) as exc:
        sys.stderr.write(f"issue_new.py: {exc}\n")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
