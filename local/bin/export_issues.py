#!/usr/bin/env python3
"""Export authoritative GitHub issues for report-only consumers."""

from __future__ import annotations

import argparse
import json
import os
import sys
import tempfile
from pathlib import Path
from typing import Any, Sequence

sys.path.insert(0, str(Path(__file__).resolve().parent))
from github_api import GitHub, GitHubError  # noqa: E402


def _atomic_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    handle, temp_name = tempfile.mkstemp(
        dir=path.parent, prefix=path.name + ".", suffix=".tmp"
    )
    try:
        with os.fdopen(handle, "w", encoding="utf-8") as stream:
            stream.write(text)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temp_name, path)
    except BaseException:
        try:
            os.unlink(temp_name)
        except OSError:
            pass
        raise


def _sanitize(text: str, limit: int = 5000) -> str:
    clean = "".join(ch for ch in text if ch in "\n\t" or ord(ch) >= 32)
    return clean.replace("```", "` ` `")[:limit]


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--state", choices=("open", "closed", "all"), default="open")
    parser.add_argument("--limit", type=int, default=500)
    parser.add_argument("--labels-as", choices=("objects", "names"), default="objects")
    parser.add_argument("--sanitize-for-prompt", action="store_true")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--repo-root", type=Path)
    return parser


def run(args: argparse.Namespace) -> int:
    if args.limit < 1:
        raise GitHubError("--limit must be positive")
    root = args.repo_root or Path(os.environ.get("MIPSTARRE_REPO_ROOT", Path.cwd()))
    client = GitHub(repo_root=root.resolve())
    client.probe_authentication()
    rows = client.paginate(f"/repos/{client.repo}/issues?state={args.state}")
    payload: list[dict[str, Any]] = []
    for issue in rows:
        if "pull_request" in issue:
            continue
        labels = issue.get("labels") or []
        if args.labels_as == "names":
            labels = [
                str(label.get("name") if isinstance(label, dict) else label)
                for label in labels
            ]
        body = str(issue.get("body") or "")
        if args.sanitize_for_prompt:
            body = _sanitize(body)
        payload.append(
            {
                "number": issue.get("number"),
                "title": issue.get("title"),
                "body": body,
                "url": issue.get("html_url") or issue.get("url"),
                "labels": labels,
            }
        )
        if len(payload) >= args.limit:
            break
    rendered = json.dumps(payload, indent=2, ensure_ascii=False) + "\n"
    if args.output:
        _atomic_text(args.output, rendered)
        print(f"wrote {len(payload)} GitHub issue(s) to {args.output}", file=sys.stderr)
    else:
        sys.stdout.write(rendered)
    return 0


def main(argv: Sequence[str] | None = None) -> int:
    try:
        return run(build_parser().parse_args(argv))
    except (GitHubError, OSError, ValueError) as exc:
        sys.stderr.write(f"export_issues.py: {exc}\n")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
