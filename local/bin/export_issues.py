#!/usr/bin/env python3
"""Export the local issue tree in the shape ``gh issue list --json`` produced.

``scripts/audit_stale_issues.py`` is offline-first and GitHub-free: it reads a
JSON file and the working tree, nothing else.  The only GitHub dependency in the
whole stale-audit job was the export step
(``.github/workflows/housekeeping.yml:237-247``)::

    gh issue list --state open --limit 500 --json number,title,body,url,labels

This script is the local replacement for exactly that one command, so the audit
script itself ports unchanged.  Fidelity of the emitted shape is the whole
contract: ``number`` is an int, ``labels`` is a list of objects with a ``name``
key (what ``gh`` emits), and ``url`` stands in for the issue's location.

Two deliberate filters:

* ``issues/standup/`` is excluded.  Standup digests are machine-written from the
  activity feed, and GitHub excluded them from its own searches with
  ``-label:standup`` (housekeeping.yml:85-95) to keep automation from reporting
  on itself.
* machine-written sections of an issue body (``## Initial classification``,
  ``## Activity``, ``## Mathlib scouting report``) are stripped.  The audit flags
  backtick-quoted tokens that do not resolve to a Lean declaration, and those
  sections render label names in backticks — ``formalization``, ``blueprint``,
  ``proof`` all match its identifier regex and none of them is a declaration.
  Exporting them would manufacture flags against text no human wrote or
  maintains.  ``--include-generated`` turns the stripping off.

Usage:
    export_issues.py --output ~/.cache/mipstarre-dev/open-issues.json
    export_issues.py | python3 scripts/audit_stale_issues.py --issues /dev/stdin
    export_issues.py --help
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
try:
    import track
except ModuleNotFoundError as exc:  # pragma: no cover - defensive
    sys.stderr.write(
        "export_issues.py: cannot import local/bin/track.py, which holds the "
        f"issue data layer ({exc}).\n"
    )
    raise SystemExit(2)

from track import LayerError  # noqa: E402


#: Headings written by this layer rather than by a human.
GENERATED_HEADINGS = (
    "## Activity",
    "## Initial classification",
    "## Mathlib scouting report",
)

def strip_generated_sections(body: str) -> str:
    """Drop machine-written ``##`` sections, keeping everything else verbatim."""
    lines = body.splitlines()
    out: list[str] = []
    skipping = False
    for line in lines:
        if line.startswith("## "):
            skipping = any(line.strip() == heading for heading in GENERATED_HEADINGS)
        if not skipping:
            out.append(line)
    return "\n".join(out).rstrip("\n") + "\n"


def issue_url(repo_root: Path, issue: track.Issue, style: str) -> str:
    relative = issue.path.relative_to(repo_root).as_posix()
    if style == "file-uri":
        return issue.path.resolve().as_uri()
    return relative


def export(args: argparse.Namespace) -> int:
    repo_root = args.repo_root.resolve()
    directory = track.issues_dir(repo_root)
    if not directory.is_dir():
        raise LayerError(
            f"no issue tree at {directory}. There is nothing to export; create an "
            "issue with local/bin/issue_new.py first."
        )

    payload: list[dict[str, object]] = []
    for issue in track.iter_issues(repo_root):
        if args.state != "all" and issue.state != args.state:
            continue
        if "standup" in issue.labels and not args.include_standup:
            continue
        body = issue.body if args.include_generated else strip_generated_sections(issue.body)
        # Control characters are stripped even here: the JSON is read back by a
        # separate process and may be pasted into a report.  Fence-breaking and
        # truncation are NOT applied — the audit needs the body's real path and
        # line citations intact, and it never interpolates the text into a
        # prompt.  Use --sanitize-for-prompt when the export feeds an agent.
        if args.sanitize_for_prompt:
            body = track.sanitize(body, track.BODY_LIMIT)
        else:
            body = track.sanitize(body)

        labels: list[object]
        if args.labels_as == "names":
            labels = list(issue.labels)
        else:
            labels = [{"name": name} for name in issue.labels]

        payload.append({
            "number": int(issue.id),
            "title": issue.title,
            "body": body,
            "url": issue_url(repo_root, issue, args.url_style),
            "labels": labels,
        })
        if args.limit and len(payload) >= args.limit:
            break

    rendered = json.dumps(payload, indent=2, ensure_ascii=False) + "\n"
    if args.output:
        track.atomic_write(args.output, rendered)
        sys.stderr.write(f"wrote {len(payload)} issue(s) to {args.output}\n")
    else:
        sys.stdout.write(rendered)
    return 0


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        prog="export_issues.py",
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("--state", choices=("open", "closed", "all"), default="open",
                        help="which issues to export (default: open, matching the "
                             "upstream 'gh issue list --state open')")
    parser.add_argument("--limit", type=int, default=500,
                        help="maximum issues to emit (default: 500, as upstream)")
    parser.add_argument("--labels-as", choices=("objects", "names"), default="objects",
                        help="'objects' reproduces gh's [{name: ...}] shape (default)")
    parser.add_argument("--url-style", choices=("path", "file-uri"), default="path",
                        help="'path' emits the repo-relative file path (default)")
    parser.add_argument("--include-standup", action="store_true",
                        help="include machine-written standup digests")
    parser.add_argument("--include-generated", action="store_true",
                        help="keep machine-written body sections in the export")
    parser.add_argument("--sanitize-for-prompt", action="store_true",
                        help="also break ``` fences and truncate bodies; use when "
                             "the export is interpolated into an agent prompt")
    parser.add_argument("--output", type=Path, help="write here instead of stdout")
    parser.add_argument("--repo-root", type=Path, default=track.default_repo_root(),
                        help="repository root (default: two levels above this script)")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        return export(args)
    except LayerError as exc:
        sys.stderr.write(f"export_issues.py: {exc}\n")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
