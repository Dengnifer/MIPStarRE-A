#!/usr/bin/env python3
"""Close an issue in the local tree and run the tracking bookkeeping.

Replaces ``gh issue close --reason ...`` plus the ``issues: [closed]`` half of
the ``track`` job in ``.github/workflows/issue-automation.yml`` (:334-338), which
fired only for ``state_reason == 'completed'``.

The distinction matters more locally than it did upstream.  GitHub's sub-issue
progress counted every closed child regardless of reason
(issue-automation.yml:392-396); the local counter in ``track.py`` counts only
children that are closed *and* completed, so an issue closed as ``not-planned``
withdraws from the denominator's numerator rather than silently advancing a
tracking parent toward its "ready to close" note.  Accordingly this script
writes ``state_reason`` on every close and invokes ``track.py`` only for
``completed``.

Usage:
    issue_close.py 0042 --reason completed
    issue_close.py 0042 --reason not-planned --note "superseded by #0051"
    issue_close.py --help
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
try:
    import track
except ModuleNotFoundError as exc:  # pragma: no cover - defensive
    sys.stderr.write(
        "issue_close.py: cannot import local/bin/track.py, which holds the issue "
        f"data layer ({exc}).\n"
    )
    raise SystemExit(2)

from track import LayerError  # noqa: E402


REASONS = ("completed", "not-planned")


def close_issue(
    repo_root: Path,
    issue_id: str,
    reason: str,
    *,
    note: str | None,
    force: bool,
    dry_run: bool,
    run_track: bool = True,
) -> int:
    """Set ``state``/``state_reason``, append one activity note, then track.

    Callable from ``pr_merge.py`` with ``run_track=False`` so the caller can
    order the tracking calls itself; see the double-fire note there.
    """
    with track.issue_lock(issue_id):
        issue = track.load_issue(repo_root, issue_id)
        if issue.state == "closed" and not force:
            sys.stderr.write(
                f"#{issue_id} is already closed "
                f"(state_reason: {issue.state_reason}); nothing to do. "
                "Pass --force to rewrite the reason.\n"
            )
            return 0

        outstanding = [
            child for child in issue.children
            if (loaded := track.try_load_issue(repo_root, child)) is not None
            and loaded.state == "open"
        ]
        if outstanding:
            sys.stderr.write(
                f"warning: #{issue_id} still has open children "
                f"({', '.join('#' + c for c in outstanding)}); closing the parent "
                "does not close them.\n"
            )

        issue.meta["state"] = "closed"
        issue.meta["state_reason"] = reason
        if dry_run:
            sys.stdout.write(
                f"[dry-run] would close #{issue_id} as {reason}\n"
            )
        else:
            issue.save()
            sys.stdout.write(
                f"{issue.path.name}: state=closed state_reason={reason}\n"
            )

        marker = f"closed as {reason}"
        detail = f" — {track.sanitize(note, track.BODY_LIMIT)}" if note else ""
        track.append_activity_once(
            issue, marker, f"Issue {marker}{detail}.", dry_run=dry_run
        )

    if reason != "completed":
        sys.stdout.write(
            "state_reason is not 'completed': skipping tracking bookkeeping, so "
            "this issue does not count toward its parent's progress.\n"
        )
        return 0

    if not run_track:
        return 0

    return track.on_issue_state_change(repo_root, issue_id, "closed", dry_run=dry_run)


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        prog="issue_close.py",
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("issue", metavar="ID", help="issue id, e.g. 0042")
    parser.add_argument("--reason", required=True, choices=REASONS,
                        help="'completed' counts toward tracking progress; "
                             "'not-planned' does not")
    parser.add_argument("--note", default=None,
                        help="one-line reason recorded in the activity log")
    parser.add_argument("--force", action="store_true",
                        help="rewrite state_reason on an already-closed issue")
    parser.add_argument("--repo-root", type=Path, default=track.default_repo_root(),
                        help="repository root (default: two levels above this script)")
    parser.add_argument("--dry-run", action="store_true",
                        help="print what would change, write nothing")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        return close_issue(
            args.repo_root.resolve(),
            track.normalize_id(args.issue),
            args.reason,
            note=args.note,
            force=args.force,
            dry_run=args.dry_run,
        )
    except LayerError as exc:
        sys.stderr.write(f"issue_close.py: {exc}\n")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
