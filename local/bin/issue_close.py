#!/usr/bin/env python3
"""Close a GitHub issue with a reason, optionally leaving one note comment.

Pre-0007 this script rewrote ``state``/``state_reason`` in ``issues/<id>-*.md``,
appended an activity bullet, and ran the tracking bookkeeping in ``track.py``.
GitHub does all of it natively: the reason is the issue's ``state_reason``,
sub-issue progress is computed from the children's own states, and the note is
a comment posted through the marker-idempotent path, so a re-run does not stack
duplicates.  The ``completed`` / ``not-planned`` distinction is still the
caller's to choose (gh_common.py:378-387).

Usage:
    issue_close.py 42 --reason completed
    issue_close.py 42 --reason not-planned --comment "superseded by #51"
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import gh_common  # noqa: E402
from wf_util import BODY_LIMIT, LayerError, sanitize  # noqa: E402

REASONS = ("completed", "not-planned")


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        prog="issue_close.py",
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("number", type=int, metavar="NUMBER",
                        help="GitHub issue number, e.g. 42")
    parser.add_argument("--reason", default="completed", choices=REASONS,
                        help="'completed' counts toward a parent's sub-issue "
                             "progress; 'not-planned' does not")
    parser.add_argument("--comment", default=None,
                        help="one-line note posted before the close")
    parser.add_argument("--dry-run", action="store_true",
                        help="print what would change, call nothing")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    comment = sanitize(args.comment, BODY_LIMIT).strip() if args.comment else None
    if args.dry_run:
        sys.stdout.write(
            f"[dry-run] would close #{args.number} as {args.reason}"
            + (f" with comment {comment!r}\n" if comment else "\n")
        )
        return 0
    try:
        gh_common.issue_close(args.number, reason=args.reason, comment=comment)
    except LayerError as exc:
        sys.stderr.write(f"issue_close.py: {exc}\n")
        return 2
    sys.stdout.write(f"closed #{args.number} as {args.reason}\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
