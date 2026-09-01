#!/usr/bin/env python3
"""Create a GitHub issue — all that survives of the old ``issues/`` create path.

Before issue 0007 this script allocated a four-digit id from ``issues/.seq``,
wrote ``issues/<id>-<slug>.md`` under a lock, ran a deterministic keyword
classifier against ``local/labels.yml``, then shelled out to a Mathlib scout.
Every one of those responsibilities moved or died:

* the id and the record are GitHub's.  ``gh_common.issue_create`` owns the
  POST, and with ``--key`` it embeds a ``mipstarre-issue-key`` marker so an
  ambiguous create is resolved by adopting the existing issue rather than by
  repeating the mutation (gh_common.py:308-347).
* labels are validated against the *repository's* labels inside that helper,
  so ``local/labels.yml`` is no longer a second source of truth that drifts
  away from what GitHub will accept.
* ``--parent`` is a native sub-issue link (``POST issues/<parent>/sub_issues``),
  not two halves of a hand-maintained relationship.
* classification and scouting are not creation-time concerns.  The old
  deterministic pass existed only to imitate ``classify-outside`` of the
  retired ``.github/workflows/issue-automation.yml``; its LLM sibling was never
  wired.  Nothing here reads a token or calls a model.

No local file is written — not a record, not telemetry: ``dispatch.sh`` owns the
session record.  Fail closed like every other consumer of the GitHub layer: an
API failure exits 2 with the layer's message and leaves nothing behind.

Usage:
    issue_new.py --title "Formalize the Pauli basis test soundness bound" \
                 --body-file /tmp/body.md --label formalization
    issue_new.py --title "Tracking - Pauli basis test" --body "..." \
                 --parent 12 --key qpbt-tracking-pauli
    issue_new.py --help
"""

from __future__ import annotations

import argparse
import hashlib
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
try:
    import gh_common
except ModuleNotFoundError as exc:  # pragma: no cover - defensive
    sys.stderr.write(
        "issue_new.py: cannot import local/bin/gh_common.py, which holds the "
        f"GitHub layer ({exc}).\n"
    )
    raise SystemExit(2)

from wf_util import slugify, BODY_LIMIT, TITLE_LIMIT, LayerError, sanitize  # noqa: E402


def flatten_labels(chunks: list[str]) -> tuple[str, ...]:
    """``--label a,b --label c`` -> ``("a", "b", "c")``, order-preserving; comma
    splitting is kept from the pre-0007 CLI, whose callers pass grouped lists."""
    names: list[str] = []
    for chunk in chunks:
        for name in (part.strip() for part in chunk.split(",")):
            if name and name not in names:
                names.append(name)
    return tuple(names)


def create(args: argparse.Namespace) -> int:
    title = sanitize(args.title, TITLE_LIMIT).strip()
    if not title:
        raise LayerError("--title is empty after sanitization")
    if args.body_file:
        raw = Path(args.body_file).read_text(encoding="utf-8")
    else:
        raw = args.body or ""
    # Bodies round-trip through GitHub, where anyone with read access can quote
    # them back into an agent prompt, so they are untrusted on the way out too
    # (wf_util.sanitize breaks ``` fences and strips control characters).
    body = sanitize(raw, BODY_LIMIT).strip()
    if not body:
        raise LayerError(
            "an issue body is required: pass --body-file PATH or --body TEXT. "
            "The old --template scaffolds are gone; GitHub's issue forms under "
            ".github/ISSUE_TEMPLATE/ are where boilerplate belongs now."
        )
    labels = flatten_labels(args.label)

    if args.dry_run:
        sys.stdout.write(
            f"[dry-run] would create issue {title!r} labels={list(labels)} "
            f"parent={args.parent} key={args.key} ({len(body)} body chars)\n"
        )
        return 0

    # Every create is adoption-safe: without an explicit --key the slug plus a
    # short digest of the FULL title is the key, so a retried create adopts —
    # and two distinct titles sharing a truncated slug cannot alias (round 2, F12).
    auto_key = f"{slugify(title)}-{hashlib.sha256(title.encode()).hexdigest()[:8]}"
    number = gh_common.issue_create(
        title, body, labels=labels, parent=args.parent,
        key=args.key or auto_key
    )
    # Bare number on stdout: shell callers capture it with $(...).
    sys.stdout.write(f"{number}\n")
    return 0


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        prog="issue_new.py",
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("--title", required=True,
                        help="bracket-free issue title (docs/CONTRIBUTING.md:122-124)")
    body = parser.add_mutually_exclusive_group(required=True)
    body.add_argument("--body-file", type=Path, metavar="PATH",
                      help="file holding the issue body")
    body.add_argument("--body", metavar="TEXT",
                      help="issue body as a literal string")
    parser.add_argument("--label", action="append", default=[], metavar="NAME",
                        help="repository label; repeatable, comma lists accepted. "
                             "Unknown labels are rejected — create them on GitHub "
                             "first (gh_common.py:318-323)")
    parser.add_argument("--parent", type=int, metavar="N",
                        help="attach the new issue as a native sub-issue of #N")
    parser.add_argument("--key", metavar="K",
                        help="idempotency key: embeds a marker so a retried "
                             "create adopts the existing issue instead of "
                             "opening a duplicate")
    parser.add_argument("--dry-run", action="store_true",
                        help="print what would be created, call nothing")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        return create(args)
    except LayerError as exc:
        sys.stderr.write(f"issue_new.py: {exc}\n")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
