#!/usr/bin/env python3
"""Which Stage 4.3 proof packets are ready to dispatch, and which are blocked.

The packet tree is GitHub's: `#47` holds one sub-issue per chapter tracker,
each tracker holds its packets, and a chain such as Magic Square rigidity nests
one level deeper.  Readiness is GitHub's too — a packet's prerequisites are its
`blocked_by` issue dependencies (`local/protocols/issues-prs.md` §1), not the
prose bullets in its body, which are commentary.  A packet is READY when it is
an open leaf of that tree and every issue blocking it is closed; a merged PR
closes its packet, so no PR state is consulted here.

Read-only, and every GET is cached for the run, so the walk costs one request
per node even when several packets share blockers.

Usage:
    ready_packets.py [--all] [--json] [--root N]
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
try:
    import gh_common
except ModuleNotFoundError as exc:  # pragma: no cover - defensive
    sys.stderr.write(f"ready_packets.py: cannot import gh_common.py ({exc}).\n")
    raise SystemExit(2)

from wf_util import LayerError  # noqa: E402

#: Stage 4.3's tracking issue; every proof packet hangs under it.
DEFAULT_ROOT = 47

_CACHE: dict[str, list] = {}


def _get(path: str) -> list:
    """One paginated GET per path per run."""
    if path not in _CACHE:
        _CACHE[path] = gh_common.api(path, paginate=True) or []
    return _CACHE[path]


def sub_issues(number: int) -> list[dict]:
    return _get(f"issues/{number}/sub_issues")


def blocked_by(number: int) -> list[dict]:
    return _get(f"issues/{number}/dependencies/blocked_by")


def collect(root: int = DEFAULT_ROOT) -> list[dict]:
    """Open leaves of *root*'s subtree, each with its blockers.

    A node carrying sub-issues is a tracker, not a packet, so only leaves are
    reported; the `seen` set keeps a mis-linked cycle from looping forever.
    """
    leaves: list[dict] = []
    seen: set[int] = {root}

    def visit(parent: int) -> None:
        for row in sub_issues(parent):
            number = int(row["number"])
            if number in seen:
                continue
            seen.add(number)
            if sub_issues(number):
                visit(number)
                continue
            if row.get("state") != "open":
                continue
            blockers = [
                {"issue": int(b["number"]), "state": b.get("state"),
                 "title": b.get("title") or ""}
                for b in blocked_by(number)
            ]
            leaves.append({
                "issue": number,
                "title": row.get("title") or "",
                "parent": parent,
                "blockers": blockers,
                "open_blockers": [b["issue"] for b in blockers
                                  if b["state"] == "open"],
            })

    visit(root)
    leaves.sort(key=lambda row: row["issue"])
    return leaves


def render(rows: list[dict], header: str) -> str:
    if not rows:
        return f"{header} (0)\n"
    width = min(58, max(len(row["title"]) for row in rows))
    out = [f"{header} ({len(rows)})",
           f"{'issue':>6}  {'title'.ljust(width)}  {'parent':>7}  blockers"]
    for row in rows:
        title = row["title"]
        if len(title) > width:
            title = title[:width - 3] + "..."
        blockers = ", ".join(f"#{n}" for n in row["open_blockers"]) or "-"
        out.append(f"{'#' + str(row['issue']):>6}  {title.ljust(width)}  "
                   f"{'#' + str(row['parent']):>7}  {blockers}")
    return "\n".join(out) + "\n"


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        prog="ready_packets.py", description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--root", type=int, default=DEFAULT_ROOT, metavar="N",
                        help=f"tracking issue to walk (default {DEFAULT_ROOT})")
    parser.add_argument("--all", action="store_true",
                        help="also list the blocked packets and their open blockers")
    parser.add_argument("--json", action="store_true",
                        help="emit JSON instead of the table")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        rows = collect(args.root)
    except LayerError as exc:
        sys.stderr.write(f"ready_packets.py: {exc}\n")
        return 2
    ready = [row for row in rows if not row["open_blockers"]]
    blocked = [row for row in rows if row["open_blockers"]]
    if args.json:
        payload = {"root": args.root, "ready": ready}
        if args.all:
            payload["blocked"] = blocked
        sys.stdout.write(json.dumps(payload, indent=2) + "\n")
        return 0
    sys.stdout.write(render(ready, "READY"))
    if args.all:
        sys.stdout.write("\n" + render(blocked, "BLOCKED"))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
