#!/usr/bin/env python3
"""The single writer of the completion-estimate issue: exactly two lines.

The owner asked for two numbers on the estimate issue and nothing else — the
bold headline and one ``<sub>`` provenance line, in the shape
``/home/drx/bin/estimate.sh`` established on 2026-09-04.  On 2026-09-12 a
session posted multi-line reports there and the operator had to reformat one by
hand.  This tool removes the possibility: it renders the body itself from
values passed on the command line and refuses to publish anything else.  There
is no ``--body`` input.

::

    estimate_post.py --percent 89 --days 2.1 --open-sites 21 \\
        --denominator 197 --main 60dbabef --in-open-prs 9 --rate 14

renders and posts::

    **2026-09-13 05:00Z — implemented ≈ 89% · days to go ≈ 2.1**
    <sub>21 of 197 sites open on main (60dbabef); 9 proved in open PRs; trailing-24h rate 14 sites/day.</sub>

``--open-prs``, ``--in-pr-source`` and ``--snapshot-generated`` are optional and
name where the in-PR figure came from — ``estimate.sh`` counts it in a throwaway
worktree from the committed GitHub snapshot, and a number read off a stale
snapshot must not read like a live count.  They are the ONLY extra options, and
the option names here and in ``estimate.sh`` are one interface: an option
``estimate.sh`` passes and this parser does not define makes ``argparse`` exit 2
on every cron tick, which posts nothing for a whole run while the cron log still
looks almost normal.  ``scripts/tests/test_estimate_post.py`` runs the exact
argument vector ``estimate.sh`` builds.

The issue number comes from the run mode (``run.estimate_issue``, validated at
briefing time), so a missing ``watchdog/estimate-issue`` can no longer silently
no-op the owner's only progress channel: an unbriefed run exits 2 and says so.
Prose progress belongs on the progress log, never here
(``local/protocols/issues-prs.md`` section 6).

``results/telemetry/estimates.jsonl`` stays the caller's record
(``results/telemetry/owner-tools/estimate.sh``); this tool writes no telemetry,
so the series has exactly one writer too.
"""

from __future__ import annotations

import argparse
import re
import sys
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
try:
    import gh_common
except ModuleNotFoundError as exc:  # pragma: no cover - defensive
    sys.stderr.write(f"estimate_post.py: cannot import gh_common.py ({exc}).\n")
    raise SystemExit(2)

import run_mode  # noqa: E402
from wf_util import LayerError  # noqa: E402

HEADLINE = "**{ts} — implemented ≈ {percent}% · days to go ≈ {days}**"
PROVENANCE = ("<sub>{open_sites} of {denominator} sites open on main ({main}); "
              "{in_open_prs} proved in{where}; trailing-24h rate {rate} "
              "sites/day.</sub>")
#: How the in-PR figure was obtained, when the caller says.  `estimate.sh` counts
#: the open PRs from the committed GitHub snapshot, so the sub line names the
#: snapshot and its age: an in-PR number from a stale snapshot must not read like
#: a live count.  Angle brackets are excluded on purpose — BODY_RE forbids them
#: inside the <sub>, which is what keeps the estimate issue to two rendered lines.
SOURCE_LABELS = {"github-snapshot": "GitHub snapshot", "live": "live"}

#: The only body this tool will publish: two lines, nothing before or after.
BODY_RE = re.compile(
    r"\A\*\*\d{4}-\d{2}-\d{2} \d{2}:\d{2}Z — implemented ≈ \d{1,3}% · "
    r"days to go ≈ (?:n/a|\d+(?:\.\d+)?)\*\*\n"
    r"<sub>[^\n<>]*</sub>\Z")

TS_FMT = "%Y-%m-%d %H:%MZ"


def _where(open_prs: int | None, source: str | None, generated: str | None) -> str:
    """The ` open PRs` clause, with its provenance when the caller supplied it."""
    if open_prs is None:
        return " open PRs"
    if open_prs < 0:
        raise LayerError(f"--open-prs {open_prs} must not be negative")
    clause = f" {open_prs} open PRs"
    label = SOURCE_LABELS.get((source or "").strip(), (source or "").strip())
    detail = " ".join(part for part in (label, (generated or "").strip()) if part)
    if detail:
        clause += f" ({_clean(detail)})"
    return clause


def _clean(text: str) -> str:
    """No angle brackets and no newline inside the ``<sub>``; see ``BODY_RE``."""
    return re.sub(r"\s+", " ", text.replace("<", "").replace(">", "")).strip()


def render(*, percent: int, days: str, open_sites: int, denominator: int,
           main: str, in_open_prs: int, rate: int, ts: str | None = None,
           open_prs: int | None = None, in_pr_source: str | None = None,
           snapshot_generated: str | None = None) -> str:
    """The two-line body, or ``LayerError`` when a value cannot be rendered."""
    moment = ts or datetime.now(timezone.utc).strftime(TS_FMT)
    if not 0 <= percent <= 100:
        raise LayerError(f"--percent {percent} is outside 0..100")
    if denominator <= 0:
        raise LayerError(f"--denominator {denominator} must be positive")
    for name, value in (("--open-sites", open_sites), ("--in-open-prs", in_open_prs)):
        if value < 0:
            raise LayerError(f"{name} {value} must not be negative")
    if not re.fullmatch(r"[0-9a-f]{7,40}", main):
        raise LayerError(f"--main {main!r} is not a commit SHA")
    body = (HEADLINE.format(ts=moment, percent=percent, days=days) + "\n" +
            PROVENANCE.format(open_sites=open_sites, denominator=denominator,
                              main=main, in_open_prs=in_open_prs, rate=rate,
                              where=_where(open_prs, in_pr_source, snapshot_generated)))
    check(body)
    return body


def check(body: str) -> None:
    """Refuse any body that is not the two rendered lines."""
    if not BODY_RE.match(body.strip("\n")):
        raise LayerError(
            "refusing this body: the estimate issue carries exactly the bold "
            "headline and one <sub> provenance line, and nothing else "
            "(issues-prs.md section 6). Post prose on the progress issue.\n"
            f"--- offered ---\n{body}\n--- end ---")


def _days(value: str) -> str:
    if value == "n/a":
        return value
    try:
        number = float(value)
    except ValueError as exc:
        raise argparse.ArgumentTypeError(f"--days must be a number or 'n/a', got {value!r}") from exc
    if number < 0:
        raise argparse.ArgumentTypeError("--days must not be negative")
    return f"{number:g}"


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="estimate_post.py", description=__doc__.splitlines()[0],
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--percent", type=int, help="implemented percentage")
    parser.add_argument("--days", type=_days, help="days to go, or n/a")
    parser.add_argument("--open-sites", type=int, help="sorry sites open on main")
    parser.add_argument("--denominator", type=int, default=197,
                        help="initial obligations (default 197: keep the series comparable)")
    parser.add_argument("--main", help="short SHA of github/main")
    parser.add_argument("--in-open-prs", type=int, help="sites proved in open PRs, deduplicated")
    parser.add_argument("--open-prs", type=int,
                        help="how many open PRs those sites came from (optional)")
    parser.add_argument("--in-pr-source", choices=tuple(SOURCE_LABELS),
                        help="how the in-PR figure was obtained (optional)")
    parser.add_argument("--snapshot-generated",
                        help="age/stamp of the snapshot the in-PR figure came from (optional)")
    parser.add_argument("--rate", type=int, help="trailing-24h sites/day")
    parser.add_argument("--ts", help=f"timestamp, default now as {TS_FMT}")
    parser.add_argument("--issue", type=int, help="estimate issue (default: run-mode)")
    parser.add_argument("--dry-run", action="store_true",
                        help="print the rendered body, publish nothing")
    parser.add_argument("--check-file", type=Path,
                        help="validate a candidate body and exit; publish nothing")
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(sys.argv[1:] if argv is None else argv)
    try:
        if args.check_file:
            check(args.check_file.read_text(encoding="utf-8"))
            sys.stdout.write("conforms\n")
            return 0
        required = ("percent", "days", "open_sites", "main", "in_open_prs", "rate")
        missing = [f"--{name.replace('_', '-')}" for name in required
                   if getattr(args, name) is None]
        if missing:
            parser.error(f"missing required value(s): {', '.join(missing)}")
        body = render(percent=args.percent, days=args.days,
                      open_sites=args.open_sites, denominator=args.denominator,
                      main=args.main, in_open_prs=args.in_open_prs,
                      rate=args.rate, ts=args.ts, open_prs=args.open_prs,
                      in_pr_source=args.in_pr_source,
                      snapshot_generated=args.snapshot_generated)
        if args.dry_run:
            sys.stdout.write(body + "\n")
            return 0
        issue = args.issue
        if issue is None:
            issue = int(run_mode.value_for(run_mode.load_mode(), "estimate_issue"))
        # One mutation, keyed on this estimate's own timestamp so a retry
        # adopts its comment instead of doubling the series.  The marker is an
        # HTML comment: GitHub renders nothing for it, so the issue still shows
        # exactly the two lines.
        slot = body.split(" — ", 1)[0].lstrip("*")
        marker = f"<!-- mipstarre-estimate slot={slot} -->"
        gh_common.ensure_pr_comment(issue, marker, body)
        sys.stdout.write(f"estimate posted on #{issue}\n{body}\n")
        return 0
    except LayerError as exc:
        sys.stderr.write(f"estimate_post.py: {exc}\n")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
