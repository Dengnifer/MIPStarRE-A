#!/usr/bin/env python3
"""Retire pull requests whose work is already on ``main`` — mechanically, never by guess.

On 2026-09-12 PRs 329, 334, 336 and 337 were detected as already merged into
``main`` at 05:37Z and stayed open for three more hours, absorbing refresh lanes
and review re-runs and inflating the ready-but-open count the owner was asked to
interpret.  They were finally closed by hand under an explicit order.  This is
the mechanism that does it, and it closes a PR only when **both** of these hold:

1. ``git diff github/main...<head>`` is empty — the three-dot diff, i.e. the
   difference between the merge base and the head: the PR proposes nothing that
   ``main`` does not already have;
2. ``git merge-base --is-ancestor <head> github/main`` succeeds — the head commit
   itself is reachable from ``main``.

Either condition alone closes nothing.  Condition 1 alone is satisfied by a
branch that adds a commit and reverts it (empty net diff, work never merged);
condition 2 is what proves that *these bytes* are on ``main``.

What this script must never do, and does not:

* it never closes an **issue** (that stays with ``pr_merge.py`` and
  ``issue_close.py``; closing the PR leaves the issue open for the work that
  actually carries it);
* it never touches a PR with a nonempty three-dot diff;
* it never acts on a heuristic such as "looks superseded", a title match, an age
  threshold or a label;
* it never converts a GitHub failure into a local success: an error is reported,
  the PR is left open and the next pass retries it.

Every closure is recorded three times so nothing disappears silently: one
idempotent PR comment carrying ``<!-- pr-janitor:superseded -->`` that names both
checks and the SHAs, one append-only row in
``$CACHE_ROOT/watchdog/janitor/closures.jsonl``, and one bullet in the event log
(``telemetry.py event``).  The hourly report reads the report fragment written by
``--report``.

This is a PR-only tool and is deliberately distinct from the report-only issue
audits in ``housekeeping.sh``.

Usage:
    pr_janitor.py [--dry-run] [--pr N]... [--limit N] [--base github/main]
                  [--report PATH] [--no-fetch] [--no-event] [--repo-root PATH]

Exit codes: 0 = pass complete (including "nothing to do"); 1 = at least one PR
could not be processed (reported; retried next pass); 2 = usage/environment.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))  # gh_common/wf_util sit here
import gh_common  # noqa: E402
from wf_util import LayerError, cache_root, default_repo_root, utcnow  # noqa: E402

#: The idempotency key of the retirement comment.  Never change it: an older
#: comment carrying it is what stops a second comment from being posted.
MARKER = "<!-- pr-janitor:superseded -->"

#: Where the append-only closure ledger lives (runtime state, never committed).
LEDGER = "watchdog/janitor/closures.jsonl"


# --------------------------------------------------------------- git helpers

def run_git(repo_root: Path, *args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(["git", "-C", str(repo_root), *args],
                          capture_output=True, text=True, check=False)


def git_out(repo_root: Path, *args: str) -> str:
    result = run_git(repo_root, *args)
    if result.returncode != 0:
        raise LayerError(f"git {' '.join(args)} failed ({result.returncode}): "
                         f"{(result.stderr or result.stdout).strip()[:400]}")
    return result.stdout.strip()


def fetch(repo_root: Path, remote: str = "github") -> None:
    result = run_git(repo_root, "fetch", "--quiet", remote)
    if result.returncode != 0:
        raise LayerError(f"git fetch {remote} failed: "
                         f"{(result.stderr or result.stdout).strip()[:400]}")


def have_commit(repo_root: Path, sha: str) -> bool:
    return run_git(repo_root, "cat-file", "-e", f"{sha}^{{commit}}").returncode == 0


def diff_is_empty(repo_root: Path, base: str, head: str) -> bool:
    """``git diff --quiet base...head`` — the PR proposes nothing new.

    ``--quiet`` exits 0 when there is no difference and 1 when there is; any
    other status is a git failure and must not be read as "empty".
    """
    result = run_git(repo_root, "diff", "--quiet", f"{base}...{head}")
    if result.returncode not in (0, 1):
        raise LayerError(f"git diff --quiet {base}...{head} failed "
                         f"({result.returncode}): "
                         f"{(result.stderr or result.stdout).strip()[:400]}")
    return result.returncode == 0


def head_is_reachable(repo_root: Path, base: str, head: str) -> bool:
    """``git merge-base --is-ancestor head base`` — the head commit is on *base*."""
    result = run_git(repo_root, "merge-base", "--is-ancestor", head, base)
    if result.returncode not in (0, 1):
        raise LayerError(f"git merge-base --is-ancestor {head} {base} failed "
                         f"({result.returncode}): "
                         f"{(result.stderr or result.stdout).strip()[:400]}")
    return result.returncode == 0


def should_close(diff_empty: bool, reachable: bool) -> bool:
    """Both conditions are required.  This is the whole decision."""
    return bool(diff_empty) and bool(reachable)


def carrier_commit(repo_root: Path, base: str, head: str) -> str:
    """The commit on *base* that carries the work — the first commit after *head*.

    With *head* reachable from *base*, the ancestry path ``head..base`` starts at
    the commit that took *head* in (the merge commit, or the rebased/duplicated
    commit that followed it).  When *head* is the tip of *base* the carrier is
    *head* itself.
    """
    result = run_git(repo_root, "rev-list", "--ancestry-path", "--reverse",
                     f"{head}..{base}")
    if result.returncode != 0:
        return head
    for line in result.stdout.splitlines():
        line = line.strip()
        if line:
            return line
    return head


# ------------------------------------------------------- GitHub, one place each
# Wrapped so a caller (and the unit test) can substitute them without reaching
# into gh_common, and so that the only PR-state mutation in this file is the one
# PATCH in close_pull().

def list_open_pulls() -> list[dict]:
    return gh_common.api("pulls?state=open", paginate=True) or []


def post_marker_comment(number: int, body: str) -> int:
    """One comment per PR, idempotent on MARKER (created once, then updated)."""
    return gh_common.ensure_pr_comment(number, MARKER, body)


def close_pull(number: int) -> None:
    """Close the PULL REQUEST.  Never the issue: this is the pulls endpoint."""
    gh_common.api(f"pulls/{number}", method="PATCH", payload={"state": "closed"},
                  mutation=True, idempotent=True)


# --------------------------------------------------------------- the pass

def comment_body(base: str, evidence: dict) -> str:
    return (
        f"**Retired by `pr_janitor.py`: this pull request's work is already on "
        f"`{base}`.**\n\n"
        f"Two mechanical checks, both required, both passed on "
        f"{evidence['checked_at']}:\n\n"
        f"1. `git diff --quiet {base}...{evidence['head']}` — empty three-dot "
        f"diff: this branch proposes nothing `{base}` does not already have.\n"
        f"2. `git merge-base --is-ancestor {evidence['head']} {base}` — the head "
        f"commit itself is reachable from `{base}`.\n\n"
        f"- head: `{evidence['head']}`\n"
        f"- `{base}`: `{evidence['base_sha']}`\n"
        f"- merge base: `{evidence['merge_base']}`\n"
        f"- the commit on `{base}` that carries the work: "
        f"`{evidence['carrier']}`\n\n"
        f"Closing the pull request only. The linked issue is untouched — if the "
        f"work is not finished, the issue still says so. Reopen this PR if the "
        f"branch is meant to carry further commits.\n"
    )


def evaluate(repo_root: Path, base: str, pull: dict) -> dict:
    """Decide for one PR.  Raises LayerError on a git failure (never 'no')."""
    number = int(pull["number"])
    head = (pull.get("head") or {}).get("sha") or ""
    ref = (pull.get("head") or {}).get("ref") or ""
    if not head:
        raise LayerError(f"PR {number}: GitHub returned no head SHA")
    if not have_commit(repo_root, head):
        raise LayerError(f"PR {number}: head {head[:12]} is not in the local "
                         f"object store (fetch the branch before deciding)")
    diff_empty = diff_is_empty(repo_root, base, head)
    reachable = head_is_reachable(repo_root, base, head)
    evidence = {
        "pr": number,
        "branch": ref,
        "head": head,
        "base": base,
        "base_sha": git_out(repo_root, "rev-parse", base),
        "merge_base": git_out(repo_root, "merge-base", base, head),
        "diff_empty": diff_empty,
        "reachable": reachable,
        "checked_at": utcnow(),
    }
    evidence["close"] = should_close(diff_empty, reachable)
    evidence["carrier"] = carrier_commit(repo_root, base, head) if evidence["close"] else ""
    return evidence


def ledger_path() -> Path:
    return cache_root() / LEDGER


def record_closure(evidence: dict) -> None:
    path = ledger_path()
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps({"ts": utcnow(), "tool": "pr_janitor.py",
                                 "action": "closed-superseded", **evidence},
                                ensure_ascii=False) + "\n")


def record_event(repo_root: Path, evidence: dict) -> None:
    """One bullet in the event log; a failure here never fails the closure."""
    text = (f"pr_janitor.py closed PR {evidence['pr']} ({evidence['branch']}): its work "
            f"is already on {evidence['base']} — empty three-dot diff and head "
            f"{evidence['head'][:12]} reachable from {evidence['base']} "
            f"({evidence['base_sha'][:12]}), carried by {evidence['carrier'][:12]}. "
            f"The linked issue was not touched.")
    subprocess.run([sys.executable, str(Path(__file__).resolve().parent / "telemetry.py"),
                    "--repo-root", str(repo_root), "event", "--text", text],
                   capture_output=True, text=True, check=False)


def process_pull(repo_root: Path, base: str, pull: dict, *, dry_run: bool,
                 write_event: bool) -> dict:
    """Return one result row; never raises for an expected GitHub/git failure."""
    number = int(pull.get("number", 0))
    try:
        evidence = evaluate(repo_root, base, pull)
    except LayerError as error:
        return {"pr": number, "action": "error", "detail": str(error)[:400]}

    if not evidence["close"]:
        reason = ("diff nonempty" if not evidence["diff_empty"] else
                  "head not reachable from " + base)
        return {"pr": number, "action": "kept", "detail": reason, **evidence}

    if dry_run:
        return {"pr": number, "action": "would-close", **evidence}

    try:
        post_marker_comment(number, comment_body(base, evidence))
        close_pull(number)
    except LayerError as error:
        # Reported, not swallowed: the PR stays open and the next pass retries.
        return {"pr": number, "action": "error", "detail": str(error)[:400], **evidence}

    record_closure(evidence)
    if write_event:
        record_event(repo_root, evidence)
    return {"pr": number, "action": "closed", **evidence}


def render_report(rows: list[dict]) -> str:
    closed = [r for r in rows if r["action"] in ("closed", "would-close")]
    errors = [r for r in rows if r["action"] == "error"]
    lines = [f"pr_janitor: {len(rows)} open PR(s) examined, {len(closed)} superseded, "
             f"{len(errors)} error(s)"]
    for row in closed:
        lines.append(f"  PR {row['pr']} {row['action']}: empty diff against "
                     f"{row.get('base', 'github/main')} and head "
                     f"{str(row.get('head', ''))[:12]} reachable "
                     f"(carried by {str(row.get('carrier', ''))[:12]})")
    for row in errors:
        lines.append(f"  PR {row['pr']} error: {row['detail']}")
    return "\n".join(lines) + "\n"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--repo-root", type=Path, default=None)
    parser.add_argument("--base", default=os.environ.get("MIPSTARRE_BASE_REF", "github/main"),
                        help="base ref both checks run against (default github/main)")
    parser.add_argument("--pr", type=int, action="append", default=[],
                        help="only consider these PR numbers (repeatable)")
    parser.add_argument("--limit", type=int, default=0,
                        help="stop after N closures (0 = no limit)")
    parser.add_argument("--dry-run", action="store_true",
                        help="decide and report; post nothing, close nothing")
    parser.add_argument("--no-fetch", action="store_true",
                        help="do not run git fetch first (the caller just did)")
    parser.add_argument("--no-event", action="store_true",
                        help="do not append an events.md bullet per closure")
    parser.add_argument("--report", type=Path,
                        help="write the report fragment here as well as to stdout")
    args = parser.parse_args(argv)

    repo_root = (args.repo_root or default_repo_root()).resolve()
    if not (repo_root / "local" / "bin").is_dir():
        parser.error(f"--repo-root {repo_root} is not a checkout (no local/bin)")

    try:
        if not args.no_fetch:
            fetch(repo_root, args.base.split("/", 1)[0] if "/" in args.base else "github")
        pulls = list_open_pulls()
    except LayerError as error:
        sys.stderr.write(f"pr_janitor: {error}\n")
        return 1

    if args.pr:
        wanted = set(args.pr)
        pulls = [p for p in pulls if int(p.get("number", 0)) in wanted]

    rows: list[dict] = []
    closed = 0
    for pull in sorted(pulls, key=lambda p: int(p.get("number", 0))):
        row = process_pull(repo_root, args.base, pull,
                           dry_run=args.dry_run, write_event=not args.no_event)
        rows.append(row)
        if row["action"] in ("closed", "would-close"):
            closed += 1
            if args.limit and closed >= args.limit:
                break

    report = render_report(rows)
    sys.stdout.write(report)
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(report, encoding="utf-8")
    return 1 if any(row["action"] == "error" for row in rows) else 0


if __name__ == "__main__":
    raise SystemExit(main())
