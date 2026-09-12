#!/usr/bin/env python3
"""Which open PRs are ready to merge, and why each ready one has not merged.

The owner's rule is *"a ready-to-merge PR left open needs a good reason"*.
This is the mechanism for it.  Readiness is computed from GitHub on the exact
head — `local-ci/summary`, `local-review/summary`, unchecked ledger lines in
the marker-bound review, a standing `CHANGES_REQUESTED`, draft — exactly as
`pr_merge.py` gates 1, 3, 4 and 5 read it, and every call goes through
`gh_common.py` (`local/protocols/issues-prs.md` section 1).

For each ready-but-open PR the reason it has not merged is **read from daemon
state, never guessed**:

| class | evidence |
|---|---|
| `refreshing` | `watchdog/daemon/pr<N>.refreshing` with a live pid |
| `failed` | `watchdog/daemon/pr<N>.failed`, the daemon's JSON marker (class + reason) |
| `parked` | `watchdog/lanes/<N>.needs-attention` and its recorded reason |
| `awaiting-adjudication` | the PR is on `watchdog/daemon/adj-list` with no exact-head ADJUDICATION comment |
| `stale` | the base moved: `pr_merge.head_is_fresh` is false, with minutes since |
| `unexplained` | ready, fresh, and no daemon record — **the alarm case; it should always be zero** |

Output: one comment per hour on the run's progress issue in the compact form
``ready N, merged-this-hour M``, one **occupancy** line (live worker sessions
against the briefed floor — the number the owner asked for three times on
2026-09-12 and which nothing measured, because the half-hourly live-vs-floor
line is a main-session duty and a stalled main session reports nothing), one
line per ready-but-open PR with its reason, and the same rows appended to
``results/telemetry/merge-latency-<YYYY-MM-DD>.jsonl``.  A post is suppressed
when the ready set and the reasons are unchanged and nothing merged, and forced
at least every six hours.  Elapsed timers are deliberately excluded from the
suppression signature, or nothing would ever be identical.

Usage::

    ready_report.py [--dry-run] [--force] [--window-min 60] [--issue N]

Exit codes: 0 posted or suppressed, 2 a GitHub or run-mode failure (nothing
partial is published; the hourly marker comment is adopted if it already
exists).
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
try:
    import gh_common
except ModuleNotFoundError as exc:  # pragma: no cover - defensive
    sys.stderr.write(f"ready_report.py: cannot import gh_common.py ({exc}).\n")
    raise SystemExit(2)

import run_mode  # noqa: E402
from wf_util import LayerError, atomic_write  # noqa: E402

#: Unchecked findings in the review ledger (review.md section 12).
UNCHECKED_RE = re.compile(r"^\s*[-*]\s*\[ \]", re.M)
REVIEW_MARKER = "mipstarre-review"
BRANCH_RE = re.compile(r"^(?:codex/)?issue-0*([0-9]+)-")
REPORT_MARKER = "mipstarre-ready-report"

#: Forced post cadence, independent of change.
FORCE_AFTER_H = 6


# ---------------------------------------------------------------------------
# Readiness, from the exact head
# ---------------------------------------------------------------------------

def issue_of(branch: str) -> int | None:
    match = BRANCH_RE.match(branch or "")
    return int(match.group(1)) if match else None


def readiness(pull: dict, statuses: dict, reviews: list[dict]) -> dict:
    """Readiness of one PR on its exact head, with the blockers named."""
    head = ((pull.get("head") or {}).get("sha")) or ""
    number = int(pull["number"])
    branch = (pull.get("head") or {}).get("ref") or ""
    ci = (statuses.get("local-ci/summary") or {}).get("state")
    review = (statuses.get("local-review/summary") or {}).get("state")
    head_reviews = [row for row in reviews if row.get("commit_id") == head]
    marked = [row for row in head_reviews if REVIEW_MARKER in (row.get("body") or "")]
    unchecked = (len(UNCHECKED_RE.findall(marked[-1].get("body") or ""))
                 if marked else None)
    adverse = any(row.get("state") == "CHANGES_REQUESTED" for row in head_reviews)

    blockers: list[str] = []
    if pull.get("draft"):
        blockers.append("draft")
    if ci != "success":
        blockers.append(f"ci={ci or 'absent'}")
    if review != "success":
        blockers.append(f"review={review or 'absent'}")
    if unchecked is None:
        blockers.append("no exact-head review")
    elif unchecked:
        blockers.append(f"{unchecked} unchecked findings")
    if adverse:
        blockers.append("CHANGES_REQUESTED")
    return {
        "pr": number,
        "head": head,
        "branch": branch,
        "issue": issue_of(branch),
        "ready": not blockers,
        "blockers": blockers,
        "unchecked": unchecked,
    }


# ---------------------------------------------------------------------------
# Why a ready PR has not merged — daemon state, not guesswork
# ---------------------------------------------------------------------------

def pid_alive(pid: int) -> bool:
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    except (OSError, TypeError, ValueError):
        return False
    return True


def _minutes_since(path: Path, now: datetime) -> int | None:
    try:
        stamp = datetime.fromtimestamp(path.stat().st_mtime, tz=timezone.utc)
    except OSError:
        return None
    return max(0, int((now - stamp).total_seconds() // 60))


def read_marker(path: Path) -> dict | None:
    """The daemon's failure marker: JSON record, or the legacy touch file."""
    try:
        text = path.read_text(encoding="utf-8").strip()
    except OSError:
        return None
    if not text:
        return {"class": "legacy", "reason": "empty marker (pre-W5 touch file)"}
    try:
        record = json.loads(text)
    except ValueError:
        return {"class": "legacy", "reason": text.splitlines()[0][:120]}
    if not isinstance(record, dict):
        return {"class": "legacy", "reason": text[:120]}
    return record


def classify_reason(row: dict, *, daemon_dir: Path, lanes_dir: Path,
                    fresh: bool | None, base_moved_min: int | None,
                    adjudicating: bool, now: datetime) -> dict:
    """One (class, detail, key) for a ready-but-open PR.

    ``key`` is the suppression-stable part: it carries no elapsed timer, so an
    unchanged situation produces an unchanged signature an hour later.
    """
    number, head = row["pr"], row["head"]
    refreshing = daemon_dir / f"pr{number}.refreshing"
    if refreshing.exists():
        try:
            pid = int(refreshing.read_text(encoding="utf-8").strip() or 0)
        except (OSError, ValueError):
            pid = 0
        if pid and pid_alive(pid):
            elapsed = _minutes_since(refreshing, now)
            lane = row.get("issue")
            return {"class": "refreshing", "key": "refreshing",
                    "detail": f"refreshing pid {pid} lane {lane}, "
                              f"{elapsed if elapsed is not None else '?'} min"}

    marker = daemon_dir / f"pr{number}.failed"
    if marker.exists():
        record = read_marker(marker) or {}
        kind = str(record.get("class") or "unknown")
        reason = str(record.get("reason") or "no reason recorded")[:160]
        attempts = record.get("attempts")
        marked_head = str(record.get("head") or "")
        stale_marker = (" (marker on a different head " f"{marked_head[:8]})"
                        if marked_head and marked_head != head else "")
        detail = (f"failed marker class={kind} reason={reason!r}"
                  + (f" attempts={attempts}" if attempts is not None else "")
                  + stale_marker)
        return {"class": "failed", "key": f"failed:{kind}:{reason}{stale_marker}",
                "detail": detail}

    lane = row.get("issue")
    if lane is not None:
        parked = lanes_dir / f"{lane}.needs-attention"
        if parked.exists():
            try:
                reason = parked.read_text(encoding="utf-8").strip().splitlines()
            except OSError:
                reason = []
            text = (reason[0] if reason else "no reason recorded")[:160]
            return {"class": "parked", "key": f"parked:{text}",
                    "detail": f"lane {lane} parked: {text}"}

    if adjudicating:
        return {"class": "awaiting-adjudication", "key": "awaiting-adjudication",
                "detail": "on the daemon adjudication list, no exact-head "
                          "ADJUDICATION comment yet"}

    if fresh is False:
        since = f"{base_moved_min} min ago" if base_moved_min is not None else "recently"
        return {"class": "stale", "key": "stale",
                "detail": f"stale: main moved {since}; needs a refresh lane"}
    if fresh is None:
        return {"class": "unknown-freshness", "key": "unknown-freshness",
                "detail": "freshness could not be read locally (git failure)"}

    return {"class": "unexplained", "key": "unexplained",
            "detail": "ready, fresh, and no daemon record — investigate"}


# ---------------------------------------------------------------------------
# Rendering, signature and suppression
# ---------------------------------------------------------------------------

def occupancy(cache: Path) -> dict | None:
    """Live worker sessions against the briefed occupancy floor, or ``None``.

    Intervention 2 of 2026-09-12 ("why are slots idle? it should be close to
    30") is addressed by four separate cause fixes, but nothing MEASURED the
    thing the owner was asking about.  The half-hourly live-vs-floor line is a
    main-session duty, so a stalled main session reports no occupancy at all —
    exactly what happened.  This report already runs hourly from cron; one line
    here means occupancy is never unreported.
    """
    try:
        mode = run_mode.load_mode()
        caps = run_mode.current_caps(mode, cache)
        floor = run_mode.floor_for(caps, mode["run"]["occupancy_target"])
    except (LayerError, KeyError, TypeError, ValueError):
        return None
    try:
        import account_router  # noqa: PLC0415 - same directory, optional
        live = {name: len(account_router.live_pids(cache / "accounts" / name))
                for name in account_router.ACCOUNTS}
    except Exception:  # pragma: no cover - a census failure must not lose the report
        return None
    total = sum(live.values())
    return {"live": total, "floor": int(floor), "cap": sum(caps.values()),
            "by_account": live, "below": total < int(floor)}


def render(rows: list[dict], merged: int, *, window_min: int, ts: str,
           unexplained: int, occ: dict | None = None) -> str:
    """The compact hourly comment."""
    ready = [row for row in rows if row["ready"]]
    lines = [f"ready {len(ready)}, merged-this-hour {merged}"]
    if occ is not None:
        detail = ", ".join(f"{name} {count}" for name, count in sorted(occ["by_account"].items()))
        lines.append(f"occupancy {occ['live']} live of cap {occ['cap']} ({detail}), "
                     f"floor {occ['floor']}" +
                     ("  <- alarm: below the occupancy floor" if occ["below"] else ""))
    for row in sorted(ready, key=lambda item: item["pr"]):
        issue = f"issue {row['issue']}" if row.get("issue") else "no issue in the branch"
        lines.append(f"- PR {row['pr']} ({issue}, head {row['head'][:8]}) "
                     f"{row['reason']['detail']}")
    if not ready:
        lines.append("- no ready-but-open PR")
    lines.append(f"unexplained {unexplained}" +
                 ("" if unexplained == 0 else "  <- alarm: a ready PR with no daemon record"))
    lines.append(f"<sub>ready_report.py, {ts}; merges counted over the last "
                 f"{window_min} min; reasons read from the merge daemon's own state.</sub>")
    return "\n".join(lines) + "\n"


def signature(rows: list[dict], occ: dict | None = None) -> str:
    """Stable digest of the ready set and its reasons (no elapsed timers).

    The occupancy ALARM state joins it — not the live count, which changes every
    minute and would defeat the suppression — so that crossing the floor in
    either direction posts instead of being suppressed as "unchanged".
    """
    keys = sorted(f"{row['pr']}:{row['head']}:{row['reason']['key']}"
                  for row in rows if row["ready"])
    payload = f"ready={len(keys)}\n" + "\n".join(keys)
    if occ is not None:
        payload += f"\noccupancy_below={int(bool(occ['below']))}"
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def state_path(root: Path | None = None) -> Path:
    return (root or run_mode.cache_root()) / "watchdog" / "reports" / "ready-report.json"


def read_state(path: Path) -> dict:
    try:
        doc = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return {}
    return doc if isinstance(doc, dict) else {}


def should_post(state: dict, digest: str, merged: int, now: datetime,
                *, force: bool = False) -> tuple[bool, str]:
    if force:
        return True, "forced"
    last = state.get("posted_at")
    if not last or state.get("signature") != digest:
        return True, "changed"
    if merged:
        return True, "merges since the last post"
    try:
        posted = run_mode.parse_timestamp(last, "posted_at")
    except LayerError:
        return True, "unreadable state"
    if now - posted >= timedelta(hours=FORCE_AFTER_H):
        return True, f"{FORCE_AFTER_H}-hour floor"
    return False, "identical to the previous post and nothing merged"


# ---------------------------------------------------------------------------
# Local evidence: freshness and the daemon's lists
# ---------------------------------------------------------------------------

def head_is_fresh(repo_root: Path, head: str) -> bool | None:
    try:
        import pr_merge  # noqa: PLC0415 - optional: absent in a bare checkout
    except ImportError:
        return None
    try:
        return bool(pr_merge.head_is_fresh(repo_root, "github/main", head))
    except Exception:  # noqa: BLE001 - a git failure is "unknown", never "stale"
        return None


def base_moved_minutes(repo_root: Path, now: datetime) -> int | None:
    proc = subprocess.run(["git", "-C", str(repo_root), "log", "-1", "--format=%ct",
                           "github/main"], capture_output=True, text=True)
    if proc.returncode != 0 or not proc.stdout.strip().isdigit():
        return None
    moved = datetime.fromtimestamp(int(proc.stdout.strip()), tz=timezone.utc)
    return max(0, int((now - moved).total_seconds() // 60))


def adjudication_list(daemon_dir: Path) -> set[int]:
    try:
        text = (daemon_dir / "adj-list").read_text(encoding="utf-8")
    except OSError:
        return set()
    return {int(token) for token in text.split() if token.isdigit()}


def has_head_adjudication(number: int, head: str) -> bool:
    for row in gh_common.api(f"issues/{number}/comments", paginate=True) or []:
        body = row.get("body") or ""
        if body.lstrip().startswith("ADJUDICATION") and f"head={head}" in body:
            return True
    return False


def merged_in_window(since: datetime) -> int:
    """Merged PRs since *since*, newest-updated first, one page is enough."""
    rows = gh_common.api("pulls?state=closed&sort=updated&direction=desc&per_page=100")
    count = 0
    for row in rows or []:
        updated = row.get("updated_at") or ""
        merged = row.get("merged_at")
        try:
            moment = run_mode.parse_timestamp(updated, "updated_at")
        except LayerError:
            continue
        if moment < since:
            break
        if merged:
            try:
                if run_mode.parse_timestamp(merged, "merged_at") >= since:
                    count += 1
            except LayerError:
                continue
    return count


# ---------------------------------------------------------------------------
# Telemetry
# ---------------------------------------------------------------------------

def latency_path(repo_root: Path, now: datetime) -> Path:
    """Dated per run until W7's union merge driver lands (design section 3.7)."""
    name = f"merge-latency-{now.strftime('%Y-%m-%d')}.jsonl"
    return repo_root / "results" / "telemetry" / name


def latency_rows(rows: list[dict], merged: int, unexplained: int, ts: str) -> list[dict]:
    out = [{"ts": ts, "pr": row["pr"], "head": row["head"], "event": "ready",
            "class": row["reason"]["class"], "reason": row["reason"]["detail"],
            "seconds": None, "par": None}
           for row in rows if row["ready"]]
    out.append({"ts": ts, "pr": None, "head": None, "event": "report",
                "class": "summary",
                "reason": f"ready {len(out)}, merged {merged}, unexplained {unexplained}",
                "seconds": None, "par": None})
    return out


# ---------------------------------------------------------------------------
# Collection
# ---------------------------------------------------------------------------

def collect(repo_root: Path, cache: Path, now: datetime) -> list[dict]:
    """Every open PR with its readiness and, when ready, its reason."""
    daemon_dir = cache / "watchdog" / "daemon"
    lanes_dir = cache / "watchdog" / "lanes"
    adjudicated = adjudication_list(daemon_dir)
    moved = base_moved_minutes(repo_root, now)
    rows: list[dict] = []
    for pull in gh_common.api("pulls?state=open", paginate=True) or []:
        head = ((pull.get("head") or {}).get("sha")) or ""
        if not head:
            continue
        statuses = gh_common.latest_statuses(head)
        reviews = gh_common.pr_reviews(int(pull["number"]))
        row = readiness(pull, statuses, reviews)
        if row["ready"]:
            number = row["pr"]
            waiting = (number in adjudicated
                       and not has_head_adjudication(number, head))
            row["reason"] = classify_reason(
                row, daemon_dir=daemon_dir, lanes_dir=lanes_dir,
                fresh=head_is_fresh(repo_root, head), base_moved_min=moved,
                adjudicating=waiting, now=now)
        rows.append(row)
    return rows


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        prog="ready_report.py", description=__doc__.splitlines()[0],
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--issue", type=int, help="progress issue (default: run-mode)")
    parser.add_argument("--window-min", type=int, default=60,
                        help="merge-counting window in minutes (default 60)")
    parser.add_argument("--force", action="store_true", help="post even when unchanged")
    parser.add_argument("--dry-run", action="store_true",
                        help="print the comment; publish and record nothing")
    args = parser.parse_args(sys.argv[1:] if argv is None else argv)

    now = datetime.now(timezone.utc)
    ts = now.strftime("%Y-%m-%dT%H:%M:%SZ")
    repo_root = run_mode.repo_root()
    cache = run_mode.cache_root()
    try:
        issue = args.issue
        if issue is None:
            issue = int(run_mode.value_for(run_mode.load_mode(), "progress_issue"))
        rows = collect(repo_root, cache, now)
        merged = merged_in_window(now - timedelta(minutes=args.window_min))
    except LayerError as exc:
        sys.stderr.write(f"ready_report.py: {exc}\n")
        return 2

    unexplained = sum(1 for row in rows if row["ready"]
                      and row["reason"]["class"] == "unexplained")
    occ = occupancy(cache)
    body = render(rows, merged, window_min=args.window_min, ts=ts,
                  unexplained=unexplained, occ=occ)
    digest = signature(rows, occ)
    state_file = state_path(cache)
    state = read_state(state_file)
    post, why = should_post(state, digest, merged, now, force=args.force)

    if args.dry_run:
        sys.stdout.write(body)
        sys.stdout.write(f"\n(dry run: would {'post' if post else 'suppress'} — {why})\n")
        return 0
    if not post:
        sys.stdout.write(f"suppressed: {why}\n")
        return 0

    marker = f"<!-- {REPORT_MARKER} slot={now.strftime('%Y-%m-%dT%H')} -->"
    try:
        gh_common.ensure_pr_comment(issue, marker, body)
    except LayerError as exc:
        sys.stderr.write(f"ready_report.py: posting to #{issue} failed: {exc}\n")
        return 2

    path = latency_path(repo_root, now)
    for record in latency_rows(rows, merged, unexplained, ts):
        run_mode.locked_append(path, json.dumps(record, ensure_ascii=False))
    atomic_write(state_file, json.dumps(
        {"signature": digest, "posted_at": ts, "issue": issue,
         "ready": sum(1 for row in rows if row["ready"]), "merged": merged,
         "unexplained": unexplained}, indent=1) + "\n")
    sys.stdout.write(f"posted on #{issue} ({why}); ready "
                     f"{sum(1 for row in rows if row['ready'])}, merged {merged}, "
                     f"unexplained {unexplained}\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
