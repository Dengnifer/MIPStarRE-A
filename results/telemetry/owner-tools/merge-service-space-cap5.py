#!/usr/bin/env python3
"""Bounded owner merge service for the active space/cap5 episode.

The service is intentionally conservative: each tick records remote/main
identity, dirty-primary and gate state, reports the oldest eligible PR age, and
only delegates an exact-head merge to ``pr_merge.py`` after all local checks
pass. Refreshing stale branches remains a separate lane-owned operation.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import fcntl
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time
from typing import Any

ROOT = Path(__file__).resolve().parents[3]
CACHE = Path(os.environ.get("MIPSTARRE_CACHE_ROOT", Path.home() / ".cache/mipstarre-dev"))
DAEMON = CACHE / "watchdog" / "daemon"
LOCK = DAEMON / "space-cap5.lock"
LOG = DAEMON / "space-cap5.jsonl"
GITHUB_MAIN = "refs/heads/main"


READ_TIMEOUT_S = 30


def git(*args: str) -> str:
    return subprocess.check_output(["git", "-C", str(ROOT), *args],
                                   text=True, timeout=READ_TIMEOUT_S).strip()


def remote_main() -> str:
    rows = git("ls-remote", "--refs", "github", GITHUB_MAIN).splitlines()
    matches = [row.split()[0] for row in rows if row.split()[-1] == GITHUB_MAIN]
    if len(matches) != 1:
        raise RuntimeError("remote main is unreadable or ambiguous")
    return matches[0]


def runtime_gate() -> tuple[bool, str]:
    capacity = CACHE / "watchdog" / "primary-key-capacity"
    external = CACHE / "watchdog" / "primary-external-admission"
    if not capacity.exists() or capacity.read_text().strip() != "5":
        return False, "space capacity file is missing or not 5"
    if not external.exists() or external.read_text().strip() != "0":
        return False, "external admission gate is missing or not 0"
    return True, "space cap5/external0 verified"


def lock_quiet() -> tuple[bool, str]:
    for path in sorted((CACHE / "locks").glob("fix-*.lock")):
        with path.open("a+") as handle:
            try:
                fcntl.flock(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                return False, f"active fix lock: {path.name}"
            finally:
                try:
                    fcntl.flock(handle.fileno(), fcntl.LOCK_UN)
                except OSError:
                    pass
    return True, "no active fix locks"


class ReadTimeout(RuntimeError):
    pass


def _alarm(_signum: int, _frame: Any) -> None:
    raise ReadTimeout("GitHub eligibility read exceeded its bounded timeout")


def eligible_prs(remote: str) -> list[dict]:
    sys.path.insert(0, str(ROOT / "local" / "bin"))
    import gh_common

    now = datetime.now(timezone.utc)
    result = []
    for pr in gh_common.api("pulls?state=open&per_page=100") or []:
        if pr.get("draft"):
            continue
        number = int(pr["number"])
        head = pr.get("head", {}).get("sha")
        if not head:
            continue
        statuses = gh_common.latest_statuses(head)
        if statuses.get("local-ci/summary", {}).get("state") != "success":
            continue
        if statuses.get("local-review/summary", {}).get("state") != "success":
            continue
        marker = False
        unresolved = 0
        for review in gh_common.pr_reviews(number):
            body = review.get("body") or ""
            if f"head={head}" not in body:
                continue
            marker = True
            if "VERDICT: APPROVED" in body or (
                    "VERDICT: COMMENTED" in body and "- [ ]" not in body):
                unresolved += body.count("- [ ]")
                if unresolved == 0:
                    fresh = subprocess.run(
                        ["git", "-C", str(ROOT), "merge-base", "--is-ancestor",
                         remote, head], timeout=READ_TIMEOUT_S).returncode == 0
                    result.append(dict(number=number, head=head,
                                       created=pr["created_at"],
                                       pr_age_s=int((now - datetime.fromisoformat(
                                           pr["created_at"].replace("Z", "+00:00"))).total_seconds()),
                                       branch=pr["head"]["ref"], marker=marker,
                                       fresh_against_remote=fresh,
                                       eligibility_age_s=None))
                    break
    return sorted(result, key=lambda row: row["created"])


def tick(merge: bool) -> dict:
    started = time.monotonic()
    local = remote = None
    clean = False
    reason = None
    reasons: list[str] = []
    try:
        local = git("rev-parse", "main")
        clean = not bool(git("status", "--porcelain", "--untracked-files=all"))
        remote = remote_main()
        if not clean:
            reasons.append("primary worktree is dirty")
        if local != remote:
            reasons.append(f"local main {local[:12]} != remote {remote[:12]}")
        ok, reason = runtime_gate()
        if not ok:
            reasons.append(reason)
        locks_ok, lock_reason = lock_quiet()
        if not locks_ok:
            reasons.append(lock_reason)
        signal.signal(signal.SIGALRM, _alarm)
        signal.alarm(READ_TIMEOUT_S)
        candidate = eligible_prs(remote)
        signal.alarm(0)
    except Exception as exc:
        signal.alarm(0)
        candidate = []
        reasons.append(f"read_failure: {type(exc).__name__}: {exc}")
        clean = False
    fresh_candidates = [row for row in candidate if row.get("fresh_against_remote")]
    stale_candidates = [row for row in candidate if not row.get("fresh_against_remote")]
    oldest = fresh_candidates[0] if fresh_candidates else None
    if stale_candidates:
        reasons.append("stale eligible PRs: " + ",".join(str(r["number"]) for r in stale_candidates))
    record = dict(ts=datetime.now(timezone.utc).isoformat(), local_main=local,
                  remote_main=remote, clean=clean, runtime=reason,
                  oldest_eligible=oldest, oldest_stale=stale_candidates,
                  oldest_fresh_against_remote=bool(oldest),
                  eligible_count=len(candidate), fresh_count=len(fresh_candidates),
                  eligible_age_s=None,
                  external_admission=0, owner_total_limit=5,
                  native_descendant_limit=4, hold_reasons=reasons,
                  action="hold", duration_s=round(time.monotonic() - started, 3))
    if not reasons and oldest and merge:
        record["action"] = "delegate-pr_merge"
        record["merge_exit"] = subprocess.run(
            [sys.executable, str(ROOT / "local" / "bin" / "pr_merge.py"),
             str(oldest["number"])], timeout=3600).returncode
    elif not oldest:
        record["hold_reasons"].append("no fresh exact-head CI/review-eligible PR")
    DAEMON.mkdir(parents=True, exist_ok=True)
    with LOG.open("a", encoding="utf-8") as handle:
        fcntl.flock(handle.fileno(), fcntl.LOCK_EX)
        handle.write(json.dumps(record, sort_keys=True) + "\n")
        handle.flush()
        os.fsync(handle.fileno())
        fcntl.flock(handle.fileno(), fcntl.LOCK_UN)
    print(json.dumps(record, sort_keys=True))
    return record


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--merge", action="store_true",
                        help="delegate one eligible merge to pr_merge.py after checks")
    parser.add_argument("--once", action="store_true", help="run one tick")
    parser.add_argument("--interval", type=int, default=300)
    args = parser.parse_args()
    if args.interval < 5:
        parser.error("--interval must be at least 5 seconds")
    with LOCK.open("a+") as handle:
        try:
            fcntl.flock(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise SystemExit("space-cap5 merge service already owns its lock")
        try:
            while True:
                record = tick(args.merge)
                if args.once:
                    return 0
                time.sleep(max(0, args.interval - float(record["duration_s"])))
        finally:
            fcntl.flock(handle.fileno(), fcntl.LOCK_UN)


if __name__ == "__main__":
    raise SystemExit(main())
