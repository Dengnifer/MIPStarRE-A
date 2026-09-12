#!/usr/bin/env python3
"""daemon-scan.py — the merge daemon's Python helper (promoted from /tmp, 2026-09-12).

Historically this file held only the candidate scan.  It now also owns every
*record format* the daemon reads and writes, so that the formats have one
writer, one reader and a unit test instead of being re-derived by `grep` in
bash (full-speed-mode v2 design §3.2-§3.5, work item W5).

Subcommands
    scan           one GraphQL call -> one line per open PR:
                   ``PR:N:BRANCH:SLUG:MODE:HEAD`` with MODE in
                   clean | adj | retire | offconv | skip.  Without ``--all``
                   only clean/adj/retire lines are printed, which is the
                   historical output plus the retirement pass.
    classify       classify a lane / merge log into one of the six failure
                   classes, printing ``CLASS<TAB>REASON``.
    marker-write   write (or refresh) a classed failure marker, the JSON
                   record that replaced ``touch pr<N>.failed``.
    marker-check   decide whether a marker still blocks its PR.  Exit 0 =
                   blocked, 10 = clear, 2 = usage.
    marker-list    one line per live marker, for the hourly report; with
                   ``--json-out`` also the machine-readable snapshot that
                   ready_report.py reads instead of guessing a reason.
    latency        append one ``merge-latency`` row.
    par            the adaptive parallelism formula, with its inputs.
    slots          free worker slots, read through local/bin/account_router.py.

The marker record is::

    {"pr": 342, "head": "<sha>", "ts": 1757650000, "class": "build",
     "reason": "lake build before push failed (see ...)", "attempts": 2,
     "lane_log": "/.../342.lane.log", "tools_version": "v9-g1a2b3c4",
     "tools_ts": 1757649000}

Clearing rules (design §3.3).  A marker is cleared on an OBSERVABLE change,
never on elapsed time alone -- except for the two classes whose backoff *is*
the documented retry (infra 5 min, preflight 15 min):

    class         blocked until
    ------------  --------------------------------------------------------
    conflict      the repair finishes (or the head changes)
    build         the repair finishes, the head changes, or a newer
                  installed tools-version supersedes the marker
    preflight     15 min elapse, the head changes, or a newer tools-version
    infra         5 min elapse (bounded by ``--infra-max-attempts``) or the
                  head changes
    gate          the head changes
    adjudication  the head changes

The tools-version rule is the 05:44Z case of 2026-09-12: eleven unrelated PRs
stayed blocked by 2 h markers after the systemic lane bugs had been fixed, and
were freed by hand with ``rm`` and with ``( sleep 1500; rm -f ... )``.

Usage stays backward compatible: ``daemon-scan.py <adj-list>`` is the old
candidate scan.
"""

from __future__ import annotations

import argparse
import json
import math
import os
import re
import subprocess
import sys
import time
from pathlib import Path

REPO_DEFAULT = os.environ.get("MIPSTARRE_GITHUB_REPO", "Dengnifer/MIPStarRE-A")

#: pr_open.py:37 — the branch convention a lane may exist for.  Kept
#: behaviourally identical to ``pr_open.BRANCH_RE`` (scripts/tests/
#: test_lane_branch_identity.py compares the two against the same corpus).
BRANCH_RE = re.compile(r"^(?:(codex|claude)/)?issue-(\d+)-([a-z0-9][a-z0-9-]*)$")

#: Historical, lenient form (``issue-0*<n>-<anything>``) used only to give an
#: off-convention branch a number in the report; a lane is never launched for
#: one (lane.sh warns and stops rather than silently renumbering).
LENIENT_RE = re.compile(r"^(?:[a-z]+/)?issue-0*(\d+)-(.*)$")

CLASSES = ("conflict", "build", "preflight", "infra", "gate", "adjudication")

#: Seconds; -1 means "not a time backoff" (see the table in the docstring).
BACKOFF_REPAIR = -1
BACKOFF_HEAD = -2
DEFAULT_BACKOFF = {
    "conflict": BACKOFF_REPAIR,
    "build": BACKOFF_REPAIR,
    "preflight": 900,
    "infra": 300,
    "gate": BACKOFF_HEAD,
    "adjudication": BACKOFF_HEAD,
}

#: A newer installed tools-version clears exactly these classes: they are the
#: failures a tool fix can have repaired.  A conflict or a gate refusal is a
#: property of the branch, not of the tools.
TOOLS_VERSION_CLEARS = ("preflight", "build")

#: Lane-log / needs-attention patterns, most specific first.  The log is read
#: BACKWARDS and the first matching line wins: the last observed failure is
#: the one that classifies the lane.
LANE_PATTERNS = [
    (r"merging github/main conflicted", "conflict"),
    (r"reason=merge-conflicted", "conflict"),
    (r"^CONFLICT \(", "conflict"),
    (r"Automatic merge failed", "conflict"),
    (r"lake build[^\n]*fail", "build"),
    (r"reason=build-failed", "build"),
    (r"pre-push gate failed", "preflight"),
    (r"MIPStarRE pre-push:[^\n]*(fail|refus)", "preflight"),
    (r"checked-push[^\n]*fail", "preflight"),
    (r"pr_open failed", "preflight"),
    (r"reason=(pr-open-failed|gate-failed)", "preflight"),
    (r"Reconnecting\.\.\. \d+/5", "infra"),
    (r"\b503\b", "infra"),
    (r"Service Unavailable", "infra"),
    (r"Bad Gateway", "infra"),
    (r"[Cc]oncurrency limit exceeded", "infra"),
    (r"concurrency_limit", "infra"),
    (r"429 Too Many Requests", "infra"),
    (r"reason=(no-slot|codex-paused|fetch-failed|build-lock-timeout)", "infra"),
    (r"left paths missing that main carries", "gate"),
    (r"reason=(worktree-mismatch|lane-id-mismatch|branch-off-convention)", "gate"),
    (r"reason=(issue-missing|no-commits-ahead|uncommitted-worker-changes)", "gate"),
    (r"reason=(worktree-add-failed|merge-loss-guard|no-capacity-record)", "gate"),
]

#: merge.sh / pr_merge.py output patterns.
MERGE_PATTERNS = [
    (r"no adjudication template", "adjudication"),
    (r"adjudicat", "adjudication"),
    (r"REBASE_FAILED", "conflict"),
    (r"conflict", "conflict"),
    (r"would be overwritten by merge", "infra"),
    (r"\b50[0234]\b", "infra"),
    (r"Service Unavailable", "infra"),
    (r"timed out|timeout", "infra"),
    (r"gate \d", "gate"),
    (r"not fresh|stale|is not an ancestor", "gate"),
    (r"MERGE_FAILED", "gate"),
]

REASON_MAX = 300


# ---------------------------------------------------------------------------
# small helpers
# ---------------------------------------------------------------------------

def _run(args: list[str], timeout: int = 60) -> subprocess.CompletedProcess:
    return subprocess.run(args, capture_output=True, text=True, timeout=timeout)


def _clip(text: str) -> str:
    text = " ".join((text or "").split())
    return text[:REASON_MAX]


def _int(value, default: int = 0) -> int:
    try:
        return int(str(value).strip())
    except (TypeError, ValueError):
        return default


def read_adj(path) -> set[str]:
    if not path:
        return set()
    try:
        return set(Path(path).read_text(encoding="utf-8").split())
    except OSError:
        return set()


# ---------------------------------------------------------------------------
# scan
# ---------------------------------------------------------------------------

GRAPHQL = '''query { repository(owner:"%s", name:"%s") { pullRequests(states:OPEN, first:100, orderBy:{field:UPDATED_AT, direction:DESC}) { nodes {
  number headRefName headRefOid isDraft
  commits(last:1) { nodes { commit { status { contexts { context state } } } } }
  reviews(last:8) { nodes { body } } } } } }'''


def graphql_open_prs(repo: str, timeout: int) -> list[dict]:
    owner, _, name = repo.partition("/")
    query = GRAPHQL % (owner, name)
    try:
        out = _run(["gh", "api", "graphql", "-f", f"query={query}"], timeout=timeout)
    except subprocess.TimeoutExpired:
        print("scan: graphql timeout", file=sys.stderr)
        raise SystemExit(1)
    if out.returncode != 0:
        print("scan: graphql failed: " + (out.stderr or out.stdout)[:200], file=sys.stderr)
        raise SystemExit(1)
    try:
        return json.loads(out.stdout)["data"]["repository"]["pullRequests"]["nodes"]
    except (KeyError, TypeError, json.JSONDecodeError) as error:
        print(f"scan: unreadable graphql payload: {error}", file=sys.stderr)
        raise SystemExit(1)


def retire_reason(head: str, base: str) -> str:
    """Mechanical retirement test (design §3.5 / §2 Item 8), read-only.

    A PR whose head is already reachable from main, or whose three-dot diff
    against main is empty, contributes nothing: it must never enter a
    candidate list, absorb a refresh, or inflate the ready-but-open count.
    Closing it is pr_janitor.py's decision, not this scan's.
    """
    if not head:
        return ""
    try:
        if _run(["git", "cat-file", "-e", head + "^{commit}"], timeout=30).returncode != 0:
            return ""
        if _run(["git", "merge-base", "--is-ancestor", head, base], timeout=30).returncode == 0:
            return "head-on-main"
        if _run(["git", "diff", "--quiet", f"{base}...{head}"], timeout=60).returncode == 0:
            return "empty-diff"
    except (subprocess.TimeoutExpired, OSError):
        return ""
    return ""


def cmd_scan(args: argparse.Namespace) -> int:
    adj = read_adj(args.adj_list)
    nodes = graphql_open_prs(args.repo, args.timeout)
    counts = {"clean": 0, "adj": 0, "retire": 0, "offconv": 0, "skip": 0}
    for pr in nodes:
        num = str(pr.get("number") or "")
        branch = pr.get("headRefName") or ""
        head = pr.get("headRefOid") or ""
        if not num or not branch:
            continue
        strict = BRANCH_RE.match(branch)
        lenient = LENIENT_RE.match(branch)
        if strict:
            lane, slug = str(int(strict.group(2))), strict.group(3)
        elif lenient:
            lane, slug = str(int(lenient.group(1))), (lenient.group(2) or "-")
        else:
            lane, slug = "-", "-"

        mode = ""
        if not args.no_retire:
            why = retire_reason(head, args.base)
            if why:
                mode = "retire"
                print(f"scan: PR {num} retirable ({why})", file=sys.stderr)
        if not mode and not strict:
            mode = "offconv"
        if not mode:
            contexts = {}
            for node in pr.get("commits", {}).get("nodes") or []:
                status = ((node or {}).get("commit") or {}).get("status") or {}
                for entry in status.get("contexts") or []:
                    contexts[entry["context"]] = entry["state"]
            ci_green = contexts.get("local-ci/summary") == "SUCCESS"
            review_green = contexts.get("local-review/summary") == "SUCCESS"
            clean = False
            if ci_green and review_green:
                bodies = [r.get("body") or "" for r in (pr.get("reviews", {}).get("nodes") or [])
                          if "mipstarre-review" in (r.get("body") or "")
                          and f"head={head}" in (r.get("body") or "")]
                if bodies:
                    clean = not re.findall(r"^- \[ \]", bodies[-1], re.M)
            if ci_green and clean and not pr.get("isDraft"):
                mode = "clean"
            elif ci_green and num in adj:
                mode = "adj"
            else:
                mode = "skip"
        counts[mode] = counts.get(mode, 0) + 1
        if args.all or mode in ("clean", "adj", "retire"):
            print(f"{num}:{lane}:{branch}:{slug}:{mode}:{head}")
    print("scan: {} open PRs, {} candidates ({} clean, {} adj), {} retirable, "
          "{} off-convention, {} not ready".format(
              len(nodes), counts["clean"] + counts["adj"], counts["clean"], counts["adj"],
              counts["retire"], counts["offconv"], counts["skip"]), file=sys.stderr)
    return 0


# ---------------------------------------------------------------------------
# classify
# ---------------------------------------------------------------------------

def classify_text(text: str, source: str = "lane") -> tuple[str, str]:
    """Return ``(class, reason)`` for a lane or merge log.

    The log is read backwards so the LAST observed failure classifies the
    run: an infra hiccup in the middle followed by a build failure is a build
    failure, and vice versa.
    """
    patterns = MERGE_PATTERNS if source == "merge" else LANE_PATTERNS
    compiled = [(re.compile(rx), cls) for rx, cls in patterns]
    lines = [line.rstrip() for line in (text or "").splitlines() if line.strip()]
    for line in reversed(lines):
        for rx, cls in compiled:
            if rx.search(line):
                return cls, _clip(line)
    fallback = "gate" if source == "merge" else "infra"
    return fallback, _clip(lines[-1] if lines else "no output")


def cmd_classify(args: argparse.Namespace) -> int:
    text = ""
    for candidate in args.file:
        path = Path(candidate)
        if path.is_file() and path.stat().st_size:
            text = path.read_text(encoding="utf-8", errors="replace")
            break
    if args.tail and text:
        text = "\n".join(text.splitlines()[-args.tail:])
    cls, reason = classify_text(text, args.source)
    print(f"{cls}\t{reason}")
    return 0


# ---------------------------------------------------------------------------
# markers
# ---------------------------------------------------------------------------

def _pr_from_name(name: str) -> int:
    match = re.match(r"^pr(\d+)\.failed$", name)
    return int(match.group(1)) if match else 0


def load_marker(path: Path) -> dict:
    """Parse a marker, tolerating the historical ``touch``ed empty file.

    A marker that cannot be parsed is treated as class ``infra`` with the
    file's mtime, i.e. it self-clears after the infra backoff.  An
    unparseable file must never block a PR forever -- that is the bug this
    record format exists to remove.
    """
    try:
        raw = path.read_text(encoding="utf-8", errors="replace").strip()
    except OSError:
        return {}
    record = {}
    if raw:
        try:
            parsed = json.loads(raw)
            if isinstance(parsed, dict):
                record = parsed
        except json.JSONDecodeError:
            record = {}
    if not record:
        try:
            mtime = int(path.stat().st_mtime)
        except OSError:
            mtime = 0
        record = {"pr": _pr_from_name(path.name), "head": "", "ts": mtime, "class": "infra",
                  "reason": "legacy marker without a record", "attempts": 1,
                  "lane_log": "", "tools_version": "", "legacy": True}
    record.setdefault("pr", _pr_from_name(path.name))
    record.setdefault("head", "")
    record.setdefault("ts", 0)
    record.setdefault("class", "infra")
    record.setdefault("reason", "")
    record.setdefault("attempts", 1)
    record.setdefault("lane_log", "")
    record.setdefault("tools_version", "")
    if record["class"] not in CLASSES:
        record["class"] = "infra"
    return record


def _tools_newer(record: dict, tools_version: str, tools_ts) -> bool:
    marker_version = (record.get("tools_version") or "").strip()
    marker_ts = record.get("tools_ts")
    if tools_ts is not None and isinstance(marker_ts, (int, float)):
        return int(tools_ts) > int(marker_ts)
    if not marker_version:
        # The marker predates tool versioning; there is nothing to compare, so
        # do not claim an upgrade happened.
        return False
    return bool(tools_version) and tools_version != marker_version


def decide(record: dict, *, head: str = "", tools_version: str = "", tools_ts=None,
           repair_state: str = "none", reason_gone: bool = False, now=None,
           backoff: dict | None = None, infra_max_attempts: int = 5) -> tuple[str, str, int]:
    """Return ``(decision, why, seconds_remaining)``; decision is block|clear."""
    now = int(time.time()) if now is None else int(now)
    table = dict(DEFAULT_BACKOFF)
    if backoff:
        table.update({k: int(v) for k, v in backoff.items() if v is not None})
    cls = record.get("class", "infra")
    marker_head = (record.get("head") or "").strip()
    if head and marker_head and head != marker_head:
        return "clear", "head-changed", 0
    if cls in TOOLS_VERSION_CLEARS and _tools_newer(record, tools_version, tools_ts):
        return "clear", "tools-version", 0
    if reason_gone:
        return "clear", "reason-gone", 0
    if cls in ("conflict", "build"):
        if repair_state == "done":
            return "clear", "repair-finished", 0
        if repair_state == "running":
            return "block", "repair-running", -1
        if repair_state == "exhausted":
            return "block", "repair-exhausted", -1
        return "block", "awaiting-repair", -1
    if cls in ("gate", "adjudication"):
        return "block", "awaiting-head-change", -1
    wait = table.get(cls, 300)
    if wait < 0:
        return "block", "awaiting-head-change", -1
    if cls == "infra" and _int(record.get("attempts"), 1) > infra_max_attempts:
        return "block", "infra-attempts-exhausted", -1
    age = max(0, now - _int(record.get("ts")))
    if age >= wait:
        return "clear", "backoff-elapsed", 0
    return "block", "backoff", wait - age


def cmd_marker_write(args: argparse.Namespace) -> int:
    path = Path(args.path)
    previous = load_marker(path) if path.exists() else {}
    attempts = 1
    if previous and (not args.head or previous.get("head") == args.head):
        attempts = _int(previous.get("attempts"), 0) + 1
    record = {
        "pr": _int(args.pr),
        "head": args.head or "",
        "ts": _int(args.ts, int(time.time())) if args.ts else int(time.time()),
        "class": args.cls if args.cls in CLASSES else "infra",
        "reason": _clip(args.reason),
        "attempts": attempts,
        "lane_log": args.lane_log or "",
        "tools_version": args.tools_version or "",
    }
    if args.tools_ts is not None:
        record["tools_ts"] = _int(args.tools_ts)
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(path.name + ".tmp")
    tmp.write_text(json.dumps(record, sort_keys=True) + "\n", encoding="utf-8")
    os.replace(tmp, path)
    print(f"{record['class']}\t{record['attempts']}")
    return 0


def cmd_marker_check(args: argparse.Namespace) -> int:
    path = Path(args.path)
    if not path.exists():
        print("clear absent 0 - :: no marker")
        return 10
    record = load_marker(path)
    backoff = {}
    if args.backoff_infra is not None:
        backoff["infra"] = args.backoff_infra
    if args.backoff_preflight is not None:
        backoff["preflight"] = args.backoff_preflight
    decision, why, remaining = decide(
        record, head=args.head or "", tools_version=args.tools_version or "",
        tools_ts=args.tools_ts, repair_state=args.repair_state,
        reason_gone=args.reason_gone, now=args.now, backoff=backoff,
        infra_max_attempts=args.infra_max_attempts)
    print("{} {} {} {} :: {}".format(decision, why, remaining, record["class"],
                                     record.get("reason", "")))
    return 0 if decision == "block" else 10


def cmd_marker_list(args: argparse.Namespace) -> int:
    directory = Path(args.dir)
    now = int(time.time()) if args.now is None else int(args.now)
    records = []
    for path in sorted(directory.glob("pr*.failed")):
        record = load_marker(path)
        record["age_s"] = max(0, now - _int(record.get("ts")))
        record["path"] = str(path)
        records.append(record)
    for record in records:
        print("pr{} class={} attempts={} age={}m head={} reason={}".format(
            record.get("pr"), record.get("class"), record.get("attempts"),
            record["age_s"] // 60, (record.get("head") or "-")[:8],
            record.get("reason") or "-"))
    if args.json_out:
        out = Path(args.json_out)
        out.parent.mkdir(parents=True, exist_ok=True)
        tmp = out.with_name(out.name + ".tmp")
        tmp.write_text(json.dumps({"generated": now, "markers": records}, sort_keys=True) + "\n",
                       encoding="utf-8")
        os.replace(tmp, out)
    return 0


# ---------------------------------------------------------------------------
# latency, par, slots
# ---------------------------------------------------------------------------

LATENCY_EVENTS = ("ready", "refresh_start", "refresh_end", "merged", "failed")


def cmd_latency(args: argparse.Namespace) -> int:
    if args.event not in LATENCY_EVENTS:
        print(f"latency: unknown event {args.event}", file=sys.stderr)
        return 2
    row = {
        "ts": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "pr": _int(args.pr),
        "head": args.head or "",
        "event": args.event,
        "class": args.cls or "",
        "reason": _clip(args.reason),
        "seconds": _int(args.seconds),
        "par": _int(args.par),
    }
    path = Path(args.file)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(row, sort_keys=True) + "\n")
    return 0


def adaptive_par(nproc, load1, cores_per_build, free_slots) -> int:
    """PAR = clamp(1, floor((nproc - load1) / cores_per_build), free_worker_slots).

    Re-evaluated every loop, so other users' load on the shared host throttles
    us instead of the owner typing ``PAR=8`` (2026-09-12 05:44Z).  The lower
    clamp is 1: one refresh is always allowed, even with no free worker slot,
    because a refresh that needs no new codex session still makes progress.
    """
    cores = max(1, _int(cores_per_build, 16))
    try:
        headroom = float(nproc) - float(load1)
    except (TypeError, ValueError):
        headroom = 0.0
    value = int(math.floor(headroom / cores))
    return max(1, min(value, _int(free_slots, 0)))


def cmd_par(args: argparse.Namespace) -> int:
    print(adaptive_par(args.nproc, args.load1, args.cores_per_build, args.free_slots))
    return 0


def _alive(pid: int) -> bool:
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    except OSError:
        return False
    return True


def cmd_slots(args: argparse.Namespace) -> int:
    """Print ``free live cap`` for the worker pool.

    The account names and the cap-file convention come from
    local/bin/account_router.py, the one component that owns them; the live
    count is read-only here (the router reaps dead markers under its own
    lock, and a monitoring read must not race with it).
    """
    cache = Path(args.cache_root)
    sys.path.insert(0, str(Path(args.checkout) / "local" / "bin"))
    try:
        import account_router  # noqa: E402
        accounts = list(account_router.ACCOUNTS)
    except Exception:  # pragma: no cover - fallback for a partial checkout
        accounts = ["primary", "second"]
    cap = live = 0
    seen = False
    for account in accounts:
        path = cache / "watchdog" / f"max-codex-{account}"
        if path.exists():
            seen = True
            cap += max(0, _int(path.read_text(), 0))
        directory = cache / "accounts" / account
        if directory.is_dir():
            live += sum(1 for entry in directory.iterdir()
                        if entry.name.isdecimal() and _alive(int(entry.name)))
    if not seen:
        aggregate = cache / "watchdog" / "max-codex"
        if not aggregate.exists():
            print("0 0 0")
            return 3
        cap = max(0, _int(aggregate.read_text(), 0))
    print(f"{max(0, cap - live)} {live} {cap}")
    return 0


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="daemon-scan.py", description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="command")

    scan = sub.add_parser("scan", help="candidate scan in one GraphQL call")
    scan.add_argument("--adj-list")
    scan.add_argument("--repo", default=REPO_DEFAULT)
    scan.add_argument("--base", default="github/main")
    scan.add_argument("--timeout", type=int, default=120)
    scan.add_argument("--all", action="store_true",
                      help="also print skip/offconv lines (the daemon needs them for GC)")
    scan.add_argument("--no-retire", action="store_true")
    scan.set_defaults(func=cmd_scan)

    classify = sub.add_parser("classify", help="classify a lane or merge log")
    classify.add_argument("file", nargs="+", help="first readable non-empty file wins")
    classify.add_argument("--source", choices=("lane", "merge"), default="lane")
    classify.add_argument("--tail", type=int, default=400)
    classify.set_defaults(func=cmd_classify)

    write = sub.add_parser("marker-write", help="write a classed failure marker")
    write.add_argument("--path", required=True)
    write.add_argument("--pr", required=True)
    write.add_argument("--head", default="")
    write.add_argument("--class", dest="cls", required=True, choices=CLASSES)
    write.add_argument("--reason", default="")
    write.add_argument("--lane-log", default="")
    write.add_argument("--tools-version", default="")
    write.add_argument("--tools-ts", type=int, default=None)
    write.add_argument("--ts", type=int, default=None)
    write.set_defaults(func=cmd_marker_write)

    check = sub.add_parser("marker-check", help="does this marker still block its PR?")
    check.add_argument("--path", required=True)
    check.add_argument("--head", default="")
    check.add_argument("--tools-version", default="")
    check.add_argument("--tools-ts", type=int, default=None)
    check.add_argument("--repair-state", choices=("none", "running", "done", "exhausted"),
                       default="none")
    check.add_argument("--reason-gone", action="store_true")
    check.add_argument("--now", type=int, default=None)
    check.add_argument("--backoff-infra", type=int, default=None)
    check.add_argument("--backoff-preflight", type=int, default=None)
    check.add_argument("--infra-max-attempts", type=int, default=5)
    check.set_defaults(func=cmd_marker_check)

    listing = sub.add_parser("marker-list", help="one line per live marker")
    listing.add_argument("--dir", required=True)
    listing.add_argument("--json-out", default="")
    listing.add_argument("--now", type=int, default=None)
    listing.set_defaults(func=cmd_marker_list)

    latency = sub.add_parser("latency", help="append one merge-latency row")
    latency.add_argument("--file", required=True)
    latency.add_argument("--pr", required=True)
    latency.add_argument("--head", default="")
    latency.add_argument("--event", required=True)
    latency.add_argument("--class", dest="cls", default="")
    latency.add_argument("--reason", default="")
    latency.add_argument("--seconds", default="0")
    latency.add_argument("--par", default="0")
    latency.set_defaults(func=cmd_latency)

    par = sub.add_parser("par", help="the adaptive parallelism formula")
    par.add_argument("--nproc", required=True)
    par.add_argument("--load1", required=True)
    par.add_argument("--cores-per-build", required=True)
    par.add_argument("--free-slots", required=True)
    par.set_defaults(func=cmd_par)

    slots = sub.add_parser("slots", help="free worker slots (free live cap)")
    slots.add_argument("--cache-root", default=str(Path.home() / ".cache" / "mipstarre-dev"))
    slots.add_argument("--checkout", default=str(Path.home() / "MIPStarRE-qpbt"))
    slots.set_defaults(func=cmd_slots)

    return parser


def main(argv: list[str] | None = None) -> int:
    argv = list(sys.argv[1:] if argv is None else argv)
    known = {"scan", "classify", "marker-write", "marker-check", "marker-list",
             "latency", "par", "slots"}
    if not argv or argv[0] not in known:
        # Legacy call shape: daemon-scan.py [adj-list-file]
        argv = ["scan"] + (["--adj-list", argv[0]] if argv else [])
    parser = build_parser()
    args = parser.parse_args(argv)
    if not getattr(args, "func", None):
        parser.print_help()
        return 2
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
