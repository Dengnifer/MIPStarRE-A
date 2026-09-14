#!/usr/bin/env python3
"""pause_landing.py — the soft landing of a pause, and the work half of a resume.

`owner-pause.sh` used to end with one blanket kill: at deadline minus two
minutes every process matching an anchored pattern was SIGTERMed.  A codex
session has already paid for its input and its reasoning by then, so a kill
throws that away and the resume pays for it again — 17 sessions died mid-work
on 2026-09-12, and on 2026-09-14 the fallout was reviewers that "exited 143",
kill-caused `daemon/pr<N>.failed` markers that made the merge daemon skip those
PRs for two hours, and lanes restarted from scratch on heads that already
carried a green CI and a finished review.

This module is the part of the pause that knows *what is running*.  It:

  * resolves the landing thresholds from `local/capacity-policy.json`
    (`landing`), the single home for them — no number below reaches a shell
    script, and the fallbacks here are used only when that file is missing;
  * classifies every live codex session by role and elapsed time into
    `stop-now` (young: little sunk cost), `finish` (a mature reviewer, which
    usually finishes, so it runs until the last minute) and `checkpoint` (a
    mature writer, whose worktree, thread id and step are recorded and which is
    stopped only at the last minute);
  * stops what the rule says to stop, SIGTERM first and SIGKILL after the
    recorded grace, and never signals a pid whose command line does not match
    the session it is recorded as;
  * builds the pause manifest — the lanes with the step they reached and the
    statuses already on their head, the stopped sessions with thread id, role,
    worktree, elapsed time and whether they are resumable, and the
    `daemon/pr<N>.failed` markers that appeared *during* the landing;
  * and turns that manifest back into a resume plan: each parked lane relaunched
    at the step it reached, each checkpointed prover resumed through
    `dispatch.sh --resume <thread>` with a continue prompt, each stopped
    reviewer restarted from scratch, and each recorded failed marker cleared.

The plan is data.  `resume-plan` prints commands; it runs none of them.

Usage:
  pause_landing.py thresholds [--json]
  pause_landing.py classify   [--json] [--now EPOCH]
  pause_landing.py manifest   [--cutoff-at TS] [--no-github] [--now EPOCH]
  pause_landing.py land --phase now|last [--state FILE] [--dry-run]
  pause_landing.py resume-plan [--state FILE] [--json]
  pause_landing.py resume-exec [--state FILE] [--log FILE] [--dry-run]

Environment: MIPSTARRE_CACHE_ROOT (runtime state root), MIPSTARRE_REPO_ROOT
  (the checkout whose `local/` tools the plan names), MIPSTARRE_CHECKOUT
  (the primary checkout a lane runs in; defaults to the repo root).

Exit codes: 0 ok · 2 usage · 3 no usable pause record.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import signal
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

SCHEMA = "mipstarre-pause-landing/1"

#: The landing thresholds, as documented fallbacks.  `local/capacity-policy.json`
#: is their home; these values are what that file ships with, and they are used
#: only when it is missing or unreadable, so a pause never fails for want of a
#: number.  Nothing else in the layer carries them: the shell scripts ask this
#: module.
DEFAULTS = {
    "phases": {"landing_lead_s": 180, "last_call_s": 90, "grace_s": 20},
    "young_max_min": 5,
    "cutoff_lead_min": 10,
    "roles": {
        "default": {"mature": "checkpoint", "resume": "thread"},
        "reviewer": {"mature": "finish", "resume": "restart"},
        "scout": {"mature": "finish", "resume": "restart"},
    },
}

#: The two statuses a lane's head carries once its CI and its review have
#: passed (`local/bin/ci.sh`, `local/bin/review.sh`; `pr_merge.py` gates on the
#: same two).  A resume that finds both `success` on an unchanged head runs
#: neither step again.
CI_STATUS = "local-ci/summary"
REVIEW_STATUS = "local-review/summary"

#: The lane steps, in the order `lane.sh` performs them.  A parked lane resumes
#: at the earliest step whose evidence is missing.
LANE_STEPS = ("warm", "dispatch", "publish", "ci", "review", "done")

#: The continue prompt a checkpointed writer is resumed with.  It says the two
#: things the session cannot know after a kill: that its worktree still holds
#: its work, and that the milestone-commit rule applies from here on.
CONTINUE_PROMPT = (
    "The run was paused by the owner and this session was stopped mid-work; it is "
    "resumed now. Your worktree is exactly as you left it, including any uncommitted "
    "edits: read it first (git status, git diff, git log) and continue from that state "
    "rather than restarting the task. Commit each proved lemma in the worktree, with "
    "the hooks running, before starting the next one, so a later interruption costs at "
    "most the work since your last commit. Do not push."
)

LANE_RE = re.compile(r"^bash\s+\S*lane(-v\d+)?\.sh\s+(\d+)(?:\s+(\S+))?(?:\s+(\S+))?")
FAILED_MARKER_RE = re.compile(r"^pr(\d+)\.failed$")


# ---------------------------------------------------------------------------
# Locations
# ---------------------------------------------------------------------------

def cache_root() -> Path:
    return Path(os.environ.get("MIPSTARRE_CACHE_ROOT",
                               "~/.cache/mipstarre-dev")).expanduser()


def repo_root() -> Path:
    override = os.environ.get("MIPSTARRE_REPO_ROOT")
    if override:
        return Path(override).expanduser()
    return Path(__file__).resolve().parents[2]


def checkout_root() -> Path:
    override = os.environ.get("MIPSTARRE_CHECKOUT")
    return Path(override).expanduser() if override else repo_root()


def watchdog_dir(root: Path | None = None) -> Path:
    return (root or cache_root()) / "watchdog"


def utcnow() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


# ---------------------------------------------------------------------------
# Thresholds
# ---------------------------------------------------------------------------

def policy_path(root: Path | None = None) -> Path:
    return (root or repo_root()) / "local" / "capacity-policy.json"


def _merge(base: dict, over) -> dict:
    """Shallow-recursive overlay: `over` wins key by key, `base` fills the rest."""
    out = dict(base)
    if not isinstance(over, dict):
        return out
    for key, value in over.items():
        if isinstance(out.get(key), dict) and isinstance(value, dict):
            out[key] = _merge(out[key], value)
        else:
            out[key] = value
    return out


def thresholds(root: Path | None = None) -> dict:
    """The resolved landing thresholds, and where they came from."""
    path = policy_path(root)
    try:
        doc = json.loads(path.read_text(encoding="utf-8"))
        briefed = doc.get("landing")
        source = str(path) if isinstance(briefed, dict) else f"{path} (no 'landing' table)"
    except (OSError, ValueError):
        briefed, source = None, f"{path} (unreadable; module defaults)"
    out = _merge(DEFAULTS, briefed if isinstance(briefed, dict) else {})
    out["source"] = source
    phases = out["phases"]
    # The two offsets are measured back from the deadline, so the landing must
    # come first and both must leave room for the grace.  A policy that says
    # otherwise is corrected here rather than at the deadline.
    for key in ("landing_lead_s", "last_call_s", "grace_s"):
        value = phases.get(key)
        if not isinstance(value, int) or isinstance(value, bool) or value < 0:
            phases[key] = DEFAULTS["phases"][key]
    if phases["last_call_s"] >= phases["landing_lead_s"]:
        phases["landing_lead_s"] = phases["last_call_s"] + DEFAULTS["phases"]["grace_s"]
    for key in ("young_max_min", "cutoff_lead_min"):
        value = out.get(key)
        if not isinstance(value, int) or isinstance(value, bool) or value < 0:
            out[key] = DEFAULTS[key]
    return out


def role_rule(limits: dict, role: str) -> dict:
    roles = limits.get("roles") or {}
    default = _merge(DEFAULTS["roles"]["default"], roles.get("default"))
    return _merge(default, roles.get(role))


# ---------------------------------------------------------------------------
# The process table, behind one seam so a test can supply fake pids
# ---------------------------------------------------------------------------

class Processes:
    """Every read of and every signal to the live process table."""

    def alive(self, pid: int) -> bool:
        try:
            os.kill(pid, 0)
        except ProcessLookupError:
            return False
        except PermissionError:
            return True
        except OSError:
            return False
        return True

    def cmdline(self, pid: int) -> str:
        try:
            raw = Path(f"/proc/{pid}/cmdline").read_bytes()
        except OSError:
            return ""
        return raw.replace(b"\0", b" ").decode("utf-8", "replace").strip()

    def started_at(self, pid: int) -> float | None:
        """Process start time as an epoch.  On Linux the /proc entry's ctime is
        it; this is the fallback for a session whose record carries no start."""
        try:
            return Path(f"/proc/{pid}").stat().st_ctime
        except OSError:
            return None

    def pids(self) -> list[int]:
        try:
            return sorted(int(name) for name in os.listdir("/proc") if name.isdecimal())
        except OSError:
            return []

    def signal(self, pid: int, sig: int) -> bool:
        try:
            os.kill(pid, sig)
        except OSError:
            return False
        return True

    def sleep(self, seconds: float) -> None:
        time.sleep(seconds)


# ---------------------------------------------------------------------------
# Live sessions
# ---------------------------------------------------------------------------

def _iso(epoch: float | None) -> str | None:
    if epoch is None:
        return None
    return datetime.fromtimestamp(epoch, timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _parse_ts(text) -> float | None:
    """One timestamp, in either shape the layer writes.

    `dispatch.sh` spools `date +%Y-%m-%dT%H:%M:%S%z`, whose offset has no colon
    (`+0900`), and `datetime.fromisoformat` rejects that before Python 3.11 —
    which would make every live session look like it had just started, and the
    landing would then class a two-hour prover as young and kill it.
    """
    if not isinstance(text, str) or not text.strip():
        return None
    value = text.strip()
    if value.endswith("Z"):
        value = value[:-1] + "+00:00"
    elif re.search(r"[+-]\d{4}$", value):
        value = value[:-2] + ":" + value[-2:]
    try:
        parsed = datetime.fromisoformat(value)
    except ValueError:
        return None
    if parsed.tzinfo is None:
        parsed = parsed.replace(tzinfo=timezone.utc)
    return parsed.timestamp()


def thread_of(name: str, root: Path | None = None) -> str | None:
    """The codex thread id of a session that is still running.

    `dispatch.sh` prints the thread id only when codex returns, and the registry
    row is appended then too — neither exists yet for a session the landing is
    about to stop.  The live capture does: `codex exec --json` emits
    `thread.started` as its first event and `dispatch.sh` tees the stream to
    $CACHE_ROOT/sessions/<name>.jsonl from the first byte.
    """
    capture = (root or cache_root()) / "sessions" / f"{name}.jsonl"
    try:
        with capture.open(encoding="utf-8") as handle:
            for _ in range(20):
                line = handle.readline()
                if not line:
                    break
                try:
                    event = json.loads(line)
                except ValueError:
                    continue
                if event.get("type") == "thread.started" and event.get("thread_id"):
                    return str(event["thread_id"])
    except OSError:
        return None
    return None


def spool_rows(root: Path | None = None) -> list[dict]:
    """The running dispatches, from the spool `dispatch.sh` writes before it
    reserves an account slot.  It is the only record a live session has."""
    directory = (root or cache_root()) / "watchdog" / "capacity" / "spool"
    rows = []
    try:
        files = sorted(directory.glob("*.json"))
    except OSError:
        return rows
    for path in files:
        try:
            row = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, ValueError):
            continue
        if isinstance(row, dict):
            row["_spool"] = str(path)
            rows.append(row)
    return rows


def live_sessions(root: Path | None = None, processes: Processes | None = None,
                  now: float | None = None) -> list[dict]:
    """Every codex session that is running right now, with what the landing
    needs to decide about it: role, elapsed time, worktree, thread id, pid."""
    root = root or cache_root()
    processes = processes or Processes()
    now = now if now is not None else time.time()
    out = []
    for row in spool_rows(root):
        if (row.get("state") or "") != "running":
            continue
        pid = row.get("pid")
        if not isinstance(pid, int) or isinstance(pid, bool) or not processes.alive(pid):
            continue
        started = _parse_ts(row.get("spooled_at")) or processes.started_at(pid)
        elapsed = max(0.0, now - started) if started else 0.0
        name = str(row.get("name") or "")
        out.append({
            "name": name,
            "role": str(row.get("role") or "unknown"),
            "issue": row.get("issue"),
            "pr": row.get("pr"),
            "account": row.get("account"),
            "worktree": row.get("worktree"),
            "branch": row.get("branch"),
            "pid": pid,
            "cmdline": processes.cmdline(pid),
            "thread_id": row.get("resume") or thread_of(name, root),
            "started_at": _iso(started),
            "elapsed_min": int(elapsed // 60),
            "spool": row.get("_spool"),
        })
    out.sort(key=lambda row: (row["role"], row["name"]))
    return out


# ---------------------------------------------------------------------------
# Classification
# ---------------------------------------------------------------------------

def classify(session: dict, limits: dict) -> dict:
    """One session's landing class, action and resumability.

    Young means little sunk cost, so a young session is stopped at once whatever
    its role.  A mature session is worth the wait: a reviewer nearly always
    finishes inside the landing window and a restarted review re-reads its whole
    context anyway, so it runs to the last call and is then restarted from
    scratch; a mature writer is checkpointed — its worktree is left exactly as
    it is, its thread id recorded, and it is stopped only at the last call.
    """
    rule = role_rule(limits, session.get("role") or "unknown")
    row = dict(session)
    if row.get("elapsed_min", 0) < limits["young_max_min"]:
        row["class"] = "young"
        row["action"] = "stop-now"
        row["reason"] = (f"elapsed {row.get('elapsed_min', 0)} min is under the "
                         f"{limits['young_max_min']}-minute young threshold")
    elif rule.get("mature") == "finish":
        row["class"] = "mature-finish"
        row["action"] = "stop-at-last-call"
        row["reason"] = (f"a mature {row.get('role')} usually finishes inside the "
                         "landing window; it runs until the last call")
    else:
        row["class"] = "checkpoint"
        row["action"] = "stop-at-last-call"
        row["reason"] = (f"a mature {row.get('role')} is checkpointed: its worktree "
                         "stays as it is and its thread is recorded")
    # Every classified row carries a signal field from the start, so the manifest
    # never has to distinguish "not stopped" from "the key is missing": `pending`
    # means the landing has not reached this one yet, and a row still `pending`
    # when the resume reads the manifest was never stopped and is not relaunched.
    row.setdefault("signal", "pending")
    resume = rule.get("resume")
    row["resume"] = "restart" if row["class"] == "mature-finish" else resume
    row["resumable"] = bool(row["resume"] == "thread" and row.get("thread_id"))
    if row["resume"] == "thread" and not row.get("thread_id"):
        row["reason"] += "; no thread id was captured, so it can only be restarted"
        row["resume"] = "restart"
    return row


def classified(root: Path | None = None, processes: Processes | None = None,
               now: float | None = None, limits: dict | None = None) -> list[dict]:
    limits = limits or thresholds()
    return [classify(row, limits)
            for row in live_sessions(root, processes, now)]


# ---------------------------------------------------------------------------
# Lanes
# ---------------------------------------------------------------------------

def lane_step(state_dir: Path, issue: str) -> str:
    """The last step `lane.sh` reached, read from the markers it leaves."""
    if (state_dir / f"{issue}.done").exists():
        return "done"
    for marker, step in ((f"{issue}.review.log", "review"),
                         (f"{issue}.ci.log", "ci"),
                         (f"{issue}.pr.md", "publish"),
                         (f"{issue}.dispatch.log", "dispatch")):
        if (state_dir / marker).exists():
            return step
    return "warm"


def git_head(worktree) -> str | None:
    if not worktree:
        return None
    try:
        done = subprocess.run(["git", "-C", str(worktree), "rev-parse", "HEAD"],
                              capture_output=True, text=True, timeout=60)
    except (OSError, subprocess.SubprocessError):
        return None
    return done.stdout.strip() or None if done.returncode == 0 else None


#: A pause runs against the owner's deadline, so the status reads are bounded
#: twice: per call, and in total across the lanes.  An unread status is recorded
#: as "not known", which makes the resume RUN the step rather than skip it — the
#: safe direction, and the resume re-reads the head's statuses anyway.
STATUS_TIMEOUT_S = 20
STATUS_BUDGET_S = 60


def head_statuses(sha: str | None, root: Path | None = None,
                  timeout: int = STATUS_TIMEOUT_S) -> dict:
    """The latest status per context on *sha*, through the one GitHub client.

    A pause must finish inside the owner's deadline, so this is bounded and a
    failure is recorded as "no statuses known" rather than raised: the resume
    then re-runs the step instead of wrongly skipping it.
    """
    if not sha:
        return {}
    helper = (root or checkout_root()) / "local" / "bin" / "gh_common.py"
    if not helper.exists():
        return {}
    try:
        done = subprocess.run([sys.executable, str(helper), "latest-statuses", sha],
                              capture_output=True, text=True, timeout=timeout)
    except (OSError, subprocess.SubprocessError):
        return {}
    if done.returncode != 0:
        return {}
    try:
        rows = json.loads(done.stdout)
    except ValueError:
        return {}
    if not isinstance(rows, dict):
        return {}
    return {name: (row or {}).get("state")
            for name, row in rows.items()
            if name in (CI_STATUS, REVIEW_STATUS)}


def live_lanes(root: Path | None = None, processes: Processes | None = None,
               statuses=None, checkout: Path | None = None,
               budget_s: int = STATUS_BUDGET_S) -> list[dict]:
    """Every running lane, with the step it reached and its head's statuses."""
    root = root or cache_root()
    processes = processes or Processes()
    checkout = checkout or checkout_root()
    if statuses is None:
        deadline = time.monotonic() + budget_s
        def statuses(sha):  # noqa: E306 — the bounded default reader
            if time.monotonic() >= deadline:
                return {}
            return head_statuses(sha, checkout)
    state_dir = watchdog_dir(root) / "lanes"
    out = []
    for pid in processes.pids():
        match = LANE_RE.match(processes.cmdline(pid))
        if not match:
            continue
        issue, slug = match.group(2), match.group(3) or ""
        branch = f"issue-{issue}-{slug}" if slug else ""
        worktree = checkout / ".worktrees" / branch if branch else None
        head = git_head(worktree) if worktree and worktree.exists() else None
        out.append({
            "issue": issue,
            "slug": slug,
            "role": match.group(4) or "prover",
            "branch": branch,
            "worktree": str(worktree) if worktree else None,
            "head": head,
            "step": lane_step(state_dir, issue),
            "statuses": statuses(head),
            "pid": pid,
        })
    out.sort(key=lambda row: int(row["issue"]))
    return out


# ---------------------------------------------------------------------------
# The failed markers the landing itself creates
# ---------------------------------------------------------------------------

def failed_markers(root: Path | None = None) -> dict[str, float]:
    directory = watchdog_dir(root) / "daemon"
    out: dict[str, float] = {}
    try:
        entries = list(directory.iterdir())
    except OSError:
        return out
    for entry in entries:
        if FAILED_MARKER_RE.match(entry.name):
            try:
                out[str(entry)] = entry.stat().st_mtime
            except OSError:
                out[str(entry)] = 0.0
    return out


def new_failed_markers(before: dict[str, float], root: Path | None = None) -> list[dict]:
    """The `daemon/pr<N>.failed` markers that appeared during the landing.

    The merge daemon writes one when a PR's processing fails, and it then skips
    that PR.  A marker a kill produced is not a verdict about the PR, so the
    landing records exactly the ones it caused — by difference, never by
    guessing from a name — and `owner-resume.sh` removes those and nothing else.
    """
    out = []
    for path, mtime in sorted(failed_markers(root).items()):
        if path in before and before[path] == mtime:
            continue
        match = FAILED_MARKER_RE.match(Path(path).name)
        first = ""
        try:
            with open(path, encoding="utf-8") as handle:
                first = handle.readline().strip()[:200]
        except OSError:
            pass
        out.append({"path": path, "pr": match.group(1) if match else None,
                    "created_by_landing": True, "first_line": first})
    return out


# ---------------------------------------------------------------------------
# Stopping
# ---------------------------------------------------------------------------

def stop(session: dict, limits: dict, processes: Processes,
         dry_run: bool = False) -> dict:
    """SIGTERM, then SIGKILL after the recorded grace.

    A pid is signalled only while it is still the process the record names: ghz
    is a 128-core host shared with other users' jobs, so a recycled pid is a
    real possibility and an unverified kill stops someone else's work.
    """
    pid, name = session.get("pid"), session.get("name") or ""
    row = {"pid": pid, "signal": "none", "stopped_at": None}
    if not isinstance(pid, int) or isinstance(pid, bool):
        row["signal"] = "no-pid"
        return row
    if not processes.alive(pid):
        row["signal"] = "already-gone"
        return row
    cmd = processes.cmdline(pid)
    if name and cmd and name not in cmd and "dispatch.sh" not in cmd:
        row["signal"] = "not-ours"
        row["cmdline"] = cmd[:60]
        return row
    if dry_run:
        row["signal"] = "TERM (dry-run)"
        return row
    processes.signal(pid, signal.SIGTERM)
    row["signal"] = "TERM"
    processes.sleep(limits["phases"]["grace_s"])
    if processes.alive(pid):
        processes.signal(pid, signal.SIGKILL)
        row["signal"] = "KILL"
    row["stopped_at"] = utcnow()
    return row


def land(sessions: list[dict], phase: str, limits: dict,
         processes: Processes | None = None, dry_run: bool = False) -> list[dict]:
    """Stop the sessions this phase owns and return them, annotated.

    `now` stops the young only.  `last` stops everything still running — the
    mature reviewers that did not finish and the checkpointed writers.
    """
    processes = processes or Processes()
    wanted = "stop-now" if phase == "now" else "stop-at-last-call"
    out = []
    for session in sessions:
        row = dict(session)
        if row.get("action") != wanted or row.get("signal") not in (None, "", "pending"):
            out.append(row)
            continue
        row.update(stop(row, limits, processes, dry_run))
        row["landed_in_phase"] = phase
        out.append(row)
    return out


# ---------------------------------------------------------------------------
# The manifest
# ---------------------------------------------------------------------------

def build_manifest(root: Path | None = None, processes: Processes | None = None,
                   statuses=None, now: float | None = None,
                   limits: dict | None = None, cutoff_at: str | None = None,
                   checkout: Path | None = None) -> dict:
    limits = limits or thresholds()
    processes = processes or Processes()
    return {
        "schema": SCHEMA,
        "classified_at": utcnow(),
        "cutoff_at": cutoff_at or None,
        "thresholds": limits,
        "lanes": live_lanes(root, processes, statuses, checkout),
        "sessions": classified(root, processes, now, limits),
        "failed_markers": [],
    }


def read_manifest(state: Path) -> dict:
    try:
        doc = json.loads(Path(state).read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return {}
    landing = doc.get("landing") if isinstance(doc, dict) else None
    return landing if isinstance(landing, dict) else {}


def write_manifest(state: Path, manifest: dict) -> None:
    """Merge the landing into the pause record without touching the rest of it."""
    path = Path(state)
    try:
        doc = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        doc = {}
    if not isinstance(doc, dict):
        doc = {}
    doc["landing"] = manifest
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(doc, indent=1, sort_keys=True) + "\n", encoding="utf-8")
    os.replace(tmp, path)


# ---------------------------------------------------------------------------
# The resume plan
# ---------------------------------------------------------------------------

def lane_resume_step(lane: dict) -> str:
    """Where a parked lane restarts.

    The head is the anchor: a lane whose worktree still holds the head the pause
    recorded needs no dispatch, no merge, no build and no push, and each of the
    two summary statuses already `success` on that head removes the step that
    posts it.  A head that moved, or that cannot be read, resumes the whole
    lane — re-running a step is cheap next to skipping one that never ran.
    """
    if lane.get("step") == "done":
        return "done"
    recorded, current = lane.get("head"), lane.get("head_now", lane.get("head"))
    if not recorded or recorded != current:
        return "dispatch"
    states = lane.get("statuses") or {}
    if states.get(CI_STATUS) == "success" and states.get(REVIEW_STATUS) == "success":
        return "done"
    if states.get(CI_STATUS) == "success":
        return "review"
    if lane.get("step") in ("ci", "review"):
        return "ci"
    return "publish"


def lane_command(lane: dict, step: str, checkout: Path) -> list[str]:
    return ["env", f"LANE_RESUME_STEP={step}",
            str(Path(checkout) / "local" / "bin" / "lane.sh"),
            str(lane.get("issue")), str(lane.get("slug") or ""),
            str(lane.get("role") or "prover")]


def session_command(session: dict, checkout: Path) -> list[str] | None:
    dispatch = str(Path(checkout) / "local" / "bin" / "dispatch.sh")
    role = session.get("role") or "prover"
    if session.get("resume") == "thread" and session.get("thread_id"):
        argv = [dispatch, "--role", role, "--issue", str(session.get("issue") or ""),
                "--sandbox", "workspace-write"]
        if session.get("worktree"):
            argv += ["--worktree", str(session["worktree"])]
        argv += ["--resume", str(session["thread_id"]), "--", CONTINUE_PROMPT]
        return argv
    if role == "reviewer":
        if not session.get("pr"):
            return None
        return [str(Path(checkout) / "local" / "bin" / "review.sh"), str(session["pr"])]
    return None


def resume_plan(manifest: dict, checkout: Path | None = None) -> list[dict]:
    """Every action the resume takes to put the work back, as data."""
    checkout = checkout or checkout_root()
    plan: list[dict] = []
    for marker in manifest.get("failed_markers") or []:
        if marker.get("created_by_landing") and marker.get("path"):
            plan.append({"kind": "clear-marker", "path": marker["path"],
                         "pr": marker.get("pr"),
                         "why": "the marker was created by the landing, not by the PR",
                         "argv": ["rm", "-f", str(marker["path"])]})
    for lane in manifest.get("lanes") or []:
        step = lane_resume_step(lane)
        entry = {"kind": "lane", "issue": lane.get("issue"), "branch": lane.get("branch"),
                 "head": lane.get("head"), "step_reached": lane.get("step"),
                 "resume_step": step, "statuses": lane.get("statuses") or {}}
        if step == "done":
            entry["argv"] = None
            entry["why"] = "the head already carries both summary statuses"
        else:
            entry["argv"] = lane_command(lane, step, checkout)
            entry["why"] = f"parked at '{lane.get('step')}'; resumed at '{step}'"
        plan.append(entry)
    for session in manifest.get("sessions") or []:
        if session.get("signal") in (None, "", "none", "pending", "already-gone",
                                     "not-ours", "no-pid"):
            continue
        argv = session_command(session, checkout)
        plan.append({
            "kind": "session", "name": session.get("name"), "role": session.get("role"),
            "resume": session.get("resume"), "thread_id": session.get("thread_id"),
            "worktree": session.get("worktree"), "argv": argv,
            "why": ("resumed on its own thread; the worktree still holds its work"
                    if session.get("resume") == "thread"
                    else "restarted from scratch; a resumed review re-reads its whole context"),
        })
    return plan


def resume_exec(plan: list[dict], log: Path | None = None, runner=None,
                dry_run: bool = False) -> list[dict]:
    """Carry out a plan: remove the recorded markers, launch the rest detached.

    Every command is an argv list built by this module, so nothing is passed
    through a shell and no generated text is ever `eval`ed.  The launcher is a
    seam: a test supplies its own and asserts the commands instead of running
    them.
    """
    handle = None
    if runner is None and not dry_run:
        if log is not None:
            log.parent.mkdir(parents=True, exist_ok=True)
            handle = open(log, "a", encoding="utf-8")

        def runner(argv):  # noqa: E306 — the real launcher, detached like the daemons
            return subprocess.Popen(argv, stdin=subprocess.DEVNULL,
                                    stdout=handle or subprocess.DEVNULL,
                                    stderr=subprocess.STDOUT,
                                    start_new_session=True).pid
    done = []
    try:
        for entry in plan:
            row = dict(entry)
            argv = entry.get("argv")
            if not argv:
                row["done"] = "nothing to run"
            elif entry["kind"] == "clear-marker":
                if dry_run:
                    row["done"] = "would clear"
                else:
                    try:
                        os.unlink(entry["path"])
                    except OSError:
                        pass
                    row["done"] = "marker cleared"
            elif dry_run:
                row["done"] = "would launch"
            else:
                row["done"] = f"launched pid {runner(argv)}"
            done.append(row)
    finally:
        if handle is not None:
            handle.close()
    return done


def quote(argv: list[str]) -> str:
    import shlex
    return " ".join(shlex.quote(part) for part in argv)


def format_plan(plan: list[dict]) -> str:
    lines = []
    for entry in plan:
        if entry["kind"] == "clear-marker":
            lines.append(f"# clear {entry['path']} — {entry['why']}")
        elif entry["kind"] == "lane":
            lines.append(f"# lane {entry['issue']} — {entry['why']}")
        else:
            lines.append(f"# session {entry['name']} ({entry['role']}) — {entry['why']}")
        lines.append(quote(entry["argv"]) if entry.get("argv") else "#   nothing to run")
    return "\n".join(lines) + ("\n" if lines else "")


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def _render_sessions(rows: list[dict]) -> str:
    if not rows:
        return "no live codex session\n"
    out = [f"{'session':<34} {'role':<11} {'elapsed':>7}  {'class':<14} action"]
    for row in rows:
        out.append(f"{(row.get('name') or '?'):<34} {(row.get('role') or '?'):<11} "
                   f"{row.get('elapsed_min', 0):>5} m  {row.get('class', '?'):<14} "
                   f"{row.get('action', '?')}"
                   f"{' (resumable)' if row.get('resumable') else ''}")
    return "\n".join(out) + "\n"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="pause_landing.py", add_help=True,
                                     description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest="cmd", required=True)
    sub.add_parser("thresholds").add_argument("--json", action="store_true")
    p = sub.add_parser("classify")
    p.add_argument("--json", action="store_true")
    p.add_argument("--now", type=float, default=None)
    p = sub.add_parser("manifest")
    p.add_argument("--cutoff-at", default=None)
    p.add_argument("--no-github", action="store_true")
    p.add_argument("--now", type=float, default=None)
    p.add_argument("--state", default=None)
    p = sub.add_parser("land")
    p.add_argument("--phase", choices=("now", "last"), required=True)
    p.add_argument("--state", default=None)
    p.add_argument("--dry-run", action="store_true")
    p = sub.add_parser("resume-plan")
    p.add_argument("--state", default=None)
    p.add_argument("--json", action="store_true")
    p = sub.add_parser("resume-exec")
    p.add_argument("--state", default=None)
    p.add_argument("--log", default=None)
    p.add_argument("--dry-run", action="store_true")
    args = parser.parse_args(argv)

    state = Path(getattr(args, "state", None) or (watchdog_dir() / "pause-state.json"))
    limits = thresholds()

    if args.cmd == "thresholds":
        if args.json:
            print(json.dumps(limits, indent=1, sort_keys=True))
        else:
            phases = limits["phases"]
            print(f"source            {limits['source']}")
            print(f"young_max_min     {limits['young_max_min']}")
            print(f"cutoff_lead_min   {limits['cutoff_lead_min']}")
            print(f"landing_lead_s    {phases['landing_lead_s']}")
            print(f"last_call_s       {phases['last_call_s']}")
            print(f"grace_s           {phases['grace_s']}")
        return 0

    if args.cmd == "classify":
        rows = classified(now=args.now, limits=limits)
        print(json.dumps(rows, indent=1) if args.json else _render_sessions(rows), end="")
        return 0

    if args.cmd == "manifest":
        statuses = (lambda sha: {}) if args.no_github else None
        manifest = build_manifest(statuses=statuses, now=args.now,
                                  limits=limits, cutoff_at=args.cutoff_at)
        # The mtimes, not only the names: `new_failed_markers` decides by
        # difference, and a snapshot of bare paths would make every marker that
        # already existed look like one the landing caused — and the resume
        # would then clear a real failure verdict.
        manifest["markers_before"] = failed_markers()
        write_manifest(state, manifest)
        print(json.dumps(manifest, indent=1, sort_keys=True))
        return 0

    if args.cmd == "land":
        manifest = read_manifest(state)
        if not manifest:
            print(f"pause_landing.py: no landing manifest in {state}", file=sys.stderr)
            return 3
        before = manifest.get("markers_before") or {}
        if not isinstance(before, dict):
            before = {}
        manifest["sessions"] = land(manifest.get("sessions") or [], args.phase,
                                    limits, dry_run=args.dry_run)
        if args.phase == "last" and not args.dry_run:
            manifest["failed_markers"] = new_failed_markers(before)
        manifest["landed_at"] = utcnow()
        if not args.dry_run:
            write_manifest(state, manifest)
        print(_render_sessions(manifest["sessions"]), end="")
        return 0

    if args.cmd in ("resume-plan", "resume-exec"):
        manifest = read_manifest(state)
        if not manifest:
            print(f"pause_landing.py: no landing manifest in {state}", file=sys.stderr)
            return 3
        for lane in manifest.get("lanes") or []:
            lane["head_now"] = git_head(lane.get("worktree"))
            # The pause read the statuses against a deadline and may have run out
            # of budget; the resume has none, so a fresh read wins over the record.
            fresh = head_statuses(lane.get("head"))
            if fresh:
                lane["statuses"] = fresh
        plan = resume_plan(manifest)
        if args.cmd == "resume-plan":
            print(json.dumps(plan, indent=1) if args.json else format_plan(plan), end="")
            return 0
        print(format_plan(plan), end="")
        log = Path(args.log) if args.log else None
        for row in resume_exec(plan, log=log, dry_run=args.dry_run):
            print(f"  {row['kind']}: {row['done']}")
        return 0

    return 2


if __name__ == "__main__":
    raise SystemExit(main())
