#!/usr/bin/env python3
r"""
Telemetry writer for the local operations layer.

Every append to ``results/telemetry/*`` goes through this script so the
research-data invariants of ``local/protocols/meta.md`` hold: one JSON object
per line, ISO-8601 timestamps with offset, locked appends (concurrent
sessions), and idempotent re-runs.

Subcommands::

    telemetry.py session-summarize CAPTURE.jsonl [--name N] [--role R] ...
    telemetry.py session-status --name N --status archived [--note TEXT]
    telemetry.py stage --stage 4.3-proofs --event start [--note TEXT]
    telemetry.py build --kind warm --outcome success --seconds 812
    telemetry.py event --text "symptom -> diagnosis -> fix -> lesson"

``session-summarize`` is the one that does real work: it reads a captured
``codex exec --json`` event stream (JSONL on stdout: ``thread.started``,
``turn.completed``, ``item.completed``) and emits the ``sessions.jsonl``
registry line described in ``local/DESIGN.md`` ("Agent sessions") and
``local/protocols/meta.md`` ("Telemetry duties").  It replaces the parent
repository's GitHub-side accounting, where session identity came from a bot
token and run metadata came from the Actions API; locally the codex
``thread_id`` is the only session handle and it exists *only* in the event
stream, so losing the capture loses the session (see
``local/protocols/sessions.md``).

This script is stdlib-only and safe to call from several processes at once.
It never starts an agent: ``local/bin/dispatch.sh`` does that and calls this.
"""

from __future__ import annotations

import argparse
import fcntl
import json
import os
import re
import shlex
import sys
import tempfile
from contextlib import contextmanager
from datetime import datetime
from pathlib import Path
from typing import Any, Iterator, Sequence

# ---------------------------------------------------------------------------
# Layout
# ---------------------------------------------------------------------------

# local/bin/telemetry.py -> repository root
REPO_ROOT_DEFAULT = Path(__file__).resolve().parents[2]

TELEMETRY_SUBDIR = Path("results") / "telemetry"

# Timestamp shape already used by results/telemetry/*.jsonl and by
# `date +%Y-%m-%dT%H:%M:%S%z` in the shell scripts.
TS_FMT = "%Y-%m-%dT%H:%M:%S%z"

# codex `turn.completed` usage keys -> meta.md `usage` schema keys.
USAGE_MAP = {
    "input_tokens": "input",
    "cached_input_tokens": "cached_input",
    "cache_write_input_tokens": "cache_write",
    "output_tokens": "output",
    "reasoning_output_tokens": "reasoning",
}
USAGE_KEYS = list(USAGE_MAP.values())

# Documented vocabularies (meta.md).  Unknown values are written anyway but
# warned about: refusing them would let a peer script lose telemetry entirely,
# which is the worse failure.
KNOWN_STAGES = (
    "1-skeleton",
    "2-references",
    "3-blueprint",
    "4.1-minimal",
    "4.2-full-skeleton",
    "4.3-proofs",
)
KNOWN_BUILD_KINDS = ("warm", "rebuild", "cache-get", "ci-build")
KNOWN_OUTCOMES = ("success", "failed", "partial", "skipped")
KNOWN_STATUSES = ("active", "done", "failed", "archived")
ROLES = ("orc", "prover", "reviewer", "simplifier", "blueprint", "splitter", "scout")

TOKEN_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]*$")

EVENTS_HEADER = """# Incident and observation log

Dated bullets, one incident each: symptom → diagnosis → fix → lesson.
This file is the raw feed for `local/protocols/EVOLUTION.md`.
"""


def warn(message: str) -> None:
    sys.stderr.write(f"telemetry.py: warning: {message}\n")


def fail(message: str, code: int = 4) -> None:
    """Abort with a diagnosis on stderr.  Never returns."""
    sys.stderr.write(f"telemetry.py: error: {message}\n")
    raise SystemExit(code)


# ---------------------------------------------------------------------------
# Time
# ---------------------------------------------------------------------------


def now_ts() -> str:
    """Current local time, ISO-8601 with numeric offset."""
    return datetime.now().astimezone().strftime(TS_FMT)


def parse_ts(text: str | None) -> datetime | None:
    if not text:
        return None
    for fmt in (TS_FMT, "%Y-%m-%dT%H:%M:%S.%f%z"):
        try:
            return datetime.strptime(text, fmt)
        except ValueError:
            pass
    try:
        return datetime.fromisoformat(text.replace("Z", "+00:00"))
    except ValueError:
        return None


# ---------------------------------------------------------------------------
# Runtime state and locking
# ---------------------------------------------------------------------------


def cache_dir() -> Path:
    """Runtime state root.  Never inside the repository (DESIGN.md, Layout)."""
    override = os.environ.get("MIPSTARRE_CACHE_ROOT")
    if override:
        return Path(override).expanduser()
    return Path.home() / ".cache" / "mipstarre-dev"


@contextmanager
def named_lock(name: str) -> Iterator[None]:
    """Advisory lock held on a file under ``~/.cache/mipstarre-dev/locks/``."""
    lock_dir = cache_dir() / "locks"
    lock_dir.mkdir(parents=True, exist_ok=True)
    lock_path = lock_dir / f"{name}.lock"
    with open(lock_path, "a+", encoding="utf-8") as handle:
        fcntl.flock(handle.fileno(), fcntl.LOCK_EX)
        try:
            yield
        finally:
            fcntl.flock(handle.fileno(), fcntl.LOCK_UN)


def append_jsonl(path: Path, record: dict[str, Any]) -> str:
    """Append one JSON object to ``path`` under an exclusive lock on the file."""
    line = json.dumps(record, ensure_ascii=False)
    path.parent.mkdir(parents=True, exist_ok=True)
    fd = os.open(path, os.O_RDWR | os.O_CREAT | os.O_APPEND, 0o644)
    with os.fdopen(fd, "r+", encoding="utf-8") as handle:
        fcntl.flock(handle.fileno(), fcntl.LOCK_EX)
        try:
            _ensure_trailing_newline(handle)
            handle.write(line + "\n")
            handle.flush()
            os.fsync(handle.fileno())
        finally:
            fcntl.flock(handle.fileno(), fcntl.LOCK_UN)
    return line


def _ensure_trailing_newline(handle: Any) -> None:
    """Guard against a previous writer that died mid-line."""
    handle.seek(0, os.SEEK_END)
    if handle.tell() == 0:
        return
    handle.seek(handle.tell() - 1)
    if handle.read(1) != "\n":
        handle.write("\n")
    handle.seek(0, os.SEEK_END)


def read_jsonl(path: Path) -> tuple[list[dict[str, Any]], int]:
    """Read a JSONL file, returning (objects, malformed line count)."""
    if not path.exists():
        return [], 0
    objects: list[dict[str, Any]] = []
    errors = 0
    for raw in path.read_text(encoding="utf-8", errors="replace").splitlines():
        raw = raw.strip()
        if not raw:
            continue
        try:
            obj = json.loads(raw)
        except json.JSONDecodeError:
            errors += 1
            continue
        if isinstance(obj, dict):
            objects.append(obj)
        else:
            errors += 1
    return objects, errors


# ---------------------------------------------------------------------------
# codex event-stream parsing
# ---------------------------------------------------------------------------


def deep_find(node: Any, keys: Sequence[str], depth: int = 0) -> str | None:
    """First string value stored under any of ``keys``, searched breadth-first."""
    if depth > 8:
        return None
    if isinstance(node, dict):
        for key in keys:
            value = node.get(key)
            if isinstance(value, str) and value:
                return value
        for value in node.values():
            found = deep_find(value, keys, depth + 1)
            if found:
                return found
    elif isinstance(node, list):
        for value in node:
            found = deep_find(value, keys, depth + 1)
            if found:
                return found
    return None


def extract_thread_id(events: Sequence[dict[str, Any]]) -> str | None:
    """codex session handle, needed for ``codex exec resume``.

    Primary source is the ``thread.started`` event; the fallbacks exist because
    a crashed run can truncate the stream before that event is flushed, and a
    session with no recoverable id must be reported (never silently nulled).
    """
    for event in events:
        if event.get("type") == "thread.started":
            thread = event.get("thread")
            candidate = event.get("thread_id")
            if not isinstance(candidate, str) or not candidate:
                candidate = thread.get("id") if isinstance(thread, dict) else None
            if isinstance(candidate, str) and candidate:
                return candidate
    for event in events:
        found = deep_find(event, ("thread_id", "conversation_id", "session_id"))
        if found:
            return found
    return None


def summarize_usage(
    events: Sequence[dict[str, Any]], mode: str = "sum"
) -> tuple[dict[str, int], int]:
    """Token usage over ``turn.completed`` events, normalized to meta.md keys.

    ``mode=sum`` treats each turn's usage as a delta (codex 0.147.0 behaviour);
    ``mode=last`` keeps only the final turn, for a codex build that ever starts
    reporting cumulative counters.  Getting this wrong silently inflates the
    paper's token totals, so the mode is recorded in the run log, not guessed.
    """
    totals = {key: 0 for key in USAGE_KEYS}
    last: dict[str, int] | None = None
    turns = 0
    for event in events:
        if event.get("type") != "turn.completed":
            continue
        usage = event.get("usage")
        if not isinstance(usage, dict):
            turn = event.get("turn")
            usage = turn.get("usage") if isinstance(turn, dict) else None
        if not isinstance(usage, dict):
            continue
        turns += 1
        normalized = {}
        for source, target in USAGE_MAP.items():
            value = usage.get(source)
            normalized[target] = int(value) if isinstance(value, (int, float)) else 0
        last = normalized
        for key, value in normalized.items():
            totals[key] += value
    if mode == "last" and last is not None:
        return last, turns
    return totals, turns


def find_rollout(thread_id: str | None) -> str | None:
    """Locate the codex rollout file for a thread.

    ``~/.codex/sessions`` is date-sharded (``YYYY/MM/DD``), so the id alone is
    not a path: archival records the resolved path, per the study-map gotcha
    that a bare UUID makes the rollout unfindable later.
    """
    if not thread_id:
        return None
    codex_home = os.environ.get("CODEX_HOME")
    base = (Path(codex_home) if codex_home else Path.home() / ".codex") / "sessions"
    if not base.is_dir():
        return None
    matches = sorted(base.glob(f"*/*/*/rollout-*{thread_id}*.jsonl"))
    return str(matches[-1]) if matches else None


# ---------------------------------------------------------------------------
# Text sanitization (untrusted-data invariant, DESIGN.md core invariant 6)
# ---------------------------------------------------------------------------

_CONTROL_RE = re.compile(r"[\x00-\x08\x0b\x0c\x0e-\x1f\x7f]")


def sanitize_text(text: str, limit: int = 4000) -> str:
    """Strip control characters and truncate.

    Applied to every free-text field that reaches a telemetry file, because
    those files are later injected into agent prompts.
    """
    cleaned = _CONTROL_RE.sub("", text).replace("\r\n", "\n").replace("\r", "\n")
    cleaned = cleaned.strip()
    if len(cleaned) > limit:
        cleaned = cleaned[:limit].rstrip() + " …[truncated]"
    return cleaned


# ---------------------------------------------------------------------------
# sessions.jsonl
# ---------------------------------------------------------------------------


def session_record(
    *,
    name: str,
    role: str | None,
    issue: str | None,
    pr: str | None,
    thread_id: str | None,
    start: str | None,
    end: str | None,
    wall_s: float | int | None,
    usage: dict[str, int],
    turns: int,
    exit_code: int | None,
    dispatcher: str | None,
    worktree: str | None,
    status: str,
    capture: str | None,
    rollout: str | None,
) -> dict[str, Any]:
    record: dict[str, Any] = {
        "name": name,
        "role": role,
        "issue": issue,
    }
    if pr:
        record["pr"] = pr
    record.update(
        {
            "thread_id": thread_id,
            "start": start,
            "end": end,
            "wall_s": wall_s,
            "usage": usage,
            "turns": turns,
            "exit": exit_code,
            "dispatcher": dispatcher,
            "worktree": worktree,
            "status": status,
        }
    )
    if capture:
        record["capture"] = capture
    if rollout:
        record["rollout"] = rollout
    return record


def append_session_record(registry: Path, record: dict[str, Any]) -> bool:
    """Append a registry line unless an identical observation is already there.

    The registry is append-only (meta.md, "Two memory disciplines"): a later
    line supersedes an earlier one for the same ``name``.  Idempotency is
    therefore keyed on (name, status, thread_id, exit) so that re-running a
    summarize over the same capture does not duplicate a line, while a genuine
    status transition still appends.
    """
    registry.parent.mkdir(parents=True, exist_ok=True)
    fd = os.open(registry, os.O_RDWR | os.O_CREAT, 0o644)
    with os.fdopen(fd, "r+", encoding="utf-8") as handle:
        fcntl.flock(handle.fileno(), fcntl.LOCK_EX)
        try:
            handle.seek(0)
            for raw in handle.read().splitlines():
                raw = raw.strip()
                if not raw:
                    continue
                try:
                    existing = json.loads(raw)
                except json.JSONDecodeError:
                    continue
                if not isinstance(existing, dict):
                    continue
                if (
                    existing.get("name") == record.get("name")
                    and existing.get("status") == record.get("status")
                    and existing.get("thread_id") == record.get("thread_id")
                    and existing.get("exit") == record.get("exit")
                ):
                    return False
            _ensure_trailing_newline(handle)
            handle.write(json.dumps(record, ensure_ascii=False) + "\n")
            handle.flush()
            os.fsync(handle.fileno())
            return True
        finally:
            fcntl.flock(handle.fileno(), fcntl.LOCK_UN)


def write_shell_out(path: Path, record: dict[str, Any]) -> None:
    """Emit shell-quoted assignments for ``dispatch.sh`` to source."""
    usage = record.get("usage") or {}
    fields = {
        "DISPATCH_NAME": record.get("name"),
        "DISPATCH_ROLE": record.get("role"),
        "DISPATCH_THREAD_ID": record.get("thread_id"),
        "DISPATCH_START": record.get("start"),
        "DISPATCH_END": record.get("end"),
        "DISPATCH_WALL_S": record.get("wall_s"),
        "DISPATCH_EXIT": record.get("exit"),
        "DISPATCH_STATUS": record.get("status"),
        "DISPATCH_CAPTURE": record.get("capture"),
        "DISPATCH_ROLLOUT": record.get("rollout"),
        "DISPATCH_TURNS": record.get("turns"),
        "DISPATCH_USAGE_INPUT": usage.get("input"),
        "DISPATCH_USAGE_OUTPUT": usage.get("output"),
        "DISPATCH_USAGE_TOTAL": sum(int(usage.get(k) or 0) for k in USAGE_KEYS),
    }
    lines = []
    for key, value in fields.items():
        text = "" if value is None else str(value)
        lines.append(f"{key}={shlex.quote(text)}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


# ---------------------------------------------------------------------------
# events.md
# ---------------------------------------------------------------------------


def append_event_bullet(path: Path, text: str, date_str: str) -> str:
    """Append a dated bullet, creating today's ``## YYYY-MM-DD`` section."""
    bullet_lines = sanitize_text(text, limit=8000).split("\n")
    bullet = "- " + bullet_lines[0]
    for continuation in bullet_lines[1:]:
        bullet += "\n  " + continuation.strip()
    heading = f"## {date_str}"
    with named_lock("events-md"):
        path.parent.mkdir(parents=True, exist_ok=True)
        original = (
            path.read_text(encoding="utf-8") if path.exists() else EVENTS_HEADER
        )
        lines = original.splitlines()
        try:
            head_index = lines.index(heading)
        except ValueError:
            head_index = -1
        if head_index < 0:
            while lines and not lines[-1].strip():
                lines.pop()
            lines.extend(["", heading, "", bullet])
        else:
            end = len(lines)
            for index in range(head_index + 1, len(lines)):
                if lines[index].startswith("## "):
                    end = index
                    break
            while end > head_index + 1 and not lines[end - 1].strip():
                end -= 1
            lines.insert(end, bullet)
        _atomic_write(path, "\n".join(lines) + "\n")
    return bullet


def _atomic_write(path: Path, content: str) -> None:
    handle = tempfile.NamedTemporaryFile(
        "w", encoding="utf-8", dir=str(path.parent), delete=False
    )
    try:
        handle.write(content)
        handle.flush()
        os.fsync(handle.fileno())
    finally:
        handle.close()
    os.replace(handle.name, path)


# ---------------------------------------------------------------------------
# Subcommands
# ---------------------------------------------------------------------------


def telemetry_dir(args: argparse.Namespace) -> Path:
    return args.repo_root.resolve() / TELEMETRY_SUBDIR


def cmd_session_summarize(args: argparse.Namespace) -> int:
    capture = args.capture.resolve()
    if not capture.exists():
        fail(
            f"capture file not found: {capture}\n"
            "  dispatch.sh tees `codex exec --json` to "
            "results/telemetry/sessions/<name>.jsonl; without it the session "
            "cannot be reconstructed."
        )

    events, parse_errors = read_jsonl(capture)
    if parse_errors:
        warn(f"{parse_errors} malformed line(s) in {capture} were skipped")
    if not events:
        warn(
            f"{capture} holds no events: recording the session with a null "
            "thread_id and zero usage (check that codex ran with --json)"
        )

    thread_id = extract_thread_id(events)
    if thread_id is None:
        warn(
            "no thread_id in the event stream: `codex exec resume` will not be "
            "possible for this session"
        )
    usage, turns = summarize_usage(events, mode=args.usage_mode)

    name = args.name or capture.stem
    role = args.role
    if role is None:
        head = name.split("-", 1)[0]
        role = head if head in ROLES else None

    start_dt = parse_ts(args.start)
    end_dt = parse_ts(args.end)
    if args.start and start_dt is None:
        warn(f"unparseable --start {args.start!r}; wall_s will be null")
    if args.end and end_dt is None:
        warn(f"unparseable --end {args.end!r}; wall_s will be null")
    wall_s: float | int | None = None
    if start_dt is not None and end_dt is not None:
        wall_s = round((end_dt - start_dt).total_seconds(), 3)
        if float(wall_s).is_integer():
            wall_s = int(wall_s)

    status = args.status
    if status is None:
        status = "done" if (args.exit_code or 0) == 0 else "failed"
    if status not in KNOWN_STATUSES:
        warn(f"status {status!r} is not one of {KNOWN_STATUSES}")

    try:
        capture_field = str(capture.relative_to(args.repo_root.resolve()))
    except ValueError:
        capture_field = str(capture)

    record = session_record(
        name=name,
        role=role,
        issue=args.issue,
        pr=args.pr,
        thread_id=thread_id,
        start=args.start,
        end=args.end,
        wall_s=wall_s,
        usage=usage,
        turns=turns,
        exit_code=args.exit_code,
        dispatcher=args.dispatcher,
        worktree=args.worktree,
        status=status,
        capture=capture_field,
        rollout=None if args.no_rollout_scan else find_rollout(thread_id),
    )

    if args.append_to is not None:
        appended = append_session_record(args.append_to, record)
        if not appended:
            warn(
                f"an identical registry line for {name!r} already exists in "
                f"{args.append_to}; not duplicating it"
            )
    if args.shell_out is not None:
        write_shell_out(args.shell_out, record)

    sys.stdout.write(json.dumps(record, ensure_ascii=False) + "\n")
    return 0


def cmd_session_status(args: argparse.Namespace) -> int:
    registry = args.registry or (telemetry_dir(args) / "sessions.jsonl")
    records, parse_errors = read_jsonl(registry)
    if parse_errors:
        warn(f"{parse_errors} malformed line(s) in {registry} were skipped")
    previous = None
    for record in records:
        if record.get("name") == args.name:
            previous = record
    if previous is None:
        fail(
            f"no registry line for session {args.name!r} in {registry}\n"
            "  Sessions must be started through local/bin/dispatch.sh. If one "
            "was not, backfill it first with:\n"
            "    telemetry.py session-summarize <capture.jsonl> --name "
            f"{args.name} --dispatcher manual --append-to {registry}"
        )

    if args.status not in KNOWN_STATUSES:
        warn(f"status {args.status!r} is not one of {KNOWN_STATUSES}")
    if previous.get("status") == args.status and not args.note:
        warn(f"session {args.name!r} is already {args.status!r}; nothing appended")
        sys.stdout.write(json.dumps(previous, ensure_ascii=False) + "\n")
        return 0

    record = dict(previous)
    record["status"] = args.status
    record["status_ts"] = now_ts()
    if args.note:
        record["note"] = sanitize_text(args.note, limit=2000)
    append_jsonl(registry, record)
    sys.stdout.write(json.dumps(record, ensure_ascii=False) + "\n")
    return 0


def cmd_stage(args: argparse.Namespace) -> int:
    if args.stage not in KNOWN_STAGES:
        warn(
            f"stage {args.stage!r} is not one of the documented stages "
            f"{KNOWN_STAGES} (meta.md allows extension; recording it anyway)"
        )
    record: dict[str, Any] = {
        "ts": args.ts or now_ts(),
        "stage": args.stage,
        "event": args.event,
    }
    if args.note:
        record["note"] = sanitize_text(args.note)
    if args.tokens_note:
        record["tokens_note"] = sanitize_text(args.tokens_note)
    path = args.out or (telemetry_dir(args) / "stages.jsonl")
    line = append_jsonl(path, record)
    sys.stdout.write(line + "\n")
    return 0


def cmd_build(args: argparse.Namespace) -> int:
    if not TOKEN_RE.match(args.kind):
        fail(f"--kind {args.kind!r} is not a bare token")
    if not TOKEN_RE.match(args.outcome):
        fail(f"--outcome {args.outcome!r} is not a bare token")
    if args.kind not in KNOWN_BUILD_KINDS:
        warn(f"build kind {args.kind!r} is not one of {KNOWN_BUILD_KINDS}")
    if args.outcome not in KNOWN_OUTCOMES:
        warn(f"build outcome {args.outcome!r} is not one of {KNOWN_OUTCOMES}")
    if args.seconds < 0:
        fail("--seconds must not be negative")

    seconds: float | int = round(args.seconds, 3)
    if float(seconds).is_integer():
        seconds = int(seconds)
    record: dict[str, Any] = {
        "ts": args.ts or now_ts(),
        "kind": args.kind,
        "trigger": sanitize_text(args.trigger or "", limit=500) or None,
        "seconds": seconds,
        "outcome": args.outcome,
    }
    if args.sha:
        record["sha"] = args.sha
    if args.note:
        record["note"] = sanitize_text(args.note)
    path = args.out or (telemetry_dir(args) / "builds.jsonl")
    line = append_jsonl(path, record)
    sys.stdout.write(line + "\n")
    return 0


def cmd_event(args: argparse.Namespace) -> int:
    text = args.text
    if text == "-":
        text = sys.stdin.read()
    text = text.strip()
    if not text:
        fail("--text is empty; an events.md bullet must say something", code=2)
    date_str = args.date or datetime.now().astimezone().strftime("%Y-%m-%d")
    path = args.out or (telemetry_dir(args) / "events.md")
    bullet = append_event_bullet(path, text, date_str)
    sys.stdout.write(bullet + "\n")
    return 0


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="telemetry.py",
        description=(
            "Append research telemetry for the local operations layer "
            "(results/telemetry/*). Schemas: local/protocols/meta.md."
        ),
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=REPO_ROOT_DEFAULT,
        help="repository root (default: inferred from this script's location)",
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    summarize = subparsers.add_parser(
        "session-summarize",
        help="turn a captured `codex exec --json` stream into a sessions.jsonl line",
    )
    summarize.add_argument("capture", type=Path, help="captured JSONL event stream")
    summarize.add_argument("--name", help="session name (default: capture file stem)")
    summarize.add_argument("--role", choices=ROLES, help="agent role")
    summarize.add_argument("--issue", help="issue id or scope this session serves")
    summarize.add_argument("--pr", help="PR id, when the session works on one")
    summarize.add_argument("--start", help="ISO-8601 start timestamp with offset")
    summarize.add_argument("--end", help="ISO-8601 end timestamp with offset")
    summarize.add_argument(
        "--exit-code",
        type=int,
        default=None,
        dest="exit_code",
        help="exit status of the codex process",
    )
    summarize.add_argument("--dispatcher", help="who dispatched (session name or user)")
    summarize.add_argument("--worktree", help="worktree the session ran in")
    summarize.add_argument(
        "--status",
        help=f"session status (default: done/failed by exit code); {KNOWN_STATUSES}",
    )
    summarize.add_argument(
        "--usage-mode",
        choices=("sum", "last"),
        default="sum",
        help="treat per-turn usage as deltas (sum, default) or cumulative (last)",
    )
    summarize.add_argument(
        "--no-rollout-scan",
        action="store_true",
        help="skip resolving the ~/.codex/sessions rollout path for the thread",
    )
    summarize.add_argument(
        "--append-to",
        type=Path,
        help="registry file to append the line to (results/telemetry/sessions.jsonl)",
    )
    summarize.add_argument(
        "--shell-out",
        type=Path,
        help="write shell-quoted DISPATCH_* assignments here for the caller",
    )
    summarize.set_defaults(func=cmd_session_summarize)

    status = subparsers.add_parser(
        "session-status",
        help="append a superseding status line for an existing session",
    )
    status.add_argument("--name", required=True, help="session name")
    status.add_argument(
        "--status",
        required=True,
        help=f"new status, one of {KNOWN_STATUSES}",
    )
    status.add_argument("--note", help="short reason, recorded on the new line")
    status.add_argument(
        "--registry",
        type=Path,
        help="registry path (default: results/telemetry/sessions.jsonl)",
    )
    status.set_defaults(func=cmd_session_status)

    stage = subparsers.add_parser("stage", help="append a stages.jsonl line")
    stage.add_argument("--stage", required=True, help=f"stage id, e.g. {KNOWN_STAGES}")
    stage.add_argument(
        "--event", required=True, choices=("start", "end", "milestone")
    )
    stage.add_argument("--note")
    stage.add_argument("--tokens-note", dest="tokens_note")
    stage.add_argument("--ts", help="override the timestamp (backfill)")
    stage.add_argument("--out", type=Path, help="override the output file")
    stage.set_defaults(func=cmd_stage)

    build = subparsers.add_parser("build", help="append a builds.jsonl line")
    build.add_argument("--kind", required=True, help=f"one of {KNOWN_BUILD_KINDS}")
    build.add_argument("--outcome", required=True, help=f"one of {KNOWN_OUTCOMES}")
    build.add_argument("--seconds", required=True, type=float, help="wall seconds")
    build.add_argument("--trigger", help="what caused the build")
    build.add_argument("--sha", help="head SHA or snapshot label")
    build.add_argument("--note")
    build.add_argument("--ts", help="override the timestamp (backfill)")
    build.add_argument("--out", type=Path, help="override the output file")
    build.set_defaults(func=cmd_build)

    event = subparsers.add_parser("event", help="append a dated bullet to events.md")
    event.add_argument(
        "--text",
        required=True,
        help="bullet text ('-' reads stdin): symptom, diagnosis, fix, lesson",
    )
    event.add_argument("--date", help="YYYY-MM-DD section (default: today)")
    event.add_argument("--out", type=Path, help="override the output file")
    event.set_defaults(func=cmd_event)

    return parser


def main(argv: Sequence[str] | None = None) -> int:
    parser = _build_parser()
    args = parser.parse_args(argv)
    repo_root = args.repo_root.resolve()
    if not (repo_root / "local").is_dir():
        parser.error(
            f"--repo-root {repo_root} has no local/ directory; pass --repo-root"
        )
    args.repo_root = repo_root
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())
