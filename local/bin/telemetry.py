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
    telemetry.py events --since 2026-09-12 [--until D] [--format md|json]
    telemetry.py classify-failure CAPTURE.jsonl [--exit N] [--field NAME]

Event bullets are **sharded**: ``telemetry.py event`` writes
``results/telemetry/events.d/<YYYY-MM-DD>-<session>.md`` so that two sessions
never append to one path and a merge of ``main`` cannot conflict on the log
(2026-09-12: append-only telemetry conflicted on nearly every merge).
``results/telemetry/events.md`` keeps its full history unrewritten and carries a
header pointing at the shard directory; ``telemetry.py events --since`` reads
both, so an existing reader keeps seeing one stream.

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
# `refused` is not a failed attempt: the dispatch was never admitted, or the
# session died before any model turn.  Scoring it as `failed` would charge a
# proof packet's budget for the provider's refusal (2026-09-12: ~90 sessions).
KNOWN_STATUSES = ("active", "done", "failed", "archived", "refused")
ROLES = (
    "orc",
    "prover",
    "reviewer",
    "simplifier",
    "blueprint",
    "splitter",
    "scout",
    "mathfix",
)

TOKEN_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]*$")

# A key label / endpoint label is a bare token that travels into JSON records
# and into log lines.  It is NEVER interpolated into a shell command or a path
# without quoting, and a label outside this class fails closed rather than
# being silently rewritten to `unknown` (which is what hid the 2026-09-12
# account attribution).  `relay-1`, `space` and `unknown` are inside the class,
# so every historical row stays valid.
LABEL_RE = re.compile(r"^[a-z0-9.-]{1,40}$")
UNKNOWN_LABEL = "unknown"

EVENTS_HEADER = """# Incident and observation log

Dated bullets, one incident each: symptom → diagnosis → fix → lesson.
This file is the raw feed for `local/protocols/EVOLUTION.md`.
"""

EVENTS_SHARD_SUBDIR = "events.d"

EVENTS_SHARD_HEADER = """# Incident and observation log — shard

One session's dated bullets.  `results/telemetry/events.md` holds the history
before sharding; `telemetry.py events --since DATE` reads both.
"""

# ---------------------------------------------------------------------------
# Failure classification
# ---------------------------------------------------------------------------

# The provider's terminal wordings, as literal case-insensitive substrings.
# They are DATA, not code: `local/capacity-policy.json` (shipped by the
# capacity controller) may override the whole table under `failure_patterns`,
# so a provider wording change is a one-file edit rather than a code change.
# Order is precedence: the first class whose pattern appears wins, because a
# concurrency refusal and a 5xx outage both end in an exhausted reconnect and
# the root cause is the one the controller must act on.
# `auth` and `insufficient_balance` come FIRST: they say the KEY is unusable,
# not that it is busy, and a key that is out of quota answers 429 with
# `insufficient_quota` — read as `concurrency_limit` it would lower the cap by a
# quarter forever instead of taking the dead key out of service.  They also
# precede `retries_exhausted` so a 401 that ends in an exhausted reconnect is
# classified by its cause.  `local/capacity-policy.json` marks both
# `"disables": true`; the two tables must name the same classes or the policy's
# disable rule can never fire (see `load_failure_patterns`).
DEFAULT_FAILURE_PATTERNS: dict[str, list[str]] = {
    "auth": [
        "401 Unauthorized",
        "403 Forbidden",
        "invalid_api_key",
        "Invalid API key",
        "invalid_request_error: api key",
    ],
    "insufficient_balance": [
        "INSUFFICIENT_BALANCE",
        "insufficient balance",
        "insufficient_quota",
        "You exceeded your current quota",
        "billing_hard_limit_reached",
    ],
    "concurrency_limit": [
        "Concurrency limit exceeded for account",
        "concurrency limit exceeded",
    ],
    "endpoint_5xx": [
        "503 Service Unavailable",
        "502 Bad Gateway",
        "504 Gateway Timeout",
        "Service Unavailable",
    ],
    "retries_exhausted": [
        "Reconnecting... 5/5",
    ],
    "timeout": [
        "deadline exceeded",
        "request timed out",
        "connection timed out",
    ],
}

#: Classes the policy legitimately names that the stream classifier does not
#: scan for: the dispatcher records `refused` and `endpoint_down` from its own
#: decision, `task_failure` follows from the exit code, and `none`/`unknown` are
#: outcomes rather than wordings.  The controller reads their `counts_as` from
#: the same policy rows, so they are skipped here silently rather than warned
#: about as "unknown failure class".
POLICY_ONLY_FAILURE_CLASSES = ("none", "refused", "endpoint_down", "task_failure",
                               "unknown")

#: Precedence for `classify_failure`: the first class whose pattern appears wins.
#: Derived from the table above so a class added there cannot be silently
#: unreachable — the drift that made `insufficient_balance` a dead letter.
FAILURE_CLASS_ORDER = tuple(DEFAULT_FAILURE_PATTERNS)

# Classes the dispatcher may retry (a refusal is not the session's fault).
TRANSIENT_FAILURE_CLASSES = (
    "refused",
    "endpoint_down",
    "concurrency_limit",
    "endpoint_5xx",
    "retries_exhausted",
)
KNOWN_FAILURE_CLASSES = (
    "none",
    "refused",
    # The key itself is unusable: the answer is "disable this key and say why",
    # not "lower the cap".  Deliberately NOT transient — retrying an invalid or
    # exhausted key five times with backoff only spends the run's wall clock.
    "auth",
    "insufficient_balance",
    # `endpoint_down` is never produced by the stream: it is what the dispatcher
    # records when it refused to reserve on an endpoint the controller had
    # already marked down, so a preflight refusal is distinguishable from a
    # death the provider caused.
    "endpoint_down",
    "concurrency_limit",
    "endpoint_5xx",
    "retries_exhausted",
    "timeout",
    "task_failure",
    "unknown",
)

# `Reconnecting... 3/5`
RETRY_RE = re.compile(r"reconnecting\.{2,}\s*(\d{1,3})\s*/\s*(\d{1,3})", re.I)
URL_HOST_RE = re.compile(r"https?://([A-Za-z0-9.-]{1,64})")
# Exit statuses `timeout(1)` uses for TERM and KILL of the session guard.
TIMEOUT_EXIT_CODES = (124, 137)


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
    """Parse an ISO-8601 timestamp and reject timezone-naive values."""
    if not text:
        return None
    text = text.strip()
    if text.endswith("Z"):
        text = text[:-1] + "+00:00"
    for fmt in (TS_FMT, "%Y-%m-%dT%H:%M:%S.%f%z"):
        try:
            parsed = datetime.strptime(text, fmt)
            return parsed if parsed.tzinfo is not None else None
        except ValueError:
            pass
    try:
        parsed = datetime.fromisoformat(text)
        return parsed if parsed.tzinfo is not None else None
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


def _policy_pattern_table(table) -> dict[str, list] | None:
    """The policy's failure wordings as ``class -> patterns``, or ``None``.

    ``local/capacity-policy.json`` writes the LIST form the capacity controller
    validates — one object per class carrying ``failure_class``, ``counts_as``
    and ``patterns`` — while older knobs wrote a plain object.  Reading only the
    object form is how the policy's ``auth`` and ``insufficient_balance``
    wordings never reached the classifier: the whole table was discarded without
    a word, every quota refusal classified ``unknown``, and ``unknown`` is
    neutral, so a dead key kept its cap.  Both shapes are read here so the file
    the controller validates and the table the classifier uses cannot disagree.
    """
    if isinstance(table, dict):
        return table
    if not isinstance(table, list):
        return None
    out: dict[str, list] = {}
    for row in table:
        if not isinstance(row, dict):
            continue
        name = row.get("failure_class")
        if isinstance(name, str) and name:
            out[name] = row.get("patterns")
    return out or None


def load_failure_patterns(repo_root: Path | None = None) -> dict[str, list[str]]:
    """Failure wordings, from ``local/capacity-policy.json`` when it exists.

    The controller ships that file (work item W3).  Until then — and whenever it
    is missing, malformed, or silent about a class — the built-in table above is
    used, so this function never raises and never returns an empty table: an
    unreadable knob file degrades to today's static behaviour instead of
    classifying every death as ``unknown``.
    """
    patterns = {key: list(value) for key, value in DEFAULT_FAILURE_PATTERNS.items()}
    root = Path(repo_root) if repo_root else REPO_ROOT_DEFAULT
    knob = root / "local" / "capacity-policy.json"
    try:
        raw = json.loads(knob.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return patterns
    table = _policy_pattern_table(raw.get("failure_patterns") if isinstance(raw, dict)
                                 else None)
    if table is None:
        return patterns
    for name, value in table.items():
        if name in POLICY_ONLY_FAILURE_CLASSES:
            continue
        if name not in DEFAULT_FAILURE_PATTERNS:
            warn(f"capacity-policy.json: ignoring unknown failure class {name!r}")
            continue
        if isinstance(value, str):
            value = [value]
        if not isinstance(value, list):
            warn(f"capacity-policy.json: failure_patterns.{name} is not a list")
            continue
        cleaned = [item for item in value if isinstance(item, str) and item.strip()]
        if cleaned:
            patterns[name] = cleaned
    return patterns


def _event_text(events: Sequence[dict[str, Any]]) -> str:
    """One searchable blob of the captured stream, control characters kept out.

    The provider's refusal arrives in different shapes across codex builds
    (an ``error`` event, a stderr passthrough, a message item), so the scan is
    over the serialized events rather than over one field that may move.
    """
    chunks: list[str] = []
    for event in events:
        try:
            chunks.append(json.dumps(event, ensure_ascii=False))
        except (TypeError, ValueError):
            chunks.append(str(event))
    return "\n".join(chunks)


def has_model_output(events: Sequence[dict[str, Any]]) -> bool:
    """Whether the session ever produced a model turn.

    A dispatch that died before this point was never really admitted: it is
    recorded ``refused``, never as a failed attempt against a packet budget.
    """
    for event in events:
        if event.get("type") in ("turn.completed", "turn.started"):
            return True
        if event.get("type") == "item.completed":
            item = event.get("item")
            if isinstance(item, dict) and item.get("item_type") in (
                "assistant_message",
                "agent_message",
                "reasoning",
                "command_execution",
            ):
                return True
    return False


def classify_failure(
    events: Sequence[dict[str, Any]],
    exit_code: int | None = None,
    patterns: dict[str, list[str]] | None = None,
) -> dict[str, Any]:
    """Classify a captured session ending.

    Returns ``{failure_class, failure_detail, failure_endpoint, retries_seen}``.

    ``unknown`` is the safe default and the capacity controller must treat it as
    **neutral** — neither an increase nor a decrease — so that a provider
    wording change degrades to today's static behaviour rather than collapsing
    the cap.  Classes:

    ``concurrency_limit``  the account is at its real limit (retryable)
    ``endpoint_5xx``       the endpoint is down (retryable, trips health)
    ``retries_exhausted``  the client gave up reconnecting (retryable)
    ``timeout``            our own session guard fired (NOT retryable)
    ``task_failure``       a clean nonzero exit with model output (NOT retryable)
    ``none``               exit 0
    ``unknown``            anything else — neutral
    """
    table = patterns if patterns is not None else load_failure_patterns()
    text = _event_text(events)
    lowered = text.lower()

    retries_seen = 0
    retry_total = 0
    for match in RETRY_RE.finditer(text):
        seen, total = int(match.group(1)), int(match.group(2))
        retries_seen = max(retries_seen, seen)
        retry_total = max(retry_total, total)

    matched_class = ""
    matched_pattern = ""
    for name in FAILURE_CLASS_ORDER:
        for pattern in table.get(name) or ():
            if pattern.lower() in lowered:
                matched_class, matched_pattern = name, pattern
                break
        if matched_class:
            break

    if not matched_class and retry_total and retries_seen >= retry_total:
        matched_class, matched_pattern = "retries_exhausted", f"{retries_seen}/{retry_total}"

    endpoint = None
    host = URL_HOST_RE.search(text)
    if host:
        candidate = host.group(1).lower().strip(".")
        if LABEL_RE.match(candidate):
            endpoint = candidate

    if matched_class:
        failure_class, detail = matched_class, matched_pattern
    elif exit_code in TIMEOUT_EXIT_CODES:
        failure_class, detail = "timeout", f"killed by the session guard (exit {exit_code})"
    elif exit_code == 0:
        failure_class, detail = "none", ""
    elif has_model_output(events):
        failure_class, detail = "task_failure", "clean nonzero exit with model output"
    else:
        failure_class, detail = "unknown", ""

    return {
        "failure_class": failure_class,
        "failure_detail": sanitize_text(detail, limit=200) or None,
        "failure_endpoint": endpoint,
        "retries_seen": retries_seen,
    }


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
    model: str | None = None,
    account: str | None = None,
    requested_effort: str | None = None,
    endpoint: str | None = None,
    failure: dict[str, Any] | None = None,
) -> dict[str, Any]:
    record: dict[str, Any] = {
        "name": name,
        "role": role,
    }
    if model:
        record["model"] = model
    if account:
        record["account"] = account
    if requested_effort:
        record["requested_effort"] = requested_effort
    record["issue"] = issue
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
    # The endpoint a failure is attributed to travels on EVERY row, so a key
    # moved between homes keeps its identity and the controller can read health
    # per endpoint instead of per account slot.
    record["endpoint"] = endpoint or UNKNOWN_LABEL
    if failure is not None:
        record["failure_class"] = failure.get("failure_class") or "unknown"
        record["failure_detail"] = failure.get("failure_detail")
        record["failure_endpoint"] = failure.get("failure_endpoint") or record["endpoint"]
        record["retries_seen"] = failure.get("retries_seen") or 0
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
                    and (record.get('dispatcher') != 'native' or existing == record)
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
        # dispatch.sh branches on these: a transient class is retried, and lane,
        # autofix and review callers read them off dispatch.sh's stdout report.
        "DISPATCH_FAILURE_CLASS": record.get("failure_class"),
        "DISPATCH_FAILURE_DETAIL": record.get("failure_detail"),
        "DISPATCH_FAILURE_ENDPOINT": record.get("failure_endpoint"),
        "DISPATCH_RETRIES_SEEN": record.get("retries_seen"),
        "DISPATCH_ENDPOINT": record.get("endpoint"),
        "DISPATCH_KEY_LABEL": record.get("key_label"),
        "DISPATCH_OVERRIDE_MODE": record.get("override_mode"),
        "DISPATCH_USAGE_INPUT": usage.get("input"),
        "DISPATCH_USAGE_OUTPUT": usage.get("output"),
        "DISPATCH_USAGE_TOTAL": (sum(int(usage.get(k) or 0) for k in USAGE_KEYS)
                                 if record.get('usage') is not None else None),
    }
    lines = []
    for key, value in fields.items():
        text = "" if value is None else str(value)
        lines.append(f"{key}={shlex.quote(text)}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


# ---------------------------------------------------------------------------
# events.md and events.d/
# ---------------------------------------------------------------------------


def event_session_label(raw: str | None = None) -> str:
    """Filename-safe shard label for the writing session.

    Two sessions must never touch one path: that is the whole point of the
    shard.  The label is the dispatching session name (``MIPSTARRE_SESSION``)
    reduced to ``[A-Za-z0-9._-]``; an unnamed writer gets ``unknown``, and
    concurrent unnamed writers still serialize on the per-path lock below.
    """
    value = raw if raw is not None else os.environ.get("MIPSTARRE_SESSION", "")
    cleaned = re.sub(r"[^A-Za-z0-9._-]+", "-", (value or "").strip()).strip("-.")
    return cleaned[:60] or "unknown"


def event_shard_path(telemetry_root: Path, date_str: str, session: str) -> Path:
    """``results/telemetry/events.d/<YYYY-MM-DD>-<session>.md``."""
    return telemetry_root / EVENTS_SHARD_SUBDIR / f"{date_str}-{session}.md"


def append_event_bullet(
    path: Path, text: str, date_str: str, header: str = EVENTS_HEADER
) -> str:
    """Append a dated bullet, creating today's ``## YYYY-MM-DD`` section."""
    bullet_lines = sanitize_text(text, limit=8000).split("\n")
    bullet = "- " + bullet_lines[0]
    for continuation in bullet_lines[1:]:
        bullet += "\n  " + continuation.strip()
    heading = f"## {date_str}"
    # The lock is per path: sharded writers never contend, and two writers that
    # do share a path (two unnamed callers) still cannot interleave a bullet.
    with named_lock("events-" + re.sub(r"[^A-Za-z0-9._-]+", "-", path.name)):
        path.parent.mkdir(parents=True, exist_ok=True)
        original = (
            path.read_text(encoding="utf-8") if path.exists() else header
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


DATE_HEADING_RE = re.compile(r"^##\s+(\d{4}-\d{2}-\d{2})")


def read_event_sections(path: Path) -> list[tuple[str, str, str]]:
    """Split a log file into ``(date, heading, body)`` sections.

    Historical headings carry a title or a timestamp after the date
    (``## 2026-09-12T06:38:22Z - Recover primary failures``); only the leading
    date is parsed, and anything before the first dated heading is ignored.
    """
    if not path.exists():
        return []
    sections: list[tuple[str, str, str]] = []
    current_date = ""
    current_heading = ""
    body: list[str] = []
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        match = DATE_HEADING_RE.match(line)
        if match:
            if current_date:
                sections.append((current_date, current_heading, "\n".join(body).strip("\n")))
            current_date, current_heading, body = match.group(1), line, []
            continue
        if current_date:
            body.append(line)
    if current_date:
        sections.append((current_date, current_heading, "\n".join(body).strip("\n")))
    return sections


def collect_events(
    telemetry_root: Path, since: str | None = None, until: str | None = None
) -> list[dict[str, str]]:
    """Merge ``events.md`` and every ``events.d/*.md`` shard, oldest first.

    Existing readers keep working because the pre-shard history is still read
    from ``events.md``; new bullets are found in the shards.
    """
    rows: list[dict[str, str]] = []
    sources = [telemetry_root / "events.md"]
    shard_dir = telemetry_root / EVENTS_SHARD_SUBDIR
    if shard_dir.is_dir():
        sources.extend(sorted(shard_dir.glob("*.md")))
    for source in sources:
        try:
            relative = str(source.relative_to(telemetry_root.parents[1]))
        except (ValueError, IndexError):
            relative = str(source)
        for date_str, heading, body in read_event_sections(source):
            if since and date_str < since:
                continue
            if until and date_str > until:
                continue
            rows.append(
                {"date": date_str, "heading": heading, "body": body, "source": relative}
            )
    rows.sort(key=lambda row: (row["date"], row["source"]))
    return rows


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


def checked_label(value: str | None, what: str) -> str | None:
    """Validate one key/endpoint label, failing closed outside the class."""
    if value is None or value == "":
        return None
    if not LABEL_RE.match(value):
        fail(
            f"{what} {value!r} is not [a-z0-9.-]{{1,40}}.\n"
            "  Labels travel into records and log lines; a malformed one is "
            "refused rather than rewritten to 'unknown', which would hide which "
            "key a failure belongs to."
        )
    return value


def native_rollout(path: Path, thread: str, *, role: str = 'orc', job_class: str = 'general',
                   requested_model: str | None = None, hardness_reason: str | None = None,
                   grandfathered: bool = False, activation_at: str | None = None) -> dict:
    """Read only attributable native metadata; never serialize credential-home paths."""
    rows, errors = read_jsonl(path)
    if errors:
        raise ValueError('malformed native rollout')
    meta = next((row for row in rows if row.get('type') == 'session_meta' and
                 row.get('payload', {}).get('id') == thread), None)
    if not meta:
        raise ValueError('native thread identity missing')
    source = meta['payload'].get('source', {})
    spawn = source.get('subagent', {}).get('thread_spawn', {}) if isinstance(source, dict) else {}
    result = dict(thread_id=thread, parent_thread_id=spawn.get('parent_thread_id'),
                  agent_path=spawn.get('agent_path'), start=meta['timestamp'],
                  end=None, final=None, assigned=None, turn_start=None, observed_usage=None)
    turn = None
    contexts, child_turns, first_assignment = {}, set(), None
    # Forks copy parent events with rewritten timestamps; require a child assignment.
    for row in rows:
        payload = row.get('payload', {})
        if row.get('type') == 'turn_context':
            context = dict(model=payload.get('model'), effort=payload.get('effort'))
            if payload.get('turn_id'):
                contexts.setdefault(payload['turn_id'], []).append(context)
            elif turn:
                contexts.setdefault(turn, []).append(context)
        elif (row.get('type') == 'response_item' and payload.get('type') == 'agent_message' and
                payload.get('author') == spawn.get('agent_path', '').rsplit('/', 1)[0] and
                payload.get('recipient') == spawn.get('agent_path')):
            result.update(assigned=row['timestamp'], end=None, final=None)
            first_assignment = first_assignment or row['timestamp']
            child_turns.add(turn)
        elif row.get('type') == 'event_msg':
            if payload.get('type') == 'task_started':
                turn = payload.get('turn_id')
                result.update(end=None, final=None, turn_start=row['timestamp'])
                if first_assignment:
                    child_turns.add(turn)
            elif (payload.get('type') == 'task_complete' and result['assigned'] and turn and
                  payload.get('turn_id') == turn):
                result.update(end=row['timestamp'], final=payload.get('last_agent_message'))
            elif payload.get('type') == 'token_count' and result['assigned']:
                usage = (payload.get('info') or {}).get('total_token_usage')
                if isinstance(usage, dict):
                    observed = {key: usage[key] for key in ('input_tokens', 'cached_input_tokens',
                        'output_tokens', 'reasoning_output_tokens', 'total_tokens')
                        if type(usage.get(key)) is int and usage[key] >= 0}
                    if observed:
                        result['observed_usage'] = observed
    from model_policy import load_policy, observe_model
    if grandfathered and load_policy()['schema_version'] != 0:
        activation, started = parse_ts(activation_at), parse_ts(result['turn_start'])
        if not activation or not started or started >= activation:
            raise ValueError('grandfathered task requires verified pre-activation turn evidence')
    active_contexts = contexts.get(turn, [])
    if not active_contexts:
        raise ValueError('native effective model requires bound current-turn context')
    for context in active_contexts:
        selection = observe_model(role, job_class, context['model'], context['effort'],
                                  requested_model, hardness_reason, grandfathered)
    if any(context != active_contexts[0] for context in active_contexts):
        raise ValueError('mixed current-turn model/effort contexts are not admissible')
    if not child_turns or any(not contexts.get(child_turn) for child_turn in child_turns):
        raise ValueError('native affinity requires bound context for every attributable child turn')
    if any(context != active_contexts[0]
           for child_turn in child_turns for context in contexts[child_turn]):
        raise ValueError('resuming an existing native thread cannot switch its model or effort')
    result.update(model=active_contexts[-1]['model'],
                  requested_effort=active_contexts[-1]['effort'], model_contexts=active_contexts)
    result.update(requested_model=requested_model,
                  selected_model=selection['model'] if requested_model is not None else None,
                  effective_model=result['model'], first_assignment=first_assignment,
                  job_class=job_class, model_policy=selection)
    return result


def record_native(args: argparse.Namespace) -> int:
    activation = getattr(args, 'activation_at', None) or os.environ.get('MIPSTARRE_MODEL_POLICY_ACTIVATION_AT')
    observation = native_rollout(args.rollout, args.thread_id, role=args.role,
        job_class=getattr(args, 'job_class', 'general'),
        requested_model=getattr(args, 'requested_model', None),
        hardness_reason=getattr(args, 'hardness_reason', None),
        grandfathered=getattr(args, 'dispatch_kind', 'grandfathered') == 'grandfathered',
        activation_at=activation)
    end = observation['end']
    if args.status == 'done' and not end:
        raise ValueError('native turn has not completed')
    kind = getattr(args, 'dispatch_kind', 'grandfathered')
    if observation['parent_thread_id'] != args.root_thread_id:
        raise ValueError('native observation root does not match actual parent')
    first, turn = parse_ts(observation['first_assignment']), parse_ts(observation['turn_start'])
    activated, started = parse_ts(activation), parse_ts(observation['start'])
    if activated and started and started >= activated and first and turn and turn <= first:
        kind = 'new'
    if kind == 'new':
        if not first or not turn or turn > first:
            raise ValueError('a resumed native task is not a new dispatch')
        if not activated or not started or started < activated:
            raise ValueError('new dispatch must follow its explicit activation boundary')
    key_label = checked_label(args.key_label, '--key-label')
    record = {key: value for key, value in observation.items() if key != 'final'}
    record.update(name=args.name, role=args.role, issue=args.issue, pr=args.pr,
                  worktree=str(args.worktree), root_thread_id=args.root_thread_id,
                  endpoint=checked_label(getattr(args, 'endpoint', None), '--endpoint')
                  or key_label or UNKNOWN_LABEL,
                  key_label=key_label, account=key_label, dispatcher='native',
                  dispatch_kind=kind, activation_at=activation,
                  status=args.status, usage=None, usage_scope='unknown',
                  usage_provenance='rollout token_count.total_token_usage; not additive',
                  wire_effort=None, returned_effort=None,
                  wall_s=(parse_ts(end) - parse_ts(observation['start'])).total_seconds()
                  if end else None)
    append_session_record(telemetry_dir(args) / 'sessions.jsonl', record)
    return 0


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

    key_label = checked_label(args.key_label, "--key-label")
    endpoint = checked_label(getattr(args, "endpoint", None), "--endpoint")

    failure = classify_failure(
        events,
        exit_code=args.exit_code,
        patterns=load_failure_patterns(args.repo_root),
    )
    if getattr(args, "failure_class", None):
        # The caller saw something the stream cannot show — a router refusal
        # leaves no capture at all.  It may only name a documented class.
        if args.failure_class not in KNOWN_FAILURE_CLASSES:
            fail(f"--failure-class {args.failure_class!r} is not one of {KNOWN_FAILURE_CLASSES}")
        failure["failure_class"] = args.failure_class

    status = args.status
    if status is None:
        status = "done" if (args.exit_code or 0) == 0 else "failed"
        # Never admitted, or dead before the first model turn: `refused`, so the
        # provider's refusal is not scored as a failed attempt against a proof
        # packet's budget (2026-09-12, ~90 sessions lost to 503s and the cap).
        if (
            status == "failed"
            and failure["failure_class"] in TRANSIENT_FAILURE_CLASSES
            and not turns
            and not has_model_output(events)
        ):
            status = "refused"
    if status not in KNOWN_STATUSES:
        warn(f"status {status!r} is not one of {KNOWN_STATUSES}")

    try:
        capture_field = str(capture.relative_to(args.repo_root.resolve()))
    except ValueError:
        capture_field = str(capture)

    record = session_record(
        name=name,
        role=role,
        model=args.model,
        account=args.account,
        requested_effort=args.requested_effort,
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
        endpoint=endpoint or key_label,
        failure=failure,
    )
    if args.continuation_json:
        record['continuation'] = json.loads(args.continuation_json)
    if getattr(args, 'model_policy_file', None):
        selection = json.loads(args.model_policy_file.read_text())
        if (selection.get('model') != args.model or selection.get('role') != role or
                selection.get('requested_effort') != args.requested_effort):
            fail('model policy snapshot differs from the dispatched configuration')
        observed = [event.get('payload', {}).get('model') for event in events
                    if event.get('type') == 'turn_context' and event.get('payload', {}).get('model')]
        mismatch = any(model != args.model for model in observed)
        record.update(requested_model=selection['requested_model'], selected_model=args.model,
                      effective_model=observed[-1] if observed and len(set(observed)) == 1 else None,
                      job_class=selection['job_class'], model_policy=selection,
                      dispatch_kind=getattr(args, 'dispatch_kind', None),
                      activation_at=getattr(args, 'activation_at', None))
        # An owner model override is recorded on the row, not hidden in a PATH
        # shim: the ratio audit excludes override-period rows by this field
        # instead of reading them as violations, and sessions.jsonl keeps
        # naming the model that actually ran (2026-09-12 telemetry inaccuracy).
        if selection.get('override_mode'):
            record.update(override_mode=selection['override_mode'],
                          override_source=selection.get('override_source'))
        if mismatch:
            record.update(status='failed', model_policy_mismatch=True)
    if key_label:
        record.update(key_label=key_label, wire_effort=None, returned_effort=None,
                      usage_provenance='codex exec turn.completed; native delegation disabled')
        if not turns:
            record.update(usage=None, usage_scope='unknown')
        if record.get('rollout'):
            record['rollout'] = Path(record['rollout']).name

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
    return 4 if record.get('model_policy_mismatch') else 0


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
    session = event_session_label(getattr(args, "session", None))
    header = EVENTS_SHARD_HEADER
    if args.out is not None:
        path = args.out
        if path.name == "events.md":
            header = EVENTS_HEADER
    else:
        # Sharded by (date, session): two sessions never touch one path, so a
        # merge of `main` no longer conflicts on the incident log.  The path is
        # inside the results/telemetry allowlist pr_merge tolerates.
        path = event_shard_path(telemetry_dir(args), date_str, session)
    bullet = append_event_bullet(path, text, date_str, header)
    sys.stdout.write(bullet + "\n")
    sys.stderr.write(f"telemetry.py: wrote {path}\n")
    return 0


def cmd_events(args: argparse.Namespace) -> int:
    """Read events.md and every events.d/ shard as one stream."""
    for bound in (args.since, args.until):
        if bound and not re.fullmatch(r"\d{4}-\d{2}-\d{2}", bound):
            fail(f"expected YYYY-MM-DD, got {bound!r}", code=2)
    rows = collect_events(telemetry_dir(args), args.since, args.until)
    if args.format == "json":
        sys.stdout.write(json.dumps(rows, ensure_ascii=False, indent=2) + "\n")
        return 0
    for row in rows:
        sys.stdout.write(f"{row['heading']}\n")
        sys.stdout.write(f"<!-- source: {row['source']} -->\n")
        if row["body"]:
            sys.stdout.write(row["body"] + "\n")
        sys.stdout.write("\n")
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
    summarize.add_argument("--model", help="explicitly selected Codex model")
    summarize.add_argument('--model-policy-file', type=Path,
                           help='immutable dispatch-time model-selection snapshot')
    summarize.add_argument('--dispatch-kind', choices=('new', 'resume', 'grandfathered'))
    summarize.add_argument('--activation-at')
    summarize.add_argument("--account", choices=("primary", "second"))
    summarize.add_argument(
        '--key-label',
        help="key label for the account that ran the session; [a-z0-9.-]{1,40} "
             "(relay-1|space|unknown remain valid)",
    )
    summarize.add_argument(
        '--endpoint',
        help="endpoint the session was routed to; failures and health are "
             "attributed to it, so a key moved between homes keeps its identity",
    )
    summarize.add_argument(
        '--failure-class',
        help=f"override the classification from the stream; one of {KNOWN_FAILURE_CLASSES}. "
             "Used when the dispatcher knows more than the capture (a router "
             "refusal leaves no capture at all).",
    )
    summarize.add_argument("--continuation-json", help="validated checkpoint and shared budget link")
    summarize.add_argument(
        "--requested-effort",
        help="effective reasoning effort requested from Codex, not provider measurement",
    )
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

    native = subparsers.add_parser('native-record', help='record a native thread observation')
    native.add_argument('rollout', type=Path)
    for option in ('name', 'thread-id', 'root-thread-id', 'issue'):
        native.add_argument('--' + option, required=True)
    native.add_argument('--role', choices=ROLES, required=True)
    native.add_argument('--key-label', required=True,
                        help="[a-z0-9.-]{1,40}; relay-1|space remain valid")
    native.add_argument('--endpoint', help="endpoint label (default: the key label)")
    native.add_argument('--worktree', type=Path, required=True)
    native.add_argument('--pr')
    native.add_argument('--job-class', default='general')
    native.add_argument('--hardness-reason')
    native.add_argument('--dispatch-kind', choices=('new', 'resume', 'grandfathered'),
                        default='grandfathered')
    native.add_argument('--activation-at')
    native.add_argument('--requested-model', choices=('gpt-6-astra', 'gpt-5.6-sol', 'auto'))
    native.add_argument('--status', choices=('active', 'done', 'failed'), required=True)
    native.set_defaults(func=record_native)

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

    event = subparsers.add_parser(
        "event", help="append a dated bullet to results/telemetry/events.d/"
    )
    event.add_argument(
        "--text",
        required=True,
        help="bullet text ('-' reads stdin): symptom, diagnosis, fix, lesson",
    )
    event.add_argument("--date", help="YYYY-MM-DD section (default: today)")
    event.add_argument(
        "--session",
        help="shard label (default: $MIPSTARRE_SESSION, else 'unknown')",
    )
    event.add_argument("--out", type=Path, help="override the output file")
    event.set_defaults(func=cmd_event)

    events = subparsers.add_parser(
        "events",
        help="read events.md and every events.d/ shard as one dated stream",
    )
    events.add_argument("--since", help="earliest YYYY-MM-DD to print")
    events.add_argument("--until", help="latest YYYY-MM-DD to print")
    events.add_argument("--format", choices=("md", "json"), default="md")
    events.set_defaults(func=cmd_events)

    classify = subparsers.add_parser(
        "classify-failure",
        help="classify how a captured session ended (one shared classifier)",
    )
    classify.add_argument("capture", type=Path, help="the session's capture .jsonl")
    classify.add_argument("--exit", dest="exit_code", type=int, default=None,
                          help="the session's exit code, when known")
    classify.add_argument("--field",
                          choices=("failure_class", "failure_detail",
                                   "failure_endpoint", "retries_seen"),
                          help="print one field instead of the JSON object")
    classify.set_defaults(func=cmd_classify_failure)

    return parser


def cmd_classify_failure(args: argparse.Namespace) -> int:
    """Expose ``classify_failure`` to the shell tools.

    ``local/bin/janitor.sh`` (``capture_class`` in ``auto`` mode) and
    ``local/protocols/capacity.md`` both say the pipeline has ONE failure
    classifier.  Without this subcommand that was a claim, not a fact: the
    janitor's probe for it always failed and it silently fell back to its own
    built-in string matching, so the janitor and the capacity controller could
    classify the same death differently.
    """
    events, parse_errors = read_jsonl(args.capture)
    if parse_errors:
        sys.stderr.write(
            f"telemetry.py: {args.capture}: {parse_errors} unparsable line(s); "
            "classifying the rest\n")
    result = classify_failure(
        events, args.exit_code,
        patterns=load_failure_patterns(args.repo_root))
    if args.field:
        value = result.get(args.field)
        sys.stdout.write(f"{'' if value is None else value}\n")
    else:
        sys.stdout.write(json.dumps(result, ensure_ascii=False) + "\n")
    return 0


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
