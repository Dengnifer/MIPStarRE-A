#!/usr/bin/env python3
"""Measured, self-healing admission capacity for the dispatcher accounts.

`local/protocols/capacity.md` is normative; this is the implementation.  On
2026-09-12 the caps were edited by hand ten times while ~90 sessions died: 69
into a primary endpoint that answered 503 for half an hour, the rest above the
second account's real provider limit.  Two independent paths replace both
interventions.  **AIMD** over refusals: one slot up per quiet window, and on a
refusal down to just under the concurrency that was refused, inside the brief's
``nominal_limit - external_reserved`` ceiling.  **Endpoint health**: three
``endpoint_5xx`` deaths in two minutes write cap 0 at once, and the way back is
a half-open, single-flight, read-only probe that restores cap 1 — never the
pre-outage cap.  Counters come from the ``failure_class`` and ``endpoint``
fields of ``sessions.jsonl``, never from a fresh grep; a class the policy does
not name is neutral in both directions.

This tool is the sole writer of ``watchdog/capacity/state.json`` and of the
derived ``watchdog/max-codex{,-primary,-second}`` files.

Usage:
    capacity_controller.py init [--force] [--dry-run] | tick [--dry-run]
    capacity_controller.py set ACCOUNT CAP | pause [--reason T] | resume
    capacity_controller.py status [--json | --brief]
"""

from __future__ import annotations

import argparse
import fcntl
import json
import math
import os
import shlex
import subprocess
import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any, Iterable

sys.path.insert(0, str(Path(__file__).resolve().parent))

from account_router import ACCOUNTS, live_pids  # noqa: E402
from wf_util import atomic_write  # noqa: E402

STATE_SCHEMA = "mipstarre-capacity-state/1"
POLICY_SCHEMA_VERSION = 1
TS_FMT = "%Y-%m-%dT%H:%M:%SZ"
#: Tail of ``sessions.jsonl`` parsed per tick; the counters look back 5 minutes.
TAIL_BYTES = 1 << 20
#: Every operator-facing failure.  The cap files are untouched on this path.
EXIT_FAIL = 2
_COUNTS_AS = ("refusal", "death", "neutral")
_HEALTH_KEYS = ("fivexx_threshold", "fivexx_window_s", "probe_backoff_s",
                "probe_backoff_max_s", "probes_to_recover")
_STATES = ("up", "degraded", "down")


class ControllerError(RuntimeError):
    """Operator-facing failure: printed without a traceback, exit ``EXIT_FAIL``."""


# --- locations.  ``wf_util`` resolves the cache root once at import time, which
# a test with a temporary root cannot override; these re-read the environment at
# call time and otherwise mean exactly what ``wf_util`` means. ----------------


def _env_path(name: str, default: Path) -> Path:
    value = os.environ.get(name)
    return Path(value).expanduser() if value else default


def cache_root() -> Path:
    return _env_path("MIPSTARRE_CACHE_ROOT", Path("~/.cache/mipstarre-dev").expanduser())


def repo_root() -> Path:
    return _env_path("MIPSTARRE_REPO_ROOT", Path(__file__).resolve().parents[2])


def telemetry_dir() -> Path:
    return _env_path("MIPSTARRE_TELEMETRY_DIR", repo_root() / "results" / "telemetry")


def watchdog_dir() -> Path:
    return cache_root() / "watchdog"


def capacity_dir() -> Path:
    return watchdog_dir() / "capacity"


def state_path() -> Path:
    return capacity_dir() / "state.json"


def health_path(account: str) -> Path:
    return capacity_dir() / f"health-{account}.json"


def utcnow() -> datetime:
    return datetime.now(timezone.utc)


def ts(moment: datetime | None) -> str | None:
    return None if moment is None else moment.astimezone(timezone.utc).strftime(TS_FMT)


def parse_ts(text: Any) -> datetime | None:
    """ISO-8601 in, aware datetime out; a naive value is read as UTC.

    ``telemetry.py`` writes local time with a numeric offset (``+0900``), which
    ``datetime.fromisoformat`` rejects before Python 3.11.
    """
    if not isinstance(text, str) or not text.strip():
        return None
    raw = text.strip()
    parsed = None
    for reader in (datetime.fromisoformat,
                   lambda value: datetime.strptime(value, "%Y-%m-%dT%H:%M:%S%z"),
                   lambda value: datetime.strptime(value, "%Y-%m-%dT%H:%M:%S.%f%z")):
        try:
            parsed = reader(raw[:-1] + "+00:00" if raw.endswith("Z") else raw)
            break
        except ValueError:
            continue
    if parsed is None:
        return None
    return parsed if parsed.tzinfo else parsed.replace(tzinfo=timezone.utc)


# --- policy and run mode ---------------------------------------------------


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise ControllerError(message)


def _int(value: Any, what: str, *, minimum: int) -> int:
    _require(isinstance(value, int) and not isinstance(value, bool) and value >= minimum,
             f"{what} must be an integer >= {minimum}, got {value!r}")
    return int(value)


def load_policy(path: Path | None = None) -> dict:
    """Read and validate the knob file; every failure precedes every write."""
    path = path or _env_path("MIPSTARRE_CAPACITY_POLICY",
                             repo_root() / "local" / "capacity-policy.json")
    try:
        policy = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as exc:
        raise ControllerError(f"{path}: capacity policy is missing or unreadable ({exc})") from exc
    _require(isinstance(policy, dict) and policy.get("schema_version") == POLICY_SCHEMA_VERSION,
             f"{path}: an object with schema_version {POLICY_SCHEMA_VERSION} is required")
    # The ceiling is the owner's, and a knob file may never raise it.
    _require(policy.get("ceiling_source") == "brief", f"{path}: ceiling_source must be 'brief'")
    _require(isinstance(policy.get("windows"), dict) and isinstance(policy.get("defaults"), dict)
             and isinstance(policy.get("accounts"), dict),
             f"{path}: windows, defaults and accounts must be objects")
    for key in ("counter_window_s", "measured_hold_s", "probe_timeout_s"):
        _int(policy["windows"].get(key), f"{path}: windows.{key}", minimum=1)
    _check_knobs(policy["defaults"], f"{path}: defaults")
    for name, entry in policy["accounts"].items():
        _require(isinstance(entry, dict), f"{path}: accounts.{name} must be an object")
        _check_knobs(knobs_for(policy, name), f"{path}: accounts.{name}")
    _check_patterns(policy.get("failure_patterns"), path)
    return policy


def _check_knobs(entry: dict, what: str) -> None:
    _int(entry.get("floor"), f"{what}.floor", minimum=0)
    aimd, health = entry.get("aimd"), entry.get("health")
    _require(isinstance(aimd, dict) and isinstance(health, dict),
             f"{what}: aimd and health must be objects")
    _int(aimd.get("increase"), f"{what}.aimd.increase", minimum=1)
    _int(aimd.get("quiet_window_s"), f"{what}.aimd.quiet_window_s", minimum=1)
    _require(isinstance(aimd.get("decrease"), (int, float))
             and not isinstance(aimd["decrease"], bool) and 0 < float(aimd["decrease"]) < 1,
             f"{what}.aimd.decrease must lie in (0, 1)")
    for key in _HEALTH_KEYS:
        _int(health.get(key), f"{what}.health.{key}", minimum=1)
    _require(health["probe_backoff_max_s"] >= health["probe_backoff_s"],
             f"{what}.health.probe_backoff_max_s must be at least probe_backoff_s")


def _check_patterns(patterns: Any, path: Path) -> None:
    _require(isinstance(patterns, list) and patterns,
             f"{path}: failure_patterns must be a non-empty array")
    seen: set[str] = set()
    for index, entry in enumerate(patterns):
        where = f"{path}: failure_patterns[{index}]"
        _require(isinstance(entry, dict), f"{where} must be an object")
        _require(isinstance(entry.get("failure_class"), str) and entry["failure_class"]
                 and entry["failure_class"] not in seen,
                 f"{where}.failure_class must be a unique non-empty string")
        seen.add(entry["failure_class"])
        _require(entry.get("counts_as") in _COUNTS_AS,
                 f"{where}.counts_as must be one of {_COUNTS_AS}")
        _require(isinstance(entry.get("patterns"), list)
                 and all(isinstance(item, str) for item in entry["patterns"]),
                 f"{where}.patterns must be an array of strings")
    _require("unknown" in seen, f"{path}: failure_patterns must define the 'unknown' class")


def knobs_for(policy: dict, account: str) -> dict:
    """Per-account knobs over the defaults, one level deep."""
    merged = json.loads(json.dumps(policy.get("defaults", {})))
    for key, value in policy.get("accounts", {}).get(account, {}).items():
        if isinstance(value, dict) and isinstance(merged.get(key), dict):
            merged[key].update(value)
        else:
            merged[key] = value
    return merged


def class_roles(policy: dict) -> dict[str, str]:
    """``failure_class`` → ``refusal`` | ``death`` | ``neutral``."""
    return {entry["failure_class"]: entry["counts_as"] for entry in policy["failure_patterns"]}


def load_run_mode(path: Path | None = None) -> dict:
    """Read and validate ``watchdog/run-mode.json`` (``run_mode.py`` writes it).

    Only the fields consumed here are validated, and the account list is accepted
    both as the brief's array and as a name-keyed object.  A missing or malformed
    file is a hard failure: never "zero capacity" and never "unlimited".
    """
    path = path or _env_path("MIPSTARRE_RUN_MODE", watchdog_dir() / "run-mode.json")
    try:
        mode = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as exc:
        raise ControllerError(f"{path}: run mode is missing or unreadable ({exc}); apply the "
                              "owner's brief first: run_mode.py apply --brief PATH") from exc
    _require(isinstance(mode, dict), f"{path}: run mode must be an object")
    raw = mode.get("accounts")
    if isinstance(raw, dict):
        entries = [dict(value, name=value.get("name", key)) for key, value in raw.items()
                   if isinstance(value, dict)]
        _require(len(entries) == len(raw), f"{path}: every account must be an object")
    else:
        _require(isinstance(raw, list) and raw, f"{path}: accounts must be a non-empty array")
        entries = list(raw)
    accounts: dict[str, dict] = {}
    for entry in entries:
        _require(isinstance(entry, dict), f"{path}: every account must be an object")
        name = entry.get("name")
        _require(isinstance(name, str) and name and name not in accounts,
                 f"{path}: account name must be a unique non-empty string, got {name!r}")
        nominal = _int(entry.get("nominal_limit"), f"{path}: {name}.nominal_limit", minimum=0)
        reserved = _int(entry.get("external_reserved"), f"{path}: {name}.external_reserved",
                        minimum=0)
        _require(reserved <= nominal,
                 f"{path}: {name}.external_reserved ({reserved}) exceeds nominal_limit ({nominal})")
        _require(isinstance(entry.get("enabled", True), bool),
                 f"{path}: {name}.enabled must be true or false")
        _require(isinstance(entry.get("endpoint") or name, str),
                 f"{path}: {name}.endpoint must be a string")
        accounts[name] = {"name": name, "endpoint": entry.get("endpoint") or name,
                          "label": entry.get("label") or "", "nominal_limit": nominal,
                          "codex_home": entry.get("codex_home") or "",
                          "external_reserved": reserved, "enabled": entry.get("enabled", True)}
    _require(bool(accounts), f"{path}: the brief must name at least one account")
    run = mode.get("run") if isinstance(mode.get("run"), dict) else {}
    return {"accounts": accounts, "run": run,
            "brief_ref": (mode.get("brief_sha256") or mode.get("brief_ref")
                          or run.get("label") or str(path))}


# --- observations ----------------------------------------------------------


def count_live(accounts: Iterable[str]) -> dict[str, int]:
    """Live worker markers per account, under the router's own lock."""
    root = cache_root() / "accounts"
    root.mkdir(parents=True, exist_ok=True)
    with (root / "router.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        return {name: len(live_pids(root / name)) for name in accounts}


def count_waiters() -> int:
    """Dispatchers blocked in ``account_router.py reserve``; advisory only."""
    try:
        result = subprocess.run(["pgrep", "-f", r"account_router\.py reserve"],
                                capture_output=True, text=True, timeout=10)
    except (OSError, subprocess.SubprocessError):
        return 0
    return len([line for line in result.stdout.splitlines() if line.strip()])


def read_session_rows(path: Path, since: datetime, *, tail_bytes: int = TAIL_BYTES) -> list[dict]:
    """Rows newer than *since* from the tail of ``sessions.jsonl``.

    The registry grows for the life of the project and the counters never look
    back further than five minutes.  A malformed row is skipped, not fatal.
    """
    try:
        size = path.stat().st_size
        with path.open("rb") as handle:
            if size > tail_bytes:
                handle.seek(size - tail_bytes)
                handle.readline()  # drop the partial row the seek landed inside
            blob = handle.read()
    except OSError:
        return []
    rows = []
    for line in blob.decode("utf-8", errors="replace").splitlines():
        try:
            row = json.loads(line)
        except ValueError:
            continue
        if not isinstance(row, dict):
            continue
        moment = parse_ts(row.get("end")) or parse_ts(row.get("start")) or parse_ts(row.get("ts"))
        if moment is not None and moment >= since:
            rows.append(dict(row, _ts=moment))
    return rows


def observe(rows: list[dict], name: str, endpoints: dict[str, str], roles: dict[str, str],
            now: datetime, *, counter_window_s: int, fivexx_window_s: int) -> dict:
    """Refusal and death counters for one account.

    A ``failure_class`` the policy does not name — including the literal
    ``unknown`` — is counted in neither direction, so a reworded provider message
    leaves the cap where a hand-set cap would have been instead of collapsing it.
    """
    bucket: dict[str, Any] = {"refusals": 0, "deaths": 0, "neutral": 0,
                              "deaths_by_class": {}, "refusal_times": [], "fivexx_times": []}
    counter_since = now - timedelta(seconds=counter_window_s)
    fivexx_since = now - timedelta(seconds=fivexx_window_s)
    for row in rows:
        owner = next((endpoints[row[field]] for field in
                      ("endpoint", "failure_endpoint", "account", "key_label")
                      if isinstance(row.get(field), str) and row[field] in endpoints), None)
        failure_class = row.get("failure_class")
        if owner != name or not isinstance(failure_class, str) or not failure_class:
            continue
        if failure_class == "endpoint_5xx" and row["_ts"] >= fivexx_since:
            bucket["fivexx_times"].append(row["_ts"])
        if row["_ts"] < counter_since:
            continue
        role = roles.get(failure_class, "neutral")
        if role == "refusal":
            bucket["refusals"] += 1
            bucket["refusal_times"].append(row["_ts"])
        elif role == "death":
            bucket["deaths"] += 1
            bucket["deaths_by_class"][failure_class] = \
                bucket["deaths_by_class"].get(failure_class, 0) + 1
        else:
            bucket["neutral"] += 1
    bucket["refusal_times"].sort()
    bucket["fivexx_times"].sort()
    return bucket


# --- documents and the derived cap files -----------------------------------


def _read_json(path: Path) -> dict | None:
    try:
        document = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return None
    return document if isinstance(document, dict) else None


def _write_json(path: Path, document: dict) -> None:
    atomic_write(path, json.dumps(document, ensure_ascii=False, indent=2) + "\n")


def new_account_state(name: str) -> dict:
    return {"cap": 0, "floor": 0, "ceiling": 0, "health": "up", "saved_cap": None,
            "external_reserved": 0, "nominal_limit": 0, "enabled": True, "endpoint": name,
            "quiet_since": None, "decrease_window_until": None, "refusal_cursor": None,
            "observed_refusal_floor": None, "measured_limit": None, "measured_since": None,
            "measured_level": None, "last_change": None}


def new_state(brief_ref: str) -> dict:
    return {"schema": STATE_SCHEMA, "updated": None, "brief_ref": brief_ref,
            "paused_at": None, "accounts": {}}


def load_state() -> dict | None:
    document = _read_json(state_path())
    if not document or document.get("schema") != STATE_SCHEMA:
        return None
    return document if isinstance(document.get("accounts"), dict) else None


def load_health(account: str, endpoint: str, now: datetime, backoff_s: int) -> dict:
    document = _read_json(health_path(account)) or {}
    if document.get("state") not in _STATES:
        document = {"state": "up", "since": ts(now)}
    if not isinstance(document.get("backoff_s"), int) or document["backoff_s"] <= 0:
        document["backoff_s"] = backoff_s
    document.setdefault("consecutive_5xx", 0)
    document.setdefault("probes_ok", 0)
    document.setdefault("next_probe_at", None)
    return dict(document, account=account, endpoint=endpoint)


def _write_cap_file(path: Path, value: int) -> None:
    """Write one cap file, refusing anything that is not a nonneg integer.

    The guard is the point: an empty or non-numeric cap file makes every dispatch
    exit 4 with ``invalid literal for int()``, silently stopping all work.
    """
    text = f"{int(value)}\n"
    _require(int(value) >= 0 and text.strip().isdecimal(),
             f"{path}: refusing to write a cap that is not a nonnegative integer ({value!r})")
    atomic_write(path, text)


def write_cap_files(caps: dict[str, int]) -> int:
    """Write the legacy derived outputs; ``max-codex`` is mechanically the sum.

    It therefore cannot disagree with the per-account files.  It is a display and
    lane-parallelism value only: admission reads the per-account files
    (``local/protocols/capacity.md`` §4).
    """
    effective = {name: int(value) for name, value in caps.items()}
    directory = watchdog_dir()
    directory.mkdir(parents=True, exist_ok=True)
    for name in (*ACCOUNTS, *(name for name in effective if name not in ACCOUNTS)):
        _write_cap_file(directory / f"max-codex-{name}", effective.get(name, 0))
    _write_cap_file(directory / "max-codex", sum(effective.values()))
    return sum(effective.values())


# --- endpoint health -------------------------------------------------------


def probe_account(account: str, codex_home: str, timeout_s: int) -> bool:
    """One bounded, read-only probe of *account*'s endpoint.

    A health check, not a work session: read-only sandbox, no persona, no task,
    no worktree write, nothing appended to ``sessions.jsonl``.  Its record is the
    health file and the ``capacity`` row in ``stages.jsonl``.
    ``MIPSTARRE_CAPACITY_PROBE_CMD`` replaces the command for the health tests
    and for a dry run on a host without ``codex``.
    """
    override = os.environ.get("MIPSTARRE_CAPACITY_PROBE_CMD")
    command = shlex.split(override) if override else [
        os.environ.get("MIPSTARRE_CODEX_BIN", "codex"), "exec", "--sandbox", "read-only",
        "-C", str(repo_root()), "--", "Reply with the single word: ok"]
    env = dict(os.environ, MIPSTARRE_CAPACITY_PROBE=account)
    if codex_home:
        env["CODEX_HOME"] = str(Path(codex_home).expanduser())
    try:
        return subprocess.run(command, capture_output=True, text=True, timeout=timeout_s,
                              env=env).returncode == 0
    except (OSError, subprocess.SubprocessError):
        return False


def _try_probe(account: str, codex_home: str, timeout_s: int) -> tuple[bool, bool]:
    """``(ran, succeeded)`` — single-flight, so two ticks cannot probe at once."""
    capacity_dir().mkdir(parents=True, exist_ok=True)
    with (capacity_dir() / f"probe-{account}.lock").open("a") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except OSError:
            return False, False
        try:
            return True, probe_account(account, codex_home, timeout_s)
        finally:
            fcntl.flock(lock, fcntl.LOCK_UN)


def update_health(account: str, health: dict, counters: dict, knobs: dict, now: datetime,
                  *, no_probe: bool, codex_home: str, probe_timeout_s: int) -> str:
    """Advance the endpoint health machine one tick; returns what it did.

    Independent of AIMD in both directions: a refusal never changes health and a
    5xx never runs the AIMD arithmetic.
    """
    fivexx = len(counters["fivexx_times"])
    base = knobs["probe_backoff_s"]
    health.update(consecutive_5xx=fivexx, updated=ts(now))
    if health["state"] != "down":
        if fivexx >= knobs["fivexx_threshold"]:
            health.update(state="down", since=ts(now), probes_ok=0, backoff_s=base,
                          next_probe_at=ts(now + timedelta(seconds=base)))
            return "trip"
        if fivexx:
            if health["state"] != "degraded":
                health.update(state="degraded", since=ts(now))
            return "degraded"
        if health["state"] != "up":
            health.update(state="up", since=ts(now))
            return "clear"
        return "none"
    if no_probe:  # an operator hold, or a key the brief disabled
        return "probe-held"
    due = parse_ts(health.get("next_probe_at"))
    if due is not None and now < due:
        return "probe-waiting"
    ran, ok = _try_probe(account, codex_home, probe_timeout_s)
    if not ran:
        return "probe-inflight"
    if not ok:
        health["probes_ok"] = 0
        health["backoff_s"] = min(int(health["backoff_s"]) * 2, knobs["probe_backoff_max_s"])
        health["next_probe_at"] = ts(now + timedelta(seconds=health["backoff_s"]))
        return "probe-failed"
    health["probes_ok"] = int(health["probes_ok"]) + 1
    if health["probes_ok"] < knobs["probes_to_recover"]:
        health["next_probe_at"] = ts(now + timedelta(seconds=base))
        return "probe-ok"
    health.update(state="up", since=ts(now), probes_ok=0, consecutive_5xx=0,
                  backoff_s=base, next_probe_at=None)
    return "recovered"


# --- AIMD, measurement, and the control step -------------------------------
