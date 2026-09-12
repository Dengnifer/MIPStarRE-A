#!/usr/bin/env python3
"""Measured, self-healing admission capacity for the dispatcher accounts.

`local/protocols/capacity.md` is normative; this is the implementation.  On
2026-09-12 the caps were edited by hand ten times while ~90 sessions died: 69
into a primary endpoint that answered 503 for half an hour, the rest above the
second account's real provider limit.  Two independent paths replace both
interventions.  **AIMD** over refusals: one slot up per quiet window, and on a
refusal down to just under the concurrency that was refused, inside the owner's
``ceiling - external_reserved``.  **Measured health**: three ``endpoint_5xx``
deaths in two minutes write cap 0 at once, and so does a single ``auth`` or
``insufficient_balance`` failure — a `401` is not a statistic — each with the
REASON recorded; the way back is a half-open, single-flight, read-only probe
that restores cap 1, never the pre-outage cap.  Counters come from the
``failure_class`` and ``endpoint`` fields of ``sessions.jsonl``, never from a
fresh grep; a class the policy does not name is neutral in both directions.

**The ceilings are re-read every tick** from ``watchdog/accounts.json``, the
owner's live file (``local/bin/accounts_file.py``), which supersedes the run
mode's account list entirely when it exists: a ceiling lowered at 05:12Z is in
force by 05:13Z, an account disabled there is cap 0 with no probe, and an entry
removed is the same — with no session prompted and no brief re-applied.  Any
number of named accounts; ``primary`` and ``second`` are ordinary entries.

This tool is the sole writer of ``watchdog/capacity/state.json``, of
``watchdog/capacity/health{,-<account>}.json`` and of the derived
``watchdog/max-codex{,-<account>}`` files.  It never writes ``accounts.json``:
that one is the owner's.

Usage:
    capacity_controller.py init [--force] [--dry-run] | tick [--dry-run]
    capacity_controller.py set ACCOUNT CAP | pause [--reason T] | resume
    capacity_controller.py probe [ACCOUNT] | status [--json | --brief]
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

import accounts_file  # noqa: E402
from account_router import DEFAULT_ACCOUNTS, live_pids  # noqa: E402
from wf_util import atomic_write  # noqa: E402

STATE_SCHEMA = "mipstarre-capacity-state/1"
HEALTH_SCHEMA = "mipstarre-capacity-health/1"
POLICY_SCHEMA_VERSION = 1
TS_FMT = "%Y-%m-%dT%H:%M:%SZ"
#: Tail of ``sessions.jsonl`` parsed per tick; the counters look back 5 minutes.
TAIL_BYTES = 1 << 20
#: Every operator-facing failure.  The cap files are untouched on this path.
EXIT_FAIL = 2
_COUNTS_AS = ("refusal", "death", "neutral")
_HEALTH_KEYS = ("fivexx_threshold", "fivexx_window_s", "probe_backoff_s",
                "probe_backoff_max_s", "probes_to_recover")
#: Knobs for the non-5xx disabling classes (an invalid key, an exhausted
#: balance).  Optional so a policy file written before this layer still
#: validates; `_health_knobs` supplies these defaults.
_DISABLE_KEYS = ("disable_threshold", "disable_backoff_s")
_DISABLE_DEFAULTS = {"disable_threshold": 1, "disable_backoff_s": 300}
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
    # The ceiling is the owner's, and a knob file may never raise it.  It is
    # stated in the brief and then lives in watchdog/accounts.json, which the
    # owner edits directly; both spellings assert the same thing — not here.
    _require(policy.get("ceiling_source") in ("brief", "accounts"),
             f"{path}: ceiling_source must be 'accounts' (the owner's live file) "
             "or the historical 'brief'")
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
    for key in _DISABLE_KEYS:
        if key in health:
            _int(health[key], f"{what}.health.{key}", minimum=1)
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


def health_knobs(policy: dict, account: str) -> dict:
    """The health block with the optional disable defaults filled in."""
    health = dict(_DISABLE_DEFAULTS)
    health.update(knobs_for(policy, account)["health"])
    return health


def disabling_classes(policy: dict) -> tuple[str, ...]:
    """Failure classes that disable the key outright, not just count against it.

    A concurrency refusal says "too many at once"; ``auth`` and
    ``insufficient_balance`` say "this key does not work at all", and no amount
    of AIMD makes an invalid key valid.  ``endpoint_5xx`` is a third kind —
    the endpoint is down, the key is fine — and keeps its own 3-in-120 s
    threshold; the others trip at ``disable_threshold`` (1 by default), because
    one ``401`` is already the whole answer.
    """
    return tuple(entry["failure_class"] for entry in policy["failure_patterns"]
                 if entry.get("disables") and entry["failure_class"] != "endpoint_5xx")


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
    accounts, source = overlay_live_accounts(accounts)
    return {"accounts": accounts, "run": run, "accounts_source": source,
            "brief_ref": (mode.get("brief_sha256") or mode.get("brief_ref")
                          or run.get("label") or str(path))}


def overlay_live_accounts(from_mode: dict[str, dict]) -> tuple[dict[str, dict], str]:
    """Replace the mode's account list with the owner's live file when it exists.

    THE HOT RELOAD.  ``load_run_mode`` runs once per tick, so the ceilings, the
    reserved slots and the enabled flags the controller uses are at most one tick
    (60 s) old.  The live file is authoritative in full: an entry the owner
    removed is gone from the tick that follows, which is cap 0 and no probe —
    the same as ``enabled: false``, and deliberately so.

    An unreadable or invalid file is a HARD failure, like a malformed run mode:
    the caller exits nonzero and leaves the cap files exactly as they are.
    Falling back to the brief would silently restore a ceiling the owner has just
    lowered, which is the one behaviour this file exists to remove.
    """
    try:
        entries = accounts_file.load()
    except accounts_file.AccountsError as exc:
        raise ControllerError(
            f"{exc}\nThe cap files are untouched. Fix the field this message names "
            f"(results/telemetry/owner-tools/accounts.sh list), or delete "
            f"{accounts_file.accounts_path()} to fall back to the brief.") from exc
    if entries is None:
        return from_mode, "run-mode.json (no accounts.json yet)"
    live: dict[str, dict] = {}
    for entry in entries:
        name = entry["name"]
        ceiling = entry["ceiling"]
        reserved = min(entry["external_reserved"], ceiling)
        live[name] = {"name": name, "endpoint": entry["endpoint"],
                      "label": entry["label"], "nominal_limit": ceiling,
                      "codex_home": entry["codex_home"],
                      "external_reserved": reserved, "enabled": entry["enabled"],
                      "note": entry["note"]}
    _require(bool(live), f"{accounts_file.accounts_path()}: no account entries")
    return live, str(accounts_file.accounts_path())


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
            now: datetime, *, counter_window_s: int, fivexx_window_s: int,
            disabling: tuple[str, ...] = ()) -> dict:
    """Refusal, death and key-invalidating counters for one account.

    A ``failure_class`` the policy does not name — including the literal
    ``unknown`` — is counted in neither direction, so a reworded provider message
    leaves the cap where a hand-set cap would have been instead of collapsing it.

    ``disabling`` names the classes that say the KEY is unusable rather than busy
    (``auth``, ``insufficient_balance``).  They are collected separately, with
    their detail, because the answer to them is "disable this key and say why",
    not "lower the cap by a quarter".
    """
    bucket: dict[str, Any] = {"refusals": 0, "deaths": 0, "neutral": 0,
                              "deaths_by_class": {}, "refusal_times": [], "fivexx_times": [],
                              "disable_times": [], "disable_class": "", "disable_detail": ""}
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
        if failure_class in disabling:
            bucket["disable_times"].append(row["_ts"])
            bucket["disable_class"] = failure_class
            bucket["disable_detail"] = str(row.get("failure_detail") or "")[:120]
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
    bucket["disable_times"].sort()
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
    document.setdefault("key_failures", 0)
    document.setdefault("probes_ok", 0)
    document.setdefault("next_probe_at", None)
    document.setdefault("reason", "")
    document.setdefault("disabled_by", "")
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
    # The two historical names keep a file even when no longer configured, so a
    # reader that predates this layer still finds a number rather than an empty
    # read; every configured account gets one whatever it is called.
    for name in (*DEFAULT_ACCOUNTS,
                 *(name for name in effective if name not in DEFAULT_ACCOUNTS)):
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

    Two kinds of trip, one machine.  ``endpoint_5xx`` says the ENDPOINT is down
    and needs ``fivexx_threshold`` deaths inside ``fivexx_window_s`` — a single
    502 is noise.  ``auth`` and ``insufficient_balance`` say the KEY is unusable
    and trip at ``disable_threshold`` (1): a `401` is not a statistic, and
    retrying an invalid key at any concurrency produces nothing but dead
    sessions.  Both write the REASON into the health file, because "cap 0" with
    no reason is the state the owner had to diagnose by reading captures on
    2026-09-12; the way back is the same half-open probe, with the key-invalid
    backoff starting longer (``disable_backoff_s``) since a key does not become
    valid again in thirty seconds.
    """
    fivexx = len(counters["fivexx_times"])
    disabling = len(counters.get("disable_times") or ())
    base = knobs["probe_backoff_s"]
    disable_base = max(base, int(knobs.get("disable_backoff_s",
                                           _DISABLE_DEFAULTS["disable_backoff_s"])))
    health.update(consecutive_5xx=fivexx, key_failures=disabling, updated=ts(now))
    if health["state"] != "down":
        if disabling >= int(knobs.get("disable_threshold",
                                      _DISABLE_DEFAULTS["disable_threshold"])):
            detail = counters.get("disable_detail") or ""
            health.update(state="down", since=ts(now), probes_ok=0,
                          backoff_s=min(disable_base, knobs["probe_backoff_max_s"]),
                          reason=f"{counters.get('disable_class') or 'key'}: "
                                 f"{detail or 'the key was refused'}",
                          disabled_by=counters.get("disable_class") or "key",
                          next_probe_at=ts(now + timedelta(
                              seconds=min(disable_base, knobs["probe_backoff_max_s"]))))
            return "trip"
        if fivexx >= knobs["fivexx_threshold"]:
            health.update(state="down", since=ts(now), probes_ok=0, backoff_s=base,
                          reason=f"endpoint_5xx: {fivexx} deaths in "
                                 f"{knobs['fivexx_window_s']}s",
                          disabled_by="endpoint_5xx",
                          next_probe_at=ts(now + timedelta(seconds=base)))
            return "trip"
        if fivexx:
            if health["state"] != "degraded":
                health.update(state="degraded", since=ts(now),
                              reason=f"endpoint_5xx: {fivexx} death(s) in "
                                     f"{knobs['fivexx_window_s']}s, below the "
                                     f"threshold of {knobs['fivexx_threshold']}")
            return "degraded"
        if health["state"] != "up":
            health.update(state="up", since=ts(now), reason="")
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
                  key_failures=0, reason="", disabled_by="",
                  backoff_s=base, next_probe_at=None)
    return "recovered"


# --- AIMD, measurement, and the control step -------------------------------


def clamp(value: int, floor: int, ceiling: int) -> int:
    """Into ``[floor, ceiling]``; the ceiling wins when the two cross."""
    return max(min(floor, ceiling), min(ceiling, int(value)))


def apply_aimd(account_state: dict, counters: dict, knobs: dict, live: int, now: datetime,
               *, floor: int, ceiling: int) -> list[str]:
    """Decrease first, so a refusal cannot be overtaken by an increase."""
    notes: list[str] = []
    aimd = knobs["aimd"]
    window = timedelta(seconds=aimd["quiet_window_s"])
    cap = int(account_state["cap"])
    cursor = parse_ts(account_state.get("refusal_cursor"))
    fresh = [moment for moment in counters["refusal_times"] if cursor is None or moment > cursor]
    if fresh:
        until = parse_ts(account_state.get("decrease_window_until"))
        if until is None or now > until:
            # The FIRST refusal of a window: step just under the concurrency that
            # was refused.  ``live`` is sampled at the tick that observes it,
            # which is the closest the controller gets to the moment of refusal —
            # but when the refused sessions have already died it is 0 or 1, and a
            # raw ``live - 1`` would collapse the cap to the floor and then climb
            # back one slot per quiet window (an hour from 1 to 30 with the
            # shipped defaults).  Fall back to what the account is KNOWN to have
            # sustained before believing an instantaneous zero.
            evidence = [value for value in
                        (account_state.get("observed_refusal_floor"),
                         account_state.get("measured_limit"))
                        if isinstance(value, int) and not isinstance(value, bool)]
            basis = live if live > 1 else max([live] + evidence)
            cap = max(floor, min(cap, basis - 1))
            account_state["decrease_window_until"] = ts(now + window)
            notes.append(f"decrease(first) live={live} basis={basis} -> {cap}")
            observed = basis
        else:
            cap = max(floor, math.ceil(cap * float(aimd["decrease"])))
            notes.append(f"decrease(x{aimd['decrease']}) -> {cap}")
            observed = live
        account_state.update(refusal_cursor=ts(max(fresh)), quiet_since=None)
        if observed >= 1:  # a zero census is not evidence that one slot refused
            seen = account_state.get("observed_refusal_floor")
            account_state["observed_refusal_floor"] = (
                observed if seen is None else min(int(seen), observed))
    # ``live >= cap - 1`` keeps the cap honest: a cap nobody uses is not evidence
    # of headroom.
    if (not counters["refusals"] and not counters["deaths"]
            and account_state["health"] == "up" and live >= cap - 1):
        started = parse_ts(account_state.get("quiet_since"))
        if started is None:
            account_state["quiet_since"] = ts(now)
        elif now - started >= window:
            if cap < ceiling:
                cap = min(ceiling, cap + int(aimd["increase"]))
                notes.append(f"increase -> {cap}")
            account_state["quiet_since"] = ts(now)
    else:
        account_state["quiet_since"] = None
    account_state["cap"] = clamp(cap, floor, ceiling)
    return notes


def update_measurement(account_state: dict, counters: dict, live: int, now: datetime,
                       *, measured_hold_s: int) -> None:
    """The highest concurrency sustained *measured_hold_s* with no refusal or death."""
    if counters["refusals"] or counters["deaths"]:
        account_state.update(measured_since=None, measured_level=None)
        return
    started = parse_ts(account_state.get("measured_since"))
    level = account_state.get("measured_level")
    if started is None or not isinstance(level, int):
        account_state.update(measured_since=ts(now), measured_level=live)
        return
    account_state["measured_level"] = min(int(level), live)
    if now - started >= timedelta(seconds=measured_hold_s):
        sustained, current = int(account_state["measured_level"]), account_state["measured_limit"]
        if current is None or sustained > int(current):
            account_state["measured_limit"] = sustained
        account_state.update(measured_since=ts(now), measured_level=live)


def refresh(account_state: dict, entry: dict, knobs: dict) -> tuple[int, int]:
    """Ceiling and floor from the brief and the policy; returns ``(floor, ceiling)``."""
    ceiling = max(0, entry["nominal_limit"] - entry["external_reserved"])
    floor = min(int(knobs["floor"]), ceiling)
    account_state.update(nominal_limit=entry["nominal_limit"], floor=floor, ceiling=ceiling,
                         external_reserved=entry["external_reserved"],
                         enabled=entry["enabled"], endpoint=entry["endpoint"])
    return floor, ceiling


def seed_cap(account_state: dict, floor: int, ceiling: int, entry: dict) -> int:
    """Starting cap for a run: ``min(brief ceiling, last measured limit)``."""
    if not entry["enabled"]:
        return 0
    measured = account_state.get("measured_limit")
    return clamp(max(ceiling if measured is None else min(ceiling, int(measured)), 1),
                 floor, ceiling)


def tick(now: datetime, *, policy: dict, run_mode: dict, state: dict,
         dry_run: bool = False) -> dict:
    """One control step: health, then decrease, then increase, then the clamp."""
    windows, roles = policy["windows"], class_roles(policy)
    disabling = disabling_classes(policy)
    hold = (capacity_dir() / "hold").exists()
    paused = state.get("paused_at") is not None
    accounts = run_mode["accounts"]
    endpoints: dict[str, str] = {}
    for name, entry in accounts.items():
        endpoints[entry["endpoint"]] = name
        endpoints[name] = name
        if entry["label"]:
            endpoints.setdefault(entry["label"], name)
    lookback = max([windows["counter_window_s"]]
                   + [health_knobs(policy, name)["fivexx_window_s"] for name in accounts])
    rows = read_session_rows(telemetry_dir() / "sessions.jsonl",
                             now - timedelta(seconds=lookback))
    live, waiters = count_live(accounts), count_waiters()
    summary: dict[str, Any] = {"ts": ts(now), "hold": hold, "paused": paused,
                               "waiters": waiters, "accounts": {}}
    caps: dict[str, int] = {}
    health_rows: dict[str, dict] = {}
    estimate = {"schema": "mipstarre-capacity-estimate/1", "updated": ts(now), "accounts": {}}

    for name, entry in accounts.items():
        knobs = knobs_for(policy, name)
        hknobs = health_knobs(policy, name)
        counters = observe(rows, name, endpoints, roles, now,
                           counter_window_s=windows["counter_window_s"],
                           fivexx_window_s=hknobs["fivexx_window_s"],
                           disabling=disabling)
        account_state = state["accounts"].setdefault(name, new_account_state(name))
        floor, ceiling = refresh(account_state, entry, knobs)
        health = load_health(name, entry["endpoint"], now, hknobs["probe_backoff_s"])
        was = health["state"]
        # A paused run has no daemons and spends no key: `paused` joins the hold
        # and the disabled account in suppressing the probe, so a pause can never
        # fire `codex exec` on the owner's keys after the deadline.
        action = update_health(name, health, counters, hknobs, now,
                               no_probe=hold or paused or not entry["enabled"],
                               codex_home=entry["codex_home"],
                               probe_timeout_s=windows["probe_timeout_s"])
        account_state["health"] = health["state"]
        notes: list[str] = []
        if hold:
            notes.append("hold: cap frozen")
        elif paused or not entry["enabled"]:
            # BEFORE the recovery branch: a recovering endpoint must not raise
            # the cap to 1 while state.json says paused (or while the brief says
            # this key is off).  Pause outranks health in both directions.
            if int(account_state["cap"]) != 0:  # a note per tick would be noise
                notes.append("paused: cap 0" if paused
                             else "disabled in the accounts file: cap 0, no probe")
            account_state.update(cap=0, quiet_since=None, decrease_window_until=None)
        elif action == "trip":
            account_state.update(cap=0, quiet_since=None, decrease_window_until=None)
            notes.append("endpoint down: cap 0")
        elif action == "recovered":
            # Never back to the pre-outage cap: the endpoint that just came back
            # is the last thing to hand twenty sessions.
            account_state.update(cap=clamp(1, floor, ceiling), quiet_since=None,
                                 decrease_window_until=None, refusal_cursor=None)
            notes.append(f"endpoint recovered: cap {account_state['cap']}, AIMD climbs")
        elif health["state"] == "down":
            account_state["cap"] = 0
        else:
            notes.extend(apply_aimd(account_state, counters, knobs, live[name], now,
                                    floor=floor, ceiling=ceiling))
            account_state["cap"] = clamp(account_state["cap"], floor, ceiling)
        update_measurement(account_state, counters, live[name], now,
                           measured_hold_s=windows["measured_hold_s"])
        if notes:
            account_state["last_change"] = ts(now)
        caps[name] = int(account_state["cap"])
        measured = account_state["measured_limit"]
        estimate["accounts"][name] = {
            "nominal": entry["nominal_limit"], "external_reserved": entry["external_reserved"],
            "cap_now": caps[name], "live": live[name], "waiters": waiters,
            "refusals_5m": counters["refusals"], "deaths_5m_by_class": counters["deaths_by_class"],
            "measured_limit": measured,
            "observed_refusal_floor": account_state["observed_refusal_floor"],
            "external_inferred": (None if measured is None else entry["nominal_limit"]
                                  - entry["external_reserved"] - int(measured)),
            "health": health["state"], "updated": ts(now)}
        summary["accounts"][name] = {
            "cap": caps[name], "live": live[name], "floor": floor, "ceiling": ceiling,
            "health": health["state"], "health_was": was, "health_action": action,
            "health_reason": health.get("reason") or "",
            "refusals_5m": counters["refusals"], "deaths_5m": counters["deaths"],
            "neutral_5m": counters["neutral"], "measured_limit": measured,
            "enabled": bool(entry["enabled"]), "endpoint": entry["endpoint"],
            "label": entry.get("label") or name, "note": entry.get("note") or "",
            "external_reserved": entry["external_reserved"], "notes": notes}
        health_rows[name] = {
            "state": health["state"], "reason": health.get("reason") or "",
            "disabled_by": health.get("disabled_by") or "", "since": health.get("since"),
            "endpoint": entry["endpoint"], "enabled": bool(entry["enabled"]),
            "cap": caps[name], "ceiling": ceiling,
            "consecutive_5xx": health.get("consecutive_5xx", 0),
            "key_failures": health.get("key_failures", 0),
            "probes_ok": health.get("probes_ok", 0),
            "next_probe_at": health.get("next_probe_at"),
            "backoff_s": health.get("backoff_s")}
        if not dry_run:
            _write_json(health_path(name), health)

    for stale in [name for name in state["accounts"] if name not in accounts]:
        state["accounts"].pop(stale)
        summary.setdefault("dropped", []).append(stale)
    state.update(updated=ts(now), brief_ref=run_mode["brief_ref"],
                 accounts_source=run_mode.get("accounts_source", ""))
    summary["max_codex"] = sum(caps.values())
    summary["accounts_source"] = run_mode.get("accounts_source", "")
    if not dry_run:
        if not hold:
            summary["max_codex"] = write_cap_files(caps)
        _write_json(state_path(), state)
        _write_json(capacity_dir() / "limit-estimate.json", estimate)
        # ONE document for every key, next to the per-account files the router
        # and dispatch.sh already read.  The per-account files stay exactly as
        # they are (they are the admission input); this is the owner's picture —
        # which key is disabled, and the REASON, which is what the hourly per-key
        # line and `accounts.sh list` quote instead of "cap 0, nobody knows why".
        _write_json(capacity_dir() / "health.json",
                    {"schema": HEALTH_SCHEMA, "updated": ts(now),
                     "source": run_mode.get("accounts_source", ""),
                     "accounts": health_rows})
    return summary


#: Transitions a human reads in the committed log.  Everything else — the
#: 60-second tick, about 1440 rows a day — goes to runtime state.
STAGE_EVENTS = ("init", "set", "pause", "resume", "endpoint-trip", "endpoint-recovered")

#: Per-tick rows kept in ``watchdog/capacity/ticks.jsonl`` (two days at 60 s).
TICKS_KEEP = 2880


def _append_jsonl(path: Path, record: dict) -> None:
    """One locked, newline-safe append."""
    path.parent.mkdir(parents=True, exist_ok=True)
    fd = os.open(path, os.O_RDWR | os.O_CREAT | os.O_APPEND, 0o644)
    with os.fdopen(fd, "r+", encoding="utf-8") as handle:
        fcntl.flock(handle.fileno(), fcntl.LOCK_EX)
        try:
            handle.seek(0, os.SEEK_END)
            if handle.tell():
                handle.seek(handle.tell() - 1)
                if handle.read(1) != "\n":  # a previous writer died mid-line
                    handle.write("\n")
            handle.write(json.dumps(record, ensure_ascii=False) + "\n")
            handle.flush()
            os.fsync(handle.fileno())
        finally:
            fcntl.flock(handle.fileno(), fcntl.LOCK_UN)


def append_stage(event: str, summary: dict, note: str) -> None:
    """One ``capacity`` TRANSITION row in ``results/telemetry/stages.jsonl``.

    Transitions only — ``init``, ``set``, ``pause``, ``resume``, and an endpoint
    tripping or recovering.  The 60-second tick writes ``append_tick`` instead:
    a row per tick would be ~1440 committed lines a day in a file that holds a
    hundred for the whole project, and every one of them would ride into ``main``
    on the merge daemon's telemetry batch.  The event names and the ``capacity``
    stage are declared in ``local/protocols/meta.md`` (Telemetry duties).
    """
    if event not in STAGE_EVENTS:
        raise ControllerError(
            f"{event!r} is not a stages.jsonl transition for the capacity stage "
            f"({', '.join(STAGE_EVENTS)}); per-tick records go to "
            f"{capacity_dir() / 'ticks.jsonl'}")
    record = {"ts": summary.get("ts") or ts(utcnow()), "stage": "capacity", "event": event,
              "note": note, "capacity": summary}
    _append_jsonl(telemetry_dir() / "stages.jsonl", record)


def append_tick(summary: dict, note: str) -> Path:
    """The per-tick record: runtime state under the cache root, never committed.

    Trimmed to the last ``TICKS_KEEP`` rows by this writer, so nobody has to
    prune it by hand and it cannot grow without bound on a long run.
    """
    path = capacity_dir() / "ticks.jsonl"
    _append_jsonl(path, {"ts": summary.get("ts") or ts(utcnow()), "event": "tick",
                         "note": note, "capacity": summary})
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
        if len(lines) > TICKS_KEEP:
            tmp = path.with_suffix(".jsonl.tmp")
            tmp.write_text("\n".join(lines[-TICKS_KEEP:]) + "\n", encoding="utf-8")
            os.replace(tmp, path)
    except OSError:
        pass  # a trim failure must never fail a control step
    return path


def render_note(summary: dict) -> str:
    parts = [f"{name} {row['live']}/{row['cap']} {row['health']}"
             + (" (" + "; ".join(row["notes"]) + ")" if row["notes"] else "")
             for name, row in summary["accounts"].items()]
    parts += ["hold"] if summary.get("hold") else []
    parts += ["paused"] if summary.get("paused") else []
    return "; ".join(parts) or "no accounts"


# --- subcommands -----------------------------------------------------------


def _lock(blocking: bool):
    capacity_dir().mkdir(parents=True, exist_ok=True)
    handle = (capacity_dir() / "controller.lock").open("a")
    try:
        fcntl.flock(handle, fcntl.LOCK_EX if blocking else fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError:
        handle.close()
        return None
    return handle


def _require_lock(blocking: bool):
    """``_lock`` or a named failure — never ``None`` reaching a ``.close()``.

    ``flock`` can fail on a blocking wait too (EINTR is reachable), and an
    unguarded ``lock.close()`` in a ``finally`` turns that into an
    ``AttributeError`` traceback that ``main``'s handler does not catch.
    """
    handle = _lock(blocking)
    if handle is None:
        raise ControllerError(
            f"cannot take {capacity_dir() / 'controller.lock'}; another capacity "
            "controller holds it or the lock could not be acquired. Nothing was "
            "written: the cap files are exactly as they were.")
    return handle


def _commit(state: dict, caps: dict[str, int], now: datetime, event: str, note: str,
            dry_run: bool) -> int:
    state["updated"] = ts(now)
    if dry_run:
        return sum(caps.values())
    total = write_cap_files(caps)
    _write_json(state_path(), state)
    append_stage(event, {"ts": ts(now), "max_codex": total,
                         "accounts": {name: {"cap": caps[name]} for name in caps}}, note)
    return total


def cmd_init(args: argparse.Namespace) -> int:
    """Validate the policy and the brief, then seed the run's starting caps.

    ``run_mode.py apply`` calls this instead of writing the cap files itself:
    this tool is the sole writer of ``state.json`` and of the derived files.
    """
    policy, run_mode = load_policy(args.policy), load_run_mode(args.run_mode)
    now = args.now or utcnow()
    previous = load_state()
    state = new_state(run_mode["brief_ref"])
    if previous and not args.force:
        # A new brief is a new run: only the measurement is carried, because it
        # is what starts the next run below the cliff instead of above it.
        for name, old in previous["accounts"].items():
            state["accounts"][name] = dict(
                new_account_state(name), measured_limit=old.get("measured_limit"),
                observed_refusal_floor=old.get("observed_refusal_floor"))
    caps, lines = {}, []
    for name, entry in run_mode["accounts"].items():
        knobs = knobs_for(policy, name)
        account_state = state["accounts"].setdefault(name, new_account_state(name))
        floor, ceiling = refresh(account_state, entry, knobs)
        health = load_health(name, entry["endpoint"], now,
                             health_knobs(policy, name)["probe_backoff_s"])
        # A fresh brief is not evidence that a dead endpoint came back.
        account_state.update(health=health["state"], saved_cap=None, quiet_since=None,
                             decrease_window_until=None, refusal_cursor=None,
                             cap=0 if health["state"] == "down"
                             else seed_cap(account_state, floor, ceiling, entry))
        caps[name] = int(account_state["cap"])
        lines.append(f"{name} cap {caps[name]} (floor {floor}, ceiling {ceiling}, health "
                     f"{health['state']}, measured {account_state['measured_limit']})")
        if not args.dry_run:
            _write_json(health_path(name), health)
    for stale in [name for name in state["accounts"] if name not in run_mode["accounts"]]:
        state["accounts"].pop(stale)
    total = _commit(state, caps, now, "init", "seeded from the brief: " + "; ".join(lines),
                    args.dry_run)
    print("\n".join(lines))
    print(f"max-codex {total}" + (" (dry run; nothing written)" if args.dry_run else ""))
    return 0


def cmd_tick(args: argparse.Namespace) -> int:
    policy, run_mode = load_policy(args.policy), load_run_mode(args.run_mode)
    now = args.now or utcnow()
    lock = _lock(blocking=False)
    if lock is None:
        print("skipped: another capacity controller holds the lock", file=sys.stderr)
        return 0
    try:
        state, seeded = load_state(), False
        if state is None:
            seeded, state = True, new_state(run_mode["brief_ref"])
            for name, entry in run_mode["accounts"].items():
                account_state = new_account_state(name)
                floor, ceiling = refresh(account_state, entry, knobs_for(policy, name))
                account_state["cap"] = seed_cap(account_state, floor, ceiling, entry)
                state["accounts"][name] = account_state
        summary = tick(now, policy=policy, run_mode=run_mode, state=state, dry_run=args.dry_run)
        note = ("seeded from the brief; " if seeded else "") + render_note(summary)
        if not args.dry_run:
            append_tick(summary, note)
            # The committed log carries the transitions a human cares about, not
            # the tick: an endpoint going down or coming back is the thing that
            # was answered by hand on 2026-09-12.
            for name, row in summary["accounts"].items():
                if row["health_action"] == "trip":
                    append_stage("endpoint-trip", summary,
                                 f"{name} ({row['health_was']} -> down): cap 0; {note}")
                elif row["health_action"] == "recovered":
                    append_stage("endpoint-recovered", summary,
                                 f"{name} (down -> up): cap {row['cap']}, AIMD climbs; {note}")
    finally:
        lock.close()
    print(f"{summary['ts']} {note} | max-codex {summary['max_codex']}")
    return 0


def cmd_set(args: argparse.Namespace) -> int:
    """Operator override of one cap, clamped to the brief's ceiling."""
    policy, run_mode = load_policy(args.policy), load_run_mode(args.run_mode)
    now = args.now or utcnow()
    _require(args.account in run_mode["accounts"], f"{args.account}: not an account in the "
             f"current brief ({', '.join(run_mode['accounts']) or 'none'})")
    _require(args.cap >= 0, "cap must be a nonnegative integer")
    lock = _require_lock(blocking=True)
    try:
        state = load_state() or new_state(run_mode["brief_ref"])
        caps = {}
        for name, entry in run_mode["accounts"].items():
            account_state = state["accounts"].setdefault(name, new_account_state(name))
            floor, ceiling = refresh(account_state, entry, knobs_for(policy, name))
            if name == args.account:
                # Clamped to the ceiling but not up to the floor: this is the
                # supported replacement for ``echo 0 > max-codex-primary``.  The
                # operator's number owns a full quiet window before AIMD moves
                # again, and a stale decrease window must not shrink it.
                account_state.update(cap=clamp(args.cap, 0, ceiling), quiet_since=None,
                                     decrease_window_until=None, last_change=ts(now))
            caps[name] = int(account_state["cap"])
        total = _commit(state, caps, now, "set",
                        f"operator set {args.account} cap {caps[args.account]}", args.dry_run)
    finally:
        lock.close()
    print(f"{args.account} cap {caps[args.account]} | max-codex {total}")
    return 0


def cmd_pause(args: argparse.Namespace) -> int:
    """Caps to 0, the pre-pause caps saved **inside** ``state.json``.

    Never to a second file: on 2026-09-12 the pause chain wrote
    ``watchdog/caps-before-pause`` in one format, a later phase overwrote it with
    another, and the resume script restored nothing.
    """
    policy, run_mode = load_policy(args.policy), load_run_mode(args.run_mode)
    now = args.now or utcnow()
    lock = _require_lock(blocking=True)
    try:
        state = load_state() or new_state(run_mode["brief_ref"])
        already = state.get("paused_at")
        caps = {}
        for name, entry in run_mode["accounts"].items():
            account_state = state["accounts"].setdefault(name, new_account_state(name))
            refresh(account_state, entry, knobs_for(policy, name))
            if account_state["saved_cap"] is None:  # a second pause saves nothing
                account_state["saved_cap"] = int(account_state["cap"])
            account_state.update(cap=0, quiet_since=None)
            caps[name] = 0
        state["paused_at"] = already or ts(now)
        if args.reason:
            state["pause_reason"] = args.reason
        saved = ", ".join(f"{name} {state['accounts'][name]['saved_cap']}" for name in caps)
        _commit(state, caps, now, "pause", f"capacity paused; saved caps {saved}", args.dry_run)
    finally:
        lock.close()
    if already:
        print(f"already paused at {already}; saved caps left untouched")
    print(f"saved {saved}; caps 0")
    return 0


def cmd_resume(args: argparse.Namespace) -> int:
    """Restore the saved caps and re-enter AIMD at the saved value."""
    policy, run_mode = load_policy(args.policy), load_run_mode(args.run_mode)
    now = args.now or utcnow()
    lock = _require_lock(blocking=True)
    try:
        state = load_state()
        _require(state is not None, f"{state_path()}: no capacity state to resume; run init")
        caps, lines = {}, []
        for name, entry in run_mode["accounts"].items():
            knobs = knobs_for(policy, name)
            account_state = state["accounts"].setdefault(name, new_account_state(name))
            floor, ceiling = refresh(account_state, entry, knobs)
            health = load_health(name, entry["endpoint"], now,
                             health_knobs(policy, name)["probe_backoff_s"])
            saved = account_state["saved_cap"]
            restored = (seed_cap(account_state, floor, ceiling, entry) if saved is None
                        else clamp(int(saved), floor, ceiling))
            if not entry["enabled"] or health["state"] == "down":
                restored = 0  # health outranks a saved number
            account_state.update(cap=restored, saved_cap=None, quiet_since=None,
                                 decrease_window_until=None, health=health["state"])
            caps[name] = restored
            lines.append(f"{name} cap {restored} (health {health['state']})")
        state["paused_at"] = None
        state.pop("pause_reason", None)
        total = _commit(state, caps, now, "resume", "capacity resumed: " + "; ".join(lines),
                        args.dry_run)
    finally:
        lock.close()
    print("\n".join(lines))
    print(f"max-codex {total}")
    return 0


def cmd_probe(args: argparse.Namespace) -> int:
    """Run the health probe now, for one account or for every one.

    The owner's "is that key working yet?", answered in a bounded read-only
    session instead of a wait for the next backoff.  It is the same probe the
    tick runs — same single-flight lock, same command, same recovery counting —
    so a success here counts toward `probes_to_recover` rather than being a
    separate opinion, and a failure doubles the backoff exactly as it would have.
    """
    policy, run_mode = load_policy(args.policy), load_run_mode(args.run_mode)
    now = args.now or utcnow()
    names = list(run_mode["accounts"]) if not args.account else [args.account]
    _require(all(name in run_mode["accounts"] for name in names),
             f"{args.account}: not a configured account "
             f"({', '.join(run_mode['accounts']) or 'none'})")
    failures = 0
    for name in names:
        entry = run_mode["accounts"][name]
        hknobs = health_knobs(policy, name)
        health = load_health(name, entry["endpoint"], now, hknobs["probe_backoff_s"])
        if not entry["enabled"]:
            print(f"{name}: disabled in {run_mode.get('accounts_source') or 'the brief'}; "
                  "not probed (enable it first)")
            continue
        ran, ok = _try_probe(name, entry["codex_home"], policy["windows"]["probe_timeout_s"])
        if not ran:
            print(f"{name}: another probe holds the lock; nothing run")
            continue
        if ok:
            health.update(probes_ok=int(health.get("probes_ok") or 0) + 1, updated=ts(now))
            if health["state"] == "down" and health["probes_ok"] >= hknobs["probes_to_recover"]:
                health.update(state="up", since=ts(now), probes_ok=0, consecutive_5xx=0,
                              key_failures=0, reason="", disabled_by="",
                              backoff_s=hknobs["probe_backoff_s"], next_probe_at=None)
                print(f"{name}: probe ok; health up (the next tick restores cap 1 and "
                      "AIMD climbs)")
            else:
                print(f"{name}: probe ok (state {health['state']}, "
                      f"{health['probes_ok']}/{hknobs['probes_to_recover']} toward recovery)")
        else:
            failures += 1
            health.update(probes_ok=0, updated=ts(now),
                          backoff_s=min(int(health.get("backoff_s") or
                                            hknobs["probe_backoff_s"]) * 2,
                                        hknobs["probe_backoff_max_s"]))
            health["next_probe_at"] = ts(now + timedelta(seconds=health["backoff_s"]))
            print(f"{name}: probe FAILED (state {health['state']}, reason "
                  f"{health.get('reason') or 'none recorded'}; next probe in "
                  f"{health['backoff_s']}s)")
        if not args.dry_run:
            _write_json(health_path(name), health)
    return 0 if not failures else EXIT_FAIL


def cmd_status(args: argparse.Namespace) -> int:
    """Read-only: the state, the health files and the live census."""
    state = load_state()
    if state is None:
        print(f"{state_path()}: no capacity state (run capacity_controller.py init)",
              file=sys.stderr)
        return EXIT_FAIL
    live, waiters = count_live(list(state["accounts"])), count_waiters()
    hold = (capacity_dir() / "hold").exists()
    estimate = (_read_json(capacity_dir() / "limit-estimate.json") or {}).get("accounts", {})
    rows = []
    for name, account_state in state["accounts"].items():
        health = _read_json(health_path(name)) or {}
        rows.append(dict({key: account_state.get(key) for key in
                          ("cap", "floor", "ceiling", "measured_limit", "observed_refusal_floor")},
                         account=name, live=live[name], waiters=waiters,
                         health=health.get("state", account_state.get("health", "up")),
                         health_reason=health.get("reason") or "",
                         probe=health.get("next_probe_at"),
                         external_inferred=estimate.get(name, {}).get("external_inferred")))
    if args.json:
        print(json.dumps({"ts": ts(utcnow()), "paused_at": state.get("paused_at"), "hold": hold,
                          "brief_ref": state.get("brief_ref"), "updated": state.get("updated"),
                          "accounts": rows}, ensure_ascii=False, indent=2))
        return 0
    brief = " | ".join(f"{row['account']} {row['live']}/{row['cap']} ({row['health']}) "
                       f"{row['waiters']}w" for row in rows) or "no accounts"
    suffix = (" [hold]" if hold else "") + (" [paused]" if state.get("paused_at") else "")
    if args.brief:
        print(brief + suffix)
        return 0
    print(f"capacity {state.get('updated')} brief={state.get('brief_ref')}{suffix}")
    for row in rows:
        print(f"  {row['account']:<8} cap {row['cap']:<4} live {row['live']:<4} "
              f"waiters {row['waiters']:<4} floor {row['floor']} ceiling {row['ceiling']} "
              f"health {row['health']:<8} measured {row['measured_limit']} refusal_floor "
              f"{row['observed_refusal_floor']} external_inferred {row['external_inferred']}"
              + (f" next probe {row['probe']}" if row["health"] == "down" else "")
              + (f"\n{'':<11}reason {row['health_reason']}" if row["health_reason"] else ""))
    return 0


# --- entry point -----------------------------------------------------------


def _moment(text: str) -> datetime:
    parsed = parse_ts(text)
    if parsed is None:
        raise argparse.ArgumentTypeError(f"{text!r} is not an ISO-8601 timestamp")
    return parsed


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--policy", type=Path, help="capacity policy (default: the checkout's)")
    parser.add_argument("--run-mode", type=Path, help="default: watchdog/run-mode.json")
    parser.add_argument("--now", type=_moment, help=argparse.SUPPRESS)
    subparsers = parser.add_subparsers(dest="command", required=True)
    for name, handler, help_text in (
            ("init", cmd_init, "validate the brief and seed the starting caps"),
            ("tick", cmd_tick, "one control step (the 60 s loop)"),
            ("set", cmd_set, "operator override of one account's cap"),
            ("pause", cmd_pause, "caps to 0, saving them inside state.json"),
            ("resume", cmd_resume, "restore the saved caps and re-enter AIMD"),
            ("probe", cmd_probe, "run the health probe now (owner-tools/accounts.sh probe)")):
        sub = subparsers.add_parser(name, help=help_text)
        sub.add_argument("--dry-run", action="store_true")
        if name == "probe":
            sub.add_argument("account", nargs="?", default="",
                             help="default: every configured account")
        if name == "init":
            sub.add_argument("--force", action="store_true",
                             help="discard the carried measurement as well as the run state")
        if name == "set":
            sub.add_argument("account")
            sub.add_argument("cap", type=int)
        if name == "pause":
            sub.add_argument("--reason")
        sub.set_defaults(handler=handler)
    status = subparsers.add_parser("status", help="read-only picture of the caps and health")
    group = status.add_mutually_exclusive_group()
    group.add_argument("--json", action="store_true")
    group.add_argument("--brief", action="store_true", help="one line for status-snapshot.sh")
    status.set_defaults(handler=cmd_status)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        return args.handler(args)
    except (ControllerError, OSError) as error:
        print(f"capacity controller: {error}", file=sys.stderr)
        return EXIT_FAIL


if __name__ == "__main__":
    raise SystemExit(main())
