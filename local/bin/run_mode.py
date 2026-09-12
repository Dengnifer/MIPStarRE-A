#!/usr/bin/env python3
"""The owner's run briefing, validated once, and the mode file everything reads.

One artifact states a run's capacity, schedule, speed and issue numbers: the
brief the owner copies to ``~/.cache/mipstarre-dev/watchdog/run-brief.json``
from the committed template
``results/telemetry/owner-tools/run-brief.template.json``.  ``apply`` validates
it strictly and turns it into ``watchdog/run-mode.json``, the record every
component reads through ``run_mode.py get KEY``.  No protocol, persona or
script carries a literal cap, floor, cadence or issue number
(``local/protocols/full-speed-mode.md``).

Subcommands::

    run_mode.py apply [--brief PATH] [--dry-run]
    run_mode.py show [--json]
    run_mode.py get KEY
    run_mode.py set speed fast|default [--dry-run]
    run_mode.py pause [--reason TEXT]
    run_mode.py resume

Validation fails loudly at briefing time rather than at 05:00Z: an unknown
key, a missing endpoint, a non-integer limit, ``external_reserved >=
nominal_limit``, an occupancy target above 1, an unknown speed or model
override, a non-positive issue number, or an account named outside
``{primary, second}`` all exit 2 naming the offending key and the template
path.  A missing brief is a hard error naming both paths — never silently zero
and never silently unlimited capacity.

The derived cap files ``watchdog/max-codex-primary``, ``max-codex-second`` and
``max-codex`` stay where ``account_router.py``, the lane runner and
``status-snapshot.sh`` already read them.  This script refuses to write an
empty or non-numeric cap file under any circumstance: the 2026-09-12 resume
script wrote empty caps and every dispatch then exited 4 with
``invalid literal for int()``.  ``max-codex`` is mechanically the sum of the
effective per-account caps and has no admission meaning.

Environment: ``MIPSTARRE_CACHE_ROOT`` (runtime root, default
``~/.cache/mipstarre-dev``), ``MIPSTARRE_REPO_ROOT`` (checkout holding
``results/telemetry``), ``MIPSTARRE_OWNER_BIN`` (installed operator tools,
default ``<cache>/owner-bin``).
"""

from __future__ import annotations

import argparse
import difflib
import fcntl
import hashlib
import json
import os
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from wf_util import LayerError, atomic_write, sanitize  # noqa: E402

#: The brief schema this tool accepts, and the mode document it writes.
BRIEF_SCHEMA = "mipstarre-run-brief/1"
MODE_SCHEMA = "mipstarre-run-mode/1"

#: `account_router.py` knows exactly these two accounts.
ACCOUNT_NAMES = ("primary", "second")

SPEEDS = ("fast", "default")
OVERRIDES = (None, "astra-all")

#: The literal `run.dispatch_cutoff` that means "no cutoff".
CUTOFF_OPEN = "until my word"

#: Derived from the speed tier so no script carries a literal cadence.
TURN_MAX_MIN = {"fast": 8, "default": 20}
ESTIMATE_CADENCE_MIN = {"fast": 30, "default": 360}

BRIEF_KEYS = ("schema", "run", "accounts", "models")
RUN_KEYS_REQUIRED = (
    "label", "start", "dispatch_cutoff", "pause_deadline_min", "speed",
    "occupancy_target", "progress_issue", "estimate_issue", "owner_inbox_issue",
)
RUN_KEYS_OPTIONAL = ("turn_max_min", "main")

#: The main session's own launch values, read by ``local/bin/main-session.sh``
#: through ``run_mode.py get main.<field>``.  Optional in the brief and defaulted
#: here to what the 2026-09-12 launcher hard-coded, so an existing brief keeps
#: working — but defaulted in ONE place that ``get`` can actually answer, rather
#: than in a shell fallback behind a ``get`` that always exits 2.
MAIN_DEFAULTS = {"model": "gpt-6-astra", "effort": "xhigh", "codex_home": ""}
MAIN_KEYS = tuple(MAIN_DEFAULTS)
EFFORTS = ("low", "medium", "high", "xhigh")
MODEL_RE = re.compile(r"^[A-Za-z0-9._-]{1,60}$")
ACCOUNT_KEYS = ("name", "label", "endpoint", "codex_home", "nominal_limit",
                "external_reserved", "enabled")
ISSUE_KEYS = ("progress_issue", "estimate_issue", "owner_inbox_issue")

#: Endpoint labels travel into telemetry rows and shell arguments (W2 validates
#: the same shape before interpolating one).
ENDPOINT_RE = re.compile(r"^[a-z0-9.-]{1,40}$")

TEMPLATE_REL = Path("results/telemetry/owner-tools/run-brief.template.json")
SHIM_TEMPLATE_REL = Path("results/telemetry/owner-tools/owner-bin-codex")

#: The speed tier is one codex config argument.  A template may mark its
#: position explicitly; otherwise it is inserted before the fan-out argument
#: every shim generation has carried.
SPEED_PLACEHOLDER = "@MIPSTARRE_SPEED_ARGS@"
PRIORITY_ARG = "-c 'service_tier=\"priority\"'"
SHIM_ANCHOR = "-c 'features.multi_agent=false'"
_PLACEHOLDER_RE = re.compile(re.escape(SPEED_PLACEHOLDER) + r" ?")
_SERVICE_TIER_RE = re.compile(r"-c +'service_tier=\"[^\"]*\"' ?")
# The committed shim template carries its speed tier on one anchored line, and
# install.sh renders exactly these two strings (results/telemetry/owner-tools/
# install.sh, render_shim).  They must stay byte-identical: install.sh records
# both renderings in owner-bin/manifest.accepted, and `set speed` refuses a
# deployed shim that matches no rendering.
SPEED_ARGS_MARK = ("# @speed-args@ regenerated by run_mode.py set speed; "
                   "do not edit by hand")
SPEED_ARGS_LINE = {
    "fast": "SPEED_ARGS=(-c 'service_tier=\"priority\"')   " + SPEED_ARGS_MARK,
    "default": "SPEED_ARGS=()   " + SPEED_ARGS_MARK,
}
_SPEED_ARGS_RE = re.compile(r"^SPEED_ARGS=.*$", re.MULTILINE)


class BriefError(LayerError):
    """A brief that must be fixed before the run starts."""

    def __init__(self, key: str, message: str) -> None:
        super().__init__(message)
        self.key = key


class Refused(LayerError):
    """A safe action this tool declines to take (exit 3)."""


# ---------------------------------------------------------------------------
# Locations
# ---------------------------------------------------------------------------

def cache_root() -> Path:
    """Runtime root, re-read per call so a test can point it at a tmpdir."""
    return Path(os.environ.get("MIPSTARRE_CACHE_ROOT",
                               "~/.cache/mipstarre-dev")).expanduser()


def watchdog_dir() -> Path:
    return cache_root() / "watchdog"


def brief_path() -> Path:
    return watchdog_dir() / "run-brief.json"


def mode_path() -> Path:
    return watchdog_dir() / "run-mode.json"


def owner_bin() -> Path:
    override = os.environ.get("MIPSTARRE_OWNER_BIN")
    return Path(override).expanduser() if override else cache_root() / "owner-bin"


def repo_root() -> Path:
    override = os.environ.get("MIPSTARRE_REPO_ROOT")
    if override:
        return Path(override).expanduser().resolve()
    return Path(__file__).resolve().parents[2]


def utcnow() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def stamp() -> str:
    """Telemetry timestamp shape (`meta.md`: ISO-8601 with offset)."""
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%S%z")


# ---------------------------------------------------------------------------
# Brief validation — every failure names the key and the template
# ---------------------------------------------------------------------------

def _template_hint() -> str:
    return (f"template: {repo_root() / TEMPLATE_REL}\n"
            f"destination: {brief_path()}")


def _require_mapping(value, key: str) -> dict:
    if not isinstance(value, dict):
        raise BriefError(key, f"{key!r} must be an object, not {type(value).__name__}")
    return value


def _require_int(value, key: str, *, minimum: int | None = None) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise BriefError(key, f"{key} must be an integer, got {value!r}")
    if minimum is not None and value < minimum:
        raise BriefError(key, f"{key} must be at least {minimum}, got {value}")
    return value


def _require_text(value, key: str, *, pattern: re.Pattern | None = None) -> str:
    if not isinstance(value, str) or not value.strip():
        raise BriefError(key, f"{key} must be a non-empty string, got {value!r}")
    text = value.strip()
    if pattern is not None and not pattern.match(text):
        raise BriefError(key, f"{key} {text!r} does not match {pattern.pattern}")
    return text


def parse_timestamp(value, key: str) -> datetime:
    """ISO-8601 instant; a bare `Z` is accepted on Python 3.10 too."""
    text = _require_text(value, key)
    candidate = text[:-1] + "+00:00" if text.endswith(("Z", "z")) else text
    try:
        moment = datetime.fromisoformat(candidate)
    except ValueError as exc:
        raise BriefError(key, f"{key} {text!r} is not an ISO-8601 timestamp "
                              f"(e.g. 2026-09-13T04:00:00Z): {exc}") from exc
    if moment.tzinfo is None:
        moment = moment.replace(tzinfo=timezone.utc)
    return moment.astimezone(timezone.utc)


def _validate_run(run: dict) -> dict:
    _require_mapping(run, "run")
    unknown = sorted(set(run) - set(RUN_KEYS_REQUIRED) - set(RUN_KEYS_OPTIONAL))
    if unknown:
        raise BriefError(f"run.{unknown[0]}",
                         f"unknown key(s) under 'run': {', '.join(unknown)}")
    missing = [key for key in RUN_KEYS_REQUIRED if key not in run]
    if missing:
        raise BriefError(f"run.{missing[0]}",
                         f"'run' is missing: {', '.join(missing)}")

    out: dict = {}
    out["label"] = sanitize(_require_text(run["label"], "run.label"), 120)
    out["start"] = parse_timestamp(run["start"], "run.start").strftime("%Y-%m-%dT%H:%M:%SZ")

    cutoff = run["dispatch_cutoff"]
    if isinstance(cutoff, str) and cutoff.strip().lower() == CUTOFF_OPEN:
        out["dispatch_cutoff"] = CUTOFF_OPEN
    else:
        out["dispatch_cutoff"] = parse_timestamp(
            cutoff, "run.dispatch_cutoff").strftime("%Y-%m-%dT%H:%M:%SZ")
        if out["dispatch_cutoff"] <= out["start"]:
            raise BriefError("run.dispatch_cutoff",
                             f"run.dispatch_cutoff {out['dispatch_cutoff']} is not after "
                             f"run.start {out['start']}; use the literal "
                             f"{CUTOFF_OPEN!r} for an open-ended run")

    out["pause_deadline_min"] = _require_int(
        run["pause_deadline_min"], "run.pause_deadline_min", minimum=1)

    speed = run["speed"]
    if speed not in SPEEDS:
        raise BriefError("run.speed",
                         f"run.speed must be one of {SPEEDS}, got {speed!r}")
    out["speed"] = speed

    target = run["occupancy_target"]
    if isinstance(target, bool) or not isinstance(target, (int, float)):
        raise BriefError("run.occupancy_target",
                         f"run.occupancy_target must be a number, got {target!r}")
    if not 0 < float(target) <= 1:
        raise BriefError("run.occupancy_target",
                         f"run.occupancy_target must lie in (0, 1], got {target} — "
                         "it is a fraction of the effective cap, not a worker count")
    out["occupancy_target"] = float(target)

    for key in ISSUE_KEYS:
        out[key] = _require_int(run[key], f"run.{key}", minimum=1)
    if len({out[key] for key in ISSUE_KEYS}) != len(ISSUE_KEYS):
        raise BriefError("run.estimate_issue",
                         "the progress log, the estimate issue and the owner inbox must be "
                         "three different issues; the estimate issue carries exactly two "
                         "rendered lines and nothing else (issues-prs.md section 6)")

    if run.get("turn_max_min") is not None:
        out["turn_max_min"] = _require_int(run["turn_max_min"], "run.turn_max_min", minimum=1)
    else:
        out["turn_max_min"] = TURN_MAX_MIN[speed]
    out["estimate_cadence_min"] = ESTIMATE_CADENCE_MIN[speed]
    out["main"] = _validate_main(run.get("main"))
    return out


def _validate_main(main) -> dict:
    """``run.main``: the launch values of the MAIN session, validated once here.

    Optional; every field defaults to what ``main-session.sh`` used to hard-code.
    Validated at briefing time so a typo is an exit 2 at ``apply`` rather than a
    codex CLI error at 04:00Z.
    """
    if main is None:
        return dict(MAIN_DEFAULTS)
    _require_mapping(main, "run.main")
    unknown = sorted(set(main) - set(MAIN_KEYS))
    if unknown:
        raise BriefError(f"run.main.{unknown[0]}",
                         f"unknown key(s) under 'run.main': {', '.join(unknown)}")
    out = dict(MAIN_DEFAULTS)
    if main.get("model") is not None:
        out["model"] = _require_text(main["model"], "run.main.model", pattern=MODEL_RE)
    if main.get("effort") is not None:
        effort = main["effort"]
        if effort not in EFFORTS:
            raise BriefError("run.main.effort",
                             f"run.main.effort must be one of {EFFORTS}, got {effort!r}")
        out["effort"] = effort
    if main.get("codex_home") is not None:
        # "" is meaningful: use the ambient CODEX_HOME rather than forcing one.
        home = main["codex_home"]
        if not isinstance(home, str):
            raise BriefError("run.main.codex_home",
                             f"run.main.codex_home must be text, got {home!r}")
        out["codex_home"] = home.strip()
    return out


def _validate_accounts(accounts) -> list[dict]:
    if not isinstance(accounts, list) or not accounts:
        raise BriefError("accounts", "'accounts' must be a non-empty list of account objects")
    seen: set[str] = set()
    out: list[dict] = []
    for index, raw in enumerate(accounts):
        where = f"accounts[{index}]"
        _require_mapping(raw, where)
        unknown = sorted(set(raw) - set(ACCOUNT_KEYS))
        if unknown:
            raise BriefError(f"{where}.{unknown[0]}",
                             f"unknown key(s) under {where}: {', '.join(unknown)}")
        missing = [key for key in ACCOUNT_KEYS if key not in raw]
        if missing:
            raise BriefError(f"{where}.{missing[0]}",
                             f"{where} is missing: {', '.join(missing)}")
        name = _require_text(raw["name"], f"{where}.name")
        if name not in ACCOUNT_NAMES:
            raise BriefError(f"{where}.name",
                             f"account name {name!r} is outside {ACCOUNT_NAMES}; "
                             "account_router.py knows exactly these two")
        if name in seen:
            raise BriefError(f"{where}.name", f"account {name!r} is listed twice")
        seen.add(name)
        endpoint = _require_text(raw["endpoint"], f"{where}.endpoint", pattern=ENDPOINT_RE)
        codex_home = _require_text(raw["codex_home"], f"{where}.codex_home")
        nominal = _require_int(raw["nominal_limit"], f"{where}.nominal_limit", minimum=1)
        reserved = _require_int(raw["external_reserved"], f"{where}.external_reserved", minimum=0)
        if reserved >= nominal:
            raise BriefError(
                f"{where}.external_reserved",
                f"{where}: external_reserved {reserved} leaves no slot below "
                f"nominal_limit {nominal}; nominal_limit is a ceiling for the whole key, "
                "and the pipeline's share is nominal_limit - external_reserved")
        enabled = raw["enabled"]
        if not isinstance(enabled, bool):
            raise BriefError(f"{where}.enabled",
                             f"{where}.enabled must be true or false, got {enabled!r}")
        out.append({
            "name": name,
            "label": sanitize(_require_text(raw["label"], f"{where}.label"), 60),
            "endpoint": endpoint,
            "codex_home": codex_home,
            "codex_home_path": str(Path(codex_home).expanduser()),
            "nominal_limit": nominal,
            "external_reserved": reserved,
            "enabled": enabled,
        })
    if not any(account["enabled"] for account in out):
        raise BriefError("accounts", "no account is enabled; the run would dispatch nowhere")
    return out


def _validate_models(models) -> dict:
    _require_mapping(models, "models")
    unknown = sorted(set(models) - {"override"})
    if unknown:
        raise BriefError(f"models.{unknown[0]}",
                         f"unknown key(s) under 'models': {', '.join(unknown)}")
    override = models.get("override")
    if override not in OVERRIDES:
        raise BriefError("models.override",
                         f"models.override must be null or 'astra-all', got {override!r}")
    return {"override": override}


def validate_brief(doc) -> dict:
    """Return the normalized brief, or raise ``BriefError`` naming the key."""
    _require_mapping(doc, "brief")
    unknown = sorted(set(doc) - set(BRIEF_KEYS))
    if unknown:
        raise BriefError(unknown[0], f"unknown top-level key(s): {', '.join(unknown)}")
    missing = [key for key in BRIEF_KEYS if key not in doc]
    if missing:
        raise BriefError(missing[0], f"the brief is missing: {', '.join(missing)}")
    if doc["schema"] != BRIEF_SCHEMA:
        raise BriefError("schema",
                         f"schema must be {BRIEF_SCHEMA!r}, got {doc['schema']!r}")
    return {
        "schema": BRIEF_SCHEMA,
        "run": _validate_run(doc["run"]),
        "accounts": _validate_accounts(doc["accounts"]),
        "models": _validate_models(doc["models"]),
    }


def read_brief(path: Path) -> tuple[dict, str]:
    """Read, validate and digest the brief at *path*."""
    if not path.exists():
        raise BriefError("brief", f"no run brief at {path}\n{_template_hint()}\n"
                                  "Copy the template, edit the values, then re-run "
                                  "'run_mode.py apply'. A run never starts with an "
                                  "assumed capacity.")
    raw = path.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    try:
        doc = json.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise BriefError("brief", f"{path} is not valid JSON: {exc}\n{_template_hint()}") from exc
    return validate_brief(doc), digest


# ---------------------------------------------------------------------------
# Derived capacity
# ---------------------------------------------------------------------------

def measured_limits(root: Path | None = None) -> dict[str, int]:
    """Per-account `measured_limit` from the capacity controller, if any.

    An unreadable or malformed estimate degrades to "no measurement" with a
    warning: a corrupt runtime file must never become zero capacity.
    """
    base = root or cache_root()
    path = base / "watchdog" / "capacity" / "limit-estimate.json"
    if not path.exists():
        return {}
    try:
        doc = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as exc:
        sys.stderr.write(f"run_mode.py: warning: ignoring {path}: {exc}\n")
        return {}
    accounts = doc.get("accounts") if isinstance(doc, dict) else None
    source = accounts if isinstance(accounts, dict) else doc if isinstance(doc, dict) else {}
    out: dict[str, int] = {}
    for name in ACCOUNT_NAMES:
        row = source.get(name)
        if not isinstance(row, dict):
            continue
        value = row.get("measured_limit")
        if isinstance(value, bool) or not isinstance(value, int) or value < 0:
            continue
        out[name] = value
    return out


def effective_caps(brief: dict, measured: dict[str, int] | None = None) -> dict[str, int]:
    """Starting cap per account.

    ``cap0 = clamp(1, nominal_limit - external_reserved,
    last_measured_limit or nominal_limit - external_reserved)`` — a run starts
    below the measured cliff instead of above it.  A disabled or unlisted
    account is 0: the pipeline never dispatches there at all.
    """
    seen = measured or {}
    caps = {name: 0 for name in ACCOUNT_NAMES}
    for account in brief["accounts"]:
        if not account["enabled"]:
            continue
        base = account["nominal_limit"] - account["external_reserved"]
        target = base
        limit = seen.get(account["name"])
        if isinstance(limit, int) and limit >= 0:
            target = min(base, limit)
        caps[account["name"]] = max(1, min(base, target))
    return caps


def floor_for(caps: dict[str, int], occupancy_target: float) -> int:
    return int(occupancy_target * sum(caps.values()))


def cap_values(caps: dict[str, int]) -> dict[str, int]:
    """The three derived files; `max-codex` is mechanically the sum.

    Values are validated, never coerced: a string or ``None`` reaching a cap
    file is the failure this refuses, so it must not be silently repaired.
    """
    values: dict[str, int] = {}
    for name in ACCOUNT_NAMES:
        value = caps.get(name, 0)
        if isinstance(value, bool) or not isinstance(value, int) or value < 0:
            raise LayerError(f"refusing max-codex-{name}: {value!r} is not a "
                             "nonnegative integer (an empty or non-numeric cap file "
                             "makes every dispatch exit 4)")
        values[f"max-codex-{name}"] = value
    values["max-codex"] = sum(values.values())
    return values


def write_caps(caps: dict[str, int], *, root: Path | None = None,
               dry_run: bool = False) -> dict[str, int]:
    """Write the derived cap files, never empty and never non-numeric."""
    values = cap_values(caps)
    if dry_run:
        return values
    base = (root or cache_root()) / "watchdog"
    for name, value in values.items():
        path = base / name
        atomic_write(path, f"{value}\n")
        readback = path.read_text(encoding="utf-8").strip()
        if not readback or not readback.isdigit() or int(readback) != value:
            raise LayerError(f"{path} did not read back as {value} (got {readback!r}); "
                             "the cap files must never be empty or non-numeric")
    return values


#: The runtime knob `model_policy.py` reads (`model_policy.OVERRIDE_KNOB`).
MODEL_OVERRIDE_REL = Path("watchdog") / "model-override"


def write_model_override(mode: dict, *, root: Path | None = None,
                         dry_run: bool = False) -> str:
    """Make ``models.override`` real: write or remove the runtime knob.

    Validating the field and exposing it through ``get model_override`` is not
    the same as applying it. Until this ran, ``models.override`` was inert: the
    only live overrides were the committed ``local/model-policy.json`` (a
    reviewed PR, impossible mid-run) and a knob file a human typed — so "every
    worker on the hard model" still cost a hand edit, the intervention the field
    exists to remove.  ``astra-all`` writes the knob, ``null`` removes it.
    """
    path = (root or cache_root()) / MODEL_OVERRIDE_REL
    override = mode["models"]["override"]
    if dry_run:
        return (f"{path} removed (no override)" if override is None
                else f"{path} = {override}")
    if override is None:
        try:
            path.unlink()
        except FileNotFoundError:
            return "no model override (runtime knob absent)"
        except OSError as exc:
            raise LayerError(f"cannot remove the model override knob {path}: {exc}") from exc
        return f"model override cleared ({path} removed)"
    document = {"mode": override,
                "set_by": f"run_mode.py apply, brief sha256 {mode['brief_sha256'][:12]}",
                "reason": "models.override in the run brief"}
    atomic_write(path, json.dumps(document, ensure_ascii=False) + "\n")
    return f"model override {override} active (runtime knob {path})"


def read_live_caps(root: Path | None = None) -> dict[str, int | None]:
    """Cap files as the router sees them; unreadable is None, never zero."""
    base = (root or cache_root()) / "watchdog"
    out: dict[str, int | None] = {}
    for name in ACCOUNT_NAMES:
        path = base / f"max-codex-{name}"
        try:
            text = path.read_text(encoding="utf-8").strip()
        except OSError:
            out[name] = None
            continue
        if not text.isdigit():
            sys.stderr.write(f"run_mode.py: warning: {path} is empty or non-numeric "
                             f"({text!r}); treating this account's cap as unknown, "
                             "not as zero\n")
            out[name] = None
            continue
        out[name] = int(text)
    return out


# ---------------------------------------------------------------------------
# The mode document
# ---------------------------------------------------------------------------

def build_mode(brief: dict, digest: str, source: Path,
               caps: dict[str, int], measured: dict[str, int]) -> dict:
    run = dict(brief["run"])
    accounts = []
    for account in brief["accounts"]:
        row = dict(account)
        row["cap"] = caps.get(account["name"], 0)
        row["base_cap"] = account["nominal_limit"] - account["external_reserved"]
        row["measured_limit"] = measured.get(account["name"])
        accounts.append(row)
    return {
        "schema": MODE_SCHEMA,
        "generated": utcnow(),
        "brief_path": str(source),
        "brief_sha256": digest,
        "run": run,
        "accounts": accounts,
        "models": dict(brief["models"]),
        "derived": {
            "caps": dict(caps),
            "max_codex": sum(caps.values()),
            "floor": floor_for(caps, run["occupancy_target"]),
        },
        "paused": False,
        "paused_at": None,
        "saved_caps": None,
    }


def write_mode(mode: dict, *, root: Path | None = None) -> Path:
    path = (root or cache_root()) / "watchdog" / "run-mode.json"
    atomic_write(path, json.dumps(mode, indent=1, ensure_ascii=False) + "\n")
    return path


def load_mode(root: Path | None = None) -> dict:
    """The mode record, or ``LayerError`` — an unreadable mode is unknown."""
    path = (root or cache_root()) / "watchdog" / "run-mode.json"
    try:
        doc = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise LayerError(
            f"no run mode at {path}: the run has not been briefed.\n"
            f"{_template_hint()}\n"
            "Run 'local/bin/run_mode.py apply' first. Treat this as unknown, "
            "never as zero capacity.") from exc
    except (OSError, ValueError) as exc:
        raise LayerError(f"{path} is unreadable ({exc}); treat the run mode as "
                         "unknown, never as zero capacity") from exc
    if not isinstance(doc, dict) or doc.get("schema") != MODE_SCHEMA:
        raise LayerError(f"{path} is not a {MODE_SCHEMA} document; re-run "
                         "'run_mode.py apply'")
    return doc


def account_row(mode: dict, name: str) -> dict:
    for account in mode.get("accounts", []):
        if account.get("name") == name:
            return account
    raise LayerError(f"account {name!r} is not in the brief "
                     f"({', '.join(a.get('name', '?') for a in mode.get('accounts', []))})")


def current_caps(mode: dict, root: Path | None = None) -> dict[str, int]:
    """Live cap files where readable, the record where not."""
    live = read_live_caps(root)
    recorded = mode.get("derived", {}).get("caps", {})
    return {name: (live[name] if live.get(name) is not None
                   else int(recorded.get(name, 0)))
            for name in ACCOUNT_NAMES}


# ---------------------------------------------------------------------------
# Accessors
# ---------------------------------------------------------------------------

SCALAR_KEYS = {
    "label": lambda m: m["run"]["label"],
    "start": lambda m: m["run"]["start"],
    "dispatch_cutoff": lambda m: m["run"]["dispatch_cutoff"],
    "pause_deadline_min": lambda m: m["run"]["pause_deadline_min"],
    "speed": lambda m: m["run"]["speed"],
    "turn_max": lambda m: m["run"]["turn_max_min"],
    "turn_max_min": lambda m: m["run"]["turn_max_min"],
    "estimate_cadence_min": lambda m: m["run"]["estimate_cadence_min"],
    "occupancy_target": lambda m: m["run"]["occupancy_target"],
    "progress_issue": lambda m: m["run"]["progress_issue"],
    "estimate_issue": lambda m: m["run"]["estimate_issue"],
    "owner_inbox_issue": lambda m: m["run"]["owner_inbox_issue"],
    "model_override": lambda m: m["models"]["override"] or "none",
    "brief_sha256": lambda m: m["brief_sha256"],
    "paused": lambda m: "yes" if m.get("paused") else "no",
    # The MAIN session's launch values.  main-session.sh reads exactly these
    # three; without them every `get` exited 2 and the launcher silently used
    # its own defaults, so the account the main session ran on came from the
    # ambient CODEX_HOME rather than from the brief.
    "main.model": lambda m: m["run"].get("main", MAIN_DEFAULTS)["model"],
    "main.effort": lambda m: m["run"].get("main", MAIN_DEFAULTS)["effort"],
    "main.codex_home": lambda m: m["run"].get("main", MAIN_DEFAULTS)["codex_home"],
}

PER_ACCOUNT_KEYS = ("cap", "endpoint", "codex_home", "label", "enabled",
                    "nominal_limit", "external_reserved")


def value_for(mode: dict, key: str, root: Path | None = None):
    """One value for ``get KEY``; unknown keys raise ``LayerError``."""
    if key in SCALAR_KEYS:
        return SCALAR_KEYS[key](mode)
    caps = current_caps(mode, root)
    if key == "floor":
        return floor_for(caps, mode["run"]["occupancy_target"])
    if key == "max_codex":
        return sum(caps.values())
    if key == "accounts":
        return " ".join(a["name"] for a in mode["accounts"] if a.get("enabled"))
    if "." in key:
        field, _, name = key.partition(".")
        if field in PER_ACCOUNT_KEYS and name in ACCOUNT_NAMES:
            row = account_row(mode, name)
            if field == "cap":
                return caps.get(name, 0)
            if field == "codex_home":
                return row.get("codex_home_path") or row["codex_home"]
            if field == "enabled":
                return "yes" if row["enabled"] else "no"
            return row[field]
    known = sorted(list(SCALAR_KEYS) + ["floor", "max_codex", "accounts"] +
                   [f"{field}.<account>" for field in PER_ACCOUNT_KEYS])
    raise LayerError(f"unknown key {key!r}; known keys: {', '.join(known)}")


def render_show(mode: dict, root: Path | None = None) -> str:
    run = mode["run"]
    caps = current_caps(mode, root)
    total = sum(caps.values())
    paused = " (PAUSED)" if mode.get("paused") else ""
    lines = [
        f"run              {run['label']}{paused}",
        f"brief            {mode['brief_path']}  sha256 {mode['brief_sha256'][:12]}",
        f"start            {run['start']}",
        f"dispatch cutoff  {run['dispatch_cutoff']}",
        f"speed            {run['speed']}  (turn max {run['turn_max_min']} min, "
        f"estimate every {run['estimate_cadence_min']} min)",
        f"occupancy        target {run['occupancy_target']:.2f}, floor "
        f"{floor_for(caps, run['occupancy_target'])} of {total}",
    ]
    for account in mode["accounts"]:
        name = account["name"]
        state = "enabled" if account["enabled"] else "DISABLED"
        measured = account.get("measured_limit")
        seen = f", measured {measured}" if isinstance(measured, int) else ""
        lines.append(
            f"cap {name:<12} {caps.get(name, 0)} of ceiling {account['nominal_limit']} "
            f"minus reserved {account['external_reserved']} "
            f"({account['label']}, {account['endpoint']}, {state}{seen})")
    lines += [
        f"max-codex        {total}  (sum of the per-account caps; no admission meaning)",
        f"issues           progress #{run['progress_issue']}, estimate "
        f"#{run['estimate_issue']}, owner inbox #{run['owner_inbox_issue']}",
        f"models           override {mode['models']['override'] or 'none (local/model-policy.json)'}",
        f"main session     {run.get('main', MAIN_DEFAULTS)['model']} effort "
        f"{run.get('main', MAIN_DEFAULTS)['effort']}, CODEX_HOME "
        f"{run.get('main', MAIN_DEFAULTS)['codex_home'] or '(ambient)'}",
        f"pause deadline   {run['pause_deadline_min']} min",
    ]
    if mode.get("paused"):
        lines.append(f"paused at        {mode.get('paused_at')} "
                     f"(saved caps {mode.get('saved_caps')})")
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------------------
# The PATH shim (the speed tier)
# ---------------------------------------------------------------------------

def shim_template_path() -> Path:
    return repo_root() / SHIM_TEMPLATE_REL


def shim_path() -> Path:
    return owner_bin() / "codex"


def render_shim(template: str, speed: str) -> str:
    """The deployed shim for *speed*, rendered from the committed template."""
    if speed not in SPEEDS:
        raise LayerError(f"speed must be one of {SPEEDS}, got {speed!r}")
    # Position 1, the one the committed template actually uses: a single
    # anchored SPEED_ARGS= line.  Anchored at the start of the line on purpose -
    # the template's header documents both renderings, and a comment that merely
    # shows the line must never be rewritten with it.
    speed_lines = _SPEED_ARGS_RE.findall(template)
    if speed_lines:
        if len(speed_lines) != 1:
            raise LayerError(
                f"{shim_template_path()} has {len(speed_lines)} lines starting "
                "with SPEED_ARGS=; exactly one is required (install.sh renders "
                "the same line and exits 5 on the same condition).")
        return _SPEED_ARGS_RE.sub(
            lambda _match: SPEED_ARGS_LINE[speed], template, count=1)
    stripped = _SERVICE_TIER_RE.sub("", template)
    if SPEED_PLACEHOLDER in stripped:
        return _PLACEHOLDER_RE.sub(PRIORITY_ARG + " " if speed == "fast" else "", stripped)
    if SHIM_ANCHOR not in stripped:
        raise LayerError(
            f"{shim_template_path()} carries neither {SPEED_PLACEHOLDER} nor the "
            f"anchor {SHIM_ANCHOR}; the speed tier has no rendering position. Fix the "
            "committed template (results/telemetry/owner-tools/owner-bin-codex) rather "
            "than hand-patching the deployed shim.")
    if speed == "default":
        return stripped
    return stripped.replace(SHIM_ANCHOR, f"{PRIORITY_ARG} {SHIM_ANCHOR}", 1)


def record_shim() -> str:
    """Re-record the regenerated shim in ``owner-bin/manifest.sha256``.

    ``install.sh`` releases both renderings into ``manifest.accepted`` but keeps
    ``manifest.sha256`` at the deployed one, and the merge daemon's start gate is
    ``install.sh --verify``.  Without this step the first ``set speed`` of a run
    makes the daemon refuse to start.  Best effort: a missing or failing
    installer is a warning, never a reason to leave the speed change unmade.
    """
    installer = repo_root() / "results" / "telemetry" / "owner-tools" / "install.sh"
    if not installer.is_file():
        return f"manifest not re-recorded: no {installer}"
    try:
        done = subprocess.run(["bash", str(installer), "--record", "codex"],
                              capture_output=True, text=True, timeout=60)
    except (OSError, subprocess.SubprocessError) as exc:
        return f"warning: install.sh --record codex did not run: {exc}"
    if done.returncode != 0:
        detail = (done.stderr or done.stdout).strip().splitlines()
        return ("warning: install.sh --record codex failed: "
                + (detail[-1] if detail else f"exit {done.returncode}"))
    return "manifest re-recorded (install.sh --record codex)"


def _shim_diff(live: str, wanted: str) -> str:
    return "".join(difflib.unified_diff(
        live.splitlines(keepends=True), wanted.splitlines(keepends=True),
        fromfile="deployed shim", tofile="rendered from the committed template"))


def apply_speed(mode: dict, speed: str, *, dry_run: bool = False) -> str:
    """Regenerate the deployed shim; refuse when it was hand-edited."""
    template_file = shim_template_path()
    try:
        template = template_file.read_text(encoding="utf-8")
    except OSError as exc:
        raise LayerError(f"cannot read the shim template {template_file}: {exc}") from exc
    wanted = render_shim(template, speed)
    renderings = {render_shim(template, tier) for tier in SPEEDS}
    live_file = shim_path()
    try:
        live = live_file.read_text(encoding="utf-8")
    except FileNotFoundError as exc:
        raise Refused(
            f"no deployed shim at {live_file}; install the operator tools first "
            "(results/telemetry/owner-tools/install.sh)") from exc
    if live not in renderings:
        raise Refused(
            f"the deployed shim {live_file} differs from every rendering of "
            f"{template_file}; refusing to discard an emergency hand-edit.\n"
            "Fold the edit into the committed template, redeploy, then retry.\n"
            + _shim_diff(live, wanted))
    if dry_run:
        return "dry-run: shim unchanged"
    if live == wanted:
        return f"shim already at {speed} speed"
    mode_bits = os.stat(live_file).st_mode & 0o777
    atomic_write(live_file, wanted)
    os.chmod(live_file, mode_bits or 0o755)
    return f"shim regenerated at {speed} speed; {record_shim()}"


# ---------------------------------------------------------------------------
# Records
# ---------------------------------------------------------------------------

def locked_append(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd = os.open(path, os.O_RDWR | os.O_CREAT | os.O_APPEND, 0o644)
    with os.fdopen(fd, "r+", encoding="utf-8") as handle:
        fcntl.flock(handle.fileno(), fcntl.LOCK_EX)
        try:
            handle.seek(0, os.SEEK_END)
            if handle.tell():
                handle.seek(handle.tell() - 1)
                if handle.read(1) != "\n":
                    handle.write("\n")
                handle.seek(0, os.SEEK_END)
            handle.write(text if text.endswith("\n") else text + "\n")
            handle.flush()
            os.fsync(handle.fileno())
        finally:
            fcntl.flock(handle.fileno(), fcntl.LOCK_UN)


def append_stage(note: str, event: str, *, root: Path | None = None) -> None:
    """One `stages.jsonl` row through telemetry.py's locked appender."""
    path = (root or repo_root()) / "results" / "telemetry" / "stages.jsonl"
    record = {"ts": stamp(), "stage": "operator", "event": event,
              "note": sanitize(note, 2000)}
    try:
        import telemetry  # noqa: PLC0415 - optional, same directory
    except ImportError:
        locked_append(path, json.dumps(record, ensure_ascii=False))
        return
    telemetry.append_jsonl(path, record)


def _cell(text: str) -> str:
    return sanitize(str(text), 400).replace("|", "/").replace("\n", " ").strip()


def append_decision(decision: str, who: str, rationale: str, record: str,
                    *, root: Path | None = None) -> None:
    """One row in the design-decisions register (newest last)."""
    path = (root or repo_root()) / "results" / "telemetry" / "design-decisions.md"
    date = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    row = (f"| {date} | {_cell(decision)} | {_cell(who)} | {_cell(rationale)} "
           f"| {_cell(record)} |")
    locked_append(path, row)


# ---------------------------------------------------------------------------
# The capacity controller round trip (W3), when it is installed
# ---------------------------------------------------------------------------

def controller_path() -> Path:
    # repo_root(), not this file's directory: capacity_controller.py resolves its
    # policy (local/capacity-policy.json) and its state under repo_root(), so a
    # controller taken from another tree would be run against a different root's
    # data.  In the checkout the two paths are the same file.
    return repo_root() / "local" / "bin" / "capacity_controller.py"


def controller_state(root: Path | None = None) -> dict | None:
    path = (root or cache_root()) / "watchdog" / "capacity" / "state.json"
    try:
        doc = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return None
    return doc if isinstance(doc, dict) else None


def controller_caps(root: Path | None = None) -> dict[str, int]:
    doc = controller_state(root) or {}
    caps = doc.get("caps") if isinstance(doc.get("caps"), dict) else {}
    accounts = doc.get("accounts") if isinstance(doc.get("accounts"), dict) else {}
    out: dict[str, int] = {}
    for name in ACCOUNT_NAMES:
        value = caps.get(name)
        if not isinstance(value, int) or isinstance(value, bool):
            row = accounts.get(name)
            value = row.get("cap") if isinstance(row, dict) else None
        if isinstance(value, int) and not isinstance(value, bool) and value >= 0:
            out[name] = value
    return out


def call_controller(command: str) -> tuple[bool, str]:
    path = controller_path()
    if not path.exists():
        return (False, "not installed")
    proc = subprocess.run([sys.executable, str(path), command],
                          capture_output=True, text=True)
    detail = (proc.stdout + proc.stderr).strip()[:800]
    return (proc.returncode == 0, detail or f"exit {proc.returncode}")


# ---------------------------------------------------------------------------
# Subcommands
# ---------------------------------------------------------------------------

def cmd_apply(args: argparse.Namespace) -> int:
    source = Path(args.brief).expanduser() if args.brief else brief_path()
    brief, digest = read_brief(source)
    measured = measured_limits()
    caps = effective_caps(brief, measured)
    mode = build_mode(brief, digest, source, caps, measured)
    values = cap_values(caps)
    run = mode["run"]
    summary = (f"speed {run['speed']}, caps " +
               ", ".join(f"{name} {caps[name]}" for name in ACCOUNT_NAMES) +
               f", max-codex {values['max-codex']}, occupancy floor "
               f"{mode['derived']['floor']} (target {run['occupancy_target']:.2f}), "
               f"cutoff {run['dispatch_cutoff']}, issues "
               f"progress #{run['progress_issue']} estimate #{run['estimate_issue']} "
               f"inbox #{run['owner_inbox_issue']}, override "
               f"{mode['models']['override'] or 'none'}")

    if args.dry_run:
        sys.stdout.write(render_show(mode))
        sys.stdout.write("\nwould write:\n")
        sys.stdout.write(f"  {mode_path()}\n")
        for name, value in values.items():
            sys.stdout.write(f"  {watchdog_dir() / name} = {value}\n")
        sys.stdout.write(f"  {shim_path()} rendered at {run['speed']} speed\n")
        sys.stdout.write(f"  {write_model_override(mode, dry_run=True)}\n")
        sys.stdout.write(f"  brief sha256 {digest}\n")
        return 0

    previous_paused = False
    try:
        previous_paused = bool(load_mode().get("paused"))
    except LayerError:
        pass
    path = write_mode(mode)
    write_caps(caps)
    override_note = write_model_override(mode)
    # Hand the briefed caps to the capacity controller, which is the sole writer
    # of watchdog/capacity/state.json and therefore the thing `pause` asks to
    # save them and `resume` asks to restore them.  Without this seed the
    # controller has no state, `pause` saves zeros, and `resume` restores the
    # floor: a briefed 5/28/33 came back as 1/1/2 while the resume message
    # announced 5/28/33 - the exact defect of the 2026-09-12 resume script.
    ok, detail = call_controller("init")
    if not ok and detail != "not installed":
        sys.stderr.write(
            "run_mode.py: warning: capacity_controller.py init failed: "
            f"{detail}\nThe cap files above are correct, but pause/resume will "
            "not round-trip until the controller has state. Fix it, then run "
            "'python3 local/bin/capacity_controller.py init'.\n")
    append_stage(f"run-mode apply: {summary}; {override_note}; brief {source} "
                 f"sha256 {digest}", "run-mode-apply")
    append_decision(
        f"Run mode applied: {summary}",
        "owner brief via run_mode.py apply",
        "one briefing per run; capacity, schedule, speed and issue numbers live only in "
        "watchdog/run-brief.json and are read through run_mode.py get",
        f"brief sha256 {digest[:12]}; {path}; stages.jsonl event=run-mode-apply")
    sys.stdout.write(render_show(mode))
    sys.stdout.write(override_note + "\n")
    if previous_paused:
        sys.stdout.write("note: the previous run mode was paused; this brief restores "
                         "capacity now.\n")
    # The briefed speed must reach the deployed shim, or `fast` is a word in a
    # file and every worker runs at default speed (2026-09-12, three hand
    # patches).  A missing or hand-edited shim is reported loudly and never
    # silently overwritten; the caps above are applied either way.
    try:
        sys.stdout.write(apply_speed(mode, run["speed"]) + "\n")
    except (Refused, LayerError) as exc:
        sys.stderr.write(f"run_mode.py: warning: the shim was NOT regenerated: {exc}\n"
                         f"Fix it, then run 'run_mode.py set speed {run['speed']}'.\n")
    return 0


def cmd_show(args: argparse.Namespace) -> int:
    mode = load_mode()
    if args.json:
        json.dump(mode, sys.stdout, indent=1, ensure_ascii=False)
        sys.stdout.write("\n")
    else:
        sys.stdout.write(render_show(mode))
    return 0


def cmd_get(args: argparse.Namespace) -> int:
    mode = load_mode()
    sys.stdout.write(f"{value_for(mode, args.key)}\n")
    return 0


def cmd_set(args: argparse.Namespace) -> int:
    mode = load_mode()
    speed = args.value
    if speed not in SPEEDS:
        raise LayerError(f"speed must be one of {SPEEDS}, got {speed!r}")
    note = apply_speed(mode, speed, dry_run=args.dry_run)
    if args.dry_run:
        sys.stdout.write(f"{note}; speed would become {speed}\n")
        return 0
    previous = mode["run"]["speed"]
    mode["run"]["speed"] = speed
    mode["run"]["turn_max_min"] = TURN_MAX_MIN[speed]
    mode["run"]["estimate_cadence_min"] = ESTIMATE_CADENCE_MIN[speed]
    mode["generated"] = utcnow()
    write_mode(mode)
    append_stage(f"run-mode speed {previous} -> {speed}: {note}; turn max "
                 f"{mode['run']['turn_max_min']} min, estimate cadence "
                 f"{mode['run']['estimate_cadence_min']} min", "run-mode-speed")
    append_decision(
        f"Run speed {previous} -> {speed}",
        "operator via run_mode.py set speed",
        "one switch regenerates the deployed shim from the committed template; "
        "a hand-edited shim is refused, not clobbered",
        f"{shim_path()}; {mode_path()}; stages.jsonl event=run-mode-speed")
    sys.stdout.write(
        f"{note}\n"
        f"speed {previous} -> {speed} (turn max {mode['run']['turn_max_min']} min, "
        f"estimate cadence {mode['run']['estimate_cadence_min']} min)\n"
        "picked up by: worker sessions dispatched from now on (yes), lane and daemon "
        "children started from now on (yes), the running main TUI (NO — relaunch it "
        "through local/bin/main-session.sh), sessions already running (NO)\n"
        "the estimate cadence changes only when the crontab is regenerated "
        "(results/telemetry/owner-tools/install-crons.sh)\n")
    return 0


def cmd_pause(args: argparse.Namespace) -> int:
    mode = load_mode()
    saved = mode.get("saved_caps")
    if not (mode.get("paused") and isinstance(saved, dict) and saved):
        saved = controller_caps() or current_caps(mode)
    saved = {name: int(saved.get(name, 0)) for name in ACCOUNT_NAMES}
    zero = {name: 0 for name in ACCOUNT_NAMES}
    mode["paused"] = True
    mode["paused_at"] = utcnow()
    mode["saved_caps"] = saved
    mode["derived"] = {"caps": zero, "max_codex": 0, "floor": 0}
    write_mode(mode)

    ok, detail = call_controller("pause")
    problem = ""
    if ok:
        source = "capacity_controller.py pause"
        live = read_live_caps()
        if any(value is None or value != 0 for value in live.values()):
            write_caps(zero)
            source += " (cap files corrected by run_mode.py)"
    elif detail == "not installed":
        write_caps(zero)
        source = "run_mode.py (no capacity controller installed)"
    else:
        write_caps(zero)
        source = "run_mode.py (controller refused)"
        problem = f"capacity_controller.py pause failed: {detail}"

    note = (f"run-mode pause: caps zeroed via {source}; saved caps " +
            ", ".join(f"{name} {saved[name]}" for name in ACCOUNT_NAMES) +
            (f"; reason {args.reason}" if args.reason else ""))
    append_stage(note, "run-mode-pause")
    append_decision(
        "Admission paused: every account cap set to 0, pre-pause caps saved in the run mode",
        "operator via run_mode.py pause",
        args.reason or "owner pause word; running work finishes, no new dispatch starts",
        f"{mode_path()}; stages.jsonl event=run-mode-pause")
    sys.stdout.write(f"{note}\n")
    if problem:
        sys.stderr.write(f"run_mode.py: {problem}\n")
        return 3
    return 0


def cmd_resume(args: argparse.Namespace) -> int:
    mode = load_mode()
    if not mode.get("paused"):
        sys.stderr.write("run_mode.py: warning: the run mode is not paused; "
                         "restoring the briefed caps anyway\n")
    saved = mode.get("saved_caps") if isinstance(mode.get("saved_caps"), dict) else {}
    briefed = effective_caps({"accounts": mode["accounts"]}, measured_limits())
    caps: dict[str, int] = {}
    for name in ACCOUNT_NAMES:
        row = next((a for a in mode["accounts"] if a["name"] == name), None)
        enabled = bool(row and row.get("enabled"))
        value = saved.get(name)
        if not isinstance(value, int) or isinstance(value, bool) or value < 0:
            value = briefed[name]
        if enabled and value < 1:
            sys.stderr.write(f"run_mode.py: warning: saved cap for {name} was {value}; "
                             f"resuming at the briefed {briefed[name]} instead of zero "
                             "capacity\n")
            value = briefed[name]
        if not enabled:
            value = 0
        caps[name] = value

    mode["paused"] = False
    mode["paused_at"] = None
    mode["saved_caps"] = None
    mode["derived"] = {"caps": dict(caps), "max_codex": sum(caps.values()),
                       "floor": floor_for(caps, mode["run"]["occupancy_target"])}
    mode["generated"] = utcnow()
    write_mode(mode)
    # Re-assert the briefed override: the knob and the mode must never diverge,
    # and a resume is exactly when someone would notice that they had.
    resume_override = write_model_override(mode)

    ok, detail = call_controller("resume")
    if ok:
        source = "capacity_controller.py resume"
    elif detail == "not installed":
        write_caps(caps)
        source = "run_mode.py (no capacity controller installed)"
    else:
        raise Refused(f"capacity_controller.py resume failed: {detail}\n"
                      "The cap files were left where they are (paused is the safe "
                      "direction). Fix the controller and re-run 'run_mode.py resume'.")

    live = read_live_caps()
    for name in ACCOUNT_NAMES:
        row = next((a for a in mode["accounts"] if a["name"] == name), None)
        enabled = bool(row and row.get("enabled"))
        value = live.get(name)
        if value is None:
            raise Refused(f"post-condition: {watchdog_dir()}/max-codex-{name} is missing, "
                          "empty or non-numeric after resume")
        if enabled and value < 1:
            raise Refused(f"post-condition: {name} is enabled but resumed at cap {value}")
        if value != caps[name]:
            raise Refused(
                f"post-condition: {name} was resumed at cap {value}, not the "
                f"restored {caps[name]}. Something else wrote the cap file, or "
                "the capacity controller has no state for this run (seed it with "
                "'python3 local/bin/capacity_controller.py init'). Refusing to "
                "report a number the files do not carry.")
    # Reported from the files, not from the intent: a resume that announces caps
    # it did not actually write is how the 2026-09-12 run lost an hour.
    live_total = sum(live[name] or 0 for name in ACCOUNT_NAMES)
    note = ("run-mode resume: caps " +
            ", ".join(f"{name} {live[name]}" for name in ACCOUNT_NAMES) +
            f", max-codex {live_total}, floor {mode['derived']['floor']} "
            f"via {source}; {resume_override}")
    append_stage(note, "run-mode-resume")
    append_decision(
        "Admission resumed from the saved caps in the run mode",
        "operator via run_mode.py resume",
        "resume restores the recorded pre-pause caps only; it never re-derives capacity "
        "from a message or a second file",
        f"{mode_path()}; stages.jsonl event=run-mode-resume")
    sys.stdout.write(f"{note}\n")
    sys.stdout.write(render_show(mode))
    return 0


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="run_mode.py", description=__doc__.splitlines()[0],
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--repo-root", help="checkout holding results/telemetry "
                                            "(default: this script's checkout)")
    sub = parser.add_subparsers(dest="cmd", required=True)

    p = sub.add_parser("apply", help="validate the brief and write the mode file")
    p.add_argument("--brief", help=f"default {'<cache>/watchdog/run-brief.json'}")
    p.add_argument("--dry-run", action="store_true", help="print the plan, write nothing")

    p = sub.add_parser("show", help="human-readable dump of the run mode")
    p.add_argument("--json", action="store_true")

    p = sub.add_parser("get", help="one value on stdout")
    p.add_argument("key")

    p = sub.add_parser("set", help="change one mid-run knob")
    p.add_argument("knob", choices=("speed",))
    p.add_argument("value")
    p.add_argument("--dry-run", action="store_true")

    p = sub.add_parser("pause", help="stop admission: caps to 0, pre-pause caps saved")
    p.add_argument("--reason", default="")

    sub.add_parser("resume", help="restore the saved caps")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(sys.argv[1:] if argv is None else argv)
    if args.repo_root:
        os.environ["MIPSTARRE_REPO_ROOT"] = args.repo_root
    handlers = {"apply": cmd_apply, "show": cmd_show, "get": cmd_get,
                "set": cmd_set, "pause": cmd_pause, "resume": cmd_resume}
    try:
        return handlers[args.cmd](args)
    except BriefError as exc:
        sys.stderr.write(f"run_mode.py: invalid brief at {exc.key}: {exc}\n")
        if _template_hint() not in str(exc):
            sys.stderr.write(f"{_template_hint()}\n")
        return 2
    except Refused as exc:
        sys.stderr.write(f"run_mode.py: refused: {exc}\n")
        return 3
    except LayerError as exc:
        sys.stderr.write(f"run_mode.py: {exc}\n")
        return 2
    except (KeyError, TypeError, ValueError) as exc:
        # A hand-edited run-mode.json is unknown, not zero: say so and stop.
        sys.stderr.write(f"run_mode.py: {mode_path()} is incomplete ({exc!r}); "
                         "re-run 'run_mode.py apply'. Treat the run mode as "
                         "unknown, never as zero capacity.\n")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
