#!/usr/bin/env python3
"""The live accounts file: which keys exist, their ceilings, and whether to use them.

``~/.cache/mipstarre-dev/watchdog/accounts.json`` is the **owner's file** and the
source of truth for admission.  The run brief states the keys once
(``local/protocols/full-speed-mode.md`` §1); this file is what the running
pipeline actually reads, and the owner may edit it at any moment without telling
any session.  ``run_mode.py apply`` SEEDS it from the brief when it does not
exist and never overwrites an existing one, so the brief stays one-shot while
the accounts stay live.

Why it exists.  The owner has one to three endpoints, each with one or two keys,
and each key's concurrency limit moves during a run: the endpoint's admin
reassigns slots, the owner wins them back, a key becomes invalid or runs out of
quota.  On 2026-09-12 every one of those events reached the pipeline as a message
to a session that had to be idle to receive it, and the caps were edited by hand
ten times.  A file the controller re-reads each tick removes both the message and
the hand edit.

One entry per KEY::

    {"name": "second", "label": "space", "endpoint": "api.finite-dimensional.space",
     "codex_home": "~/.cache/mipstarre-dev/codex-home-yxy",
     "ceiling": 30, "external_reserved": 2, "enabled": true, "note": "admin cut to 20"}

* ``name`` — any number of accounts, any names (``[a-z0-9][a-z0-9_-]{0,31}``).
  ``primary`` and ``second`` are ordinary entries, not special cases.
* ``ceiling`` — **a ceiling, never a target.**  The controller's AIMD discovery
  runs below it and may never exceed ``ceiling - external_reserved``.  Lowering it
  takes effect on the next tick; raising it lets the additive creep continue.
* ``external_reserved`` — slots on that key the pipeline must not use (a forked
  session sharing it).  ``external_reserved == ceiling`` is legal and means the
  key has no slot for the pipeline right now — an honest state during a run, and
  different from ``enabled: false``, which is a decision.
* ``enabled: false`` — cap 0 immediately and no health probe.  Removing the entry
  means the same and also stops it being reported.
* ``note`` — free text the owner writes for themselves; it is echoed in the
  hourly per-key line and changes nothing.

**No key value ever appears here.**  The secret lives in the codex home the entry
points at, which only the owner touches; this file names that directory and
nothing else.

Every write is atomic (temp file + ``os.replace``) and appends one line to
``watchdog/capacity/accounts.log``, so "who lowered the ceiling and when" is a
``grep`` rather than an archaeology.

CLI (the operator wrapper is ``results/telemetry/owner-tools/accounts.sh``)::

    accounts_file.py list [--json]
    accounts_file.py get NAME [FIELD]
    accounts_file.py set NAME FIELD VALUE
    accounts_file.py enable NAME | disable NAME [--note TEXT]
    accounts_file.py add NAME --endpoint E --codex-home D --ceiling N
                             [--label L] [--reserved N] [--note TEXT] [--disabled]
    accounts_file.py remove NAME
    accounts_file.py seed --brief-accounts FILE [--source TEXT]
    accounts_file.py apply-directives --text-file FILE [--actor WHO]

Environment: ``MIPSTARRE_CACHE_ROOT`` (runtime root, default
``~/.cache/mipstarre-dev``).

Exit codes: 0 ok · 2 an invalid file, field or value (nothing written) ·
3 the requested account does not exist.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from wf_util import LayerError, atomic_write, sanitize  # noqa: E402

SCHEMA = "mipstarre-accounts/1"

#: Every field an entry may carry.  An unknown key is an error, not a warning:
#: a typo like ``"cieling": 40`` must not read as "ceiling unchanged".
ENTRY_KEYS = ("name", "label", "endpoint", "codex_home", "ceiling",
              "external_reserved", "enabled", "note")
REQUIRED_KEYS = ("name", "endpoint", "codex_home", "ceiling")

#: Account names travel into file names (``max-codex-<name>``), directory names
#: (``accounts/<name>/``) and shell arguments, so they are narrow on purpose.
NAME_RE = re.compile(r"^[a-z0-9][a-z0-9_-]{0,31}$")
#: Endpoint labels travel into telemetry rows and shell arguments; the same class
#: ``run_mode.py`` and ``dispatch.sh`` already validate.
ENDPOINT_RE = re.compile(r"^[a-z0-9.-]{1,40}$")

#: Fields the owner may change on an existing entry, and how each is read.
#: ``reserved`` and ``nominal_limit`` are accepted spellings of the two fields
#: the brief and the mode file use, so a line copied from either still applies.
SETTABLE = {
    "ceiling": "int", "nominal_limit": "int", "external_reserved": "int",
    "reserved": "int", "enabled": "bool", "note": "text", "label": "label",
    "endpoint": "endpoint", "codex_home": "path",
}
FIELD_ALIASES = {"reserved": "external_reserved", "nominal_limit": "ceiling"}

NOTE_LIMIT = 200

#: The owner-inbox comment form (design point 4b).  One directive per line,
#: several lines per comment allowed.  Deliberately rigid: this is a control
#: channel, not a conversation, and an unparsable line is rejected by name
#: rather than guessed at.
DIRECTIVE_RE = re.compile(r"^\s*ACCOUNTS:\s*(?P<rest>\S.*?)\s*$", re.IGNORECASE)
ASSIGN_RE = re.compile(r"^(?P<key>[a-z_]+)=(?P<value>\S+)$", re.IGNORECASE)
#: Only these may travel over GitHub.  An endpoint or a codex home is a path on
#: the owner's host and is never taken from a comment.
DIRECTIVE_FIELDS = ("ceiling", "reserved", "external_reserved", "enabled", "note")


class AccountsError(LayerError):
    """An invalid accounts file, field or value.  Nothing is written (exit 2)."""


class UnknownAccount(AccountsError):
    """The named account is not in the file (exit 3)."""


# ---------------------------------------------------------------------------
# Locations
# ---------------------------------------------------------------------------

def cache_root() -> Path:
    """Re-read per call, so a test can point it at a temporary directory."""
    return Path(os.environ.get("MIPSTARRE_CACHE_ROOT",
                               "~/.cache/mipstarre-dev")).expanduser()


def accounts_path(root: Path | None = None) -> Path:
    return (root or cache_root()) / "watchdog" / "accounts.json"


def log_path(root: Path | None = None) -> Path:
    return (root or cache_root()) / "watchdog" / "capacity" / "accounts.log"


def utcnow() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


# ---------------------------------------------------------------------------
# Validation — every failure names the entry and the field
# ---------------------------------------------------------------------------

def _int(value, where: str, *, minimum: int = 0) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise AccountsError(f"{where} must be an integer, got {value!r}")
    if value < minimum:
        raise AccountsError(f"{where} must be at least {minimum}, got {value}")
    return value


def _text(value, where: str, *, pattern: re.Pattern | None = None,
          limit: int = 200) -> str:
    if not isinstance(value, str) or not value.strip():
        raise AccountsError(f"{where} must be a non-empty string, got {value!r}")
    text = sanitize(value.strip(), limit)
    if pattern is not None and not pattern.match(text):
        raise AccountsError(f"{where} {text!r} does not match {pattern.pattern}")
    return text


def validate_entry(raw, where: str) -> dict:
    """One normalized entry, or ``AccountsError`` naming the offending field."""
    if not isinstance(raw, dict):
        raise AccountsError(f"{where} must be an object, not {type(raw).__name__}")
    unknown = sorted(set(raw) - set(ENTRY_KEYS))
    if unknown:
        raise AccountsError(
            f"{where}: unknown field(s) {', '.join(unknown)}; an entry carries "
            f"exactly {', '.join(ENTRY_KEYS)}")
    missing = [key for key in REQUIRED_KEYS if key not in raw]
    if missing:
        raise AccountsError(f"{where} is missing: {', '.join(missing)}")
    name = _text(raw["name"], f"{where}.name", pattern=NAME_RE, limit=32)
    entry = {
        "name": name,
        "label": _text(raw.get("label") or name, f"{where}.label", limit=60),
        "endpoint": _text(raw["endpoint"], f"{where}.endpoint", pattern=ENDPOINT_RE),
        "codex_home": _text(raw["codex_home"], f"{where}.codex_home", limit=400),
        "ceiling": _int(raw["ceiling"], f"{where}.ceiling", minimum=0),
        "external_reserved": _int(raw.get("external_reserved", 0),
                                  f"{where}.external_reserved", minimum=0),
        "enabled": raw.get("enabled", True),
        "note": sanitize(str(raw.get("note") or ""), NOTE_LIMIT),
    }
    if not isinstance(entry["enabled"], bool):
        raise AccountsError(f"{where}.enabled must be true or false, "
                            f"got {raw.get('enabled')!r}")
    if entry["external_reserved"] > entry["ceiling"]:
        raise AccountsError(
            f"{where}: external_reserved {entry['external_reserved']} exceeds ceiling "
            f"{entry['ceiling']}; the pipeline's share is ceiling - external_reserved, "
            "and it may not be negative. Equal values are legal and mean the key has "
            "no slot for the pipeline right now.")
    return entry


def validate(document, *, source: str = "accounts.json") -> list[dict]:
    """The entry list of a whole document (object form or bare array)."""
    if isinstance(document, list):
        raw_entries, meta = document, {}
    elif isinstance(document, dict):
        meta = document
        schema = document.get("schema")
        if schema is not None and schema != SCHEMA:
            raise AccountsError(f"{source}: schema must be {SCHEMA!r}, got {schema!r}")
        raw_entries = document.get("accounts")
        if not isinstance(raw_entries, list):
            raise AccountsError(f"{source}: 'accounts' must be an array of entries")
    else:
        raise AccountsError(f"{source}: expected an object or an array, "
                            f"got {type(document).__name__}")
    del meta
    if not raw_entries:
        raise AccountsError(f"{source}: at least one account is required; an empty "
                            "file would dispatch nowhere and reads as a mistake, "
                            "not as a decision (disable the entries instead)")
    entries: list[dict] = []
    seen: set[str] = set()
    for index, raw in enumerate(raw_entries):
        entry = validate_entry(raw, f"{source}: accounts[{index}]")
        if entry["name"] in seen:
            raise AccountsError(f"{source}: account {entry['name']!r} is listed twice; "
                                "one entry per key")
        seen.add(entry["name"])
        entries.append(entry)
    return entries


# ---------------------------------------------------------------------------
# Reading and writing
# ---------------------------------------------------------------------------

def load(root: Path | None = None) -> list[dict] | None:
    """The live entries, or ``None`` when the file does not exist.

    ``None`` means "no live file, use the run mode" — it never means "no
    accounts".  An existing but INVALID file raises: a typo in the owner's file
    must stop the controller with a named field, never silently zero the caps.
    """
    path = accounts_path(root)
    try:
        raw = path.read_text(encoding="utf-8")
    except FileNotFoundError:
        return None
    except OSError as exc:
        raise AccountsError(f"{path} is unreadable ({exc})") from exc
    try:
        document = json.loads(raw)
    except ValueError as exc:
        raise AccountsError(f"{path} is not valid JSON: {exc}") from exc
    return validate(document, source=str(path))


def load_map(root: Path | None = None) -> dict[str, dict]:
    """Live entries keyed by name; empty when there is no file."""
    entries = load(root)
    return {entry["name"]: entry for entry in entries or []}


def account_names(root: Path | None = None) -> list[str]:
    """Every account name in the live file, in file order; ``[]`` when absent.

    Callers that must still work without the file (the router, the lane runner)
    fall back to the cap files and then to the two historical names.
    """
    try:
        return [entry["name"] for entry in load(root) or []]
    except AccountsError:
        return []


def render(entries: list[dict], *, source: str = "", now: str | None = None) -> str:
    document = {"schema": SCHEMA, "updated": now or utcnow(),
                "source": sanitize(source, 400), "accounts": entries}
    return json.dumps(document, indent=1, ensure_ascii=False) + "\n"


def append_log(line: str, root: Path | None = None) -> None:
    """One line in ``watchdog/capacity/accounts.log``; never fatal.

    The log is the owner's audit trail of their own edits.  A write failure must
    not lose the edit itself, which is already on disk by the time this runs.
    """
    path = log_path(root)
    try:
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open("a", encoding="utf-8") as handle:
            handle.write(line.rstrip("\n") + "\n")
    except OSError as exc:
        sys.stderr.write(f"accounts_file.py: warning: cannot append to {path}: {exc}\n")


def save(entries: list[dict], *, root: Path | None = None, actor: str,
         action: str, detail: str, source: str = "") -> Path:
    """Validate, write atomically, then log.  Nothing is written on a bad entry."""
    checked = validate({"schema": SCHEMA, "accounts": entries}, source="the new file")
    path = accounts_path(root)
    atomic_write(path, render(checked, source=source))
    append_log(f"{utcnow()} actor={sanitize(actor, 60) or 'unknown'} "
               f"action={sanitize(action, 40)} {sanitize(detail, 400)}", root)
    return path


def seed(brief_entries, *, root: Path | None = None, source: str = "",
         actor: str = "run_mode.py apply") -> tuple[bool, Path]:
    """Write the file from the brief **only when it does not exist**.

    The brief is one-shot; the accounts file is live.  Re-applying a brief
    mid-run must not undo an hour of the owner's ceiling edits, so an existing
    file is left exactly as it is and the caller is told so.
    """
    path = accounts_path(root)
    if path.exists():
        return False, path
    entries = [from_brief_row(row, f"brief accounts[{index}]")
               for index, row in enumerate(brief_entries or [])]
    if not entries:
        raise AccountsError("the brief names no account; nothing to seed")
    save(entries, root=root, actor=actor, action="seed",
         detail="seeded " + ", ".join(f"{e['name']}={e['ceiling']}" for e in entries),
         source=source or "seeded from the run brief")
    return True, path


def from_brief_row(row, where: str) -> dict:
    """A brief/run-mode account row as a live entry (``nominal_limit`` → ``ceiling``)."""
    if not isinstance(row, dict):
        raise AccountsError(f"{where} must be an object")
    ceiling = row.get("ceiling")
    if ceiling is None:
        ceiling = row.get("nominal_limit")
    return validate_entry({
        "name": row.get("name"),
        "label": row.get("label") or row.get("name"),
        "endpoint": row.get("endpoint"),
        "codex_home": row.get("codex_home"),
        "ceiling": ceiling,
        "external_reserved": row.get("external_reserved", 0),
        "enabled": row.get("enabled", True),
        "note": row.get("note") or "",
    }, where)


def as_mode_rows(entries: list[dict]) -> list[dict]:
    """Live entries in the shape the controller and the mode file speak.

    ``ceiling`` is the live name of what the brief calls ``nominal_limit``; both
    are carried so a consumer of either spelling reads the same number.
    """
    return [dict(entry, nominal_limit=entry["ceiling"],
                 codex_home_path=str(Path(entry["codex_home"]).expanduser()))
            for entry in entries]


# ---------------------------------------------------------------------------
# Operations — the CLI and the GitHub channel share exactly these
# ---------------------------------------------------------------------------

def coerce(field: str, value) -> tuple[str, object]:
    """``(canonical field, typed value)``, or ``AccountsError`` saying why not."""
    key = field.strip().lower()
    kind = SETTABLE.get(key)
    if kind is None:
        raise AccountsError(
            f"unknown field {field!r}; settable fields are "
            f"{', '.join(sorted(set(SETTABLE) - set(FIELD_ALIASES)))}")
    canonical = FIELD_ALIASES.get(key, key)
    if kind == "int":
        text = str(value).strip()
        if not text.isdigit():
            raise AccountsError(f"{canonical} must be a nonnegative whole number, "
                                f"got {value!r}")
        return canonical, int(text)
    if kind == "bool":
        text = str(value).strip().lower()
        if text in ("true", "yes", "on", "1"):
            return canonical, True
        if text in ("false", "no", "off", "0"):
            return canonical, False
        raise AccountsError(f"{canonical} must be true or false, got {value!r}")
    if kind == "endpoint":
        return canonical, _text(value, canonical, pattern=ENDPOINT_RE)
    if kind == "label":
        return canonical, _text(value, canonical, limit=60)
    if kind == "path":
        return canonical, _text(value, canonical, limit=400)
    return canonical, sanitize(str(value), NOTE_LIMIT)


def find(entries: list[dict], name: str) -> dict:
    for entry in entries:
        if entry["name"] == name:
            return entry
    raise UnknownAccount(
        f"no account named {name!r}; the file has "
        f"{', '.join(entry['name'] for entry in entries) or 'none'}")


def apply_fields(entries: list[dict], name: str, fields: dict) -> list[str]:
    """Apply ``{field: value}`` to one entry; returns one note per change.

    The whole set is type-checked before anything is mutated, so a directive
    with one bad field changes nothing at all.
    """
    entry = find(entries, name)
    typed = [coerce(field, value) for field, value in fields.items()]
    changes: list[str] = []
    for canonical, value in typed:
        before = entry.get(canonical)
        entry[canonical] = value
        if before != value:
            changes.append(f"{canonical} {before!r} -> {value!r}")
    validate_entry(entry, f"account {name}")
    return changes


def add(entries: list[dict], name: str, *, endpoint: str, codex_home: str,
        ceiling: int, label: str = "", reserved: int = 0, note: str = "",
        enabled: bool = True) -> dict:
    if any(entry["name"] == name for entry in entries):
        raise AccountsError(f"account {name!r} already exists; use 'set' to change it")
    entry = validate_entry({
        "name": name, "label": label or name, "endpoint": endpoint,
        "codex_home": codex_home, "ceiling": ceiling,
        "external_reserved": reserved, "enabled": enabled, "note": note,
    }, f"account {name}")
    entries.append(entry)
    return entry


def remove(entries: list[dict], name: str) -> dict:
    entry = find(entries, name)
    if len(entries) == 1:
        raise AccountsError(
            f"{name!r} is the only account; removing it would leave a file that "
            "dispatches nowhere. Disable it instead, or add its replacement first.")
    entries.remove(entry)
    return entry


# ---------------------------------------------------------------------------
# The owner-inbox comment channel
# ---------------------------------------------------------------------------

def parse_directives(text: str) -> list[dict]:
    """Every ``ACCOUNTS:`` line of a comment, parsed or rejected by name.

    Returns one record per directive line::

        {"raw": "...", "name": "second", "fields": {"ceiling": "20"}, "error": ""}

    A record with a non-empty ``error`` is reported back to the owner rather than
    applied, so a typo is answered instead of ignored.  Nothing outside an
    ``ACCOUNTS:`` line is looked at: the rest of the comment is prose.
    """
    out: list[dict] = []
    for line in (text or "").splitlines():
        match = DIRECTIVE_RE.match(line)
        if not match:
            continue
        record = {"raw": sanitize(line.strip(), 200), "name": "", "fields": {},
                  "error": ""}
        tokens = match.group("rest").split()
        name = tokens[0] if tokens else ""
        if not NAME_RE.match(name or ""):
            record["error"] = (f"the first word after 'ACCOUNTS:' must be an account "
                               f"name matching {NAME_RE.pattern}, got {name!r}")
            out.append(record)
            continue
        record["name"] = name
        for token in tokens[1:]:
            assignment = ASSIGN_RE.match(token)
            if not assignment:
                record["error"] = (f"{token!r} is not a 'field=value' assignment; the "
                                   "form is 'ACCOUNTS: <name> ceiling=<n> "
                                   "[reserved=<n>] [enabled=true|false]'")
                break
            key = assignment.group("key").lower()
            if key not in DIRECTIVE_FIELDS:
                record["error"] = (f"field {key!r} may not be set from a comment; this "
                                   f"channel carries {', '.join(DIRECTIVE_FIELDS)} only "
                                   "(an endpoint or a codex home is a path on the host "
                                   "and is set with accounts.sh)")
                break
            record["fields"][key] = assignment.group("value")
        if not record["error"] and not record["fields"]:
            record["error"] = ("no field to set; the form is 'ACCOUNTS: <name> "
                               "ceiling=<n> [reserved=<n>] [enabled=true|false]'")
        out.append(record)
    return out


def apply_directives(text: str, *, root: Path | None = None, actor: str,
                     origin: str = "") -> list[str]:
    """Apply every directive of one comment; returns the owner-facing lines.

    Each line begins with ``applied:`` or ``rejected:`` and names the account and
    what changed, so the confirmation reply says exactly what took effect.  A
    rejected directive never blocks the others: the owner gets one answer per
    line they wrote.
    """
    directives = parse_directives(text)
    if not directives:
        return []
    entries = load(root)
    if entries is None:
        return [f"rejected: {record['raw']} — no {accounts_path(root)} on the host yet; "
                "the run brief has not been applied" for record in directives]
    results: list[str] = []
    dirty = False
    for record in directives:
        if record["error"]:
            results.append(f"rejected: {record['raw']} — {record['error']}")
            continue
        try:
            changes = apply_fields(entries, record["name"], record["fields"])
        except AccountsError as exc:
            results.append(f"rejected: {record['raw']} — {exc}")
            continue
        dirty = True
        results.append(f"applied: {record['name']} " +
                       ("; ".join(changes) if changes
                        else "already at the requested values"))
    if dirty:
        save(entries, root=root, actor=actor, action="inbox",
             detail=f"{origin}: " + " | ".join(results),
             source=f"owner inbox comment {origin}".strip())
    return results


# ---------------------------------------------------------------------------
# Rendering
# ---------------------------------------------------------------------------

def render_table(entries: list[dict]) -> str:
    width = max((len(entry["name"]) for entry in entries), default=4)
    lines = []
    for entry in entries:
        share = entry["ceiling"] - entry["external_reserved"]
        lines.append(
            f"{entry['name']:<{width}}  ceiling {entry['ceiling']:<4} reserved "
            f"{entry['external_reserved']:<3} share {share:<4} "
            f"{'enabled ' if entry['enabled'] else 'DISABLED'} "
            f"{entry['label']} ({entry['endpoint']}, {entry['codex_home']})"
            + (f"  note: {entry['note']}" if entry["note"] else ""))
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def _require_file(root: Path | None) -> list[dict]:
    entries = load(root)
    if entries is None:
        raise AccountsError(
            f"no accounts file at {accounts_path(root)}.\n"
            "It is seeded from the run brief by 'local/bin/run_mode.py apply'; "
            "run that first, or write the file by hand from the template in "
            "local/protocols/full-speed-mode.md.")
    return entries


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="accounts_file.py", description=__doc__.splitlines()[0],
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--actor", default=os.environ.get("MIPSTARRE_ACCOUNTS_ACTOR")
                        or os.environ.get("USER") or "operator",
                        help="who is making the change (recorded in accounts.log)")
    sub = parser.add_subparsers(dest="cmd", required=True)

    p = sub.add_parser("list", help="every entry")
    p.add_argument("--json", action="store_true")

    p = sub.add_parser("get", help="one entry, or one field of it")
    p.add_argument("name")
    p.add_argument("field", nargs="?")

    p = sub.add_parser("set", help="change one field of one entry")
    p.add_argument("name")
    p.add_argument("field")
    p.add_argument("value")

    for word in ("enable", "disable"):
        p = sub.add_parser(word, help=f"{word} one account")
        p.add_argument("name")
        p.add_argument("--note", default=None, help="replace the entry's note")

    p = sub.add_parser("add", help="add a key")
    p.add_argument("name")
    p.add_argument("--endpoint", required=True)
    p.add_argument("--codex-home", required=True)
    p.add_argument("--ceiling", type=int, required=True)
    p.add_argument("--label", default="")
    p.add_argument("--reserved", type=int, default=0)
    p.add_argument("--note", default="")
    p.add_argument("--disabled", action="store_true",
                   help="add the entry without enabling it yet")

    p = sub.add_parser("remove", help="drop a key (cap 0 immediately)")
    p.add_argument("name")

    p = sub.add_parser("seed", help="write the file from a brief, if absent")
    p.add_argument("--brief-accounts", required=True,
                   help="JSON file holding the brief's accounts array")
    p.add_argument("--source", default="")

    p = sub.add_parser("apply-directives", help="apply one ACCOUNTS: comment body")
    p.add_argument("--text-file", required=True)
    p.add_argument("--origin", default="")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    root = None
    try:
        if args.cmd == "list":
            entries = _require_file(root)
            if args.json:
                json.dump(entries, sys.stdout, indent=1, ensure_ascii=False)
                sys.stdout.write("\n")
            else:
                sys.stdout.write(render_table(entries))
            return 0
        if args.cmd == "get":
            entry = find(_require_file(root), args.name)
            if args.field:
                canonical = FIELD_ALIASES.get(args.field.lower(), args.field.lower())
                if canonical not in entry:
                    raise AccountsError(f"unknown field {args.field!r}; an entry carries "
                                        f"{', '.join(ENTRY_KEYS)}")
                sys.stdout.write(f"{entry[canonical]}\n")
            else:
                json.dump(entry, sys.stdout, indent=1, ensure_ascii=False)
                sys.stdout.write("\n")
            return 0
        if args.cmd == "set":
            entries = _require_file(root)
            changes = apply_fields(entries, args.name, {args.field: args.value})
            save(entries, root=root, actor=args.actor, action="set",
                 detail=f"{args.name}: " + ("; ".join(changes) or "no change"),
                 source="accounts.sh set")
            sys.stdout.write(f"{args.name}: {'; '.join(changes) or 'no change'}\n")
            return 0
        if args.cmd in ("enable", "disable"):
            entries = _require_file(root)
            fields: dict = {"enabled": args.cmd == "enable"}
            if args.note is not None:
                fields["note"] = args.note
            changes = apply_fields(entries, args.name, fields)
            save(entries, root=root, actor=args.actor, action=args.cmd,
                 detail=f"{args.name}: " + ("; ".join(changes) or "no change"),
                 source=f"accounts.sh {args.cmd}")
            sys.stdout.write(f"{args.name}: {'; '.join(changes) or 'no change'}\n")
            return 0
        if args.cmd == "add":
            entries = _require_file(root)
            entry = add(entries, args.name, endpoint=args.endpoint,
                        codex_home=args.codex_home, ceiling=args.ceiling,
                        label=args.label, reserved=args.reserved, note=args.note,
                        enabled=not args.disabled)
            save(entries, root=root, actor=args.actor, action="add",
                 detail=f"{entry['name']} endpoint={entry['endpoint']} "
                        f"ceiling={entry['ceiling']} enabled={entry['enabled']}",
                 source="accounts.sh add")
            sys.stdout.write(f"added {entry['name']} (ceiling {entry['ceiling']}, "
                             f"{'enabled' if entry['enabled'] else 'disabled'})\n")
            return 0
        if args.cmd == "remove":
            entries = _require_file(root)
            entry = remove(entries, args.name)
            save(entries, root=root, actor=args.actor, action="remove",
                 detail=f"{entry['name']} (ceiling {entry['ceiling']})",
                 source="accounts.sh remove")
            sys.stdout.write(f"removed {entry['name']}; its cap is 0 from the next "
                             "controller tick\n")
            return 0
        if args.cmd == "seed":
            raw = json.loads(Path(args.brief_accounts).read_text(encoding="utf-8"))
            rows = raw.get("accounts") if isinstance(raw, dict) else raw
            written, path = seed(rows, root=root, source=args.source)
            sys.stdout.write(f"{'wrote' if written else 'kept existing'} {path}\n")
            return 0
        if args.cmd == "apply-directives":
            text = Path(args.text_file).read_text(encoding="utf-8")
            lines = apply_directives(text, root=root, actor=args.actor,
                                     origin=args.origin)
            sys.stdout.write("\n".join(lines) + ("\n" if lines else ""))
            return 0
    except UnknownAccount as exc:
        sys.stderr.write(f"accounts_file.py: {exc}\n")
        return 3
    except (AccountsError, ValueError, OSError) as exc:
        sys.stderr.write(f"accounts_file.py: {exc}\n")
        return 2
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
