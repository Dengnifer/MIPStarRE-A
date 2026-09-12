"""Atomic dispatcher account reservations and resume affinity.

Three admission inputs are additive and fail open to the historical behaviour:
``watchdog/accounts.json`` (the owner's live list of keys and their ceilings),
``watchdog/capacity/health-<account>.json`` (a ``down`` endpoint is cap 0) and
``watchdog/drain`` (a pause releases queued dispatches with `DRAIN_EXIT`).
Absent files reproduce the previous behaviour exactly, and none of them can
widen capacity — they only turn a waiting reservation into a clean refusal.

**Any number of named accounts.**  The account set is read per call from the
live accounts file, and otherwise from the two historical names plus whatever
extra name has a cap file, so a third key added with ``accounts.sh add`` is
routable at the next reservation with nothing restarted and no code change.
``primary`` and ``second`` are ordinary entries of that list, not special cases.
"""

import argparse
import fcntl
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))

#: The same class `accounts_file.NAME_RE` enforces when the owner adds a key.
_NAME_RE = re.compile(r"^[a-z0-9][a-z0-9_-]{0,31}$")

#: The two names every historical brief, cap file and session row uses.  They are
#: the fallback when nothing on disk says otherwise — never a restriction.
DEFAULT_ACCOUNTS = ("primary", "second")

#: Kept as the module constant older callers import, and deliberately NOT
#: computed from disk: a constant whose value depends on a file read at import
#: time is unpredictable in a test and stale in a long-lived process.  Every
#: admission decision below calls `account_names(root)` per call instead, so a
#: file the owner edits mid-run is honoured with nothing reimported, and the
#: in-tree callers (`lane.sh`, `daemon-scan.py`, `ready_report.py`) do the same.
ACCOUNTS = DEFAULT_ACCOUNTS

#: Exit status of a reservation released by an operator drain.  Distinct from
#: the exit 4 every other routing failure uses, so a caller can tell "the run is
#: pausing, come back later" from "this request is wrong".
DRAIN_EXIT = 6


def _cache_root() -> Path:
    return Path(os.environ.get("MIPSTARRE_CACHE_ROOT",
                               "~/.cache/mipstarre-dev")).expanduser()


def account_names(root: Path | None = None) -> tuple[str, ...]:
    """Every routable account name, newest source first.

    1. ``watchdog/accounts.json`` — the owner's live file, which is the only
       place a key may be added or retired during a run.  It is authoritative in
       full: an account it does not list is not routable.
    2. ``DEFAULT_ACCOUNTS`` plus any extra name that has a
       ``watchdog/max-codex-<name>`` file — so a host with no accounts file yet
       routes exactly as it did before, including the invariant that a
       historical name with no cap file is cap 0 rather than absent.

    An unreadable or invalid accounts file falls through to (2): admission must
    never stop because the owner mistyped a field, and the capacity controller
    is the component that reports that error loudly.
    """
    base = root or _cache_root()
    try:
        import accounts_file  # noqa: PLC0415 - same directory, optional
        names = tuple(entry["name"] for entry in accounts_file.load(base) or ())
        if names:
            return names
    except Exception:  # noqa: BLE001 - a bad file must not stop every dispatch
        pass
    watchdog = base / "watchdog"
    found = sorted(
        path.name[len("max-codex-"):] for path in watchdog.glob("max-codex-*")
        if path.is_file() and path.name != "max-codex")
    return DEFAULT_ACCOUNTS + tuple(name for name in found
                                    if name not in DEFAULT_ACCOUNTS)


def account_homes(root: Path | None = None) -> dict[str, Path]:
    """``name -> CODEX_HOME`` from the live file, with the historical defaults.

    The homes are resume affinity's evidence (a rollout file lives under the home
    that produced it), so an account the file names must contribute its home even
    when the two historical entries are also present.
    """
    base = root or _cache_root()
    homes: dict[str, Path] = {}
    try:
        import accounts_file  # noqa: PLC0415 - same directory, optional
        for entry in accounts_file.load(base) or ():
            homes[entry["name"]] = Path(entry["codex_home"]).expanduser()
    except Exception:  # noqa: BLE001 - fall back to the historical pair
        homes = {}
    homes.setdefault("primary", Path.home() / ".codex")
    homes.setdefault("second", Path(os.environ.get("MIPSTARRE_CODEX_HOME_SECOND")
                                    or Path.home() / ".cache/mipstarre-dev/codex-home-yxy"))
    if os.environ.get("MIPSTARRE_CODEX_HOME_SECOND"):
        homes["second"] = Path(os.environ["MIPSTARRE_CODEX_HOME_SECOND"]).expanduser()
    return homes


class DrainRequested(Exception):
    """``watchdog/drain`` appeared while this dispatch was queued.

    The pause path touches that file, and a queued dispatch must then release
    itself: on 2026-09-12 forty-nine waiters sat behind twelve workers and the
    pause could only clear them by killing the processes, which threw away the
    dispatch requests with them.
    """


def choose_account(live: list[int], caps: list[int],
                   names: tuple[str, ...] = DEFAULT_ACCOUNTS) -> str:
    """The account with the most headroom, as a fraction of its own cap.

    The rule is unchanged for two accounts — ``live[0]*caps[1] <= live[1]*caps[0]``
    is exactly "the first account's occupancy is no higher" — and generalizes to
    N by comparing ``live/cap`` as a fraction, with ties going to the earlier
    entry so a two-account file keeps preferring ``primary``.  A zero cap is
    never chosen: `reserve` has already filtered it out, and treating it as
    infinitely free is how a dead endpoint attracted every dispatch.
    """
    best, best_key = names[0], None
    for index, name in enumerate(names):
        cap = caps[index]
        if cap <= 0:
            continue
        key = (live[index] * 1.0 / cap, index)
        if best_key is None or key < best_key:
            best, best_key = name, key
    return best


def health_state(root: Path, account: str) -> str:
    """Endpoint health as ``capacity_controller.py`` last recorded it.

    Absent, unreadable or unrecognized is ``up``: with no controller running the
    router behaves exactly as it did before this field existed, and the cap
    files alone govern admission.
    """
    path = root / "watchdog" / "capacity" / f"health-{account}.json"
    try:
        document = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return "up"
    state = document.get("state") if isinstance(document, dict) else None
    return state if state in ("up", "degraded", "down") else "up"


def disabled_accounts(root: Path) -> set[str]:
    """Names the owner's live file marks ``enabled: false``, or has dropped.

    Belt and braces with the capacity controller, which writes cap 0 for such an
    account at its next tick: between the owner's edit and that tick — up to 60
    seconds — the cap file still holds the old number, and a dispatch admitted in
    that window runs on a key the owner has just taken away.  Reading the file
    here closes the window.  It can only ever narrow admission.
    """
    try:
        import accounts_file  # noqa: PLC0415 - same directory, optional
        entries = accounts_file.load(root)
    except Exception:  # noqa: BLE001 - an unreadable file changes nothing
        return set()
    if entries is None:
        return set()
    return {entry["name"] for entry in entries if not entry["enabled"]}


def effective_caps(root: Path, names: tuple[str, ...] | None = None) -> list[int]:
    """Per-account caps, with a dead or disabled endpoint forced to zero.

    Without the health part the router *prefers* the dead account:
    `choose_account` picks the lower live/cap ratio, and an endpoint answering
    503 keeps freeing slots as its sessions die, so every new dispatch is routed
    into the outage.  That is how one hour of relay-us7 503s cost 69 sessions on
    2026-09-12.  Forcing the cap to zero only ever narrows admission; it can
    never widen it.
    """
    accounts = names if names is not None else account_names(root)
    disabled = disabled_accounts(root)
    caps = []
    for account in accounts:
        path = root / 'watchdog' / f'max-codex-{account}'
        cap = int(path.read_text().strip()) if path.exists() else 0
        if cap < 0:
            raise ValueError(f'{path}: cap must be nonnegative')
        if account in disabled or health_state(root, account) == "down":
            cap = 0
        caps.append(cap)
    return caps


def live_pids(directory: Path) -> set[int]:
    directory.mkdir(parents=True, exist_ok=True)
    live = set()
    for marker in directory.iterdir():
        if not marker.name.isdecimal() or int(marker.name) <= 0 or not marker.is_file():
            continue
        try:
            os.kill(int(marker.name), 0)
        except ProcessLookupError:
            marker.unlink(missing_ok=True)
        except PermissionError:
            live.add(int(marker.name))
        else:
            live.add(int(marker.name))
    return live


def session_rows(registry: Path) -> list[dict]:
    """Share locked, malformed-row-tolerant history without discarding object metadata."""
    rows = []
    if registry.exists():
        with registry.open(encoding="utf-8", errors="replace") as handle:
            fcntl.flock(handle, fcntl.LOCK_SH)
            for number, line in enumerate(handle, 1):
                if not line.strip():
                    continue
                try:
                    row = json.loads(line)
                except json.JSONDecodeError:
                    row = None
                if not isinstance(row, dict):
                    print(f"account routing: {registry}:{number}: "
                          "skipping malformed registry record", file=sys.stderr)
                    continue
                rows.append(row)
    return rows


def is_account_name(value) -> bool:
    """A syntactically valid account name.

    Affinity and continuation are judged on the *recorded* name, not on today's
    account list: a thread started on a key the owner has since retired still
    belongs to that key, and the reservation for it will simply find no capacity.
    Reading the historical row as "not an account" instead would silently turn a
    resume into a fresh thread.
    """
    return isinstance(value, str) and bool(_NAME_RE.match(value))


def resume_account(thread: str, registry: Path, homes: dict[str, Path]) -> str:
    matches = {row['account'] for row in session_rows(registry)
               if row.get('thread_id') == thread and is_account_name(row.get('account'))}
    for account, home in homes.items():
        for area in ("sessions", "archived_sessions"):
            if any((home / area).rglob(f"rollout-*{thread}.jsonl")):
                matches.add(account)
    if len(matches) != 1:
        raise ValueError(f"cannot establish unique resume account for {thread}")
    return matches.pop()


def resume_continuation(registry: Path, thread: str) -> dict:
    """Carry the original snapshot and completed segments, deduplicating status appends."""
    history = {}
    for row in session_rows(registry):
        if row.get('thread_id') != thread:
            continue
        if not row.get('name'):
            # Legacy affinity rows have no session identity for charge deduplication.
            if row.get('continuation', {}) != {}:
                raise ValueError('invalid continuation metadata on unnamed registry record')
            continue
        history[row['name']] = row
    prior = {}
    for row in history.values():
        metadata = row.get('continuation', {})
        if not isinstance(metadata, dict) or (metadata and (
                not metadata.get('budget_file') or not isinstance(metadata.get('budget'), dict) or
                not {'anchor', 'attempt_limit', 'attempts', 'working_seconds', 'sessions'} <=
                metadata['budget'].keys())):
            raise ValueError('invalid continuation metadata')
        if metadata:
            prior = dict(metadata)
        if prior:
            prior['completed_wall_s'] = prior.get('completed_wall_s', 0) + row['wall_s']
    return prior


def resume_model(thread: str, registry: Path, homes: dict[str, Path]) -> str:
    """Require observed model affinity; a new default cannot relabel an old thread."""
    observed = [row.get('effective_model') for row in session_rows(registry)
                if row.get('thread_id') == thread and row.get('effective_model')]
    for home in homes.values():
        for area in ('sessions', 'archived_sessions'):
            for rollout in (home / area).rglob(f'rollout-*{thread}.jsonl'):
                for row in session_rows(rollout):
                    if row.get('type') == 'turn_context' and row.get('payload', {}).get('model'):
                        observed.append(row['payload']['model'])
    if not observed or len(set(observed)) != 1:
        raise ValueError('resume model is unknown or mixed; use a fresh linked assignment')
    return observed[0]


def continuation(path: Path, registry: Path, worktree: Path, issue: str) -> dict:
    """Validate an operator checkpoint handoff without changing the old thread or budget."""
    request = json.loads(path.read_text())
    rows = session_rows(registry)
    previous = next(row for row in reversed(rows) if row.get('name') == request['previous_session'])
    if (previous.get('status') not in ('done', 'failed', 'archived') or
            not is_account_name(previous.get('account')) or not previous.get('thread_id') or
            str(previous.get('issue')) != issue):
        raise ValueError('continuation requires a terminal, same-issue predecessor with affinity')
    checkpoint = subprocess.check_output(['git', '-C', str(worktree), 'rev-parse', '--verify',
        '--end-of-options', request['checkpoint'] + '^{commit}'], text=True).strip()
    subprocess.run(['git', '-C', str(worktree), 'merge-base', '--is-ancestor',
                    checkpoint, 'HEAD'], check=True, capture_output=True)
    budget_path = Path(request['budget_file']).resolve(strict=True)
    budget = json.loads(budget_path.read_text())
    if (not budget['anchor'] or previous['name'] not in budget['sessions'] or
            not 0 < budget['attempts'] < budget['attempt_limit'] or
            budget['working_seconds'] < previous.get('wall_s', 0)):
        raise ValueError('continuation requires the shared, charged, unexhausted budget')
    prior = resume_continuation(registry, previous['thread_id'])
    if prior and (prior['budget_file'] != str(budget_path) or
                  prior['budget']['anchor'] != budget['anchor'] or
                  prior['budget']['attempt_limit'] != budget['attempt_limit'] or
                  prior['budget']['attempts'] >= budget['attempts'] or
                  prior['budget']['working_seconds'] + prior['completed_wall_s'] >
                  budget['working_seconds']):
        raise ValueError('continuation must retain its original budget and accumulated charges')
    return dict(previous_session=previous['name'], previous_thread_id=previous['thread_id'],
                previous_account=previous['account'], checkpoint=checkpoint,
                budget_file=str(budget_path), budget=budget)


def reserve(root: Path, requested: str, pid: int, wait: int, dry_run: bool = False) -> str:
    """Reserve one worker slot under the lock shared by all dispatchers.

    ``watchdog/drain`` is checked on every poll iteration, before the lock, and
    raises `DrainRequested` so a queued dispatch releases itself during a pause
    instead of being killed.  Absent file, absent health file: unchanged
    behaviour in every respect.
    """
    if (requested != 'auto' and not is_account_name(requested)) or pid <= 0 or wait < 0:
        raise ValueError('expected a valid account, positive pid and nonnegative wait')
    accounts = root / "accounts"
    accounts.mkdir(parents=True, exist_ok=True)
    deadline = time.monotonic() + wait
    while True:
        if (root / "watchdog" / "drain").exists():
            raise DrainRequested('drain in progress; no reservation made')
        with (accounts / "router.lock").open("a") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            # Re-read per iteration, inside the lock: a waiter queued for half an
            # hour must see the key the owner added, the ceiling they raised and
            # the account they disabled, without being restarted.
            names = account_names(root)
            if requested != 'auto' and requested not in names:
                raise ValueError(
                    f'{requested!r} is not one of the configured accounts '
                    f'({", ".join(names)}); add it with owner-tools/accounts.sh add')
            caps = effective_caps(root, names)
            live = [len(live_pids(accounts / account)) for account in names]
            free = [index for index, account in enumerate(names)
                    if live[index] < caps[index] and requested in ('auto', account)]
            if free:
                # Only the accounts with a free slot compete, exactly as the
                # two-account form did: a full account is not a candidate.
                selected = (names[free[0]] if len(free) == 1 else choose_account(
                    [live[index] for index in free], [caps[index] for index in free],
                    tuple(names[index] for index in free)))
                if not dry_run:
                    (accounts / selected / str(pid)).touch()
                return selected
            remaining = deadline - time.monotonic()
            if dry_run or remaining <= 0:
                raise ValueError('account capacity exhausted; no reservation made')
        time.sleep(min(10, remaining))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("reserve",))
    parser.add_argument("root", type=Path)
    # Not `choices=`: the account set is on disk, not in this file, and a name
    # the owner added minutes ago must be accepted.  `reserve` validates it
    # against the live list and names the alternatives when it does not match.
    parser.add_argument("account")
    parser.add_argument("pid", type=int)
    parser.add_argument("wait", type=int)
    parser.add_argument("registry", type=Path, nargs="?",
                        help="dispatch history; when supplied, also print the selected model")
    parser.add_argument("--resume")
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()
    homes = account_homes(args.root)
    try:
        if args.resume and args.registry is None:
            raise ValueError("resume requires a session registry")
        if args.resume:
            affinity = resume_account(args.resume, args.registry, homes)
            if args.account not in ("auto", affinity):
                raise ValueError(f"resume belongs to {affinity}, not {args.account}")
            args.account = affinity
        if args.registry is None:
            print(reserve(args.root, args.account, args.pid, args.wait, args.dry_run))
            return
        from model_policy import load_policy, select_model
        model = select_model(os.environ.get('MIPSTARRE_DISPATCH_ROLE', 'orc'),
            os.environ.get('MIPSTARRE_JOB_CLASS', 'general'),
            os.environ.get('MIPSTARRE_CODEX_MODEL') or 'auto',
            os.environ.get('MIPSTARRE_REQUESTED_EFFORT', 'ultra'),
            os.environ.get('MIPSTARRE_HARDNESS_REASON') or None)['model']
        if args.resume and load_policy()['schema_version'] == 2 and model != resume_model(
                args.resume, args.registry, homes):
            raise ValueError('resume cannot switch model; create a fresh linked assignment')
        selected = reserve(args.root, args.account, args.pid, args.wait, args.dry_run)
        print(selected)
        print(model)
    except DrainRequested as error:
        parser.exit(DRAIN_EXIT, f"account routing: {error}\n")
    except (OSError, ValueError) as error:
        parser.exit(4, f"account routing: {error}\n")


if __name__ == "__main__":
    main()
