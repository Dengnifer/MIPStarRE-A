"""Atomic dispatcher account reservations and resume affinity."""

import argparse
import fcntl
import json
import os
from pathlib import Path
import subprocess
import sys
import time


ACCOUNTS = ("primary", "second")


def choose_account(live: list[int], caps: list[int]) -> str:
    return "primary" if live[0] * caps[1] <= live[1] * caps[0] else "second"


def live_pids(directory: Path) -> set[int]:
    directory.mkdir(parents=True, exist_ok=True)
    live = set()
    for marker in directory.iterdir():
        if not marker.name.isdecimal() or int(marker.name) <= 0:
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


def host_processes(exclusions=()) -> tuple[dict[int, int], dict[int, tuple[str, bool]]]:
    """Require a host PID view; count same-user Codex executables, not Node wrappers."""
    namespace = [line.split()[1:] for line in Path('/proc/self/status').read_text().splitlines()
                 if line.startswith('NSpid:')]
    if Path('/proc/1/comm').read_text().strip() not in ('systemd', 'init') or namespace != [
            [str(os.getpid())]]:
        raise ValueError('host process visibility unavailable; no admission or stale cleanup')
    parents, candidates = {}, {}
    second_home = Path(os.environ.get('MIPSTARRE_CODEX_HOME_SECOND') or
                       Path.home() / '.cache/mipstarre-dev/codex-home-yxy')
    for process in Path('/proc').iterdir():
        if not process.name.isdecimal():
            continue
        try:
            if process.stat().st_uid != os.getuid():
                continue
            status = dict(line.split(':', 1) for line in
                          (process / 'status').read_text().splitlines() if ':' in line)
            pid = int(process.name)
            parents[pid] = int(status['PPid'])
            if status['Name'].strip() != 'codex':
                continue
            arguments = (process / 'cmdline').read_bytes().split(b'\0')
            if not arguments[0] or Path(os.fsdecode(arguments[0])).name != 'codex':
                continue
            environment = dict(entry.split(b'=', 1) for entry in
                               (process / 'environ').read_bytes().split(b'\0') if b'=' in entry)
            home = Path(os.fsdecode(environment.get(b'CODEX_HOME') or
                        environment.get(b'HOME', b'/unknown') + b'/.codex'))
            account = 'second' if home == second_home else 'primary'
            boundary = arguments.index(b'--') if b'--' in arguments else len(arguments)
            interactive = not any(command in arguments[:boundary] for command in
                                  (b'exec', b'e', b'review', b'app-server', b'mcp-server', b'exec-server'))
            if (interactive and home == Path.home() / '.codex' and exclusions and
                    os.readlink(process / 'cwd') in exclusions):
                continue
            candidates[pid] = (account, interactive)
        except FileNotFoundError:
            continue
    return parents, candidates


def occupancy(root: Path) -> tuple[list[int], list[int]]:
    path = root / 'watchdog/primary-excluded-interactive-cwds.json'
    exclusions = json.loads(path.read_text()) if path.exists() else []
    allowed = ('/home/drx/FV', '/home/drx/LDT-Lean-Paper', '/home/drx')
    if (not isinstance(exclusions, list) or any(item not in allowed for item in exclusions) or
            len(set(exclusions)) != len(exclusions)):
        raise ValueError('invalid owner-designated interactive CWD exclusions')
    parents, processes = host_processes(exclusions)
    reservations = [live_pids(root / 'accounts' / account) for account in ACCOUNTS]
    workers = [len(live) for live in reservations]
    interactive = [0, 0]
    matched = set()
    for pid, (account, is_interactive) in processes.items():
        index = ACCOUNTS.index(account)
        ancestor = pid
        seen = set()
        while ancestor not in reservations[index] and ancestor in parents and ancestor not in seen:
            seen.add(ancestor)
            ancestor = parents[ancestor]
        if ancestor in reservations[index] and ancestor not in matched:
            matched.add(ancestor)
        elif is_interactive:
            interactive[index] += 1
        else:
            workers[index] += 1
    interactive[0] = max(1, interactive[0])
    return workers, interactive


def resume_account(thread: str, registry: Path, homes: dict[str, Path]) -> str:
    matches = set()
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
                if row.get("thread_id") == thread and row.get("account") in ACCOUNTS:
                    matches.add(row["account"])
    for account, home in homes.items():
        for area in ("sessions", "archived_sessions"):
            if any((home / area).rglob(f"rollout-*{thread}.jsonl")):
                matches.add(account)
    if len(matches) != 1:
        raise ValueError(f"cannot establish unique resume account for {thread}")
    return matches.pop()


def session_rows(registry: Path) -> list[dict]:
    if not registry.exists():
        return []
    with registry.open() as handle:
        fcntl.flock(handle, fcntl.LOCK_SH)
        return [json.loads(line) for line in handle if line.strip()]


def resume_continuation(registry: Path, thread: str) -> dict:
    """Carry the original snapshot and completed segments, deduplicating status appends."""
    history = list({row['name']: row for row in session_rows(registry)
                    if row.get('thread_id') == thread}.values())
    for index in reversed(range(len(history))):
        if history[index].get('continuation'):
            prior = dict(history[index]['continuation'])
            prior['completed_wall_s'] = prior.get('completed_wall_s', 0) + sum(
                row['wall_s'] for row in history[index:])
            return prior
    return {}


def continuation(path: Path, registry: Path, worktree: Path, issue: str) -> dict:
    """Validate an operator checkpoint handoff without changing the old thread or budget."""
    request = json.loads(path.read_text())
    rows = session_rows(registry)
    previous = next(row for row in reversed(rows) if row.get('name') == request['previous_session'])
    if (previous.get('status') not in ('done', 'failed', 'archived') or
            previous.get('account') not in ACCOUNTS or not previous.get('thread_id') or
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


def reserve(root: Path, requested: str, pid: int, wait: int, dry_run: bool) -> str:
    accounts = root / "accounts"
    accounts.mkdir(parents=True, exist_ok=True)
    deadline = time.monotonic() + wait
    while True:
        with (accounts / "router.lock").open("a") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            mode_path = root / 'watchdog/account-mode'
            mode = mode_path.read_text().strip() if mode_path.exists() else 'primary'
            if mode not in ('primary', 'both'):
                raise ValueError(f'{mode_path}: expected primary or both')
            if mode == 'primary' and requested == 'second':
                raise ValueError('second account disabled; cross-account resume is unsupported; '
                                 'use --continue-from with a checkpoint in a fresh primary session')
            preserved_path = root / 'watchdog/account-mode-both-preserved.json'
            preserved = (json.loads(preserved_path.read_text())
                         if mode == 'both' and preserved_path.exists() else {})
            caps = []
            for account, default in zip(ACCOUNTS, (11, 9)):
                path = root / "watchdog" / f"max-codex-{account}"
                cap = int(preserved.get(account, path.read_text().strip()
                          if path.exists() else default))
                if cap < 0:
                    raise ValueError(f"{path}: cap must be nonnegative")
                caps.append(cap)
            live, interactive = occupancy(root)
            external_path = root / 'watchdog/primary-external-reserved'
            external = int(external_path.read_text()) if external_path.exists() else 0
            if external < 0:
                raise ValueError('primary-external-reserved must be nonnegative')
            interactive[0] += external
            caps[0] = min(caps[0], max(0, 12 - interactive[0]))
            caps[1] = max(0, caps[1] - interactive[1]) if mode == 'both' else 0
            total_path = root / 'watchdog/max-codex'
            total = int(preserved.get('max_codex', total_path.read_text().strip()
                        if total_path.exists() else sum(caps)))
            available = [index for index, account in enumerate(ACCOUNTS)
                         if live[index] < caps[index] and requested in ('auto', account)]
            if available and sum(live) < total:
                index = min(available, key=lambda index: live[index] / caps[index])
                selected = ACCOUNTS[index]
                if not dry_run:
                    (accounts / selected / str(pid)).touch()
                return selected
            if dry_run or time.monotonic() >= deadline:
                raise ValueError('account capacity exhausted; no reservation made')
        time.sleep(min(20, max(0, deadline - time.monotonic())))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", type=Path)
    parser.add_argument("account", choices=("auto", *ACCOUNTS))
    parser.add_argument("pid", type=int)
    parser.add_argument("wait", type=int)
    parser.add_argument("registry", type=Path)
    parser.add_argument("--resume")
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()
    homes = {"primary": Path.home() / ".codex", "second": Path(os.environ.get(
        "MIPSTARRE_CODEX_HOME_SECOND") or Path.home() / ".cache/mipstarre-dev/codex-home-yxy")}
    try:
        if args.resume:
            affinity = resume_account(args.resume, args.registry, homes)
            if args.account not in ("auto", affinity):
                raise ValueError(f"resume belongs to {affinity}, not {args.account}")
            args.account = affinity
        model = os.environ.get('MIPSTARRE_CODEX_MODEL') or 'gpt-6-astra'
        if model != 'gpt-6-astra':
            raise ValueError('owner policy requires gpt-6-astra for every role')
        selected = reserve(args.root, args.account, args.pid, args.wait, args.dry_run)
        print(selected)
        print(model)
    except (OSError, ValueError) as error:
        parser.exit(4, f"account routing: {error}\n")


if __name__ == "__main__":
    main()
