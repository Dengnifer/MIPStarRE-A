"""Atomic dispatcher account reservations and resume affinity."""

import argparse
import fcntl
import json
import os
from pathlib import Path
import re
import sys
import time


ACCOUNTS = ("primary", "second")


def choose_account(live: list[int], caps: list[int]) -> str:
    return "primary" if live[0] * caps[1] <= live[1] * caps[0] else "second"


def live_count(directory: Path) -> int:
    directory.mkdir(parents=True, exist_ok=True)
    count = 0
    for marker in directory.iterdir():
        if not marker.name.isdecimal() or int(marker.name) <= 0:
            continue
        try:
            os.kill(int(marker.name), 0)
        except ProcessLookupError:
            marker.unlink(missing_ok=True)
        except PermissionError:
            count += 1
        else:
            count += 1
    return count


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


def reserve(root: Path, requested: str, pid: int, wait: int, dry_run: bool) -> str:
    accounts = root / "accounts"
    accounts.mkdir(parents=True, exist_ok=True)
    deadline = time.monotonic() + wait
    while True:
        with (accounts / "router.lock").open("a") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            caps = []
            for account, default in zip(ACCOUNTS, (9, 10)):
                path = root / "watchdog" / f"max-codex-{account}"
                cap = int(path.read_text().strip()) if path.exists() else default
                if cap <= 0:
                    raise ValueError(f"{path}: cap must be positive")
                caps.append(cap)
            live = [live_count(accounts / account) for account in ACCOUNTS]
            selected = choose_account(live, caps) if requested == "auto" else requested
            index = ACCOUNTS.index(selected)
            if dry_run or live[index] < caps[index] or time.monotonic() >= deadline:
                if not dry_run:
                    (accounts / selected / str(pid)).touch()
                return selected
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
        selected = reserve(args.root, args.account, args.pid, args.wait, args.dry_run)
        model = os.environ.get("MIPSTARRE_CODEX_MODEL")
        if not model:
            for line in (homes[selected] / "config.toml").read_text().splitlines():
                if line.lstrip().startswith("["):
                    break
                match = re.fullmatch(r'''\s*model\s*=\s*(["'])([\w./:-]+)\1\s*(?:#.*)?''', line)
                if match:
                    model = match[2]
        if not isinstance(model, str) or not model.strip():
            raise ValueError("set MIPSTARRE_CODEX_MODEL or an account config model")
        print(selected)
        print(model)
    except (OSError, ValueError) as error:
        parser.exit(4, f"account routing: {error}\n")


if __name__ == "__main__":
    main()
