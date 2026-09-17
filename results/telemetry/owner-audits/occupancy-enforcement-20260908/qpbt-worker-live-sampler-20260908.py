#!/usr/bin/env python3
"""Read-only native-worker lifecycle/activity sampler; stdout contains metadata only."""
import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import time

ROOT = '01a076bc-f4ad-7813-805b-c8b4dac71a14'
HOME = Path.home() / '.cache/mipstarre-dev/codex-home-qpbt-relay1/sessions'


def stamp(value):
    try:
        return datetime.fromisoformat(value.replace('Z', '+00:00')).timestamp()
    except (AttributeError, TypeError, ValueError):
        return None


class Worker:
    def __init__(self, metadata):
        self.id = metadata.get('id')
        self.parent = metadata.get('parent_thread_id')
        if not self.parent:
            self.parent = metadata.get('source', {}).get('subagent', {}).get(
                'thread_spawn', {}).get('parent_thread_id') if isinstance(metadata.get('source'), dict) else None
        self.task = metadata.get('agent_path')
        self.born = stamp(metadata.get('timestamp'))
        self.turn = self.started = self.activity = self.latest = self.event = None
        self.live = False

    def consume(self, row):
        at = stamp(row.get('timestamp'))
        if at is None or self.born is None or at < self.born:
            return
        payload = row.get('payload', {})
        if not isinstance(payload, dict):
            return
        kind = payload.get('type')
        lifecycle = row.get('type') == 'event_msg' and kind in (
            'task_started', 'task_complete', 'turn_aborted')
        turn = payload.get('turn_id')
        if lifecycle:
            if kind == 'task_started':
                if self.started is not None and at < self.started:
                    return
                self.turn, self.started, self.live, self.activity = turn, at, bool(turn), None
            elif self.started is None or at < self.started or (turn and turn != self.turn):
                return
            else:
                self.live = False
            self.latest, self.event = at, kind
            return
        if not self.live or at < self.started or (turn and turn != self.turn):
            return
        active = kind in ('token_count', 'item_completed', 'function_call', 'function_call_output',
                          'output', 'agent_message', 'agent_reasoning') or (
                              kind == 'message' and payload.get('role') == 'assistant')
        if active:
            self.activity = max(self.activity or at, at)
            if self.latest is None or at >= self.latest:
                self.latest, self.event = at, kind

    def report(self, now, recent):
        age = lambda value: None if value is None else round(max(0, now - value), 1)
        if self.live:
            state = 'live_unknown' if self.activity is None else (
                'live_recent' if now - self.activity <= recent else 'live_stale')
        else:
            state = 'inactive' if self.event in ('task_complete', 'turn_aborted') else 'unknown'
        return dict(id=self.id, parent=self.parent, task=self.task, turn_id=self.turn, state=state,
                    live_unclosed=self.live, latest_event=self.event,
                    latest_event_age_s=age(self.latest), activity_age_s=age(self.activity),
                    turn_age_s=age(self.started))


class Sampler:
    def __init__(self, home, root):
        self.home, self.root, self.files = Path(home), root, {}

    def sample(self, now, recent):
        errors = 0
        for path in self.home.rglob('*.jsonl'):
            try:
                stat = path.stat()
                cache = self.files.get(path)
                if cache is None or cache['inode'] != stat.st_ino or stat.st_size < cache['offset']:
                    with path.open('rb') as handle:
                        line = handle.readline()
                        if not line.endswith(b'\n'):
                            continue
                        first = json.loads(line)
                        if first.get('type') != 'session_meta':
                            continue
                        cache = dict(inode=stat.st_ino, offset=handle.tell(), worker=Worker(first['payload']))
                    self.files[path] = cache
            except (OSError, ValueError, KeyError, TypeError):
                errors += 1
        selected = {self.root}
        while True:
            more = {v['worker'].id for v in self.files.values() if v['worker'].parent in selected}
            if more <= selected:
                break
            selected |= more
        reports = []
        for path, cache in self.files.items():
            worker = cache['worker']
            if worker.id == self.root or worker.id not in selected:
                continue
            try:
                with path.open('rb') as handle:
                    handle.seek(cache['offset'])
                    while True:
                        line = handle.readline()
                        if not line or not line.endswith(b'\n'):
                            break
                        cache['offset'] = handle.tell()
                        try:
                            worker.consume(json.loads(line))
                        except (ValueError, TypeError, AttributeError):
                            errors += 1
                reports.append(worker.report(now, recent))
            except OSError:
                errors += 1
        counts = {state: sum(w['state'] == state for w in reports) for state in (
            'live_recent', 'live_stale', 'live_unknown', 'inactive', 'unknown')}
        return dict(at=datetime.fromtimestamp(now, timezone.utc).isoformat(), root=self.root,
                    recent_window_s=recent, confirmed_active=counts['live_recent'],
                    live_unclosed=sum(w['live_unclosed'] for w in reports), counts=counts,
                    read_errors=errors, workers=sorted(reports, key=lambda w: w['id']))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--home', type=Path, default=HOME)
    parser.add_argument('--root', default=ROOT)
    parser.add_argument('--samples', type=int, default=1)
    parser.add_argument('--interval', type=float, default=30)
    parser.add_argument('--recent-seconds', type=float, default=180)
    parser.add_argument('--journal', type=Path)
    args = parser.parse_args()
    if args.samples < 1 or args.interval < 0 or args.recent_seconds <= 0:
        parser.error('Samples must be positive; interval nonnegative; recent window positive')
    if args.journal and not any(args.journal.resolve().is_relative_to(Path(p)) for p in ('/tmp', '/private/tmp')):
        parser.error('Journal must be under /tmp or /private/tmp')
    sampler = Sampler(args.home, args.root)
    for index in range(args.samples):
        line = json.dumps(sampler.sample(time.time(), args.recent_seconds), sort_keys=True)
        print(line, flush=True)
        if args.journal:
            with args.journal.open('a') as handle:
                handle.write(line + '\n')
        if index + 1 < args.samples:
            time.sleep(args.interval)


if __name__ == '__main__':
    main()
