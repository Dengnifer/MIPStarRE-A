#!/usr/bin/env python3
"""Opt-in, main-selected one-shot admissions; never select tasks or repair launches."""
from __future__ import annotations
import argparse
from contextlib import contextmanager
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
import uuid
import account_router as router
import gh_common
from wf_util import LayerError, atomic_write, utcnow
ROLES = {'prover', 'simplifier', 'blueprint', 'splitter', 'scout'}
REFUSAL = re.compile(r'concurren|too many|\b(?:429|502|503)\b|rate.limit|quota|'
                     r'capacity exhausted|service.unavailable', re.I)
RETRY = re.compile(r'reconnect|retry|retrying', re.I)
DIAGNOSTIC = re.compile(r'^(?:\d{4}-\d\d-\d\dT\S+\s+)?(?:ERROR[: ]|'
                        r'(?:dispatch|review)\.sh: (?:error|warning):|Reconnecting \d+/\d+)', re.I)
SHA = re.compile(r'[0-9a-f]{40}')
def load(path: Path, default=None):
    return json.loads(path.read_text()) if path.exists() else default
def save(path: Path, value) -> None:
    atomic_write(path, json.dumps(value, indent=2, sort_keys=True) + '\n')
@contextmanager
def locked(path: Path):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('a') as handle:
        fcntl.flock(handle, fcntl.LOCK_EX)
        yield
def git(worktree: Path, *args: str) -> str:
    result = subprocess.run(['git', '-C', str(worktree), *args], check=True,
                            capture_output=True, text=True, timeout=30)
    return result.stdout.strip()
def fingerprint(packet: dict) -> str:
    return hashlib.sha256(json.dumps({key: value for key, value in packet.items()
                                     if key != 'id'}, sort_keys=True).encode()).hexdigest()
def configuration(path: Path) -> dict:
    """Accept only typed packets, not commands, environments, resumes, or discovery rules."""
    config = load(path, {'version': 1, 'enabled': False, 'packets': []})
    if (not isinstance(config, dict) or set(config) != {'version', 'enabled', 'packets'} or
            config['version'] != 1 or type(config['enabled']) is not bool or
            not isinstance(config['packets'], list)):
        raise ValueError('queue.json requires version=1, enabled boolean, and packets list')
    identifiers = set()
    common = {'id', 'kind', 'issue', 'worktree', 'head', 'effort', 'parents'}
    for packet in config['packets']:
        if not isinstance(packet, dict): raise ValueError('packet must be an object')
        fields = ({'role', 'task_file', 'task_sha256'}
                  if packet.get('kind') == 'dispatch' else {'pr'})
        if set(packet) != common | fields or packet['kind'] not in ('dispatch', 'review'):
            raise ValueError('unknown or missing packet fields')
        if (not isinstance(packet['id'], str) or
                not re.fullmatch(r'[a-z0-9][a-z0-9-]{0,79}', packet['id']) or
                packet['id'] in identifiers):
            raise ValueError('packet ids must be unique lowercase names')
        identifiers.add(packet['id'])
        if (type(packet['issue']) is not int or packet['issue'] <= 0 or
                packet['effort'] != 'ultra' or
                not isinstance(packet['head'], str) or not SHA.fullmatch(packet['head']) or
                not isinstance(packet['worktree'], str) or
                not Path(packet['worktree']).is_absolute() or
                not isinstance(packet['parents'], list)):
            raise ValueError('invalid issue, effort, head, worktree, or parents')
        for parent in packet['parents']:
            if (not isinstance(parent, dict) or set(parent) != {'issue', 'pr', 'merge_sha'} or
                    any(type(parent[key]) is not int or parent[key] <= 0
                        for key in ('issue', 'pr')) or not isinstance(parent['merge_sha'], str) or
                    not SHA.fullmatch(parent['merge_sha'])):
                raise ValueError('parents require issue, pr, and exact merge_sha')
        if packet['kind'] == 'dispatch':
            if (packet['role'] not in ROLES or not isinstance(packet['task_file'], str) or
                    not Path(packet['task_file']).is_absolute() or
                    not isinstance(packet['task_sha256'], str) or
                    not re.fullmatch(r'[0-9a-f]{64}', packet['task_sha256'])):
                raise ValueError('dispatch requires a permitted role and hash-bound task file')
        elif type(packet['pr']) is not int or packet['pr'] <= 0:
            raise ValueError('review requires a positive PR number')
    return config
def review_evidence(packet: dict, *, finished: bool = False) -> None:
    """Bind normal review to its selected head, complete evidence, and four-round cap."""
    pull = gh_common.pr_view(packet['pr'])
    if pull['state'] != 'open' or pull['head']['sha'] != packet['head']:
        raise ValueError('PR closed or selected review head moved')
    statuses = gh_common.latest_statuses(packet['head'])
    if statuses.get('local-ci/summary', {}).get('state') != 'success':
        raise ValueError('exact-head CI is not green')
    reviews = gh_common.pr_reviews(packet['pr'])
    marker = f"<!-- mipstarre-review pr={packet['pr']} head={packet['head']} -->"
    exact = [row for row in reviews if row.get('commit_id') == packet['head'] and
             marker in (row.get('body') or '')]
    summary = statuses.get('local-review/summary', {}).get('state')
    if finished:
        if not exact or summary not in ('success', 'failure'):
            raise ValueError('partial review publication; adoption required')
    elif exact or summary:
        raise ValueError('review evidence already exists; adopt, never repeat this head')
    rounds = {match.group(1) for row in reviews
              if '<!-- mipstarre-review-carried' not in (row.get('body') or '')
              for match in re.finditer(r'mipstarre-review pr=\d+ head=([0-9a-f]{40})',
                                       row.get('body') or '')}
    if not finished and len(rounds) >= 4:
        raise ValueError('four review rounds reached; main must handle disposition')
def packet_gate(packet: dict, primary: Path, root: Path) -> str:
    """Check source ancestry and worktree binding without creating or updating either."""
    worktree = Path(packet['worktree']).resolve(strict=True)
    if worktree == primary or git(worktree, 'rev-parse', 'HEAD') != packet['head']:
        raise ValueError('primary worktree or selected worktree head mismatch')
    common = Path(git(worktree, 'rev-parse', '--path-format=absolute', '--git-common-dir'))
    if common != primary / '.git' or git(worktree, 'status', '--porcelain'):
        raise ValueError('worktree is dirty or belongs to another repository')
    issue = gh_common.issue_view(packet['issue'])
    if issue['state'] != 'open': raise ValueError('selected issue is no longer open')
    blockers = gh_common.api(f"issues/{packet['issue']}/dependencies/blocked_by", paginate=True)
    parents = {parent['issue'] for parent in packet['parents']}
    if any(blocker['state'] != 'closed' or blocker['number'] not in parents
           for blocker in blockers):
        raise ValueError('issue prerequisites need explicit, actually merged parent bindings')
    for parent in packet['parents']:
        pull = gh_common.pr_view(parent['pr'])
        if (not pull.get('merged') or pull.get('merge_commit_sha') != parent['merge_sha'] or
                gh_common.issue_view(parent['issue'])['state'] != 'closed'):
            raise ValueError('parent merge is not confirmed by GitHub')
        git(worktree, 'merge-base', '--is-ancestor', parent['merge_sha'], packet['head'])
    if packet['kind'] == 'review':
        if os.environ.get('LOCAL_REVIEW_ENABLED') == 'false':
            raise ValueError('review kill switch is false')
        if (root / f"reviews/pr{packet['pr']}" / packet['head']).exists():
            raise ValueError('prior review runtime exists; adopt uncertain launches before review')
        review_evidence(packet)
        pull = gh_common.pr_view(packet['pr'])
        if git(worktree, 'symbolic-ref', '--short', 'HEAD') != pull['head']['ref']:
            raise ValueError('review worktree is not the selected PR branch')
        return ''
    task = Path(packet['task_file']).read_bytes()
    if (not task.strip() or len(task) > 60000 or
            hashlib.sha256(task).hexdigest() != packet['task_sha256']):
        raise ValueError('task file is empty, oversized, or changed since main selected it')
    return task.decode('utf-8')
def worktree_busy(packet: dict, root: Path, *, token: str | None = None) -> bool:
    worktree = str(Path(packet['worktree']).resolve())
    if any(ticket.get('worktree') == worktree for key, ticket in router.queue_tickets(root).items()
           if key != token):
        return True
    basename = re.sub(r'[^A-Za-z0-9._-]', '-', Path(worktree).name)
    checksum = subprocess.run(['cksum'], input=worktree, capture_output=True,
                              text=True, check=True).stdout.replace(' ', '').strip()[:12]
    lock = root / 'locks' / f'worktree-{basename}-{checksum}.lock'
    if lock.exists(): return True
    if packet['kind'] == 'review' and (root / f"locks/review-{packet['pr']}.lock").exists():
        return True
    _, processes = router.host_processes()
    return any(os.readlink(f'/proc/{pid}/cwd') == worktree for pid in processes)
def observe(path: Path, cursor: dict) -> dict:
    """Count completed event evidence separately from clients, retries, and refusals."""
    stat = path.stat()
    if cursor and (cursor['inode'] != stat.st_ino or stat.st_size < cursor['offset']):
        raise ValueError(f'evidence log replaced or truncated: {path}')
    result = dict(cursor) if cursor else dict(inode=stat.st_ino, offset=0, turns=0,
                                             items=0, retries=0, refusals=0)
    with path.open('rb') as handle:
        handle.seek(result['offset'])
        for _ in range(10000):
            line = handle.readline(1048576)
            if not line: break
            if not line.endswith(b'\n'):
                if len(line) == 1048576:
                    raise ValueError('oversized evidence event; admission held')
                break
            text = line.decode('utf-8', errors='replace')
            diagnostic = ''
            try:
                event = json.loads(text)
            except ValueError:
                event = {}
                if DIAGNOSTIC.match(text): diagnostic = text
            if isinstance(event, dict):
                result['turns'] += event.get('type') == 'turn.completed'
                result['items'] += event.get('type') == 'item.completed'
                if event.get('type') in ('error', 'turn.failed'):
                    diagnostic = json.dumps(event.get('error') or event.get('message', ''))
            result['retries'] += bool(RETRY.search(diagnostic))
            result['refusals'] += bool(REFUSAL.search(diagnostic))
            result['offset'] = handle.tell()
        if handle.read(1):
            raise ValueError('evidence backlog or partial event; wait before admitting')
    return result

class Supervisor:
    """A durable single-attempt state machine; failures are holds, not retry invitations."""
    def __init__(self, primary: Path, root: Path):
        self.primary, self.root = primary, root
        self.directory = root / 'useful-queue'
        self.state_path = self.directory / 'state.json'
        self.children = []
    def event(self, kind: str, **data) -> None:
        with (self.directory / 'events.jsonl').open('a') as handle:
            fcntl.flock(handle, fcntl.LOCK_EX)
            handle.write(json.dumps(dict(ts=utcnow(), event=kind, **data)) + '\n')
            handle.flush()
            os.fsync(handle.fileno())
    def hold(self, reason: str) -> None:
        atomic_write(self.directory / 'HOLD', reason + '\n')
        self.event('hold', reason=reason)
    def refresh(self, state: dict) -> None:
        self.children = [child for child in self.children if child.poll() is None]
        paths = list(self.directory.glob('*/launch.log'))
        paths += [path for path in (self.root / 'sessions').glob('*.jsonl')
                  if path.stat().st_mtime >= state['since']]
        for key in state['evidence'].keys() | set(map(str, paths)):
            previous = state['evidence'].get(key, {})
            state['evidence'][key] = observe(Path(key), previous)
            if state['evidence'][key]['refusals'] > previous.get('refusals', 0):
                self.hold(f'service refusal in {key}; main must assess recovery')
        for identifier, entry in state['packets'].items():
            if entry['status'] not in ('launching', 'running'): continue
            receipt = load(self.directory / identifier / 'receipt.json')
            if receipt is not None:
                if receipt.get('ok') is True and receipt.get('token') == entry['token']:
                    entry['status'] = 'done'
                    with locked(self.root / 'accounts/router.lock'):
                        tickets = router.queue_tickets(self.root)
                        tickets.pop(entry['token'], None)
                        router.write_queue_tickets(self.root, tickets)
                    self.event('done', packet=identifier, evidence=receipt)
                else:
                    entry['status'] = 'held'
                    self.hold(f'{identifier}: uncertain launch or publication; adopt receipt')
            else:
                try:
                    alive = router.process_identity(entry['pid']) == entry['start']
                except (OSError, KeyError): alive = False
                if not alive:
                    entry['status'] = 'held'
                    self.hold(f'{identifier}: launcher disappeared without receipt; '
                              'adopt, do not retry')
        known = {entry['token'] for entry in state['packets'].values()}
        if set(router.queue_tickets(self.root)) - known:
            self.hold('orphan reservation has no intent record; adoption required')
    def launch(self, packet: dict, task: str, state: dict) -> None:
        identifier, token = packet['id'], uuid.uuid4().hex
        launch_dir = self.directory / identifier
        launch_dir.mkdir()
        entry = dict(packet=packet, fingerprint=fingerprint(packet), token=token,
                     status='launching', attempts=1, pid=os.getpid(),
                     start=router.process_identity(os.getpid()))
        state['packets'][identifier] = entry
        save(self.state_path, state)
        save(launch_dir / 'launch.json', dict(packet=packet, task=task, token=token))
        tickets = router.queue_tickets(self.root)
        tickets[token] = dict(slots=2 if packet['kind'] == 'review' else 1,
                              pid=entry['pid'], start=entry['start'], claims=[],
                              worktree=str(Path(packet['worktree']).resolve()))
        router.write_queue_tickets(self.root, tickets)
        self.event('attempt', packet=identifier, token=token, slots=tickets[token]['slots'])
        with (launch_dir / 'launch.log').open('xb') as output:
            child = subprocess.Popen([sys.executable, str(Path(__file__).resolve()),
                                      '--execute', identifier], env=child_environment(self.root),
                                     stdin=subprocess.DEVNULL, stdout=output, stderr=output,
                                     start_new_session=True, close_fds=True)
        self.children.append(child)
        entry.update(pid=child.pid, start=router.process_identity(child.pid), status='running')
        tickets[token].update(pid=entry['pid'], start=entry['start'])
        router.write_queue_tickets(self.root, tickets)
        save(self.state_path, state)
    def tick(self, run: bool = False) -> dict:
        with locked(self.directory / 'controller.lock'):
            state = None
            report = dict(ts=utcnow(), status='idle', packets=[],
                          limitation=('Client occupancy and completed events '
                                      'are not server admission.'))
            try:
                state = load(self.state_path, dict(version=1, since=time.time(),
                                                  packets={}, evidence={}))
                if (not isinstance(state, dict) or state.get('version') != 1 or
                        not isinstance(state.get('packets'), dict) or
                        not isinstance(state.get('evidence'), dict)):
                    raise ValueError('invalid queue state; adoption required')
                self.refresh(state)
                config = configuration(self.directory / 'queue.json')
                enabled = run and config['enabled']
                if not enabled: report['status'] = 'disabled'
                for packet in config['packets']:
                    prior = state['packets'].get(packet['id'])
                    if prior:
                        if prior['fingerprint'] != fingerprint(packet):
                            raise ValueError('attempted packet changed; adoption required')
                        report['packets'].append(dict(id=packet['id'], status=prior['status']))
                        continue
                    if any(entry['fingerprint'] == fingerprint(packet)
                           for entry in state['packets'].values()):
                        raise ValueError('duplicate task under a new id; adoption required')
                    if not enabled:
                        report['packets'].append(dict(id=packet['id'], status='not-enabled'))
                        continue
                    if report['status'] == 'admitted':
                        report['packets'].append(dict(id=packet['id'], status='queued'))
                        continue
                    if (self.directory / 'STOP').exists() or (self.directory / 'HOLD').exists():
                        report['status'] = 'stopped'
                        break
                    try:
                        task = packet_gate(packet, self.primary, self.root)
                        with locked(self.root / 'accounts/router.lock'):
                            live, interactive = router.occupancy(self.root)
                            caps, total, mode = router.admission_limits(self.root, interactive)
                            slots = 2 if packet['kind'] == 'review' else 1
                            recovery_ceiling = min(caps[0], total)
                            if (mode != 'primary' or live[0] + slots > recovery_ceiling or
                                    sum(live) + sum(interactive) + slots > total):
                                raise ValueError('capacity: primary recovery ceiling '
                                                 f'{recovery_ceiling} or owner limit')
                            if worktree_busy(packet, self.root):
                                raise ValueError('worktree already occupied or reserved')
                            if any((self.directory / name).exists() for name in ('STOP', 'HOLD')):
                                raise ValueError('stop/hold appeared before reservation')
                            self.launch(packet, task, state)
                        report['status'] = 'admitted'
                        report['packets'].append(dict(id=packet['id'], status='running'))
                    except (OSError, ValueError, LayerError, subprocess.SubprocessError) as error:
                        if packet['id'] in state['packets']:
                            state['packets'][packet['id']]['status'] = 'held'
                            self.hold(f"{packet['id']}: {error}")
                        report['packets'].append(dict(id=packet['id'], status='blocked',
                                                      reason=str(error)))
                with locked(self.root / 'accounts/router.lock'):
                    live, interactive = router.occupancy(self.root)
                    caps, total, mode = router.admission_limits(self.root, interactive)
                    report['census'] = dict(workers_and_reservations=live, interactive=interactive,
                                            caps=caps, total=total, mode=mode,
                                            recovery_ceiling=min(caps[0], total),
                                            tickets=router.queue_tickets(self.root))
                    _, clients = router.host_processes()
                    report['census']['observed_clients_including_exempt'] = {
                        pid: dict(account=account, interactive=is_interactive)
                        for pid, (account, is_interactive) in clients.items()}
                if (self.directory / 'HOLD').exists() or (self.directory / 'STOP').exists():
                    report['status'] = 'stopped'
                elif report['status'] == 'idle' and report['packets']:
                    statuses = {row['status'] for row in report['packets']}
                    if 'blocked' in statuses or 'held' in statuses: report['status'] = 'blocked'
                    elif statuses & {'running', 'launching'}: report['status'] = 'active'
                if report['status'] == 'idle':
                    report['reason'] = 'No unattempted useful packets; main must select more work.'
                report['evidence'] = state['evidence']
            except (OSError, ValueError, KeyError, TypeError, LayerError,
                    subprocess.SubprocessError) as error:
                self.hold(str(error))
                report.update(status='held', reason=str(error))
            if state is not None: save(self.state_path, state)
            save(self.directory / 'census.json', report)
            self.event('census', report=report)
            return report
def child_environment(root: Path) -> dict:
    """Do not inherit routing, prompt-ref, resume, model, or automatic-fix overrides."""
    environment = {key: value for key, value in os.environ.items()
                   if key == 'MIPSTARRE_LAKE_ROOT' or
                   (not key.startswith('MIPSTARRE_') and key != 'CODEX_HOME')}
    environment.update(MIPSTARRE_CACHE_ROOT=str(root), MIPSTARRE_CODEX_ACCOUNT='primary',
                       MIPSTARRE_CODEX_MODEL='gpt-6-astra', MIPSTARRE_REVIEW_MODEL='gpt-6-astra',
                       MIPSTARRE_PROSE_MODEL='gpt-6-astra', MIPSTARRE_ACCOUNT_WAIT='0',
                       MIPSTARRE_REVIEW_LOCK_WAIT='0', MIPSTARRE_DISPATCH_LOCK_WAIT='0',
                       MIPSTARRE_SESSION=os.environ.get('MIPSTARRE_SESSION', 'main-useful-queue'),
                       LOCAL_AUTO_FIX_ENABLED='false')
    return environment
def execute(primary: Path, root: Path, identifier: str) -> int:
    """Run a frozen intent once; only a matching live reservation authorizes execution."""
    supervisor = Supervisor(primary, root)
    launch_dir = supervisor.directory / identifier
    with locked(supervisor.directory / 'controller.lock'):
        launch = load(launch_dir / 'launch.json')
        with locked(root / 'accounts/router.lock'):
            ticket = router.queue_tickets(root).get(launch['token'])
            if (not ticket or ticket['pid'] != os.getpid() or
                    ticket['start'] != router.process_identity(os.getpid()) or
                    (launch_dir / 'receipt.json').exists()):
                raise ValueError('execution has no matching live one-shot intent')
    packet = launch['packet']
    receipt = dict(token=launch['token'], ok=False, ts=utcnow())
    try:
        if (supervisor.directory / 'STOP').exists() or (supervisor.directory / 'HOLD').exists():
            raise ValueError('stopped before launch')
        task = packet_gate(packet, primary, root)
        if task != launch['task']: raise ValueError('selected task changed before execution')
        environment = child_environment(root)
        environment.update(MIPSTARRE_QUEUE_TICKET=launch['token'],
                           MIPSTARRE_QUEUE_EXPECTED_HEAD=packet['head'],
                           MIPSTARRE_REVIEW_EFFORT=packet['effort'])
        if packet['kind'] == 'review':
            command = [str(primary / 'local/bin/review.sh'), str(packet['pr'])]
        else:
            command = [str(primary / 'local/bin/dispatch.sh'), '--account', 'primary',
                       '--role', packet['role'], '--issue', str(packet['issue']),
                       '--worktree', packet['worktree'], '--effort', packet['effort'], '--',
                       task + '\nComplete this one-shot packet without dispatching other sessions. '
                       'Do not merge, resume proof budgets, or dispose of owner inbox items.']
        result = subprocess.run(command, env=environment, stdin=subprocess.DEVNULL)
        receipt['exit'] = result.returncode
        if receipt['exit'] != 0:
            raise ValueError('canonical tool failed; preserve launch evidence for adoption')
        if packet['kind'] == 'review':
            review_evidence(packet, finished=True)
            review_dir = root / f"reviews/pr{packet['pr']}" / packet['head']
            for path in review_dir.glob('*.rc'):
                if path.read_text().strip() != '0':
                    raise ValueError('review lane failed; adopt partial publication')
        else:
            log = (launch_dir / 'launch.log').read_text(errors='replace')
            names = re.findall(r'^name: ([a-z0-9-]+)$', log, re.M)
            rows = router.session_rows(primary / 'results/telemetry/sessions.jsonl')
            rows = [row for row in rows if names and row.get('name') == names[-1]]
            if not rows or not rows[-1].get('thread_id') or rows[-1].get('exit') != 0:
                raise ValueError('dispatch telemetry incomplete; adoption required')
            name = names[-1]
            published = primary / 'results/telemetry/sessions'
            if any(not (published / f'{name}{suffix}').is_file() or
                   not (published / f'{name}{suffix}').stat().st_size
                   for suffix in ('.jsonl', '.last.md')):
                raise ValueError('dispatch capture publication incomplete; adoption required')
            receipt['session'] = name
        receipt['ok'] = True
    except (OSError, ValueError, KeyError, LayerError, subprocess.SubprocessError) as error:
        receipt['reason'] = str(error)
        supervisor.hold(f'{identifier}: {error}')
    save(launch_dir / 'receipt.json', receipt)
    return 0 if receipt['ok'] else 1
def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true',
                        help='admit only if queue.json also enables it')
    parser.add_argument('--watch', type=int, default=0, metavar='SECONDS')
    parser.add_argument('--execute', help=argparse.SUPPRESS)
    args = parser.parse_args(argv)
    os.umask(0o077)
    source = Path(__file__).resolve().parents[2]
    primary = Path(git(source, 'rev-parse', '--path-format=absolute', '--git-common-dir')).parent
    root = Path(os.environ.get('MIPSTARRE_CACHE_ROOT', '~/.cache/mipstarre-dev'))
    root = root.expanduser().resolve()
    if root.is_relative_to(primary) or args.watch < 0 or (args.watch and args.watch < 5):
        parser.error('runtime must be outside the repository; watch interval must be >=5 seconds')
    if (args.run or args.execute) and (source != primary or
            git(primary, 'symbolic-ref', '--short', 'HEAD') != 'main' or
            git(primary, 'status', '--porcelain',
            '--', 'local/bin/useful_queue.py', 'local/bin/account_router.py',
            'local/bin/review.sh', 'local/bin/dispatch.sh')):
        parser.error('run only reviewed, installed primary-checkout source; '
                     'worktree execution refused')
    if args.execute:
        if not re.fullmatch(r'[a-z0-9][a-z0-9-]{0,79}', args.execute):
            parser.error('invalid packet id')
        return execute(primary, root, args.execute)
    supervisor = Supervisor(primary, root)
    while True:
        print(json.dumps(supervisor.tick(args.run), sort_keys=True), flush=True)
        if not args.watch: return 0
        time.sleep(args.watch)
if __name__ == '__main__': raise SystemExit(main())
