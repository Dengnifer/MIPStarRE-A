"""Bridge independent native reviews into review.sh's unchanged exact-head publisher."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time
import uuid

from account_router import native_leases, native_process
from telemetry import native_rollout, now_ts, parse_ts, record_native
from wf_util import atomic_write


def canonical_thread(value: object, field: str) -> str:
    """Validate UUID identity fields before using them as mailbox selectors."""
    if not isinstance(value, str):
        raise ValueError(f'{field} must be a canonical UUID')
    try:
        parsed = str(uuid.UUID(value))
    except (ValueError, AttributeError):
        raise ValueError(f'{field} must be a canonical UUID') from None
    if parsed != value:
        raise ValueError(f'{field} must be a canonical UUID')
    return value


def verify_root(cache: Path, thread: str) -> dict:
    canonical_thread(thread, 'native root thread')
    lease = native_leases(cache).get(thread)
    if not lease:
        raise ValueError('native review requires a live, capacity-leased root')
    observed = native_process(thread, lease['pid'], lease['slots'])
    if any(observed[key] != value for key, value in lease.items()):
        raise ValueError('native review root lease identity changed')
    return observed


def completed_review(request: dict, thread: str) -> tuple[dict, Path]:
    """Re-derive the review from the canonical live root's child rollout."""
    canonical_thread(thread, 'reviewer thread')
    root_thread = canonical_thread(request['root_thread_id'], 'native root thread')
    authors = request.get('authors')
    if (not isinstance(authors, list) or
            any(canonical_thread(author, 'review author') != author for author in authors)):
        raise ValueError('review authors must be canonical UUIDs')
    root = verify_root(Path(request['cache']), root_thread)
    if root_thread not in authors or request.get('key_label') != root['key_label']:
        raise ValueError('native review request identity does not match its leased root')
    matches = list((root['home'] / 'sessions').glob(f'*/*/*/rollout-*{thread}.jsonl'))
    if len(matches) != 1:
        raise ValueError('a unique canonical child rollout is required')
    rollout = matches[0]
    child = native_rollout(rollout, thread)
    assigned, turn = parse_ts(child['assigned']), parse_ts(child['turn_start'])
    ended = parse_ts(child['end'])
    created = parse_ts(request['created'])
    if (thread in authors or child['parent_thread_id'] != root_thread or not assigned or
            not turn or not ended or not created or min(assigned, turn) <= created or
            ended < max(assigned, turn) or not child['final']):
        raise ValueError('review requires a fresh independently assigned native turn')
    binding = f"Native review binding: {request['nonce']} {request['head']} {request['prompt_sha256']}"
    if binding not in child['final'].splitlines():
        raise ValueError('completed child review lacks its request/head/prompt binding')
    prompt = Path(request['prompt']).read_bytes()
    if hashlib.sha256(prompt).hexdigest() != request['prompt_sha256']:
        raise ValueError('trusted review request changed')
    head = subprocess.check_output(['git', '-C', request['worktree'], 'rev-parse', 'HEAD'],
                                   text=True).strip()
    if head != request['head']:
        raise ValueError('reviewed worktree head changed')
    if subprocess.check_output(['git', '-C', request['worktree'], 'status', '--porcelain',
                                '--untracked-files=all'], text=True).strip():
        raise ValueError('reviewed worktree is not clean')
    return child, rollout


def complete(request_path: Path, thread: str) -> None:
    """Signal child completion; the waiting publisher independently rechecks the rollout."""
    request = json.loads(request_path.read_text())
    completed_review(request, thread)
    atomic_write(request_path.with_suffix('.response.json'), json.dumps(dict(
        nonce=request['nonce'], thread_id=thread)) + '\n')


def accept_response(request: dict, response: dict, out: Path) -> None:
    if not isinstance(response, dict):
        raise ValueError('native review response must be an object')
    if response.get('nonce') != request['nonce']:
        raise ValueError('native review response identity mismatch')
    thread = canonical_thread(response.get('thread_id'), 'reviewer thread')
    child, rollout = completed_review(request, thread)
    record_native(argparse.Namespace(rollout=rollout, thread_id=thread,
        root_thread_id=request['root_thread_id'], repo_root=Path(request['repo']),
        name='reviewer-native-' + thread, role='reviewer', issue='pr' + request['pr'],
        pr=request['pr'], key_label=request['key_label'], worktree=Path(request['worktree']),
        status='done'))
    atomic_write(out, child['final'])


def request_review(args: argparse.Namespace) -> None:
    root = os.environ['MIPSTARRE_NATIVE_REVIEW_ROOT']
    authors = [author.strip() for author in
               os.environ.get('MIPSTARRE_NATIVE_REVIEW_AUTHORS', '').split(',')]
    if not authors or any(not author for author in authors):
        raise ValueError('native review author thread IDs are required')
    authors = [canonical_thread(author, 'review author') for author in authors]
    lease = verify_root(args.cache, root)
    nonce = uuid.uuid4().hex
    directory = args.cache / 'native-reviews'
    directory.mkdir(parents=True, exist_ok=True)
    path = directory / (nonce + '.json')
    prompt = args.prompt.read_bytes()
    request = dict(nonce=nonce, root_thread_id=root, authors=[root, *authors], created=now_ts(),
                   task_name='review_' + nonce,
                   key_label=lease['key_label'], cache=str(args.cache), repo=str(args.repo),
                   head=args.head, worktree=str(args.worktree), prompt=str(args.prompt),
                   prompt_sha256=hashlib.sha256(prompt).hexdigest(), pr=args.pr)
    atomic_write(path, json.dumps(request) + '\n')
    print('native_request: ' + str(path), flush=True)
    response_path = path.with_suffix('.response.json')
    deadline = time.monotonic() + args.timeout
    while not response_path.exists():
        verify_root(args.cache, root)
        if time.monotonic() >= deadline:
            raise ValueError('native review observation timed out; do not restart a live child')
        time.sleep(1)
    response = json.loads(response_path.read_text())
    accept_response(request, response, args.out)
    print('name: reviewer-native-' + response['thread_id'])


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    request = sub.add_parser('request')
    for field in ('cache', 'repo', 'head', 'worktree', 'prompt', 'out', 'pr', 'timeout'):
        request.add_argument(field, type=int if field == 'timeout' else
                             str if field in ('head', 'pr') else Path)
    reply = sub.add_parser('complete')
    reply.add_argument('request', type=Path)
    reply.add_argument('thread')
    args = parser.parse_args()
    if args.command == 'request':
        request_review(args)
    else:
        complete(args.request, args.thread)


if __name__ == '__main__':
    main()
