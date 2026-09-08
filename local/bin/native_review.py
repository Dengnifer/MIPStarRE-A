"""Bridge independent native reviews into review.sh's unchanged exact-head publisher."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
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
    selection = request.get('model_policy') or dict(job_class='hard_review', model='gpt-6-astra',
        hardness_reason='Grandfathered pre-policy review request')
    child = native_rollout(rollout, thread, role='reviewer', job_class=selection['job_class'],
                           requested_model=selection['model'],
                           hardness_reason=selection.get('hardness_reason'))
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
    selection = child['model_policy']
    record_native(argparse.Namespace(rollout=rollout, thread_id=thread,
        root_thread_id=request['root_thread_id'], repo_root=Path(request['repo']),
        name='reviewer-native-' + thread, role='reviewer', issue='pr' + request['pr'],
        pr=request['pr'], key_label=request['key_label'], worktree=Path(request['worktree']),
        status='done', job_class=selection['job_class'], requested_model=selection['model'],
        hardness_reason=selection.get('hardness_reason'),
        dispatch_kind='resume', activation_at=request.get('activation_at')))
    atomic_write(out, child['final'])


def accept_existing(args: argparse.Namespace) -> None:
    """Validate one persisted request/response pair before materializing its review."""
    cache = args.cache.resolve(strict=True)
    mailbox = (cache / 'native-reviews').resolve(strict=True)
    request_path = args.request
    if (not request_path.is_absolute() or request_path.is_symlink() or
            request_path.resolve(strict=True) != request_path or
            request_path.parent != mailbox or
            not re.fullmatch(r'[0-9a-f]{32}\.json', request_path.name)):
        raise ValueError('native review request must be a canonical cache mailbox file')
    response_path = request_path.with_suffix('.response.json')
    if response_path.is_symlink() or not response_path.is_file():
        raise ValueError('completed native review response is required')
    request = json.loads(request_path.read_text())
    response = json.loads(response_path.read_text())
    if not isinstance(request, dict):
        raise ValueError('native review request must be an object')

    nonce = request_path.stem
    root = canonical_thread(args.root_thread, 'native root thread')
    author_values = [value.strip() for value in args.authors.split(',')]
    if not author_values or any(not value for value in author_values):
        raise ValueError('native review author exclusions must be nonempty')
    author_ids = [canonical_thread(value, 'review author') for value in author_values]
    expected_authors = {root, *author_ids}
    request_authors = request.get('authors')
    if not isinstance(request_authors, list) or not request_authors:
        raise ValueError('native review request authors must be a nonempty list')
    request_author_set = {
        canonical_thread(value, 'review author') for value in request_authors
    }
    expected_paths = dict(cache=cache, repo=args.repo.resolve(strict=True),
                          worktree=args.worktree.resolve(strict=True),
                          prompt=args.prompt.resolve(strict=True))
    for field, expected in expected_paths.items():
        value = request.get(field)
        if not isinstance(value, str) or Path(value) != expected:
            raise ValueError(f'native review request {field} mismatch')
    if (request.get('nonce') != nonce or request.get('task_name') != 'review_' + nonce or
            request.get('pr') != args.pr or request.get('head') != args.head or
            request.get('root_thread_id') != root or request_author_set != expected_authors):
        raise ValueError('native review request identity mismatch')
    prompt_digest = hashlib.sha256(args.prompt.read_bytes()).hexdigest()
    if request.get('prompt_sha256') != prompt_digest:
        raise ValueError('native review request prompt digest mismatch')
    from model_policy import select_model
    expected_policy = select_model('reviewer', args.job_class, args.model, args.effort,
                                   args.hardness_reason)
    if request.get('model_policy') != expected_policy:
        raise ValueError('native review request model policy mismatch')
    if request.get('activation_at') != args.activation_at:
        raise ValueError('native review request activation boundary mismatch')
    if isinstance(response, dict) and response.get('thread_id') in request_author_set:
        raise ValueError('reviewer must be excluded from the review authors')
    accept_response(request, response, args.out)
    print('name: reviewer-native-' + response['thread_id'])


def request_review(args: argparse.Namespace) -> None:
    root = os.environ['MIPSTARRE_NATIVE_REVIEW_ROOT']
    authors = [author.strip() for author in
               os.environ.get('MIPSTARRE_NATIVE_REVIEW_AUTHORS', '').split(',')]
    if not authors or any(not author for author in authors):
        raise ValueError('native review author thread IDs are required')
    authors = [canonical_thread(author, 'review author') for author in authors]
    lease = verify_root(args.cache, root)
    from model_policy import select_model
    selection = select_model('reviewer', args.job_class, args.model, 'ultra', args.hardness_reason)
    nonce = uuid.uuid4().hex
    directory = args.cache / 'native-reviews'
    directory.mkdir(parents=True, exist_ok=True)
    path = directory / (nonce + '.json')
    prompt = args.prompt.read_bytes()
    request = dict(nonce=nonce, root_thread_id=root, authors=[root, *authors], created=now_ts(),
                   task_name='review_' + nonce,
                   key_label=lease['key_label'], cache=str(args.cache), repo=str(args.repo),
                   head=args.head, worktree=str(args.worktree), prompt=str(args.prompt),
                   prompt_sha256=hashlib.sha256(prompt).hexdigest(), pr=args.pr,
                   model_policy=selection,
                   activation_at=os.environ.get('MIPSTARRE_MODEL_POLICY_ACTIVATION_AT'))
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
    request.add_argument('--job-class', default='independent_review')
    request.add_argument('--model', default='auto')
    request.add_argument('--hardness-reason')
    reply = sub.add_parser('complete')
    reply.add_argument('request', type=Path)
    reply.add_argument('thread')
    accept = sub.add_parser('accept')
    accept.add_argument('request', type=Path)
    accept.add_argument('out', type=Path)
    accept.add_argument('--cache', type=Path, required=True)
    accept.add_argument('--repo', type=Path, required=True)
    accept.add_argument('--head', required=True)
    accept.add_argument('--worktree', type=Path, required=True)
    accept.add_argument('--prompt', type=Path, required=True)
    accept.add_argument('--pr', required=True)
    accept.add_argument('--root-thread', required=True)
    accept.add_argument('--authors', required=True)
    accept.add_argument('--job-class', default='independent_review')
    accept.add_argument('--model', default='auto')
    accept.add_argument('--effort', default='ultra')
    accept.add_argument('--hardness-reason')
    accept.add_argument('--activation-at', default=os.environ.get(
        'MIPSTARRE_MODEL_POLICY_ACTIVATION_AT'))
    args = parser.parse_args()
    if args.command == 'request':
        request_review(args)
    elif args.command == 'complete':
        complete(args.request, args.thread)
    else:
        accept_existing(args)


if __name__ == '__main__':
    main()
