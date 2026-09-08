"""Owner-directed Sol-first subagent selection and observation-based dispatch accounting."""

import argparse
from datetime import datetime
import json
import os
from pathlib import Path
import subprocess

ASTRA, SOL = 'gpt-6-astra', 'gpt-5.6-sol'
ROLES = ('orc', 'prover', 'reviewer', 'simplifier', 'blueprint', 'splitter', 'scout', 'mathfix')
ROUTINE = ('general', 'routine', 'bounded', 'independent_review',
           'review_directed_nonsemantic_cleanup')
HARD = ('hard', 'escalated', 'source_semantic', 'control_policy', 'hard_review')


def load_policy() -> dict:
    """Routing becomes active only with the reviewed policy on committed main."""
    command = ['git', '--no-replace-objects', '-C', str(Path(__file__).resolve().parents[2])]
    env = {k: v for k, v in os.environ.items() if not k.startswith('GIT_')}
    if not subprocess.check_output(command + ['ls-tree', '--name-only', 'main', '--',
        'local/model-policy.json'], text=True, stderr=subprocess.PIPE, env=env).strip():
        return dict(schema_version=0, default_model=ASTRA)
    policy = json.loads(subprocess.check_output(command + ['show', 'main:local/model-policy.json'],
                                               text=True, stderr=subprocess.PIPE, env=env))
    if (not isinstance(policy, dict) or policy.get('schema_version') != 2 or
            policy.get('default_model') != SOL or policy.get('hard_model') != ASTRA or
            policy.get('effort') != 'ultra'):
        raise ValueError('invalid owner model policy')
    return policy


def select_model(role: str, job_class: str = 'general', requested_model: str = 'auto',
                 effort: str = 'ultra', hardness_reason: str | None = None) -> dict:
    """Main classifies the actual job; the ratio never reclassifies necessary hard work."""
    if role not in ROLES or job_class not in ROUTINE + HARD:
        raise ValueError('unknown role/job class')
    if job_class in ('independent_review', 'hard_review') and role != 'reviewer':
        raise ValueError('review job classes require the reviewer role')
    if effort != 'ultra':
        raise ValueError('model policy requires literal ultra; no downgrade is authorized')
    if requested_model not in ('auto', ASTRA, SOL):
        raise ValueError('model policy requires exact gpt-6-astra or gpt-5.6-sol')
    hard = job_class in HARD or role == 'mathfix'
    reason = hardness_reason.strip() if isinstance(hardness_reason, str) else ''
    if hard and not reason:
        raise ValueError('hard/escalated Astra work requires an explicit reason')
    policy = load_policy()
    selected = ASTRA if hard else policy['default_model']
    if requested_model != 'auto' and requested_model != selected:
        raise ValueError('requested model conflicts with the routine/hard classification')
    if reason and not hard:
        raise ValueError('an escalation reason requires a hard job classification')
    return dict(role=role, job_class=job_class, classification='hard' if hard else 'routine',
                requested_model=requested_model, model=selected, requested_effort=effort,
                hardness_reason=reason or None, policy_version=policy['schema_version'],
                rationale=reason or ('Owner-authorized routine/bounded Sol default' if selected == SOL
                                    else 'Pre-activation Astra configuration'))


def observe_model(role: str, job_class: str, observed_model: str, effort: str,
                  requested_model: str | None = None, hardness_reason: str | None = None,
                  grandfathered: bool = False) -> dict:
    """Validate actual configuration; absent request evidence is not an inferred request."""
    if grandfathered:
        if observed_model not in (ASTRA, SOL) or effort != 'ultra':
            raise ValueError('invalid grandfathered native model/effort')
        return dict(role=role, job_class=job_class, model=observed_model,
                    requested_model=requested_model, requested_effort=effort,
                    rationale='Grandfathered worker; excluded from new-dispatch ratio')
    selection = select_model(role, job_class, requested_model or 'auto', effort, hardness_reason)
    if selection['model'] != observed_model:
        raise ValueError('native effective model differs from the requested job policy')
    selection['requested_model'] = requested_model
    return selection


def dispatch_ratio(rows: list[dict], activation_at: str, window: int = 100) -> dict:
    """Count distinct observed new threads, not resumes, status appends, main or unknowns."""
    activated = datetime.fromisoformat(activation_at.replace('Z', '+00:00'))
    if activated.tzinfo is None:
        raise ValueError('activation boundary needs an explicit timezone')
    if type(window) is not int or window < 1:
        raise ValueError('ratio window must be positive')
    threads, conflicts, starts = {}, set(), {}
    for row in rows:
        thread = row.get('thread_id')
        if (not thread or thread == row.get('root_thread_id') or
                row.get('dispatch_kind') != 'new' or row.get('activation_at') != activation_at):
            continue
        started = datetime.fromisoformat(row['start'].replace('Z', '+00:00'))
        if started.tzinfo is None or started < activated:
            continue
        starts[thread] = min(started, starts.get(thread, started))
        model, selected = row.get('effective_model'), row.get('selected_model')
        if model in (ASTRA, SOL) and selected in (ASTRA, SOL) and model != selected:
            conflicts.add(thread)
        if model not in (ASTRA, SOL) or model != selected:
            threads.setdefault(thread, None)
            continue
        if threads.get(thread) and threads[thread] != model:
            conflicts.add(thread)
        threads[thread] = model
    cumulative = {model: sum(value == model for thread, value in threads.items()
                            if thread not in conflicts) for model in (SOL, ASTRA)}
    recent = set(sorted(starts, key=lambda thread: (starts[thread], thread))[-window:])
    unknown = {thread for thread in recent if not threads[thread] or thread in conflicts}
    counts = {model: sum(value == model for thread, value in threads.items()
                        if thread in recent and thread not in unknown)
              for model in (SOL, ASTRA)}
    sol, astra = counts[SOL], counts[ASTRA]
    return dict(sol=sol, astra=astra, unknown=len(unknown), target=20, minimum=10, maximum=50,
                window=window, sampled_dispatches=len(recent), cumulative=cumulative,
                ratio=sol / astra if astra else None,
                status='not-measurable' if not astra else
                'within-range' if 10 * astra <= sol <= 50 * astra else 'outside-range',
                action='Assign useful work by difficulty; record deviations, never add filler or delay hard work')


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--role')
    parser.add_argument('--job-class', default='general')
    parser.add_argument('--model', default='auto')
    parser.add_argument('--effort', default='ultra')
    parser.add_argument('--hardness-reason')
    parser.add_argument('--external', action='store_true')
    parser.add_argument('--field', choices=('model',))
    parser.add_argument('--ratio-registry', type=Path)
    parser.add_argument('--activation-at')
    parser.add_argument('--window', type=int, default=100)
    args = parser.parse_args()
    try:
        if args.ratio_registry:
            from account_router import session_rows
            print(json.dumps(dispatch_ratio(session_rows(args.ratio_registry), args.activation_at,
                                            args.window)))
            return
        if args.external:
            from account_router import external_admission_enabled
            if not external_admission_enabled(Path(os.environ.get('MIPSTARRE_CACHE_ROOT',
                                                    Path.home() / '.cache/mipstarre-dev'))):
                raise ValueError('external admission disabled by owner gate')
        selection = select_model(args.role, args.job_class, args.model, args.effort,
                                 args.hardness_reason)
    except (OSError, ValueError, TypeError, KeyError, AttributeError, subprocess.CalledProcessError) as error:
        parser.exit(4, f'model policy: {error}\n')
    print(selection[args.field] if args.field else json.dumps(selection))


if __name__ == '__main__':
    main()
