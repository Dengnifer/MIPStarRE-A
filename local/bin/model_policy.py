"""Which model a dispatched worker runs, and the observed routine/hard dispatch ratio.

No model name lives in this file or in `local/model-policy.json`.  The names come
from `local/project.json`:

    session.workers.model        the routine ("default") model
    session.workers.hard_model   the model for work classified as hard
                                 (empty falls back to the routine model)
    session.main.model           the supervising session's model, reported only

An empty name means "let the codex CLI pick its own default": the caller then
omits `-m` entirely, which is what a freshly bootstrapped project does.

`local/model-policy.json` carries the ROUTING RULES that are independent of any
model: the schema version, an optional required reasoning effort ("" = accept
whatever the caller asks for), and the routine/hard ratio the operator watches.
The committed copy on `main` wins when there is one; a repository that has no
commit yet, or whose `main` never carried the file, falls back to the work-tree
copy, because the first commit of a new project has to be able to run the tests.

Set `MIPSTARRE_PROJECT_ROOT` to point these lookups at another checkout (a
worktree, or a test fixture); by default the repository is the one this file
lives in.
"""

import argparse
from datetime import datetime
import json
import os
from pathlib import Path
import subprocess

ROLES = ('orc', 'prover', 'reviewer', 'simplifier', 'blueprint', 'splitter', 'scout', 'mathfix')
ROUTINE = ('general', 'routine', 'bounded', 'independent_review',
           'review_directed_nonsemantic_cleanup')
HARD = ('hard', 'escalated', 'source_semantic', 'control_policy', 'hard_review')
RATIO_DEFAULTS = {'target': 20, 'minimum': 10, 'maximum': 50}


def project_root() -> Path:
    """The repository whose configuration decides the models."""
    override = os.environ.get('MIPSTARRE_PROJECT_ROOT')
    return Path(override) if override else Path(__file__).resolve().parents[2]


def configured_models(root: Path | None = None) -> dict:
    """The three model names from `local/project.json`; "" means the CLI default.

    Read with plain json rather than `scripts/project_config.py`, so that the
    policy still answers in a tree that carries `local/` but no `scripts/`
    (a dispatch fixture, a stripped worker checkout).
    """
    root = root or project_root()
    try:
        data = json.loads((root / 'local/project.json').read_text(encoding='utf-8'))
    except (OSError, ValueError):
        data = {}
    session = data.get('session') if isinstance(data.get('session'), dict) else {}
    workers = session.get('workers') if isinstance(session.get('workers'), dict) else {}
    main = session.get('main') if isinstance(session.get('main'), dict) else {}
    default = str(workers.get('model') or '')
    return dict(default_model=default,
                hard_model=str(workers.get('hard_model') or '') or default,
                main_model=str(main.get('model') or ''))


def known_models(policy: dict) -> tuple[str, ...]:
    """The distinct, non-empty models this project configures."""
    seen = []
    for key in ('default_model', 'hard_model'):
        name = policy.get(key) or ''
        if name and name not in seen:
            seen.append(name)
    return tuple(seen)


def load_policy() -> dict:
    """Routing rules from `local/model-policy.json`, plus the configured models.

    The reviewed copy committed on `main` is authoritative; a repository without
    that history reads its work tree instead and says so with `schema_version: 0`
    (`account_router` uses that to leave resumed threads alone).
    """
    root = project_root()
    raw, committed = None, False
    command = ['git', '--no-replace-objects', '-C', str(root)]
    env = {k: v for k, v in os.environ.items() if not k.startswith('GIT_')}
    try:
        listed = subprocess.check_output(
            command + ['ls-tree', '--name-only', 'main', '--', 'local/model-policy.json'],
            text=True, stderr=subprocess.PIPE, env=env).strip()
    except (OSError, subprocess.CalledProcessError):
        listed = ''          # no repository, no commit, no `main`: not an error here
    if listed:
        raw = json.loads(subprocess.check_output(
            command + ['show', 'main:local/model-policy.json'],
            text=True, stderr=subprocess.PIPE, env=env))
        committed = True
    else:
        try:
            raw = json.loads((root / 'local/model-policy.json').read_text(encoding='utf-8'))
        except (OSError, ValueError):
            raw = None
    models = configured_models(root)
    if not isinstance(raw, dict) or not committed or raw.get('schema_version') != 2:
        # Pre-activation: the models still apply, the ratio rules do not.
        return dict(schema_version=0, effort='', dispatch_ratio=dict(RATIO_DEFAULTS), **models)
    if not isinstance(raw.get('effort', ''), str):
        raise ValueError('invalid owner model policy: effort must be a string')
    ratio = raw.get('dispatch_ratio') or RATIO_DEFAULTS
    if not isinstance(ratio, dict) or not {'target', 'minimum', 'maximum'} <= ratio.keys():
        raise ValueError('invalid owner model policy: dispatch_ratio needs target/minimum/maximum')
    return dict(schema_version=2, effort=raw.get('effort', ''), dispatch_ratio=ratio, **models)


def select_model(role: str, job_class: str = 'general', requested_model: str = 'auto',
                 effort: str | None = None, hardness_reason: str | None = None) -> dict:
    """Main classifies the actual job; the ratio never reclassifies necessary hard work.

    `effort=None` means "whatever `local/model-policy.json` requires" (and nothing
    at all when it requires nothing); any other value must match that requirement.
    """
    if role not in ROLES or job_class not in ROUTINE + HARD:
        raise ValueError('unknown role/job class')
    if job_class in ('independent_review', 'hard_review') and role != 'reviewer':
        raise ValueError('review job classes require the reviewer role')
    policy = load_policy()
    required_effort = policy.get('effort') or ''
    if effort is None:
        effort = required_effort
    if required_effort and effort != required_effort:
        raise ValueError(f'model policy requires literal {required_effort}; no downgrade is authorized')
    allowed = known_models(policy)
    if requested_model not in ('auto', *allowed):
        raise ValueError('model policy accepts only auto or a model configured in '
                         f"local/project.json ({', '.join(allowed) or 'none configured'})")
    hard = job_class in HARD or role == 'mathfix'
    reason = hardness_reason.strip() if isinstance(hardness_reason, str) else ''
    if hard and not reason:
        raise ValueError('hard/escalated work requires an explicit reason')
    selected = policy['hard_model'] if hard else policy['default_model']
    if requested_model != 'auto' and requested_model != selected:
        raise ValueError('requested model conflicts with the routine/hard classification')
    if reason and not hard:
        raise ValueError('an escalation reason requires a hard job classification')
    return dict(role=role, job_class=job_class, classification='hard' if hard else 'routine',
                requested_model=requested_model, model=selected, requested_effort=effort,
                hardness_reason=reason or None, policy_version=policy['schema_version'],
                rationale=reason or ('Configured routine worker model' if selected
                                     else 'No model configured: the codex CLI default applies'))


def observe_model(role: str, job_class: str, observed_model: str, effort: str,
                  requested_model: str | None = None, hardness_reason: str | None = None,
                  grandfathered: bool = False) -> dict:
    """Validate actual configuration; absent request evidence is not an inferred request."""
    if grandfathered:
        policy = load_policy()
        required_effort = policy.get('effort') or ''
        if observed_model not in known_models(policy) or (required_effort and effort != required_effort):
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
    """Count distinct observed new threads, not resumes, status appends, main or unknowns.

    The two buckets are the project's ROUTINE model and its HARD model; the keys
    are `routine` and `hard`, never a model name, so the report reads the same on
    every project.
    """
    policy = load_policy()
    routine_model, hard_model = policy['default_model'], policy['hard_model']
    pair = (routine_model, hard_model)
    limits = policy.get('dispatch_ratio') or RATIO_DEFAULTS
    minimum, maximum = limits['minimum'], limits['maximum']
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
        if model in pair and selected in pair and model != selected:
            conflicts.add(thread)
        if model not in pair or model != selected:
            threads.setdefault(thread, None)
            continue
        if threads.get(thread) and threads[thread] != model:
            conflicts.add(thread)
        threads[thread] = model
    cumulative = {model: sum(value == model for thread, value in threads.items()
                             if thread not in conflicts) for model in pair}
    recent = set(sorted(starts, key=lambda thread: (starts[thread], thread))[-window:])
    unknown = {thread for thread in recent if not threads[thread] or thread in conflicts}
    counts = {model: sum(value == model for thread, value in threads.items()
                         if thread in recent and thread not in unknown)
              for model in pair}
    routine = counts[routine_model]
    # One configured model (or none) means there is no separate hard bucket to count.
    hard = counts[hard_model] if hard_model != routine_model else 0
    return dict(routine=routine, hard=hard, unknown=len(unknown), window=window,
                sampled_dispatches=len(recent), cumulative=cumulative,
                routine_model=routine_model, hard_model=hard_model, **limits,
                ratio=routine / hard if hard else None,
                status='not-measurable' if not hard else
                'within-range' if minimum * hard <= routine <= maximum * hard else 'outside-range',
                action='Assign useful work by difficulty; record deviations, never add filler '
                       'or delay hard work')


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('--role')
    parser.add_argument('--job-class', default='general')
    parser.add_argument('--model', default='auto')
    parser.add_argument('--effort', default=None,
                        help='required reasoning effort; default: whatever the policy requires')
    parser.add_argument('--hardness-reason')
    parser.add_argument('--field', choices=('model',))
    parser.add_argument('--list-models', action='store_true',
                        help='print the models this project configures, one per line, and exit')
    parser.add_argument('--ratio-registry', type=Path)
    parser.add_argument('--activation-at')
    parser.add_argument('--window', type=int, default=100)
    args = parser.parse_args()
    try:
        if args.list_models:
            for name in known_models(load_policy()):
                print(name)
            return
        if args.ratio_registry:
            from account_router import session_rows
            print(json.dumps(dispatch_ratio(session_rows(args.ratio_registry), args.activation_at,
                                            args.window)))
            return
        selection = select_model(args.role, args.job_class, args.model, args.effort,
                                 args.hardness_reason)
    except (OSError, ValueError, TypeError, KeyError, AttributeError, subprocess.CalledProcessError) as error:
        parser.exit(4, f'model policy: {error}\n')
    print(selection[args.field] if args.field else json.dumps(selection))


if __name__ == '__main__':
    main()
