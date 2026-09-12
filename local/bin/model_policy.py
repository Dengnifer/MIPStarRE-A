"""Owner-directed Sol-first subagent selection and observation-based dispatch accounting."""

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import subprocess

ASTRA, SOL = 'gpt-6-astra', 'gpt-5.6-sol'
ROLES = ('orc', 'prover', 'reviewer', 'simplifier', 'blueprint', 'splitter', 'scout', 'mathfix')
ROUTINE = ('general', 'routine', 'bounded', 'independent_review',
           'review_directed_nonsemantic_cleanup')
HARD = ('hard', 'escalated', 'source_semantic', 'control_policy', 'hard_review')

# The owner's run-wide model switch.  `astra-all` narrows every role and job
# class TOWARD the hard model; there is deliberately no mode that widens toward
# the cheap model and none that touches effort.  On 2026-09-12 this switch only
# existed as a `sol -> astra` rewrite inside the PATH shim, so sessions.jsonl
# recorded `sol` for sessions that ran Astra.  It lives in the policy layer now.
OVERRIDE_MODES = ('astra-all',)
OVERRIDE_OFF = ('', 'none', 'null', 'off', 'default')
OVERRIDE_FIELDS = ('mode', 'reason', 'set_by', 'expires')
OVERRIDE_KNOB = 'watchdog/model-override'


def cache_root() -> Path:
    """Runtime state root; never inside the repository (DESIGN.md, Layout)."""
    override = os.environ.get('MIPSTARRE_CACHE_ROOT')
    return Path(override).expanduser() if override else Path.home() / '.cache' / 'mipstarre-dev'


def _parse_ts(text) -> datetime | None:
    if not isinstance(text, str) or not text.strip():
        return None
    value = text.strip()
    if value.endswith('Z'):
        value = value[:-1] + '+00:00'
    try:
        parsed = datetime.fromisoformat(value)
    except ValueError:
        raise ValueError(f'model override expires is not ISO-8601: {text!r}')
    if parsed.tzinfo is None:
        raise ValueError('model override expires needs an explicit timezone')
    return parsed


def _validate_override(raw, where: str) -> dict | None:
    """Validate one override object; an unknown mode fails closed and loudly."""
    if raw is None:
        return None
    if isinstance(raw, str):
        raw = dict(mode=raw.strip())
    if not isinstance(raw, dict):
        raise ValueError(f'model override in {where} must be an object or a mode string')
    unknown = sorted(set(raw) - set(OVERRIDE_FIELDS))
    if unknown:
        raise ValueError(f'model override in {where} has unknown field(s): {", ".join(unknown)}')
    mode = raw.get('mode')
    if mode is None or (isinstance(mode, str) and mode.strip().lower() in OVERRIDE_OFF):
        return None
    if not isinstance(mode, str) or mode.strip() not in OVERRIDE_MODES:
        raise ValueError(f'unknown model override mode {mode!r} in {where}; '
                         f'expected one of {", ".join(OVERRIDE_MODES)}')
    for field in ('reason', 'set_by'):
        if field in raw and not isinstance(raw[field], (str, type(None))):
            raise ValueError(f'model override {field} in {where} must be text')
    expires = _parse_ts(raw.get('expires'))
    if expires is not None and expires <= datetime.now(timezone.utc):
        return None
    return dict(mode=mode.strip(), reason=raw.get('reason'), set_by=raw.get('set_by'),
                expires=raw.get('expires'), source=where)


def runtime_override() -> dict | None:
    """The mid-run switch: `$CACHE_ROOT/watchdog/model-override`.

    A bare mode on one line is the documented form; a JSON object with the same
    fields is accepted so the owner's brief can be copied verbatim.  The file
    exists so a briefing switch needs no repository PR mid-run; it never widens
    capacity and never changes effort.
    """
    path = cache_root() / OVERRIDE_KNOB
    try:
        text = path.read_text(encoding='utf-8').strip()
    except OSError:
        return None
    if not text:
        return None
    # The label is the knob's role, not its absolute path: the row it lands on is
    # a committed record, and a private home does not belong in one (meta.md).
    where = f'runtime:{OVERRIDE_KNOB}'
    try:
        if text.startswith('{'):
            try:
                raw = json.loads(text)
            except ValueError:
                raise ValueError('neither a mode word nor a JSON object')
            return _validate_override(raw, where)
        return _validate_override(text.splitlines()[0], where)
    except ValueError as error:
        # Fail closed and say which file to edit; the recorded label stays relative.
        raise ValueError(f'{error} (file: {path})')


def active_override(policy: dict) -> dict | None:
    """The override in force: the runtime knob first, then the reviewed policy."""
    return runtime_override() or _validate_override(
        policy.get('override'), 'policy:local/model-policy.json')


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
    # Optional and validated here so a malformed override is refused at the
    # policy boundary rather than at every call site.
    _validate_override(policy.get('override'), 'policy:local/model-policy.json')
    return policy


def select_model(role: str, job_class: str = 'general', requested_model: str = 'auto',
                 effort: str = 'ultra', hardness_reason: str | None = None) -> dict:
    """Main classifies the actual job; the ratio never reclassifies necessary hard work."""
    if role not in ROLES or job_class not in ROUTINE + HARD:
        raise ValueError('unknown role/job class')
    if job_class in ('independent_review', 'hard_review') and role != 'reviewer':
        raise ValueError('review job classes require the reviewer role')
    if effort != 'ultra':
        # The override may only narrow toward the hard model; it may NEVER
        # lower effort, so this check runs before and regardless of it.
        raise ValueError('model policy requires literal ultra; no downgrade is authorized')
    if requested_model not in ('auto', ASTRA, SOL):
        raise ValueError('model policy requires exact gpt-6-astra or gpt-5.6-sol')
    hard = job_class in HARD or role == 'mathfix'
    reason = hardness_reason.strip() if isinstance(hardness_reason, str) else ''
    if hard and not reason:
        raise ValueError('hard/escalated Astra work requires an explicit reason')
    policy = load_policy()
    selected = ASTRA if hard else policy['default_model']
    override = active_override(policy)
    if override:
        # Every role and job class runs the hard model, and an explicit Astra
        # request is no longer a conflict with a routine classification.
        selected = policy.get('hard_model', ASTRA)
        if requested_model == SOL:
            raise ValueError(f"model override {override['mode']} is active "
                             f"({override['source']}); an explicit {SOL} request cannot be honored")
    if requested_model != 'auto' and requested_model != selected:
        raise ValueError('requested model conflicts with the routine/hard classification')
    if reason and not hard:
        raise ValueError('an escalation reason requires a hard job classification')
    selection = dict(role=role, job_class=job_class, classification='hard' if hard else 'routine',
                     requested_model=requested_model, model=selected, requested_effort=effort,
                     hardness_reason=reason or None, policy_version=policy['schema_version'],
                     rationale=reason or ('Owner-authorized routine/bounded Sol default'
                                          if selected == SOL else 'Pre-activation Astra configuration'))
    selection.update(override_mode=override['mode'] if override else None,
                     override_source=override['source'] if override else None)
    if override:
        selection['rationale'] = (f"Owner model override {override['mode']} "
                                  f"({override['source']})"
                                  + (f": {override['reason']}" if override.get('reason') else ''))
    return selection


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
    threads, conflicts, starts, overridden = {}, set(), {}, set()
    for row in rows:
        thread = row.get('thread_id')
        if (not thread or thread == row.get('root_thread_id') or
                row.get('dispatch_kind') != 'new' or row.get('activation_at') != activation_at):
            continue
        if row.get('override_mode'):
            # An override period is an owner decision recorded on the row, not
            # a routing violation: the rows are excluded from the ratio rather
            # than counted against it.
            overridden.add(thread)
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
                override_excluded=len(overridden),
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
    parser.add_argument('--field', choices=('model', 'override_mode', 'override_source'))
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
        selection = select_model(args.role, args.job_class, args.model, args.effort,
                                 args.hardness_reason)
    except (OSError, ValueError, TypeError, KeyError, AttributeError, subprocess.CalledProcessError) as error:
        parser.exit(4, f'model policy: {error}\n')
    if args.field:
        value = selection[args.field]
        print('' if value is None else value)
    else:
        print(json.dumps(selection))


if __name__ == '__main__':
    main()
