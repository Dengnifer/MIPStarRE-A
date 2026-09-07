"""Audit-backed model selection for bounded jobs; root and review defaults stay Astra."""

import argparse
import json
from pathlib import Path
import re
import subprocess
import os


ASTRA = 'gpt-6-astra'
SOL = 'gpt-5.6-sol'
CLEANUP = 'review_directed_nonsemantic_cleanup'
ROLES = ('orc', 'prover', 'reviewer', 'simplifier', 'blueprint', 'splitter', 'scout', 'mathfix')
JOB_ROLES = {'general': ROLES, 'independent_review': ('reviewer',), CLEANUP: ('prover',)}
JOB_ROLES.update({
    'proof_helper_consolidation_or_new_proof': ('prover',),
    'mathematical_exposition_source_gap_or_blueprint_status':
        ('blueprint', 'prover', 'reviewer', 'scout'),
    'authoritative_mathematical_security_or_runtime_review': ('reviewer',),
    'non_authoritative_deterministic_findings': ('reviewer', 'scout'),
    'proof_inventory_api_scouting_or_dependency_decomposition': ('scout', 'splitter'),
    'guarded_telemetry_only_merge_recovery': ('orc',),
    'runtime_security_policy_tests_deployment_and_control': ('orc', 'prover', 'reviewer'),
    'mathfix_frontier_or_source_faithfulness_adjudication': ('mathfix', 'prover', 'reviewer', 'orc'),
    'unknown_or_expanded_scope': ROLES,
})
POLICY_PATH = Path(__file__).resolve().parents[1] / 'model-policy.json'


def load_policy() -> dict:
    """Read the published main policy, never a worker-owned table or environment override."""
    try:
        policy = json.loads(subprocess.check_output(['git', '--no-replace-objects', '-C',
            str(Path(__file__).resolve().parents[2]), 'show', 'main:local/model-policy.json'],
            text=True, stderr=subprocess.PIPE,
            env={k: v for k, v in os.environ.items() if not k.startswith('GIT_')}))
    except subprocess.CalledProcessError:
        policy = dict(schema_version=1, audit=None, qualified_job_classes={})
    qualified = policy.get('qualified_job_classes') if isinstance(policy, dict) else None
    if (not isinstance(policy, dict) or policy.get('schema_version') != 1 or
            not isinstance(qualified, dict)):
        raise ValueError('invalid model policy')
    for job, entry in qualified.items():
        audit = policy.get('audit')
        if (job != CLEANUP or not isinstance(entry, dict) or
                entry.get('roles') != ['prover'] or entry.get('model') != SOL or
                entry.get('effort') != 'ultra' or
                not isinstance(entry.get('rationale'), str) or not entry['rationale'].strip() or
                not isinstance(entry.get('case_ids'), list) or len(entry['case_ids']) < 2 or
                any(not isinstance(case, str) or not case for case in entry['case_ids']) or
                len(set(entry['case_ids'])) != len(entry['case_ids']) or
                not isinstance(audit, dict) or not isinstance(audit.get('reference'), str) or
                not audit['reference'] or not isinstance(audit.get('sha256'), str) or
                not re.fullmatch('[0-9a-f]{64}', audit['sha256'])):
            raise ValueError('Sol qualification requires bounded scope and independent audit evidence')
    return policy


def select_model(role: str, job_class: str = 'general', requested_model: str = 'auto',
                 effort: str = 'ultra', job_spec: str | None = None, *,
                 observation: bool = False, worktree: str | None = None) -> dict:
    """Select only an exact model for a recognized role/class; explicit unsafe choices fail."""
    if role not in ROLES or job_class not in JOB_ROLES or role not in JOB_ROLES[job_class]:
        raise ValueError('unknown or incompatible role/job class')
    if effort != 'ultra':
        raise ValueError('model policy requires literal ultra; no effort downgrade is authorized')
    if requested_model not in ('auto', ASTRA, SOL):
        raise ValueError('owner policy requires gpt-6-astra or audit-qualified exact gpt-5.6-sol')
    policy = load_policy()
    qualification = policy['qualified_job_classes'].get(job_class)
    if job_spec is not None and (not isinstance(job_spec, str) or not job_spec.strip()):
        raise ValueError('invalid dispatcher edit-specification reference')
    selected = SOL if qualification and job_spec else ASTRA
    if requested_model == SOL and selected != SOL:
        raise ValueError('owner policy requires gpt-6-astra without qualification and an exact edit spec')
    if requested_model == ASTRA:
        selected = ASTRA
    request = None
    if selected == SOL:
        from model_job import validate_job
        request = validate_job(job_spec, worktree, admission=not observation)
    rationale = (qualification['rationale'] if qualification and selected == SOL else
                 'Astra fallback: unqualified scope, absent exact edit spec, or explicit selection')
    return dict(role=role, job_class=job_class, requested_model=requested_model,
                model=selected, requested_effort=effort, rationale=rationale,
                audit=policy.get('audit') if qualification else None,
                job_spec=job_spec, job_request=request,
                case_ids=qualification['case_ids'] if qualification and selected == SOL else [])


def observe_model(role: str, job_class: str, observed_model: str, effort: str,
                  requested_model: str | None = None, job_spec: str | None = None) -> dict:
    """Validate observed native configuration without inferring an unrecorded request."""
    if observed_model == SOL and requested_model != SOL:
        raise ValueError('an explicit trusted Sol request is required, not inference from observation')
    selection = select_model(role, job_class, requested_model or observed_model, effort, job_spec,
                             observation=True)
    if selection['model'] != observed_model:
        raise ValueError('native effective model differs from its requested model policy')
    selection['requested_model'] = requested_model
    return selection


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--role', required=True)
    parser.add_argument('--job-class', default='general')
    parser.add_argument('--model', default='auto')
    parser.add_argument('--effort', default='ultra')
    parser.add_argument('--job-spec', help='main-owned fixed file/replacement specification reference')
    parser.add_argument('--worktree')
    parser.add_argument('--result', action='store_true')
    parser.add_argument('--external', action='store_true')
    parser.add_argument('--field', choices=('model',))
    args = parser.parse_args()
    try:
        if args.external:
            from account_router import external_admission_enabled
            if not external_admission_enabled(Path(os.environ.get('MIPSTARRE_CACHE_ROOT',
                                                    Path.home() / '.cache/mipstarre-dev'))):
                raise ValueError('external admission disabled by owner gate')
        selection = select_model(args.role, args.job_class, args.model, args.effort, args.job_spec,
                                 observation=args.result, worktree=args.worktree)
        if args.result and selection['model'] == SOL:
            from model_job import validate_job
            validate_job(args.job_spec, args.worktree, completed=True)
    except (OSError, ValueError, TypeError, KeyError, subprocess.CalledProcessError) as error:
        parser.exit(4, f'model policy: {error}\n')
    print(selection[args.field] if args.field else json.dumps(selection))


if __name__ == '__main__':
    main()
