"""Isolated owner-policy regressions; no live dispatch, credential or lease changes."""

import argparse
from contextlib import redirect_stdout
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'local/bin'))
import account_router
import model_policy as policy
import telemetry
from scripts.tests import test_native_workflow as native_tests
from scripts.tests import test_dispatch as dispatch_tests

ACTIVE = dict(schema_version=2, default_model=policy.SOL, hard_model=policy.ASTRA, effort='ultra')
ACTIVATION = '2026-09-06T13:00:00Z'


class ModelPolicyTests(unittest.TestCase):
    def setUp(self):
        patch = mock.patch.object(policy, 'load_policy', return_value=ACTIVE)
        patch.start()
        self.addCleanup(patch.stop)

    def test_routine_defaults_include_proofs_and_independent_reviews(self):
        for role in policy.ROLES:
            if role != 'mathfix':
                for job in ('general', 'routine', 'bounded'):
                    decision = policy.select_model(role, job)
                    self.assertEqual(decision['model'], policy.SOL)
                    self.assertEqual(decision['requested_model'], 'auto')
        self.assertEqual(policy.select_model('reviewer', 'independent_review')['model'], policy.SOL)
        self.assertEqual(policy.select_model('prover', 'review_directed_nonsemantic_cleanup')[
            'model'], policy.SOL)

    def test_dispatch_command_selects_routine_sol_and_reasoned_hard_astra(self):
        fixture = dispatch_tests.DispatchCommandTests()
        argv = fixture.dispatch_command('--role', 'prover', '--job-class', 'bounded',
                                        model='auto', policy_data=ACTIVE)
        self.assertEqual(argv[argv.index('-m') + 1], policy.SOL)
        argv = fixture.dispatch_command('--role', 'reviewer', '--job-class', 'hard_review',
            '--hardness-reason', 'Control-policy review', model='auto', policy_data=ACTIVE)
        self.assertEqual(argv[argv.index('-m') + 1], policy.ASTRA)

    def test_hard_astra_needs_reason_and_unknown_or_conflicting_choices_fail(self):
        for role, job in [('reviewer', 'hard_review'), ('orc', 'control_policy'),
                          ('prover', 'source_semantic'), ('mathfix', 'hard')]:
            decision = policy.select_model(role, job, hardness_reason='Explicit difficult obligation')
            self.assertEqual(decision['model'], policy.ASTRA)
            self.assertTrue(decision['hardness_reason'])
            with self.assertRaises(ValueError):
                policy.select_model(role, job)
        for args in [('bad',), ('prover', 'bad'), ('prover', 'independent_review'),
                     ('prover', 'routine', policy.ASTRA), ('prover', 'general', 'gpt-5.6'),
                     ('prover', 'general', 'gpt-6-sol'), ('prover', 'general', policy.SOL, 'max')]:
            with self.subTest(args=args), self.assertRaises(ValueError):
                policy.select_model(*args)

    def test_native_model_mismatch_and_missing_request_are_distinct(self):
        observed = policy.observe_model('prover', 'bounded', policy.SOL, 'ultra')
        self.assertIsNone(observed['requested_model'])
        with self.assertRaises(ValueError):
            policy.observe_model('prover', 'bounded', policy.ASTRA, 'ultra', policy.SOL)
        with self.assertRaises(ValueError):
            policy.observe_model('reviewer', 'hard_review', policy.SOL, 'ultra',
                                 policy.ASTRA, 'Control-policy review')

    def test_resume_affinity_uses_observation_not_requested_model(self):
        with tempfile.TemporaryDirectory() as directory:
            registry = Path(directory) / 'sessions.jsonl'
            registry.write_text(json.dumps(dict(thread_id='old', model=policy.ASTRA)) + '\n')
            with self.assertRaisesRegex(ValueError, 'unknown'):
                account_router.resume_model('old', registry, {})
            registry.write_text(json.dumps(dict(thread_id='old', effective_model=policy.ASTRA)) + '\n')
            self.assertEqual(account_router.resume_model('old', registry, {}), policy.ASTRA)

    def test_native_resume_does_not_turn_old_astra_into_routine_sol(self):
        fixture = native_tests.NativeWorkflowTests()
        fixture.setUp()
        self.addCleanup(fixture.doCleanups)
        fixture.write_rollout()
        rows = [json.loads(line) for line in fixture.rollout.read_text().splitlines()]
        for row in rows:
            if row['type'] == 'turn_context':
                row['payload']['turn_id'] = 'turn'
        rows += [dict(type='event_msg', timestamp='2026-09-06T13:15:00Z',
                      payload=dict(type='task_started', turn_id='resumed')),
                 dict(type='turn_context', payload=dict(turn_id='resumed', model=policy.SOL,
                                                       effort='ultra'))]
        fixture.rollout.write_text(''.join(json.dumps(row) + '\n' for row in rows))
        with self.assertRaisesRegex(ValueError, 'cannot switch'):
            telemetry.native_rollout(fixture.rollout, native_tests.CHILD, role='prover',
                                     job_class='routine', requested_model=policy.SOL)

    def test_all_child_turns_need_consistent_bound_contexts(self):
        fixture = native_tests.NativeWorkflowTests()
        fixture.setUp()
        self.addCleanup(fixture.doCleanups)
        fixture.write_rollout()
        meta = json.loads(fixture.rollout.read_text().splitlines()[0])
        cases = [([policy.SOL, policy.ASTRA, policy.SOL], policy.SOL, False),
                 ([policy.SOL, None, policy.SOL], policy.SOL, False),
                 ([None, policy.SOL], policy.SOL, False),
                 ([policy.SOL, None], policy.SOL, False), ([None], policy.ASTRA, False),
                 ([policy.ASTRA, None], policy.ASTRA, False),
                 ([policy.SOL, policy.SOL], policy.SOL, True)]
        for models, requested, valid in cases:
            rows = [meta, dict(type='turn_context', payload=dict(model=policy.ASTRA, effort='ultra')),
                    dict(type='turn_context', payload=dict(turn_id='parent', model=policy.ASTRA,
                                                          effort='ultra'))]
            for index, model in enumerate(models):
                turn, ts = f'child-{index}', f'2026-09-06T13:14:{index + 1:02}Z'
                rows.append(dict(type='event_msg', timestamp=ts,
                    payload=dict(type='task_started', turn_id=turn)))
                if model:
                    rows.append(dict(type='turn_context', payload=dict(turn_id=turn,
                                     model=model, effort='ultra')))
                rows.append(dict(type='response_item', timestamp=ts, payload=dict(type='agent_message',
                    author='/root', recipient='/root/review_nonce', content=[])))
            fixture.rollout.write_text(''.join(json.dumps(row) + '\n' for row in rows))
            with self.subTest(models=models):
                args = dict(role='reviewer', requested_model=requested,
                    job_class='hard_review' if requested == policy.ASTRA else 'independent_review',
                    hardness_reason='Control-policy review' if requested == policy.ASTRA else None)
                if valid:
                    self.assertEqual(telemetry.native_rollout(fixture.rollout, native_tests.CHILD,
                                     **args)['effective_model'], requested)
                else:
                    with self.assertRaises(ValueError):
                        telemetry.native_rollout(fixture.rollout, native_tests.CHILD, **args)

    def test_routine_sol_review_keeps_independence_binding_and_mixed_context_guards(self):
        fixture = native_tests.NativeWorkflowTests()
        fixture.setUp()
        self.addCleanup(fixture.doCleanups)
        fixture.request['model_policy'] = policy.select_model('reviewer', 'independent_review')
        fixture.write_rollout()
        rows = [json.loads(line) for line in fixture.rollout.read_text().splitlines()]
        for row in rows:
            if row['type'] == 'turn_context':
                row['payload'].update(model=policy.SOL, turn_id='turn')
        def write():
            fixture.rollout.write_text(''.join(json.dumps(row) + '\n' for row in rows))
        write()
        with mock.patch.object(native_tests.review, 'verify_root', return_value=fixture.info), \
             mock.patch.object(native_tests.review.subprocess, 'check_output',
                side_effect=lambda args, **kw: 'a' * 40 if 'rev-parse' in args else ''):
            native_tests.review.completed_review(fixture.request, native_tests.CHILD)
            with mock.patch.dict(fixture.request, authors=[native_tests.ROOT, native_tests.CHILD]), \
                    self.assertRaises(ValueError):
                native_tests.review.completed_review(fixture.request, native_tests.CHILD)
            with mock.patch.dict(fixture.request, head='b' * 40), self.assertRaises(ValueError):
                native_tests.review.completed_review(fixture.request, native_tests.CHILD)
        rows.append(dict(type='turn_context', payload=dict(turn_id='turn',
                         model=policy.ASTRA, effort='ultra')))
        write()
        with self.assertRaises(ValueError):
            telemetry.native_rollout(fixture.rollout, native_tests.CHILD, role='reviewer',
                job_class='hard_review', requested_model=policy.ASTRA, hardness_reason='Hard review')

    def test_grandfathering_requires_pre_activation_task_and_new_rejects_resume(self):
        fixture = native_tests.NativeWorkflowTests()
        fixture.setUp()
        self.addCleanup(fixture.doCleanups)
        fixture.write_rollout()
        with self.assertRaisesRegex(ValueError, 'pre-activation'):
            telemetry.native_rollout(fixture.rollout, native_tests.CHILD, grandfathered=True,
                                     activation_at=ACTIVATION)
        old = telemetry.native_rollout(fixture.rollout, native_tests.CHILD, grandfathered=True,
                                      activation_at='2026-09-07T00:00:00Z')
        self.assertEqual(old['model'], policy.ASTRA)
        args = argparse.Namespace(rollout=fixture.rollout, thread_id=native_tests.CHILD,
            root_thread_id=native_tests.ROOT, role='prover', job_class='hard',
            hardness_reason='Difficult source obligation', requested_model=policy.ASTRA,
            dispatch_kind='new', activation_at=ACTIVATION, status='done', repo_root=fixture.root,
            name='new', issue='301', pr=None, key_label='space', worktree=fixture.root)
        with mock.patch.object(telemetry, 'native_rollout', return_value=old | {
                'turn_start': '2026-09-06T13:15:00Z'}), self.assertRaisesRegex(ValueError, 'resumed'):
            telemetry.record_native(args)
        args.dispatch_kind = 'resume'
        with mock.patch.object(telemetry, 'native_rollout', return_value=old):
            telemetry.record_native(args)
        record = json.loads((fixture.root / 'results/telemetry/sessions.jsonl').read_text())
        self.assertEqual(record['dispatch_kind'], 'new')

    def test_rolling_ratio_excludes_resumes_main_old_and_resolves_unknowns(self):
        def row(thread, model, kind='new', **kwargs):
            return dict(thread_id=thread, root_thread_id='root', dispatch_kind=kind,
                start='2026-09-06T13:14:00Z', activation_at=ACTIVATION,
                selected_model=model, effective_model=model, **kwargs)
        rows = [row(f'sol-{i:03}', policy.SOL) for i in range(20)] + [row('astra', policy.ASTRA)]
        rows += [rows[0], row('resume', policy.ASTRA, 'resume'), row('root', policy.ASTRA),
                 row('old', policy.ASTRA, 'grandfathered')]
        result = policy.dispatch_ratio(rows, ACTIVATION)
        self.assertEqual((result['sol'], result['astra'], result['ratio']), (20, 1, 20))
        rows += [row('unknown', policy.SOL) | {'effective_model': None}, row('unknown', policy.SOL)]
        self.assertEqual(policy.dispatch_ratio(rows, ACTIVATION)['unknown'], 0)
        rows += [row('unknown', policy.ASTRA)]
        self.assertEqual(policy.dispatch_ratio(rows, ACTIVATION)['unknown'], 1)
        self.assertEqual(policy.dispatch_ratio(rows, ACTIVATION, window=10)['sampled_dispatches'], 10)
        self.assertIsNone(policy.dispatch_ratio([row('only-sol', policy.SOL)], ACTIVATION)['ratio'])
        good = row('contradictory', policy.SOL)
        bad = good | {'effective_model': policy.ASTRA}
        for observations in ([good, bad], [bad, good]):
            with self.subTest(observations=observations):
                result = policy.dispatch_ratio(observations, ACTIVATION)
                self.assertEqual((result['sol'], result['astra'], result['unknown']), (0, 0, 1))
                self.assertEqual(result['cumulative'], {policy.SOL: 0, policy.ASTRA: 0})

    def test_external_selected_model_is_not_fabricated_observation(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            capture, snapshot = root / 'capture.jsonl', root / 'policy.json'
            capture.write_text(json.dumps(dict(type='thread.started', thread_id='fixture')) + '\n')
            snapshot.write_text(json.dumps(policy.select_model('prover', 'bounded')))
            args = telemetry._build_parser().parse_args(['--repo-root', directory,
                'session-summarize', str(capture), '--role', 'prover', '--model', policy.SOL,
                '--requested-effort', 'ultra', '--model-policy-file', str(snapshot),
                '--no-rollout-scan', '--dispatch-kind', 'new', '--activation-at', ACTIVATION])
            output = io.StringIO()
            with redirect_stdout(output):
                telemetry.cmd_session_summarize(args)
            record = json.loads(output.getvalue())
            self.assertEqual(record['selected_model'], policy.SOL)
            self.assertEqual(record['requested_model'], 'auto')
            self.assertIsNone(record['effective_model'])
            capture.write_text(capture.read_text() + json.dumps(dict(type='turn_context',
                payload=dict(model=policy.ASTRA))) + '\n')
            output = io.StringIO()
            with redirect_stdout(output):
                self.assertEqual(telemetry.cmd_session_summarize(args), 4)
            mismatch = json.loads(output.getvalue())
            self.assertEqual(mismatch['effective_model'], policy.ASTRA)
            self.assertEqual(mismatch['status'], 'failed')

    def test_external_zero_blocks_routine_sol_without_a_new_pool(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'watchdog').mkdir()
            (root / 'watchdog/primary-external-admission').write_text('0')
            with mock.patch.dict(os.environ, MIPSTARRE_CODEX_MODEL=policy.SOL,
                                 MIPSTARRE_DISPATCH_ROLE='prover'), \
                 mock.patch('sys.argv', ['account_router.py', directory, 'auto', '123', '0',
                                        str(root / 'registry')]), self.assertRaises(SystemExit) as error:
                account_router.main()
            self.assertEqual(error.exception.code, 4)

    def test_post_activation_routine_shim_uses_sol_and_keeps_external_zero(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            local = root / 'local/bin'
            local.mkdir(parents=True)
            for name in ('model_policy.py', 'account_router.py', 'codex-policy-shim.sh'):
                shutil.copy2(ROOT / 'local/bin' / name, local / name)
            (local.parent / 'model-policy.json').write_text(json.dumps(ACTIVE))
            subprocess.run(['git', 'init', '-qb', 'main', str(root)], check=True)
            subprocess.run(['git', '-C', str(root), 'add', 'local'], check=True)
            subprocess.run(['git', '-C', str(root), '-c', 'user.name=Test', '-c',
                            'user.email=test@test', 'commit', '-qm', 'policy fixture'], check=True)
            binary = root / '.local/bin/codex'
            binary.parent.mkdir(parents=True)
            binary.write_text('#!/usr/bin/env python3\nimport json,sys\nprint(json.dumps(sys.argv))\n')
            binary.chmod(0o755)
            marker = root / 'cache/accounts/primary/123'
            marker.parent.mkdir(parents=True)
            marker.touch()
            env = dict(os.environ, HOME=directory, CODEX_HOME=str(root / '.codex'),
                MIPSTARRE_CACHE_ROOT=str(root / 'cache'), MIPSTARRE_DISPATCH_ROLE='prover',
                MIPSTARRE_JOB_CLASS='bounded', MIPSTARRE_HARDNESS_REASON='',
                MIPSTARRE_CODEX_MODEL='auto', MIPSTARRE_DISPATCH_ACCOUNT='primary',
                MIPSTARRE_DISPATCH_PID='123')
            args = ['bash', str(local / 'codex-policy-shim.sh'), 'exec', '--', 'fixture']
            result = subprocess.run(args, env=env, capture_output=True, text=True, check=True)
            self.assertIn(policy.SOL, json.loads(result.stdout))
            (root / 'cache/watchdog').mkdir()
            (root / 'cache/watchdog/primary-external-admission').write_text('0')
            self.assertEqual(subprocess.run(args, env=env, capture_output=True).returncode, 4)


if __name__ == '__main__':
    unittest.main()
