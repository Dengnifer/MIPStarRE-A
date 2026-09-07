"""Isolated model-policy and exact-recipe tests; no model sessions are launched."""

import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'local/bin'))
import model_job
import model_policy as policy
import native_review
import telemetry
from scripts.tests import test_native_workflow as native_tests
THREAD_ROOT, CHILD = native_tests.ROOT, native_tests.CHILD


def qualification():
    return dict(schema_version=1, audit=dict(reference='independent-fixture', sha256='a' * 64),
        qualified_job_classes={policy.CLEANUP: dict(roles=['prover'], model=policy.SOL,
            effort='ultra', rationale='C01/C02 exact adjudicated replacements', case_ids=['C01', 'C02'])})


class ModelPolicyTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.worktree = self.root / 'worktree'
        self.worktree.mkdir()
        self.file = self.worktree / 'MIPStarRE/Test.lean'
        self.file.parent.mkdir()
        self.file.write_text('/-- Old wording. -/\ntheorem old_name : True := by trivial\n'
                             'example : True := old_name\n')
        subprocess.run(['git', 'init', '-qb', 'main', str(self.worktree)], check=True)
        subprocess.run(['git', '-C', str(self.worktree), 'add', '.'], check=True)
        subprocess.run(['git', '-C', str(self.worktree), '-c', 'user.name=Test', '-c',
            'user.email=test@test', 'commit', '-qm', 'base'], check=True)
        self.base = model_job.git(self.worktree, 'rev-parse', 'HEAD').strip()
        blob = model_job.git(self.worktree, 'rev-parse', 'HEAD:MIPStarRE/Test.lean').strip()
        self.recipe = dict(worktree=str(self.worktree), base_sha=self.base,
            review_reference='Astra exact replacement specification',
            allowed_edits=[dict(path='MIPStarRE/Test.lean', before_blob=blob,
                hunks=[dict(old_start=1, before=['/-- Old wording. -/'],
                            after=['/-- Prescribed wording. -/'])])])
        self.request = dict(nonce='fixture', root_thread_id=THREAD_ROOT,
            created='2026-09-06T13:13:00Z', pid=100, start='123', recipe=self.recipe)
        self.request['digest'] = model_job.digest(self.request)
        self.reference = self.root / 'model-jobs/fixture.json'
        self.reference.parent.mkdir()
        self.reference.write_text(json.dumps(self.request))
        for patch in (mock.patch.dict(os.environ, MIPSTARRE_CACHE_ROOT=str(self.root),
                                     CODEX_THREAD_ID=THREAD_ROOT),
                      mock.patch.object(native_review, 'verify_root',
                                        return_value=dict(pid=100, start='123'))):
            patch.start()
            self.addCleanup(patch.stop)

    def test_qualified_selection_and_explicit_astra_fallback(self):
        with mock.patch.object(policy, 'load_policy', return_value=qualification()):
            selected = policy.select_model('prover', policy.CLEANUP, 'auto',
                                            job_spec=str(self.reference))
            self.assertEqual(selected['model'], policy.SOL)
            self.assertEqual(selected['requested_model'], 'auto')
            self.assertEqual(selected['case_ids'], ['C01', 'C02'])
            self.assertEqual(policy.select_model('prover', policy.CLEANUP)['model'], policy.ASTRA)
            self.assertEqual(policy.select_model('prover', policy.CLEANUP, policy.ASTRA,
                job_spec=str(self.reference))['model'], policy.ASTRA)
            with self.assertRaises(ValueError):
                policy.observe_model('prover', policy.CLEANUP, policy.SOL, 'ultra',
                                     job_spec=str(self.reference))

    def test_unqualified_unknown_role_class_model_and_effort_fail_closed(self):
        with mock.patch.object(policy, 'load_policy', return_value=dict(qualified_job_classes={},
                                                                       audit=None)):
            for role in policy.ROLES:
                self.assertEqual(policy.select_model(role)['model'], policy.ASTRA)
            for args in [('bad',), ('prover', 'bad'), ('reviewer', policy.CLEANUP),
                         ('prover', 'general', policy.SOL), ('prover', 'general', 'gpt-5.6'),
                         ('prover', 'general', 'gpt-6-sol'),
                         ('prover', 'general', policy.ASTRA, 'max')]:
                with self.subTest(args=args), self.assertRaises(ValueError):
                    policy.select_model(*args)

    def test_request_authority_base_digest_and_exact_result(self):
        with mock.patch.object(policy, 'load_policy', return_value=qualification()):
            for changed in (dict(CODEX_THREAD_ID=CHILD),):
                with mock.patch.dict(os.environ, changed), self.assertRaises(ValueError):
                    policy.select_model('prover', policy.CLEANUP, policy.SOL,
                                        job_spec=str(self.reference))
            with self.assertRaises(ValueError):
                model_job.validate_job(str(self.reference), str(self.root))
            output = model_job.recipe_outputs(self.recipe)['MIPStarRE/Test.lean']
            self.file.write_text(output)
            model_job.validate_job(str(self.reference), completed=True)
            for text in (output.replace('Prescribed', 'Mathematically different'),
                         output.replace(': True', '(h : False) : True')):
                self.file.write_text(text)
                with self.assertRaises(ValueError):
                    model_job.validate_job(str(self.reference), completed=True)
            self.file.write_text(output)
            (self.worktree / 'extra').touch()
            with self.assertRaises(ValueError):
                model_job.validate_job(str(self.reference), completed=True)
            bad = dict(self.request, created='changed')
            self.reference.write_text(json.dumps(bad))
            with self.assertRaises(ValueError):
                model_job.read_job(str(self.reference))

    def test_recipe_rejects_proof_paths_limits_and_string_changes(self):
        for change in (dict(path='local/bin/dispatch.sh'), dict(path='../MIPStarRE/Test.lean'),
                       dict(path='blueprint/src/chapter/test.tex'), dict(before_blob='0' * 40),
                       dict(hunks=[dict(old_start=2, before=['theorem old_name : True := by trivial'],
                            after=['theorem old_name (h : False) : True := by trivial'])])):
            recipe = copy.deepcopy(self.recipe)
            recipe['allowed_edits'][0].update(change)
            with self.subTest(change=change), self.assertRaises(ValueError):
                model_job.recipe_outputs(recipe)
        renamed = copy.deepcopy(self.recipe)
        renamed['renames'] = {'old_name': 'new_name'}
        renamed['allowed_edits'][0]['hunks'] = [dict(old_start=2,
            before=['theorem old_name : True := by trivial', 'example : True := old_name'],
            after=['theorem new_name : True := by trivial', 'example : True := new_name'])]
        self.assertIn('theorem new_name', model_job.recipe_outputs(renamed)['MIPStarRE/Test.lean'])
        renamed['renames'] = {'True': 'False'}
        with self.assertRaises(ValueError):
            model_job.recipe_outputs(renamed)

    def test_root_only_request_issuance(self):
        with mock.patch.dict(os.environ, CODEX_THREAD_ID=CHILD), \
             mock.patch('sys.argv', ['model_job.py', str(self.reference), '--root-thread-id', THREAD_ROOT]), \
             self.assertRaises(SystemExit) as failure:
            model_job.main()
        self.assertEqual(failure.exception.code, 4)

    def test_native_qualified_child_and_mixed_or_unbound_contexts(self):
        fixture = native_tests.NativeWorkflowTests()
        fixture.setUp()
        self.addCleanup(fixture.doCleanups)
        fixture.write_rollout()
        rows = [json.loads(line) for line in fixture.rollout.read_text().splitlines()]
        for row in rows:
            if row['type'] == 'turn_context':
                row['payload'].update(model=policy.SOL, turn_id='turn')
            if row['type'] == 'response_item':
                row['payload']['content'] = [dict(type='input_text',
                    text='Native model binding: ' + self.request['digest'])]
        def write():
            fixture.rollout.write_text(''.join(json.dumps(row) + '\n' for row in rows))
        write()
        with mock.patch.object(policy, 'load_policy', return_value=qualification()):
            observation = telemetry.native_rollout(fixture.rollout, CHILD, role='prover',
                job_class=policy.CLEANUP, requested_model=policy.SOL, job_spec=str(self.reference))
            self.assertEqual(observation['effective_model'], policy.SOL)
            with self.assertRaises(ValueError):
                telemetry.native_rollout(fixture.rollout, CHILD, role='reviewer',
                                         job_class='independent_review', requested_model=policy.ASTRA)
            for row in rows:
                if row['type'] == 'turn_context':
                    row['payload'].pop('turn_id', None)
            rows.insert(-1, dict(type='turn_context', payload=dict(model=policy.SOL, effort='ultra')))
            write()
            with self.assertRaises(ValueError):
                telemetry.native_rollout(fixture.rollout, CHILD, role='reviewer',
                                         job_class='independent_review', requested_model=policy.ASTRA)
            rows.append(dict(type='turn_context', payload=dict(turn_id='turn',
                             model=policy.ASTRA, effort='ultra')))
            write()
            with self.assertRaises(ValueError):
                telemetry.native_rollout(fixture.rollout, CHILD, role='reviewer',
                                         job_class='independent_review', requested_model=policy.ASTRA)

    def test_external_zero_refuses_even_a_qualified_sol_job(self):
        import account_router
        (self.root / 'watchdog').mkdir()
        (self.root / 'watchdog/primary-external-admission').write_text('0')
        with mock.patch.object(policy, 'load_policy', return_value=qualification()), \
             mock.patch.dict(os.environ, MIPSTARRE_CODEX_MODEL=policy.SOL,
                 MIPSTARRE_DISPATCH_ROLE='prover', MIPSTARRE_JOB_CLASS=policy.CLEANUP,
                 MIPSTARRE_JOB_SPEC=str(self.reference)), \
             mock.patch('sys.argv', ['account_router.py', str(self.root), 'auto', '123', '0',
                                    str(self.root / 'registry')]), \
             self.assertRaises(SystemExit) as failure:
            account_router.main()
        self.assertEqual(failure.exception.code, 4)
        self.assertFalse(list((self.root / 'accounts').glob('*/*[0-9]')))


if __name__ == '__main__':
    unittest.main()
