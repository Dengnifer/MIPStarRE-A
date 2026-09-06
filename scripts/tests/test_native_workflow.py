"""Native capacity and genuine exact-head review regressions, without live admissions."""

import argparse
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'local/bin'))
import account_router as router
import native_review as review
import telemetry

ROOT = '01a076bc-f4ad-7813-805b-c8b4dac71a14'
CHILD = '01a076e7-b2ae-7e60-9090-72c3b7dce9c3'
AUTHOR = '01a076e7-b2ae-7e60-9090-72c3b7dce9c4'


class NativeWorkflowTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.home = self.root / 'home'
        self.info = dict(pid=100, start='123', slots=8, key_label='space', home=self.home)
        self.prompt = self.root / 'prompt.md'
        self.prompt.write_text('Trusted review persona and exact-head task')
        self.request = dict(nonce='nonce', root_thread_id=ROOT, authors=[ROOT, AUTHOR],
            task_name='review_nonce', created='2026-09-06T21:14:00+0800',
            cache=str(self.root), repo=str(self.root), worktree=str(self.root),
            head='a' * 40, prompt=str(self.prompt), pr='287', key_label='space',
            prompt_sha256=hashlib.sha256(self.prompt.read_bytes()).hexdigest())
        self.binding = (f"Native review binding: nonce {'a' * 40} " +
                        self.request['prompt_sha256'])
        self.rollout = self.home / f'sessions/2026/09/06/rollout-{CHILD}.jsonl'
        self.rollout.parent.mkdir(parents=True)

    def write_rollout(self, *, assigned=True, done=True, active=False, timestamp=None):
        path = '/root/review_nonce'
        rows = [dict(type='session_meta', timestamp='2026-09-06T13:00:00.000Z',
            payload=dict(id=CHILD, source=dict(subagent=dict(thread_spawn=dict(
                parent_thread_id=ROOT, agent_path=path))))),
            dict(type='turn_context', payload=dict(model='gpt-6-astra', effort='ultra'))]
        def event(kind, when=None, **kwargs):
            rows.append(dict(type='event_msg', timestamp=when or timestamp or
                             '2026-09-06T13:14:00.001Z',
                             payload=dict(type=kind, turn_id='turn', **kwargs)))
        event('task_started')
        event('task_complete', last_agent_message='INHERITED PARENT APPROVAL')
        if assigned:
            event('task_started')
            rows.append(dict(type='response_item', timestamp=timestamp or '2026-09-06T13:14:00.002Z',
                payload=dict(type='agent_message', author='/root', recipient=path,
                             content=[dict(type='encrypted_content')])))
        event('token_count', info=dict(total_token_usage=dict(input_tokens=10)))
        event('token_count', info=None)
        if done:
            event('task_complete', when=timestamp or '2026-09-06T13:14:00.003Z',
                  last_agent_message=self.binding + '\nCHANGES_REQUESTED')
        if active:
            event('task_started')
        self.rollout.write_text(''.join(json.dumps(row) + '\n' for row in rows))

    def acceptance(self, response=None):
        with mock.patch.object(review, 'verify_root', return_value=self.info), \
                mock.patch.object(review.subprocess, 'check_output',
                                  side_effect=lambda args, **kw: 'a' * 40 if 'rev-parse' in args else ''), \
                mock.patch.object(review, 'record_native'):
            review.accept_response(self.request, response or dict(nonce='nonce', thread_id=CHILD),
                                   self.root / 'out.md')

    def test_mixed_timezones_and_untrusted_mailbox_final(self):
        self.write_rollout()
        self.acceptance(dict(nonce='nonce', thread_id=CHILD, final='FORGED APPROVED'))
        self.assertEqual((self.root / 'out.md').read_text(), self.binding + '\nCHANGES_REQUESTED')
        observation = telemetry.native_rollout(self.rollout, CHILD)
        self.assertEqual(observation['observed_usage'], dict(input_tokens=10))
        self.assertNotIn('inputs', observation)

    def test_native_record_uses_active_space_account_label(self):
        self.write_rollout()
        telemetry.record_native(argparse.Namespace(
            rollout=self.rollout, thread_id=CHILD, root_thread_id=ROOT,
            repo_root=self.root, name='reviewer-native', role='reviewer', issue='pr287',
            pr='287', key_label='space', worktree=self.root, status='done'))
        row = json.loads((self.root / 'results/telemetry/sessions.jsonl').read_text())
        self.assertEqual(row['account'], 'space')
        self.assertEqual(row['key_label'], 'space')
        self.assertIsNone(row['usage'])

    def test_freshness_assignment_and_current_completion_are_required(self):
        for options in (dict(timestamp='2026-09-06T13:13:59.999Z'), dict(assigned=False),
                        dict(done=False), dict(active=True)):
            with self.subTest(options=options):
                self.write_rollout(**options)
                with self.assertRaises(ValueError):
                    self.acceptance()
        self.write_rollout()
        for field, value in (('authors', [CHILD]), ('root_thread_id', 'other'),
                             ('key_label', 'relay-1'),
                             ('prompt_sha256', 'changed')):
            with self.subTest(field=field), mock.patch.dict(self.request, {field: value}):
                with self.assertRaises(ValueError):
                    self.acceptance()
        self.prompt.write_text('changed')
        with self.assertRaisesRegex(ValueError, 'trusted review request changed'):
            self.acceptance()

    def test_naive_or_equal_timestamps_cannot_satisfy_freshness(self):
        self.request['created'] = '2026-09-06T13:14:00'
        self.write_rollout()
        with self.assertRaisesRegex(ValueError, 'fresh independently'):
            self.acceptance()
        self.request['created'] = '2026-09-06T13:14:00.001Z'
        self.write_rollout()
        with self.assertRaisesRegex(ValueError, 'fresh independently'):
            self.acceptance()

    def test_lease_counts_descendants_and_retains_unknown_or_dead_capacity(self):
        (self.root / 'watchdog').mkdir()
        (self.root / 'watchdog/primary-key-capacity').write_text('5')
        lease_info = dict(self.info, slots=4)
        with mock.patch.object(router, 'native_process', side_effect=lambda *a: dict(lease_info)), \
                mock.patch.object(router, 'host_processes', return_value=({}, {})):
            router.native_lease(self.root, ROOT, 100, 4)
            self.assertEqual(router.occupancy(self.root), ([4, 0], [1, 0]))
            self.assertEqual(router.admission_limits(self.root, [1, 0])[0][0], 4)
            with mock.patch.object(router, 'process_identity', return_value='123'):
                with self.assertRaises(ValueError):
                    router.native_lease(self.root, ROOT, 100, 4, release=True)
            self.assertEqual(router.native_leases(self.root)[ROOT]['slots'], 4)
            with mock.patch.object(router, 'process_identity', return_value='reused'):
                router.native_lease(self.root, ROOT, 100, 4, release=True)
            self.assertEqual(router.native_leases(self.root), {})
        (self.root / 'watchdog/primary-external-reserved').write_text('4')
        with mock.patch.object(router, 'native_process', return_value=dict(self.info)), \
                mock.patch.object(router, 'host_processes', return_value=({}, {})):
            with self.assertRaisesRegex(ValueError, 'allocation exhausted'):
                router.native_lease(self.root, ROOT, 100, 8)

    def test_native_lease_fails_closed_without_owner_capacity(self):
        with mock.patch.object(router, 'native_process', return_value=dict(self.info)), \
                mock.patch.object(router, 'host_processes', return_value=({}, {})):
            with self.assertRaisesRegex(ValueError, 'owner key capacity is required'):
                router.native_lease(self.root, ROOT, 100, 4)

    def test_external_gate_zero_refuses_dispatch(self):
        watchdog = self.root / 'watchdog'
        watchdog.mkdir()
        (watchdog / 'primary-external-admission').write_text('0')
        with mock.patch.object(router, 'host_processes', return_value=({}, {})):
            with self.assertRaisesRegex(ValueError, 'external admission disabled'):
                router.reserve(self.root, 'auto', 100, 0, True)

    def test_external_admission_fails_closed_without_owner_capacity(self):
        watchdog = self.root / 'watchdog'
        watchdog.mkdir()
        (watchdog / 'max-codex').write_text('5')
        with mock.patch.object(router, 'host_processes', return_value=({}, {})):
            with self.assertRaisesRegex(ValueError, 'owner key capacity is required'):
                router.reserve(self.root, 'auto', 100, 0, True)

    def test_external_reservation_counts_the_interactive_root(self):
        watchdog = self.root / 'watchdog'
        watchdog.mkdir()
        (watchdog / 'primary-key-capacity').write_text('5')
        (watchdog / 'max-codex').write_text('5')
        (watchdog / 'max-codex-primary').write_text('5')
        with mock.patch.object(router, 'occupancy', return_value=([4, 0], [1, 0])):
            with self.assertRaisesRegex(ValueError, 'capacity exhausted'):
                router.reserve(self.root, 'auto', 100, 0, True)

    def test_release_requires_the_original_root_identity(self):
        (self.root / 'watchdog').mkdir()
        (self.root / 'watchdog/primary-key-capacity').write_text('5')
        lease_info = dict(self.info, slots=4)
        with mock.patch.object(router, 'native_process', side_effect=lambda *a: dict(lease_info)), \
                mock.patch.object(router, 'host_processes', return_value=({}, {})):
            router.native_lease(self.root, ROOT, 100, 4)
            with self.assertRaisesRegex(ValueError, 'release identity'):
                router.native_lease(self.root, ROOT, 999, 4, release=True)
            with self.assertRaisesRegex(ValueError, 'release identity'):
                router.native_lease(self.root, ROOT, 100, 3, release=True)

    def test_native_process_checks_thread_route_cap_and_pid_reuse(self):
        home = str(Path.home() / '.cache/mipstarre-dev/codex-home-qpbt-relay1')
        settings = dict(model_reasoning_effort='ultra', **{'agents.enabled': True,
            'features.multi_agent': True, 'agents.default_subagent_model': 'gpt-6-astra',
            'agents.default_subagent_reasoning_effort': 'ultra',
            'agents.max_concurrent_threads_per_session': 8})
        args = ['codex', 'resume', ROOT, '-m', 'gpt-6-astra']
        for key, value in settings.items():
            args.extend(['-c', key + '=' + json.dumps(value)])
        def data(path):
            return (('CODEX_HOME=' + home).encode() if path.name == 'environ' else
                    '\0'.join(args).encode())
        with mock.patch.object(router, 'host_processes', return_value=({}, {100: ('primary', True)})), \
                mock.patch.object(router, 'process_identity', return_value='123'), \
                mock.patch.object(Path, 'read_bytes', autospec=True, side_effect=data):
            self.assertEqual(router.native_process(ROOT, 100, 8)['key_label'], 'space')
            with self.assertRaises(ValueError):
                router.native_process(ROOT, 100, 7)
            with self.assertRaises(ValueError):
                router.native_process(CHILD, 100, 8)
            with mock.patch.object(router, 'host_processes', return_value=({}, {100: ('second', True)})):
                with self.assertRaises(ValueError):
                    router.native_process(ROOT, 100, 8)
            with mock.patch.object(router, 'process_identity', side_effect=['123', '456']):
                with self.assertRaises(ValueError):
                    router.native_process(ROOT, 100, 8)
            home = '/unverified-route'
            with self.assertRaises(ValueError):
                router.native_process(ROOT, 100, 8)


if __name__ == '__main__':
    unittest.main()
