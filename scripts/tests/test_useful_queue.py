#!/usr/bin/env python3
"""Queue regressions: preserved scenarios consolidated into fake-process/API fixtures."""
import hashlib
from contextlib import ExitStack
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock
REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / 'local/bin'))
import useful_queue as queue
HEAD, PARENT = 'a' * 40, 'b' * 40

class QueueTests(unittest.TestCase):
    def patch(self, target, name, **kwargs):
        return self.stack.enter_context(mock.patch.object(target, name, **kwargs))
    def setUp(self):
        self.stack = ExitStack()
        self.addCleanup(self.stack.close)
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.base = Path(temporary.name)
        self.primary, self.worktree = self.base / 'repo', self.base / 'worktree'
        self.worktree.mkdir()
        self.task = self.base / 'task.md'
        self.task.write_text('Prove the explicitly selected lemma.\n')
        self.packet = dict(id='proof-257', kind='dispatch', issue=257,
            worktree=str(self.worktree), head=HEAD, parents=[], effort='xhigh', role='prover',
            task_file=str(self.task), task_sha256=hashlib.sha256(self.task.read_bytes()).hexdigest())
        self.host = self.patch(queue.router, 'host_processes', return_value=({}, {}))
        self.identity = self.patch(queue.router, 'process_identity', return_value='123')
        self.stack.enter_context(mock.patch.dict(os.environ, {}, clear=True))
        self.reset()
    def reset(self, name='cache'):
        self.root = self.base / name
        self.supervisor = queue.Supervisor(self.primary, self.root)
        self.directory = self.supervisor.directory
        self.config()
    def config(self, packets=None, enabled=True):
        queue.save(self.directory / 'queue.json', dict(version=1, enabled=enabled,
                   packets=[self.packet] if packets is None else packets))
    def review(self):
        return {key: value for key, value in dict(self.packet, kind='review', pr=258).items()
                if key not in ('role', 'task_file', 'task_sha256')}
    def tick(self, status=None, calls=0, run=True, error=None):
        with mock.patch.object(queue, 'packet_gate', return_value=self.task.read_text()), \
             mock.patch.object(queue, 'worktree_busy', return_value=False), \
             mock.patch.object(queue.subprocess, 'Popen', side_effect=error) as popen:
            popen.return_value.pid = 1000
            result = self.supervisor.tick(run)
        self.assertEqual(popen.call_count, calls)
        if status is not None: self.assertEqual(result['status'], status, result)
        return result
    def tickets(self): return queue.router.queue_tickets(self.root)
    def api(self):
        defaults = dict(issue_view={'state': 'open'}, api=[], pr_reviews=[],
            pr_view={'state': 'open', 'head': {'sha': HEAD, 'ref': 'issue-257-proof'}},
            latest_statuses={'local-ci/summary': {'state': 'success'}})
        return {name: self.patch(queue.gh_common, name, return_value=value)
                for name, value in defaults.items()}
    def fake_git(self, worktree, *args):
        if args == ('rev-parse', 'HEAD'): return HEAD
        if '--git-common-dir' in args: return str(self.primary / '.git')
        return 'issue-257-proof' if args[0] == 'symbolic-ref' else ''
    def test_opt_in_empty_queue_and_capacity(self):
        for enabled, run in ((False, False), (False, True), (True, False)):
            self.config(enabled=enabled)
            self.tick('disabled', run=run)
        self.config([])
        self.tick('idle')
        for name, live, interactive, settings, review, calls, cap in (
            ('review-full', 9, 1, {}, True, 0, 11), ('review-room', 8, 1, {}, True, 1, 11),
            ('external', 3, 4, {'max-codex-primary': 4, 'primary-external-reserved': 5},
             False, 0, 3), ):
            with self.subTest(name=name):
                self.reset(name)
                self.config([self.review() if review else self.packet])
                for key, value in settings.items():
                    queue.atomic_write(self.root / 'watchdog' / key, str(value))
                with mock.patch.object(queue.router, 'occupancy',
                                       return_value=([live, 0], [interactive, 0])):
                    result = self.tick(calls=calls)
                self.assertEqual(result['census']['caps'][0], cap)
                if calls: self.assertEqual(next(iter(self.tickets().values()))['slots'], 2)
                else:
                    self.assertIn('capacity', result['packets'][0]['reason'])
        self.reset('enabled')
        result = self.tick('admitted', calls=1)
        self.assertEqual(result['census']['workers_and_reservations'], [1, 0])
        self.assertIn('not server admission', result['limitation'])
    def test_terminal_and_uncertain_lifecycle_preserves_attempts(self):
        for scenario in ('stop', 'rename', 'missing', 'success', 'partial', 'restart', 'uncertain'):
            with self.subTest(scenario=scenario):
                self.reset(scenario)
                self.tick(calls=1, error=OSError('uncertain') if scenario == 'uncertain' else None)
                token = next(iter(self.tickets()))
                if scenario == 'stop':
                    (self.directory / 'STOP').touch()
                    self.config([self.packet, dict(self.packet, id='other', issue=999)])
                if scenario == 'rename': self.config([dict(self.packet, id='renamed')])
                if scenario in ('success', 'partial'):
                    queue.save(self.directory / self.packet['id'] / 'receipt.json',
                               dict(ok=scenario == 'success', token=token))
                if scenario == 'restart':
                    self.supervisor = queue.Supervisor(self.primary, self.root)
                with mock.patch.object(queue.router, 'process_identity',
                        side_effect=ProcessLookupError if scenario == 'missing' else None,
                        return_value='123'), mock.patch.object(queue.os, 'kill') as kill:
                    result = self.tick()
                kill.assert_not_called()
                self.assertEqual(bool(self.tickets()), scenario != 'success')
                expected = {'restart': 'active', 'success': 'idle', 'rename': 'held'}
                self.assertEqual(result['status'], expected.get(scenario, 'stopped'))
                if scenario == 'success': self.assertEqual(result['packets'][0]['status'], 'done')
    def test_corrupt_state_unobservable_host_and_single_admission(self):
        (self.directory / 'state.json').write_text('{broken')
        self.tick('held')
        self.assertEqual((self.directory / 'state.json').read_text(), '{broken')
        self.reset('host')
        with mock.patch.object(queue.router, 'host_processes', side_effect=PermissionError):
            self.tick('held')
        self.reset('single')
        self.config([self.packet, dict(self.packet, id='second-packet', issue=999)])
        self.assertEqual(self.tick(calls=1)['packets'][1]['status'], 'queued')
    def test_ticket_accounting_identity_and_duplicate_worktree(self):
        (self.root / 'accounts').mkdir()
        ticket = dict(slots=2, pid=1000, start='123', claims=[], worktree=str(self.worktree))
        queue.router.write_queue_tickets(self.root, {'token': ticket})
        self.assertEqual(queue.router.occupancy(self.root), ([2, 0], [1, 0]))
        self.assertTrue(queue.worktree_busy(self.packet, self.root))
        queue.atomic_write(self.root / 'watchdog/max-codex-primary', '2')
        with self.assertRaisesRegex(ValueError, 'capacity'):
            queue.router.reserve(self.root, 'primary', 1001, 0, True)
        self.host.return_value = ({1001: 1000}, {})
        self.stack.enter_context(mock.patch.dict(os.environ, {
            'MIPSTARRE_QUEUE_TICKET': 'token', 'MIPSTARRE_DISPATCH_WORKTREE': str(self.worktree)}))
        self.patch(queue.router.os, 'kill')
        self.assertEqual(queue.router.reserve(self.root, 'primary', 1001, 0, False), 'primary')
        self.assertEqual(queue.router.occupancy(self.root)[0], [2, 0])
        with self.assertRaisesRegex(ValueError, 'unused descendant'):
            queue.router.reserve(self.root, 'primary', 1001, 0, False)
        for token, account, parent, identity in (
            ('missing', 'primary', 1000, '123'), ('token', 'second', 1000, '123'),
            ('token', 'primary', 2000, '123'), ('token', 'primary', 1000, '456')):
            os.environ['MIPSTARRE_QUEUE_TICKET'] = token
            self.host.return_value, self.identity.return_value = ({1002: parent}, {}), identity
            with self.assertRaises(ValueError):
                queue.router.reserve(self.root, account, 1002, 0, False)
        (self.directory / 'STOP').touch()
        with self.assertRaisesRegex(ValueError, 'stopped'):
            queue.router.reserve(self.root, 'primary', 1002, 0, False)
        del os.environ['MIPSTARRE_QUEUE_TICKET']
        with self.assertRaisesRegex(ValueError, 'worktree reserved'):
            queue.router.reserve(self.root, 'primary', 1002, 0, True)
        queue.router.write_queue_tickets(self.root, {})
        (self.root / 'locks/review-258.lock').mkdir(parents=True)
        self.assertTrue(queue.worktree_busy(self.review(), self.root))
    def test_observed_refusals_progress_and_partial_logs(self):
        self.tick(calls=1)
        path = self.directory / self.packet['id'] / 'launch.log'
        events = [{'type': 'turn.completed'}, {'type': 'item.completed'},
                  {'type': 'error', 'message': 'Reconnecting: concurrency limit exceeded'}]
        path.write_text('\n'.join(map(json.dumps, events)) + '\n')
        result = self.tick('stopped')
        self.assertEqual([result['evidence'][str(path)][key]
                          for key in ('turns', 'items', 'retries', 'refusals')], [1, 1, 1, 1])
        self.assertEqual(self.tick()['evidence'][str(path)]['turns'], 1)
        (self.directory / 'HOLD').unlink()
        self.tick('active')
        path = self.base / 'partial'
        path.write_text('{"type":"turn.completed"')
        cursor = queue.observe(path, {})
        self.assertEqual(cursor['offset'], 0)
        path.write_text('{"type":"turn.completed"}\n' + json.dumps({
            'type': 'item.completed', 'item': {'output': 'test concurrency refusal'}}) + '\n')
        cursor = queue.observe(path, cursor)
        self.assertEqual((cursor['turns'], cursor['refusals']), (1, 0))
        path.write_text('')
        with self.assertRaisesRegex(ValueError, 'truncated'): queue.observe(path, cursor)
    def test_schema_environment_and_canonical_handoff_guards(self):
        for field, value in (('command', 'touch /tmp/injection'), ('resume', 'thread'),
                             ('effort', 'low'), ('role', 'orc'), ('kind', 'merge')):
            self.config([dict(self.packet, **{field: value})])
            with self.subTest(field=field), self.assertRaises(ValueError):
                queue.configuration(self.directory / 'queue.json')
        with mock.patch.dict(os.environ, {'CODEX_HOME': '/second',
                'MIPSTARRE_CODEX_ACCOUNT': 'second', 'MIPSTARRE_PERSONA_REF': 'evil',
                'MIPSTARRE_REVIEW_EFFORT': 'low', 'LOCAL_REVIEW_ENABLED': 'false'}):
            environment = queue.child_environment(self.root)
        self.assertFalse({'CODEX_HOME', 'MIPSTARRE_PERSONA_REF'} & environment.keys())
        self.assertEqual([environment[key] for key in ('MIPSTARRE_CODEX_ACCOUNT',
            'MIPSTARRE_CODEX_MODEL', 'MIPSTARRE_ACCOUNT_WAIT', 'LOCAL_REVIEW_ENABLED')],
            ['primary', 'gpt-6-astra', '0', 'false'])
        for filename, markers in {
            'review.sh': ['[ -z "${MIPSTARRE_QUEUE_TICKET:-}" ]', '[ "$ROUND" -le 4 ]',
                          'MIPSTARRE_QUEUE_EXPECTED_HEAD'],
            'dispatch.sh': ['queued worktree head moved', 'features.multi_agent=false',
                            'queued dispatch must be a fresh one-shot session']}.items():
            for marker in markers:
                self.assertIn(marker, (REPO_ROOT / 'local/bin' / filename).read_text())
    def test_parent_merge_binding_task_integrity_and_dirty_worktree(self):
        api = self.api()
        self.patch(queue, 'git', side_effect=self.fake_git)
        api['api'].return_value = [{'number': 256, 'state': 'closed'}]
        with self.assertRaisesRegex(ValueError, 'parent bindings'):
            queue.packet_gate(self.packet, self.primary, self.root)
        self.packet['parents'] = [dict(issue=256, pr=255, merge_sha=PARENT)]
        api['pr_view'].return_value = dict(merged=False, merge_commit_sha=PARENT)
        with self.assertRaisesRegex(ValueError, 'not confirmed'):
            queue.packet_gate(self.packet, self.primary, self.root)
        api['pr_view'].return_value['merged'] = True
        api['issue_view'].side_effect = lambda number: {
            'state': 'open' if number == 257 else 'closed'}
        self.assertEqual(queue.packet_gate(self.packet, self.primary, self.root),
                         self.task.read_text())
        self.task.write_text('Changed task')
        with self.assertRaisesRegex(ValueError, 'changed'):
            queue.packet_gate(self.packet, self.primary, self.root)
        with mock.patch.object(queue, 'git',
                side_effect=[HEAD, str(self.primary / '.git'), ' M file']), \
             self.assertRaisesRegex(ValueError, 'dirty'):
            queue.packet_gate(self.packet, self.primary, self.root)
    def test_review_gate_exact_ci_publication_cap_and_prior_runtime(self):
        api, packet = self.api(), self.review()
        queue.review_evidence(packet)
        for state, reason in (({}, 'CI'), ({'local-ci/summary': {'state': 'success'},
                                           'local-review/summary': {'state': 'pending'}},
                                          'already exists')):
            api['latest_statuses'].return_value = state
            with self.assertRaisesRegex(ValueError, reason): queue.review_evidence(packet)
        api['latest_statuses'].return_value = {'local-ci/summary': {'state': 'success'}}
        api['pr_view'].return_value['head']['sha'] = PARENT
        with self.assertRaisesRegex(ValueError, 'head moved'): queue.review_evidence(packet)
        api['pr_view'].return_value['head']['sha'] = HEAD
        api['pr_reviews'].return_value = [dict(commit_id=HEAD,
            body=f'<!-- mipstarre-review pr=258 head={HEAD} -->')]
        for finished, reason in ((False, 'already exists'), (True, 'partial')):
            with self.assertRaisesRegex(ValueError, reason):
                queue.review_evidence(packet, finished=finished)
        api['latest_statuses'].return_value['local-review/summary'] = {'state': 'failure'}
        queue.review_evidence(packet, finished=True)
        self.patch(queue, 'git', side_effect=self.fake_git)
        with mock.patch.dict(os.environ, {'LOCAL_REVIEW_ENABLED': 'false'}), \
             self.assertRaisesRegex(ValueError, 'kill switch'):
            queue.packet_gate(packet, self.primary, self.root)
        (self.root / 'reviews/pr258' / HEAD).mkdir(parents=True)
        with self.assertRaisesRegex(ValueError, 'prior review runtime'):
            queue.packet_gate(packet, self.primary, self.root)
        del api['latest_statuses'].return_value['local-review/summary']
        api['pr_reviews'].return_value = [
            dict(body=f'<!-- mipstarre-review pr=258 head={number:040x} -->')
            for number in range(4)]
        with self.assertRaisesRegex(ValueError, 'four review rounds'): queue.review_evidence(packet)
        api['pr_reviews'].return_value[-1]['body'] += '<!-- mipstarre-review-carried from=old -->'
        queue.review_evidence(packet)
    def test_execute_identity_one_shot_effort_and_publication(self):
        self.tick(calls=1)
        with mock.patch.object(queue.subprocess, 'run') as run, \
             self.assertRaisesRegex(ValueError, 'matching live'):
            queue.execute(self.primary, self.root, self.packet['id'])
        run.assert_not_called()
        tickets = self.tickets()
        token, ticket = next(iter(tickets.items()))
        ticket['pid'] = os.getpid()
        queue.router.write_queue_tickets(self.root, tickets)
        name = 'prover-257-20260906-01'
        (self.directory / self.packet['id'] / 'launch.log').write_text(f'name: {name}\n')
        published = self.primary / 'results/telemetry/sessions'
        published.mkdir(parents=True)
        for suffix in ('.jsonl', '.last.md'):
            (published / f'{name}{suffix}').write_text('fake published evidence\n')
        self.patch(queue, 'packet_gate', return_value=self.task.read_text())
        self.patch(queue.router, 'session_rows',
                   return_value=[dict(name=name, thread_id='test-thread', exit=0)])
        run = self.patch(queue.subprocess, 'run', return_value=mock.Mock(returncode=0))
        self.assertEqual(queue.execute(self.primary, self.root, self.packet['id']), 0)
        command = run.call_args.args[0]
        self.assertEqual(command[0], str(self.primary / 'local/bin/dispatch.sh'))
        self.assertEqual(command[command.index('--effort') + 1], 'xhigh')
        self.assertNotIn('--resume', command)
        self.assertNotIn('shell', run.call_args.kwargs)
        self.assertEqual(run.call_args.kwargs['env']['MIPSTARRE_QUEUE_TICKET'], token)
        with self.assertRaisesRegex(ValueError, 'one-shot intent'):
            queue.execute(self.primary, self.root, self.packet['id'])
if __name__ == '__main__': unittest.main()
