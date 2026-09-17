import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location('sampler', Path(__file__).with_name(
    'qpbt-worker-live-sampler-20260908.py'))
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


def timestamp(seconds):
    return module.datetime.fromtimestamp(seconds, module.timezone.utc).isoformat()


def event(seconds, kind, turn=None, **extra):
    payload = dict(type=kind, **extra)
    if turn:
        payload['turn_id'] = turn
    return dict(timestamp=timestamp(seconds), type='event_msg', payload=payload)


class LifecycleTests(unittest.TestCase):
    def worker(self):
        return module.Worker(dict(id='child', parent_thread_id='root',
                                  timestamp=timestamp(100), agent_path='/root/useful'))

    def test_completed_with_recent_output_is_inactive(self):
        worker = self.worker()
        for row in (event(101, 'task_started', 'a'), event(102, 'token_count'),
                    event(103, 'task_complete', 'a'), event(104, 'agent_message')):
            worker.consume(row)
        result = worker.report(105, 180)
        self.assertEqual(result['state'], 'inactive')
        self.assertFalse(result['live_unclosed'])
        self.assertEqual(result['latest_event'], 'task_complete')

    def test_resume_new_turn_is_active_and_old_terminal_does_not_close_it(self):
        worker = self.worker()
        for row in (event(101, 'task_started', 'a'), event(102, 'task_complete', 'a'),
                    event(110, 'task_started', 'b'), event(111, 'function_call', 'b'),
                    event(112, 'task_complete', 'a')):
            worker.consume(row)
        result = worker.report(113, 180)
        self.assertEqual((result['state'], result['turn_id']), ('live_recent', 'b'))

    def test_stale_live_is_separate_from_confirmed_activity(self):
        worker = self.worker()
        worker.consume(event(101, 'task_started', 'a'))
        self.assertEqual(worker.report(102, 180)['state'], 'live_unknown')
        worker.consume(event(102, 'token_count'))
        self.assertEqual(worker.report(400, 180)['state'], 'live_stale')

    def test_inherited_parent_history_is_ignored(self):
        worker = self.worker()
        worker.consume(event(90, 'task_started', 'parent-turn'))
        worker.consume(event(99, 'token_count'))
        result = worker.report(101, 180)
        self.assertEqual(result['state'], 'unknown')
        self.assertFalse(result['live_unclosed'])

    def test_aborted_recent_turn_is_inactive(self):
        worker = self.worker()
        worker.consume(event(101, 'task_started', 'a'))
        worker.consume(event(102, 'item_completed', 'a'))
        worker.consume(event(103, 'turn_aborted', 'a'))
        self.assertEqual(worker.report(104, 180)['state'], 'inactive')

    def test_only_descendants_count_and_incremental_partial_lines_wait(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            for identity, parent in (('root', None), ('child', 'root'),
                                     ('grandchild', 'child'), ('unrelated', 'other')):
                meta = dict(type='session_meta', payload=dict(id=identity,
                    timestamp=timestamp(100), source=dict(subagent=dict(thread_spawn=dict(
                        parent_thread_id=parent)))))
                rows = [meta, event(101, 'task_started', identity), event(102, 'token_count')]
                (path / (identity + '.jsonl')).write_text(''.join(json.dumps(r) + '\n' for r in rows))
            sampler = module.Sampler(path, 'root')
            first = sampler.sample(103, 180)
            self.assertEqual((first['confirmed_active'], first['live_unclosed']), (2, 2))
            self.assertEqual({w['id'] for w in first['workers']}, {'child', 'grandchild'})
            with (path / 'child.jsonl').open('a') as handle:
                handle.write(json.dumps(event(104, 'task_complete', 'child')))
            self.assertEqual(sampler.sample(105, 180)['confirmed_active'], 2)
            with (path / 'child.jsonl').open('a') as handle:
                handle.write('\n')
            final = sampler.sample(106, 180)
            self.assertEqual((final['confirmed_active'], final['counts']['inactive']), (1, 1))


if __name__ == '__main__':
    unittest.main()
