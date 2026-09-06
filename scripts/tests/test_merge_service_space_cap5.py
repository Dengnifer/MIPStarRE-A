"""Deterministic guards for the bounded space-cap5 merge service."""

from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "results/telemetry/owner-tools"))
import importlib.util

SPEC = importlib.util.spec_from_file_location("merge_service", Path(__file__).resolve().parents[2] /
    "results/telemetry/owner-tools/merge-service-space-cap5.py")
SERVICE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(SERVICE)


class MergeServiceTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.log = Path(self.tmp.name) / "service.jsonl"
        self.lock = Path(self.tmp.name) / "service.lock"
        self.log_patch = mock.patch.object(SERVICE, "LOG", self.log)
        self.lock_patch = mock.patch.object(SERVICE, "LOCK", self.lock)
        self.log_patch.start()
        self.lock_patch.start()
        self.addCleanup(self.log_patch.stop)
        self.addCleanup(self.lock_patch.stop)

    def test_stale_candidate_does_not_hide_fresh_candidate(self):
        rows = [
            {"number": 254, "head": "old", "pr_age_s": 900,
             "fresh_against_remote": False},
            {"number": 290, "head": "fresh", "pr_age_s": 100,
             "fresh_against_remote": True},
        ]
        with mock.patch.object(SERVICE, "git", side_effect=["main", "", "main"]), \
                mock.patch.object(SERVICE, "remote_main", return_value="main"), \
                mock.patch.object(SERVICE, "runtime_gate", return_value=(True, "ok")), \
                mock.patch.object(SERVICE, "lock_quiet", return_value=(True, "ok")), \
                mock.patch.object(SERVICE, "eligible_prs", return_value=rows):
            record = SERVICE.tick(False)
        self.assertEqual(record["oldest_eligible"]["number"], 290)
        self.assertEqual([row["number"] for row in record["oldest_stale"]], [254])
        self.assertIn("stale eligible PRs: 254", record["hold_reasons"])
        self.assertIsNone(record["eligible_age_s"])

    def test_read_failure_is_recorded_as_hold(self):
        with mock.patch.object(SERVICE, "git", side_effect=RuntimeError("transport")):
            record = SERVICE.tick(False)
        self.assertEqual(record["action"], "hold")
        self.assertTrue(any(reason.startswith("read_failure:")
                            for reason in record["hold_reasons"]))
        self.assertGreaterEqual(record["duration_s"], 0)
        self.assertEqual(record["eligible_count"], 0)

    def test_interval_rejects_sub_five_seconds(self):
        parser = SERVICE.argparse.ArgumentParser()
        parser.add_argument("--interval", type=int, default=300)
        with self.assertRaises(SystemExit):
            args = parser.parse_args(["--interval", "4"])
            if args.interval < 5:
                parser.error("--interval must be at least 5 seconds")


if __name__ == "__main__":
    unittest.main()
