#!/usr/bin/env python3
"""Unit tests for ``local/bin/session/key-watch.sh``.

The point of these tests is the decision table.  A hint (pane text, a worker
log) must never be enough to take a key out of use; only a direct probe of that
key's own endpoint is.  The probes go through the real ``probe-key.sh`` against
a stub ``curl`` whose canned answers the test chooses, so the whole path from
answer to decision to consequence is covered.
"""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from test_session_tools import SessionHarness  # noqa: E402


class KeyWatchHarness(SessionHarness):
    def setUp(self):
        super().setUp()
        self.key_home("mainkey")
        self.key_home("workerkey")
        (self.state / "main-key").write_text("mainkey\n")
        for name in ("max-codex-primary", "max-codex-second", "max-codex"):
            (self.state / name).write_text("2\n" if name != "max-codex-second" else "0\n")

    def watch(self, *args, **envextra):
        env = {
            "KIT_KEY_HOME_MAINKEY": str(self.root / "codex-home-mainkey"),
            "KIT_KEY_HOME_WORKERKEY": str(self.root / "codex-home-workerkey"),
            "KIT_KEYWATCH_RECHECK_S": "0",
            "KIT_KEYWATCH_CONFIRM_GAP": "0",
            "KIT_MAIN_KEY": "mainkey",
        }
        env.update(envextra)
        return self.run_script("key-watch.sh", *args, **env)

    def decision(self, result) -> str:
        for line in result.stdout.splitlines():
            if line.startswith("decision="):
                return line.split()[0].split("=", 1)[1]
        self.fail(f"no decision printed: {result.stdout}\n{result.stderr}")

    def probe_count(self) -> int:
        if not self.curl_log.exists():
            return 0
        return len([l for l in self.curl_log.read_text().splitlines() if l.strip()])


class DecisionTableTests(KeyWatchHarness):
    def test_a_body_that_names_a_quota_refusal_retires_after_one_probe(self):
        self.reply(1, '{"error":{"code":"insufficient_quota","message":"quota exhausted"}}', 429)
        result = self.watch("confirm", "workerkey", "a worker log showed an error")
        self.assertEqual(self.decision(result), "retire", result.stdout)
        self.assertEqual(self.probe_count(), 1, "one probe is enough for an explicit refusal")

    def test_a_bare_refusal_code_needs_two_probes(self):
        self.reply(1, '{"error":"forbidden"}', 403)
        self.reply(2, '{"error":"forbidden"}', 403)
        result = self.watch("confirm", "workerkey", "the pane showed a 403")
        self.assertEqual(self.decision(result), "retire", result.stdout)
        self.assertEqual(self.probe_count(), 2)
        self.assertIn("two direct probes confirm", (self.state / "key-disabled" / "workerkey").read_text())

    def test_a_refusal_that_does_not_repeat_is_transient(self):
        self.reply(1, '{"error":"service unavailable"}', 503)
        self.reply(2, '{"output":"ok"}', 200)
        result = self.watch("confirm", "workerkey", "the pane showed a 503")
        self.assertEqual(self.decision(result), "transient", result.stdout)
        self.assertFalse((self.state / "key-disabled" / "workerkey").exists())

    def test_a_healthy_probe_means_the_hint_was_not_evidence(self):
        self.reply(1, '{"output":"ok"}', 200)
        result = self.watch("confirm", "workerkey",
                            "the pane quoted an error string out of a diff")
        self.assertEqual(self.decision(result), "not-retired", result.stdout)
        self.assertEqual(self.probe_count(), 1)
        self.assertFalse((self.state / "key-disabled" / "workerkey").exists())
        self.assertIn("not evidence", (self.state / "key-watch.log").read_text())

    def test_a_probe_that_cannot_reach_anything_never_retires_a_key(self):
        # no canned reply at all: the stub prints nothing, so there is no HTTP code
        result = self.watch("confirm", "workerkey", "the machine lost its network")
        self.assertEqual(self.decision(result), "not-retired", result.stdout)
        self.assertFalse((self.state / "key-disabled" / "workerkey").exists())

    def test_the_confirmation_is_throttled(self):
        self.reply(1, '{"output":"ok"}', 200)
        self.watch("confirm", "workerkey", "first hint", KIT_KEYWATCH_CONFIRM_GAP="600")
        before = self.probe_count()
        result = self.watch("confirm", "workerkey", "second hint", KIT_KEYWATCH_CONFIRM_GAP="600")
        self.assertEqual(self.decision(result), "throttled", result.stdout)
        self.assertEqual(self.probe_count(), before, "a throttled check must not spend the key")


class ConsequenceTests(KeyWatchHarness):
    def test_retiring_a_worker_key_turns_off_its_rotation_and_lowers_the_caps(self):
        rot = self.cache / "keyrot" / "workerkey"
        rot.mkdir(parents=True)
        (rot / ".limit").write_text("2\n")
        result = self.watch("retire", "workerkey", "out of quota")
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        self.assertTrue((self.state / "key-disabled" / "workerkey").exists())
        self.assertFalse(rot.exists(), "the key is still in the worker rotation")
        self.assertTrue((self.cache / "keyrot-off" / "workerkey").exists())
        self.assertEqual((self.state / "max-codex-primary").read_text().strip(), "1")
        self.assertEqual((self.state / "max-codex").read_text().strip(), "1")
        self.assertFalse((self.state / "cutoff").exists(), "a worker key must not cut off the project")

    def test_retiring_the_main_sessions_key_writes_the_cutoff_marker(self):
        result = self.watch("retire", "mainkey", "out of quota")
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        self.assertTrue((self.state / "key-disabled" / "main").exists())
        self.assertTrue((self.state / "cutoff").exists())
        self.assertEqual((self.state / "max-codex").read_text().strip(), "0")
        self.assertTrue((self.state / "goal-keeper.stop").exists(),
                        "the goal keeper must not re-send a goal into a cut-off session")
        self.assertIn("NOT a pause", (self.state / "key-watch.log").read_text())

    def test_a_retired_key_is_never_brought_back_or_retired_twice(self):
        self.watch("retire", "workerkey", "out of quota")
        caps = (self.state / "max-codex-primary").read_text()
        reason = (self.state / "key-disabled" / "workerkey").read_text()
        self.reply(1, '{"output":"ok"}', 200)
        again = self.watch("confirm", "workerkey", "another hint")
        self.assertEqual(self.decision(again), "already-retired")
        self.assertEqual(self.probe_count(), 0, "a retired key must not be probed again")
        self.watch("retire", "workerkey", "a different reason")
        self.assertEqual((self.state / "max-codex-primary").read_text(), caps,
                         "a second retirement lowered the caps again")
        self.assertEqual((self.state / "key-disabled" / "workerkey").read_text(), reason,
                         "the original reason was overwritten")


class OnePassTests(KeyWatchHarness):
    def test_a_worker_log_that_cannot_be_attributed_retires_nothing(self):
        captures = self.root / "sessions"
        captures.mkdir()
        (captures / "abc123.jsonl").write_text(
            '{"type":"error","message":"unexpected status 403 Forbidden"}\n' * 3)
        result = self.watch("once", KIT_SESSION_CAPTURE_DIR=str(captures))
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        self.assertIn("no configured key could be attributed", result.stdout)
        self.assertEqual(self.probe_count(), 0)
        self.assertFalse((self.state / "cutoff").exists())

    def test_a_quiet_pass_does_nothing(self):
        self.pane(1, "gpt-x  ultra  ·  ~/widgetlib\nAsk Codex to do anything")
        result = self.watch("once")
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        self.assertEqual(self.probe_count(), 0)

    def test_status_reports_what_is_out_of_use(self):
        self.watch("retire", "workerkey", "out of quota")
        result = self.watch("status")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("main key: mainkey", result.stdout)
        self.assertIn("workerkey", result.stdout)
        self.assertIn("out of quota", result.stdout)


if __name__ == "__main__":
    unittest.main()
