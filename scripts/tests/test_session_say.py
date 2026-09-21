#!/usr/bin/env python3
"""Unit tests for ``local/bin/session/say.sh`` — the three ways of delivering a
message to the main session's TUI.

Everything runs against the stub ``tmux`` from ``test_session_tools``: it records
the calls and replays canned pane text, so the idle detector, the re-press of
Enter on a pasted attachment and the Tab that queues a message are all exercised
without a terminal.
"""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from test_session_tools import SessionHarness  # noqa: E402

BUSY = "building the thing\n\ngpt-x  ultra  ·  ~/widgetlib\nWorking (3m 12s · esc to interrupt)"
IDLE = "done\n\ngpt-x  ultra  ·  ~/widgetlib\nAsk Codex to do anything"
IDLE_PASTED = "done\n\ngpt-x  ultra  ·  ~/widgetlib\n[Pasted Content 4211 chars]"
IDLE_QUEUED = "done\n\ngpt-x  ultra  ·  ~/widgetlib\nQueued follow-up inputs (1)"
BUSY_QUEUED = "working\n\ngpt-x  ultra  ·  ~/widgetlib\nWorking (2m · esc to interrupt)\nQueued follow-up inputs (1)"
OTHER_REPO = "done\n\ngpt-x  ultra  ·  ~/someotherproject\nAsk Codex to do anything"


class SayHarness(SessionHarness):
    def setUp(self):
        super().setUp()
        self.repo = self.root / "widgetlib"
        self.repo.mkdir()

    def say(self, *args, advance="capture-pane", **envextra):
        env = {"KIT_REPO_ROOT": str(self.repo), "FAKE_TMUX_ADVANCE_ON": advance,
               "KIT_SAY_SETTLE": "0", "KIT_SAY_TAB_SETTLE": "0"}
        env.update(envextra)
        return self.run_script("say.sh", *args, **env)

    def sent_literals(self):
        return [c for c in self.tmux_calls() if " -l " in c]


class IdleModeTests(SayHarness):
    def test_a_short_message_is_typed_and_submitted_when_the_session_is_idle(self):
        self.pane(1, IDLE)
        result = self.say("--mode", "idle", "/goal resume")
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        calls = self.tmux_calls()
        self.assertTrue(any(c.endswith("-l /goal resume") for c in calls), calls)
        self.assertTrue(any(c == "send-keys -t kittest Enter" for c in calls), calls)
        self.assertIn("sent at", result.stdout)

    def test_it_waits_for_a_busy_session_to_finish(self):
        self.pane(1, BUSY)
        self.pane(2, BUSY)
        self.pane(3, IDLE)
        result = self.say("--mode", "idle", "--timeout", "600", "hello")
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        captures_before_send = 0
        for call in self.tmux_calls():
            if call.startswith("capture-pane"):
                captures_before_send += 1
            if " -l " in call:
                break
        self.assertGreaterEqual(captures_before_send, 3, "it did not wait for the turn to end")

    def test_it_gives_up_and_sends_nothing_when_the_session_never_idles(self):
        self.pane(1, BUSY)
        result = self.say("--mode", "idle", "--timeout", "30", "hello")
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn("nothing sent", result.stdout)
        self.assertEqual(self.sent_literals(), [])

    def test_a_pane_of_another_repository_is_never_taken_for_our_idle_session(self):
        self.pane(1, OTHER_REPO)
        result = self.say("--mode", "idle", "--timeout", "20", "hello")
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertEqual(self.sent_literals(), [])

    def test_a_missing_tmux_session_is_never_mistaken_for_an_idle_one(self):
        # no canned pane at all: capture-pane prints nothing, as it does when the
        # session does not exist
        result = self.say("--mode", "idle", "--timeout", "20", "hello")
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertEqual(self.sent_literals(), [])

    def test_a_long_message_goes_through_a_tmux_buffer(self):
        long_text = self.root / "briefing.txt"
        long_text.write_text("line one\n" + ("x" * 4000) + "\n")
        self.pane(1, IDLE)
        result = self.say("--mode", "idle", "--file", str(long_text))
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        calls = self.tmux_calls()
        self.assertTrue(any(c.startswith("load-buffer") for c in calls), calls)
        self.assertTrue(any(c.startswith("paste-buffer") for c in calls), calls)
        self.assertEqual(self.buffer.read_text(), long_text.read_text())

    def test_enter_is_pressed_again_while_the_paste_is_still_an_attachment(self):
        # pane 1: idle -> paste; after the first Enter the composer still shows
        # the attachment; after the second Enter the turn is running.
        self.pane(1, IDLE)
        self.pane(2, IDLE_PASTED)
        self.pane(3, BUSY)
        big = self.root / "big.txt"
        big.write_text("y" * 3000)
        result = self.say("--mode", "idle", "--file", str(big), advance="send-keys -t kittest Enter")
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        enters = [c for c in self.tmux_calls() if c == "send-keys -t kittest Enter"]
        self.assertGreaterEqual(len(enters), 2, "the attachment was never re-submitted")

    def test_an_attachment_that_never_goes_away_is_reported(self):
        self.pane(1, IDLE)
        self.pane(2, IDLE_PASTED)
        big = self.root / "big.txt"
        big.write_text("z" * 3000)
        result = self.say("--mode", "idle", "--file", str(big), advance="send-keys -t kittest Enter")
        self.assertEqual(result.returncode, 6, result.stdout)
        self.assertIn("still in the composer", result.stdout)


class QueueModeTests(SayHarness):
    def test_a_message_is_queued_behind_a_running_turn_with_tab(self):
        self.pane(1, BUSY)
        self.pane(2, BUSY_QUEUED)
        result = self.say("--mode", "queue", "--file", self.write_message(),
                          advance="send-keys -t kittest Tab")
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        tabs = [c for c in self.tmux_calls() if c.endswith("Tab")]
        self.assertEqual(len(tabs), 1, self.tmux_calls())
        self.assertIn("queued at", result.stdout)

    def test_tab_is_pressed_again_when_the_queue_confirmation_does_not_appear(self):
        self.pane(1, BUSY)
        result = self.say("--mode", "queue", "--file", self.write_message(), advance="")
        self.assertEqual(result.returncode, 4, result.stdout)
        tabs = [c for c in self.tmux_calls() if c.endswith("Tab")]
        self.assertEqual(len(tabs), 3, "Tab must be retried three times before giving up")
        self.assertIn("never appeared", result.stdout)

    def test_an_idle_session_gets_the_message_submitted_instead_of_queued(self):
        self.pane(1, IDLE)
        result = self.say("--mode", "queue", "--file", self.write_message(), advance="")
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        self.assertNotIn("Tab", "\n".join(self.tmux_calls()))
        self.assertIn("nothing to queue behind", result.stdout)

    def write_message(self) -> str:
        path = self.root / "standdown.txt"
        path.write_text("stand down now, please\n" + ("w" * 2500))
        return str(path)


class InterruptModeTests(SayHarness):
    def test_a_running_turn_is_escaped_and_the_goal_is_resumed_afterwards(self):
        self.pane(1, BUSY)
        self.pane(2, IDLE)
        result = self.say("--mode", "interrupt", "--grace", "1", "stop what you are doing")
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        calls = "\n".join(self.tmux_calls())
        self.assertIn("send-keys -t kittest Escape", calls)
        self.assertIn("-l stop what you are doing", calls)
        self.assertIn("-l /goal resume", calls)
        self.assertIn("interrupted=1", result.stdout)

    def test_an_idle_session_is_not_escaped_and_the_goal_is_left_alone(self):
        self.pane(1, IDLE)
        result = self.say("--mode", "interrupt", "--grace", "60", "a question")
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        calls = "\n".join(self.tmux_calls())
        self.assertNotIn("Escape", calls)
        self.assertNotIn("/goal resume", calls)
        self.assertIn("interrupted=0", result.stdout)


class UsageTests(SayHarness):
    def test_a_missing_mode_or_message_is_a_usage_error(self):
        self.assertEqual(self.say("hello").returncode, 3)
        self.assertEqual(self.say("--mode", "idle").returncode, 3)
        self.assertEqual(self.say("--mode", "sideways", "hi").returncode, 3)

    def test_dry_run_sends_nothing(self):
        self.pane(1, IDLE)
        result = self.say("--mode", "idle", "--dry-run", "hello")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("DRY say --mode idle", result.stdout)
        self.assertEqual(self.tmux_calls(), [])


if __name__ == "__main__":
    unittest.main()
