#!/usr/bin/env python3
"""Unit tests for ``local/bin/session/goal-keeper.sh``.

One pass of the keeper is run against a canned pane, with the message tool
replaced by a stub that records what it was asked to send.  The four decisions
the keeper can take (resume a stalled goal, set a goal on an idle session, leave
a working session alone, interrupt an over-long turn) are asserted one by one.
"""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from test_session_tools import SessionHarness  # noqa: E402

STALLED = "...\n\ngpt-x  ultra  ·  ~/widgetlib\nGoal stalled — /goal resume to continue"
IDLE_NO_GOAL = "...\n\ngpt-x  ultra  ·  ~/widgetlib"
PURSUING = "...\n\nPursuing goal (3 steps)\ngpt-x  ultra  ·  ~/widgetlib"
LONG_TURN = "...\n\ngpt-x  ultra  ·  ~/widgetlib\nWorking (41m 03s · esc to interrupt)"
SHORT_TURN = "...\n\ngpt-x  ultra  ·  ~/widgetlib\nWorking (4m 10s · esc to interrupt)"
OTHER_REPO = "...\n\ngpt-x  ultra  ·  ~/someotherproject"


class GoalKeeperTests(SessionHarness):
    def setUp(self):
        super().setUp()
        self.repo = self.root / "widgetlib"
        self.repo.mkdir()

    def keeper(self, *args, **envextra):
        env = {"KIT_REPO_ROOT": str(self.repo), "KIT_SAY": str(self.say_stub),
               "KIT_KEEPER_PRINT_DECISION": "1", "KIT_TURN_MAX": "25"}
        env.update(envextra)
        return self.run_script("goal-keeper.sh", "--once", *args, **env)

    def decision(self, result) -> str:
        for line in result.stdout.splitlines():
            if line.startswith("decision="):
                return line.split("=", 1)[1]
        self.fail(f"no decision printed: {result.stdout}\n{result.stderr}")

    def set_goal_text(self, text="/goal do the work of this project\n"):
        (self.state / "goal-text").write_text(text)

    # -- the decisions ---------------------------------------------------
    def test_a_stalled_goal_is_resumed(self):
        self.pane(1, STALLED)
        self.set_goal_text()
        result = self.keeper()
        self.assertEqual(self.decision(result), "resume")
        self.assertTrue(any("/goal resume" in c for c in self.say_calls()), self.say_calls())

    def test_an_idle_session_without_a_goal_is_given_the_goal_from_the_state_file(self):
        self.pane(1, IDLE_NO_GOAL)
        self.set_goal_text()
        result = self.keeper()
        self.assertEqual(self.decision(result), "set-goal")
        self.assertTrue(any(str(self.state / "goal-text") in c for c in self.say_calls()),
                        self.say_calls())

    def test_without_a_goal_file_nothing_is_sent_and_there_is_no_built_in_goal(self):
        self.pane(1, IDLE_NO_GOAL)
        result = self.keeper()
        self.assertEqual(self.decision(result), "no-goal-text")
        self.assertEqual(self.say_calls(), [], "the keeper invented a goal")
        self.assertIn("no built-in goal", (self.state / "goal-keeper.log").read_text())

    def test_a_session_that_is_pursuing_its_goal_is_left_alone(self):
        self.pane(1, PURSUING)
        self.set_goal_text()
        result = self.keeper()
        self.assertEqual(self.decision(result), "none")
        self.assertEqual(self.say_calls(), [])

    def test_a_pane_from_another_repository_is_never_taken_for_our_idle_session(self):
        self.pane(1, OTHER_REPO)
        self.set_goal_text()
        result = self.keeper()
        self.assertEqual(self.decision(result), "none")
        self.assertEqual(self.say_calls(), [])

    def test_a_turn_over_the_limit_is_interrupted_once(self):
        self.pane(1, LONG_TURN)
        self.set_goal_text()
        result = self.keeper()
        self.assertIn("escape", self.decision(result))
        self.assertIn("send-keys -t kittest Escape", "\n".join(self.tmux_calls()))
        self.assertIn("interrupted a 41-minute turn", (self.state / "goal-keeper.log").read_text())

    def test_a_turn_inside_the_limit_is_not_interrupted(self):
        self.pane(1, SHORT_TURN)
        self.set_goal_text()
        result = self.keeper()
        self.assertEqual(self.decision(result), "none")
        self.assertNotIn("Escape", "\n".join(self.tmux_calls()))

    def test_the_turn_limit_can_be_raised_from_the_state_directory(self):
        self.pane(1, LONG_TURN)
        self.set_goal_text()
        (self.state / "turn-max").write_text("90\n")
        result = self.keeper()
        self.assertEqual(self.decision(result), "none")

    # -- lifecycle -------------------------------------------------------
    def test_the_keeper_records_its_pid_and_honours_its_stop_file(self):
        self.pane(1, PURSUING)
        self.keeper()
        self.assertTrue((self.state / "goal-keeper.pid").exists())
        (self.state / "goal-keeper.stop").touch()
        result = self.run_script("goal-keeper.sh", "--interval", "1",
                                 KIT_REPO_ROOT=str(self.repo), KIT_SAY=str(self.say_stub),
                                 timeout=30)
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn("stop file", (self.state / "goal-keeper.log").read_text())

    def test_dry_run_reports_what_it_would_do_and_sends_nothing(self):
        self.pane(1, STALLED)
        self.set_goal_text()
        result = self.run_script("goal-keeper.sh", "--dry-run",
                                 KIT_REPO_ROOT=str(self.repo), KIT_SAY=str(self.say_stub))
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.say_calls(), [])


if __name__ == "__main__":
    unittest.main()
