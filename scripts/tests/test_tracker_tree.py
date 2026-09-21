#!/usr/bin/env python3
"""Regression tests for local/bin/tracker_tree.py.

Offline: the two tools that talk to GitHub (`issue_new.py` and
`gh_common.py add-blocked-by`) are replaced by a recorder, so the tests check
the ordering, the parent links, the dependency edges and the write-back
without a single API call.
"""

from __future__ import annotations

import io
import json
import shutil
import sys
import tempfile
import unittest
from contextlib import redirect_stdout, redirect_stderr
from pathlib import Path
from unittest import mock

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "local" / "bin"))

import tracker_tree  # noqa: E402

FIXTURE = Path(__file__).resolve().parent / "fixtures" / "kit" / "chapter-plan.json"


class Recorder:
    """Stands in for issue_new.py and gh_common.py; hands out numbers."""

    def __init__(self, first: int = 101) -> None:
        self.next = first
        self.creates: list[list[str]] = []
        self.edges: list[tuple[int, int]] = []

    def __call__(self, cmd: list[str], cwd: Path) -> tuple[int, str, str]:
        if any(part.endswith("issue_new.py") for part in cmd):
            self.creates.append(cmd)
            number = self.next
            self.next += 1
            return 0, f"{number}\n", ""
        if "add-blocked-by" in cmd:
            index = cmd.index("add-blocked-by")
            self.edges.append((int(cmd[index + 1]), int(cmd[index + 2])))
            return 0, "", ""
        raise AssertionError(f"unexpected command: {cmd}")


def option_of(cmd: list[str], flag: str) -> str | None:
    return cmd[cmd.index(flag) + 1] if flag in cmd else None


def create_for(recorder: Recorder, title_fragment: str) -> list[str]:
    for cmd in recorder.creates:
        if title_fragment in option_of(cmd, "--title"):
            return cmd
    raise AssertionError(f"no issue was created for {title_fragment!r}")


class PlanReadingTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.dir = Path(self.tmp.name)
        self.addCleanup(self.tmp.cleanup)
        self.plan = self.dir / "plan.json"
        shutil.copyfile(FIXTURE, self.plan)

    def edit(self, change) -> Path:
        data = json.loads(self.plan.read_text(encoding="utf-8"))
        change(data)
        self.plan.write_text(json.dumps(data), encoding="utf-8")
        return self.plan

    def test_creation_order_puts_blockers_and_parents_first(self) -> None:
        _, nodes = tracker_tree.read_plan(self.plan)
        order = [node.ident for node in tracker_tree.order(nodes)]
        self.assertEqual(order[0], "tracker")
        self.assertLess(order.index("ch01"), order.index("ch02"))
        self.assertLess(order.index("p01a"), order.index("p02a"))
        self.assertLess(order.index("ch02"), order.index("p02a"))

    def test_a_body_file_is_read_relative_to_the_plan(self) -> None:
        (self.dir / "body.md").write_text("The tracker body.\n", encoding="utf-8")
        self.edit(lambda d: d["tracker"].update({"body": None, "body_file": "body.md"}))
        _, nodes = tracker_tree.read_plan(self.plan)
        self.assertEqual(nodes[0].body, "The tracker body.\n")

    def test_a_node_needs_exactly_one_of_body_and_body_file(self) -> None:
        self.edit(lambda d: d["chapters"][0].update({"body_file": "body.md"}))
        with self.assertRaises(tracker_tree.PlanError) as caught:
            tracker_tree.read_plan(self.plan)
        self.assertIn("exactly one", str(caught.exception))

    def test_an_unknown_blocker_id_is_named(self) -> None:
        self.edit(lambda d: d["packets"][0].update({"blocked_by": ["ch99"]}))
        with self.assertRaises(tracker_tree.PlanError) as caught:
            tracker_tree.read_plan(self.plan)
        self.assertIn("ch99", str(caught.exception))

    def test_a_cycle_is_reported_instead_of_looping(self) -> None:
        def make_cycle(data):
            data["chapters"][1]["blocked_by"] = ["ch02"]
        self.edit(make_cycle)
        _, nodes = tracker_tree.read_plan(self.plan)
        with self.assertRaises(tracker_tree.PlanError) as caught:
            tracker_tree.order(nodes)
        self.assertIn("cycle", str(caught.exception))

    def test_duplicate_ids_are_refused(self) -> None:
        self.edit(lambda d: d["chapters"][1].update({"id": "ch02"}))
        with self.assertRaises(tracker_tree.PlanError) as caught:
            tracker_tree.read_plan(self.plan)
        self.assertIn("duplicate id", str(caught.exception))

    def test_bracketed_titles_are_refused(self) -> None:
        self.edit(lambda d: d["chapters"][0].update({"title": "[WIP] chapter two"}))
        with self.assertRaises(tracker_tree.PlanError) as caught:
            tracker_tree.read_plan(self.plan)
        self.assertIn("bracket-free", str(caught.exception))


class DryRunTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.dir = Path(self.tmp.name)
        self.addCleanup(self.tmp.cleanup)
        self.plan = self.dir / "plan.json"
        shutil.copyfile(FIXTURE, self.plan)

    def test_dry_run_prints_the_tree_and_calls_nothing(self) -> None:
        recorder = Recorder()
        out = io.StringIO()
        before = self.plan.read_bytes()
        with mock.patch.object(tracker_tree, "run_cmd", recorder), redirect_stdout(out):
            rc = tracker_tree.main([str(self.plan), "--dry-run", "--root", str(self.dir)])
        text = out.getvalue()
        self.assertEqual(rc, 0)
        self.assertEqual(recorder.creates, [])
        self.assertEqual(self.plan.read_bytes(), before)
        self.assertIn("5 issues in creation order", text)
        self.assertIn("[ch01]", text)
        self.assertIn("blocked by: ch01", text)
        self.assertIn("2 blocked_by edges", text)
        self.assertLess(text.index("[ch01]"), text.index("[ch02]"))
        self.assertLess(text.index("[p01a]"), text.index("[p02a]"))


class CreateTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.dir = Path(self.tmp.name)
        self.addCleanup(self.tmp.cleanup)
        self.plan = self.dir / "plan.json"
        shutil.copyfile(FIXTURE, self.plan)
        (self.dir / "local").mkdir()
        (self.dir / "local" / "project.json").write_text(
            json.dumps({"schema": 1, "issues": {"progress": None, "owner_inbox": None,
                                                "tracker_root": None}}) + "\n",
            encoding="utf-8")
        self.recorder = Recorder()
        with mock.patch.object(tracker_tree, "run_cmd", self.recorder), \
                redirect_stdout(io.StringIO()):
            self.rc = tracker_tree.main([str(self.plan), "--root", str(self.dir)])
        self.created = json.loads(self.plan.read_text(encoding="utf-8"))["created"]

    def test_every_node_is_created_once(self) -> None:
        self.assertEqual(self.rc, 0)
        self.assertEqual(len(self.recorder.creates), 5)
        self.assertEqual(sorted(self.created), ["ch01", "ch02", "p01a", "p02a", "tracker"])

    def test_chapters_hang_under_the_tracker_and_packets_under_their_chapter(self) -> None:
        tracker = self.created["tracker"]
        self.assertIsNone(option_of(create_for(self.recorder, "Tracking -"), "--parent"))
        self.assertEqual(option_of(create_for(self.recorder, "Chapter 1"), "--parent"),
                         str(tracker))
        self.assertEqual(option_of(create_for(self.recorder, "basic definitions"),
                                   "--parent"), str(self.created["ch01"]))
        self.assertEqual(option_of(create_for(self.recorder, "estimate itself"),
                                   "--parent"), str(self.created["ch02"]))

    def test_each_create_carries_an_adoption_key_and_its_labels(self) -> None:
        chapter = create_for(self.recorder, "Chapter 1")
        self.assertEqual(option_of(chapter, "--key"), "fixture-plan-ch01")
        self.assertEqual(option_of(chapter, "--label"), "formalization")

    def test_prerequisites_become_blocked_by_edges_between_real_numbers(self) -> None:
        self.assertEqual(sorted(self.recorder.edges), sorted([
            (self.created["ch02"], self.created["ch01"]),
            (self.created["p02a"], self.created["p01a"]),
        ]))

    def test_the_tracker_is_recorded_in_project_json(self) -> None:
        config = json.loads((self.dir / "local" / "project.json").read_text(
            encoding="utf-8"))
        self.assertEqual(config["issues"]["tracker_root"], self.created["tracker"])

    def test_running_it_again_creates_nothing(self) -> None:
        again = Recorder(first=900)
        with mock.patch.object(tracker_tree, "run_cmd", again), redirect_stdout(io.StringIO()):
            rc = tracker_tree.main([str(self.plan), "--root", str(self.dir)])
        self.assertEqual(rc, 0)
        self.assertEqual(again.creates, [])
        self.assertEqual(len(again.edges), 2)
        self.assertEqual(
            json.loads(self.plan.read_text(encoding="utf-8"))["created"], self.created)


class FailureTests(unittest.TestCase):
    def test_a_failing_create_stops_with_the_tool_s_message(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        plan = Path(tmp.name) / "plan.json"
        shutil.copyfile(FIXTURE, plan)

        def refuse(cmd, cwd):
            return 2, "", "issue_new.py: unknown label 'formalization'\n"

        err = io.StringIO()
        with mock.patch.object(tracker_tree, "run_cmd", refuse), redirect_stderr(err):
            rc = tracker_tree.main([str(plan), "--root", str(tmp.name)])
        self.assertEqual(rc, 2)
        self.assertIn("unknown label", err.getvalue())


if __name__ == "__main__":
    unittest.main()
