#!/usr/bin/env python3
"""Regression tests for local/bin/ready_packets.py against a fake GitHub API."""

from __future__ import annotations

import io
import json
import sys
import unittest
from contextlib import redirect_stdout
from pathlib import Path
from unittest import mock

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "local" / "bin"))

import ready_packets  # noqa: E402


def _issue(number: int, state: str = "open", title: str = "") -> dict:
    return {"number": number, "state": state,
            "title": title or f"feat(QPBT): packet {number}"}


#: #47 -> two chapter trackers; #164 nests a chain parent (#77) one level down.
#: #106 is ready, #107 waits on it, #105 waits on the closed #104, #99 is a
#: closed leaf and #164 itself is a tracker, so neither may be reported.
TREE = {
    "issues/47/sub_issues": [_issue(163), _issue(164)],
    "issues/163/sub_issues": [_issue(97), _issue(99, "closed")],
    "issues/164/sub_issues": [_issue(77), _issue(106), _issue(107)],
    "issues/77/sub_issues": [_issue(105)],
    "issues/97/sub_issues": [],
    "issues/99/sub_issues": [],
    "issues/105/sub_issues": [],
    "issues/106/sub_issues": [],
    "issues/107/sub_issues": [],
    "issues/97/dependencies/blocked_by": [],
    "issues/105/dependencies/blocked_by": [_issue(104, "closed")],
    "issues/106/dependencies/blocked_by": [_issue(97)],
    "issues/107/dependencies/blocked_by": [_issue(97), _issue(106)],
}


class FakeApi:
    """`gh_common.api` stand-in that records every path it is asked for."""

    def __init__(self, tree: dict | None = None) -> None:
        self.tree = TREE if tree is None else tree
        self.calls: list[str] = []

    def __call__(self, path: str, **kwargs):
        assert kwargs.get("paginate") is True, "reads must paginate"
        assert "method" not in kwargs, "ready_packets.py is read-only"
        self.calls.append(path)
        return self.tree[path]


class ReadyPacketsTests(unittest.TestCase):
    def setUp(self) -> None:
        ready_packets._CACHE.clear()
        self.api = FakeApi()
        patcher = mock.patch.object(ready_packets.gh_common, "api", self.api)
        patcher.start()
        self.addCleanup(patcher.stop)
        self.addCleanup(ready_packets._CACHE.clear)

    def test_collect_returns_open_leaves_with_parent_and_blockers(self) -> None:
        rows = ready_packets.collect(47)
        self.assertEqual([row["issue"] for row in rows], [97, 105, 106, 107])
        parents = {row["issue"]: row["parent"] for row in rows}
        # #77 is a chain parent inside #164, so its child reports #77, and #77
        # itself is a tracker rather than a packet.
        self.assertEqual(parents, {97: 163, 105: 77, 106: 164, 107: 164})
        self.assertEqual([row["issue"] for row in rows if not row["open_blockers"]],
                         [97, 105])
        blocked = {row["issue"]: row["open_blockers"] for row in rows
                   if row["open_blockers"]}
        self.assertEqual(blocked, {106: [97], 107: [97, 106]})

    def test_closed_blockers_do_not_block(self) -> None:
        row = next(r for r in ready_packets.collect(47) if r["issue"] == 105)
        self.assertEqual([b["issue"] for b in row["blockers"]], [104])
        self.assertEqual(row["open_blockers"], [])

    def test_each_path_is_fetched_once(self) -> None:
        ready_packets.collect(47)
        ready_packets.collect(47)
        self.assertEqual(len(self.api.calls), len(set(self.api.calls)))
        self.assertIn("issues/47/sub_issues", self.api.calls)

    def test_json_output_lists_ready_and_blocked_only_with_all(self) -> None:
        out = io.StringIO()
        with redirect_stdout(out):
            self.assertEqual(ready_packets.main(["--json"]), 0)
        payload = json.loads(out.getvalue())
        self.assertEqual(payload["root"], 47)
        self.assertEqual([row["issue"] for row in payload["ready"]], [97, 105])
        self.assertNotIn("blocked", payload)

        ready_packets._CACHE.clear()
        out = io.StringIO()
        with redirect_stdout(out):
            self.assertEqual(ready_packets.main(["--json", "--all"]), 0)
        payload = json.loads(out.getvalue())
        self.assertEqual([row["issue"] for row in payload["blocked"]], [106, 107])

    def test_table_shows_blockers_and_hides_them_without_all(self) -> None:
        out = io.StringIO()
        with redirect_stdout(out):
            self.assertEqual(ready_packets.main([]), 0)
        text = out.getvalue()
        self.assertIn("READY (2)", text)
        self.assertIn("#105", text)
        self.assertNotIn("BLOCKED", text)

        ready_packets._CACHE.clear()
        out = io.StringIO()
        with redirect_stdout(out):
            self.assertEqual(ready_packets.main(["--all"]), 0)
        text = out.getvalue()
        self.assertIn("BLOCKED (2)", text)
        self.assertRegex(text, r"#107\s+.*#164\s+#97, #106")

    def test_api_failure_exits_two(self) -> None:
        def boom(path: str, **kwargs):
            raise ready_packets.LayerError("gh api ... failed: offline")

        with mock.patch.object(ready_packets.gh_common, "api", boom):
            err = io.StringIO()
            with redirect_stdout(io.StringIO()), mock.patch.object(sys, "stderr", err):
                self.assertEqual(ready_packets.main([]), 2)
            self.assertIn("offline", err.getvalue())


if __name__ == "__main__":
    unittest.main()
