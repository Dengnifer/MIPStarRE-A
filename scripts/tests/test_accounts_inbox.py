#!/usr/bin/env python3
"""The owner-inbox comment channel for the live accounts file.

`local/bin/accounts_inbox.py` applies `ACCOUNTS:` comments on the owner inbox
issue and answers each one.  Three properties are load-bearing and are what
these cases check: only the repository owner's comments are applied, a comment
is applied exactly once however often the janitor sweeps, and every directive —
applied or rejected — is echoed back so the owner knows what took effect.

`gh` is never invoked: `gh_common.api` is replaced by a fake GitHub that serves
a comment list and records the writes.
"""

from __future__ import annotations

import contextlib
import io
import json
import os
import sys
import tempfile
import unittest
from datetime import datetime, timedelta, timezone
from pathlib import Path
from unittest import mock

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "local" / "bin"))

import accounts_file as af  # noqa: E402
import accounts_inbox as inbox  # noqa: E402

OWNER = "Dengnifer"
ISSUE = 500

BRIEF_ROWS = [
    {"name": "primary", "label": "relay-us7", "endpoint": "relay-us7",
     "codex_home": "~/.codex", "nominal_limit": 5, "external_reserved": 0,
     "enabled": True},
    {"name": "second", "label": "space", "endpoint": "api.finite-dimensional.space",
     "codex_home": "~/.cache/mipstarre-dev/codex-home-yxy", "nominal_limit": 30,
     "external_reserved": 2, "enabled": True},
]


class FakeGitHub:
    """Just enough of the REST surface: list comments, create one, patch one."""

    def __init__(self) -> None:
        self.comments: list[dict] = []
        self.posted: list[dict] = []
        self.next_id = 1000

    def comment(self, body: str, login: str) -> int:
        self.next_id += 1
        self.comments.append({"id": self.next_id, "body": body,
                              "user": {"login": login}})
        return self.next_id

    def api(self, path, *, method=None, payload=None, paginate=False,
            mutation=False, idempotent=False, absolute=False):
        if path.startswith(f"issues/{ISSUE}/comments") and method is None:
            return list(self.comments)
        if path.startswith(f"issues/{ISSUE}/comments") and method == "POST":
            number = self.comment(payload["body"], "github-actions")
            self.posted.append(payload)
            return {"id": number}
        if path.startswith("issues/comments/") and method == "PATCH":
            self.posted.append(payload)
            return {"id": 0}
        raise AssertionError(f"unexpected API call {method or 'GET'} {path}")


class InboxHarness(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.cache = Path(self.tmp.name) / "cache"
        (self.cache / "watchdog").mkdir(parents=True)
        environment = mock.patch.dict(os.environ, {
            "MIPSTARRE_CACHE_ROOT": str(self.cache),
            "MIPSTARRE_OWNER_LOGIN": OWNER,
        })
        environment.start()
        self.addCleanup(environment.stop)
        af.seed(BRIEF_ROWS, root=self.cache, source="test")
        self.github = FakeGitHub()
        patched = mock.patch.object(inbox.gh_common, "api", self.github.api)
        patched.start()
        self.addCleanup(patched.stop)

    def sweep(self, **kwargs) -> list[str]:
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            report = inbox.sweep(ISSUE, **kwargs)
        return report

    def ceiling(self, name: str) -> int:
        return af.load_map(self.cache)[name]["ceiling"]


class TestOwnerChannel(InboxHarness):
    def test_an_owner_directive_is_applied_and_answered(self) -> None:
        self.github.comment("The admin took slots back.\n"
                            "ACCOUNTS: second ceiling=20\n", OWNER)
        report = self.sweep()
        self.assertEqual(self.ceiling("second"), 20)
        self.assertTrue(any("applied: second" in line for line in report))
        self.assertEqual(len(self.github.posted), 1)
        body = self.github.posted[0]["body"]
        self.assertIn("applied: second ceiling 30 -> 20", body)
        self.assertIn(inbox.MARKER, body)

    def test_several_directives_in_one_comment(self) -> None:
        self.github.comment("ACCOUNTS: second ceiling=12 reserved=4\n"
                            "ACCOUNTS: primary enabled=false\n", OWNER)
        self.sweep()
        entries = af.load_map(self.cache)
        self.assertEqual(entries["second"]["ceiling"], 12)
        self.assertEqual(entries["second"]["external_reserved"], 4)
        self.assertFalse(entries["primary"]["enabled"])

    def test_a_comment_by_anyone_else_is_ignored_and_reported(self) -> None:
        # Never applied, and never answered in public: replying echoed the
        # stranger's own text back, so anyone with comment access could make the
        # bot comment once per comment they wrote.  The attempt stays visible —
        # in the janitor's report, which is where the owner reads it.
        self.github.comment("ACCOUNTS: second ceiling=999\n", "a-stranger")
        report = self.sweep()
        self.assertEqual(self.ceiling("second"), 30)
        self.assertTrue(any("a-stranger" in line for line in report))
        self.assertTrue(any("repository owner" in line for line in report))
        self.assertEqual(self.github.posted, [])

    def test_a_comment_is_applied_exactly_once(self) -> None:
        self.github.comment("ACCOUNTS: second ceiling=20\n", OWNER)
        self.sweep()
        # The owner then lowers it further at the shell; a second sweep must not
        # re-apply the comment and undo that.
        entries = af.load(self.cache)
        af.apply_fields(entries, "second", {"ceiling": "8"})
        af.save(entries, root=self.cache, actor="owner", action="set", detail="8")
        report = self.sweep()
        self.assertEqual(self.ceiling("second"), 8)
        self.assertEqual(len(self.github.posted), 1)
        self.assertIn("no new ACCOUNTS: directive", report[0])

    def test_prose_without_a_directive_is_left_alone(self) -> None:
        self.github.comment("Can you raise the yxy key a bit?", OWNER)
        report = self.sweep()
        self.assertEqual(self.github.posted, [])
        self.assertIn("no new ACCOUNTS: directive", report[0])

    def test_a_bad_directive_is_answered_with_the_reason(self) -> None:
        self.github.comment("ACCOUNTS: fourth ceiling=3\n"
                            "ACCOUNTS: second ceiling=notanumber\n", OWNER)
        self.sweep()
        self.assertEqual(self.ceiling("second"), 30)
        body = self.github.posted[0]["body"]
        self.assertIn("no account named 'fourth'", body)
        self.assertIn("nonnegative whole number", body)

    def test_dry_run_writes_nothing(self) -> None:
        self.github.comment("ACCOUNTS: second ceiling=20\n", OWNER)
        report = self.sweep(dry_run=True)
        self.assertEqual(self.ceiling("second"), 30)
        self.assertEqual(self.github.posted, [])
        self.assertTrue(any("dry run" in line for line in report))

    def test_our_own_reply_is_never_read_as_a_directive(self) -> None:
        self.github.comment("ACCOUNTS: second ceiling=20\n", OWNER)
        self.sweep()
        # The reply quotes the rejected directive lines verbatim; re-reading it
        # as input would loop the channel against itself.
        self.github.comment("ACCOUNTS: nope ceiling=1\n", OWNER)
        self.sweep()
        report = self.sweep()
        self.assertIn("no new ACCOUNTS: directive", report[0])


class TestStaleness(InboxHarness):
    """A directive the janitor never saw is stale capacity advice.

    The count cap alone did not implement the module's own rule: the owner inbox
    issue is permissions-only and low traffic, so every `ACCOUNTS:` comment ever
    written stayed in scope forever.  With the pipeline deliberately paused, the
    first sweep after a resume would have applied the whole backlog at once —
    `enabled=false` included, which is cap 0 and no probe.
    """

    def old_comment(self, body: str, minutes: int) -> int:
        number = self.github.comment(body, OWNER)
        moment = datetime.now(timezone.utc) - timedelta(minutes=minutes)
        self.github.comments[-1]["created_at"] = \
            moment.strftime("%Y-%m-%dT%H:%M:%SZ")
        return number

    def test_a_day_old_directive_is_neither_applied_nor_answered(self) -> None:
        self.old_comment("ACCOUNTS: second enabled=false\n", 60 * 24)
        report = self.sweep()
        self.assertEqual(self.ceiling("second"), 30)
        self.assertTrue(af.load_map(self.cache)["second"]["enabled"])
        self.assertEqual(self.github.posted, [])
        self.assertTrue(any("NOT applied" in line for line in report))

    def test_a_recent_directive_still_applies(self) -> None:
        self.old_comment("ACCOUNTS: second ceiling=20\n", 5)
        self.sweep()
        self.assertEqual(self.ceiling("second"), 20)
        self.assertEqual(len(self.github.posted), 1)

    def test_a_comment_with_no_timestamp_is_not_treated_as_stale(self) -> None:
        # The REST API always supplies created_at; a missing one is an unusual
        # payload, not an old comment, and dropping it would lose a real edit.
        self.github.comment("ACCOUNTS: second ceiling=18\n", OWNER)
        self.sweep()
        self.assertEqual(self.ceiling("second"), 18)

    def test_the_bound_can_be_turned_off(self) -> None:
        self.old_comment("ACCOUNTS: second ceiling=20\n", 60 * 24)
        self.sweep(max_age_min=0)
        self.assertEqual(self.ceiling("second"), 20)


class TestApplyOnce(InboxHarness):
    def test_a_failed_reply_does_not_re_apply_the_directive(self) -> None:
        # apply_directives writes the file; the reply marker lives on GitHub and
        # is written after it.  If that POST fails, the next sweep must not
        # re-apply the same directive and revert an `accounts.sh set` the owner
        # made in between.
        self.github.comment("ACCOUNTS: second ceiling=20\n", OWNER)
        with mock.patch.object(inbox.gh_common, "ensure_pr_comment",
                               side_effect=OSError("rate limited")):
            with self.assertRaises(OSError):
                self.sweep()
        self.assertEqual(self.ceiling("second"), 20)
        af.apply_fields(entries := af.load(self.cache), "second", {"ceiling": "9"})
        af.save(entries, root=self.cache, actor="owner", action="set", detail="shell")
        report = self.sweep()
        self.assertEqual(self.ceiling("second"), 9)
        self.assertTrue(any("already applied" in line for line in report))


class TestOwnerLogin(InboxHarness):
    def test_the_environment_wins(self) -> None:
        login, source = inbox.owner_login()
        self.assertEqual(login, OWNER)
        self.assertIn("MIPSTARRE_OWNER_LOGIN", source)

    def test_the_readme_line_is_the_recorded_source(self) -> None:
        with mock.patch.dict(os.environ, {"MIPSTARRE_OWNER_LOGIN": ""}):
            login, source = inbox.owner_login(REPO_ROOT)
        self.assertEqual(login, OWNER)
        self.assertIn("README.md", source)

    def test_local_readme_actually_carries_the_line(self) -> None:
        # The parser reads exactly one documented line; if the README is
        # reworded without it, the channel silently falls back to the repository
        # slug, so the line is part of the contract and is checked here.
        text = (REPO_ROOT / "local" / "README.md").read_text(encoding="utf-8")
        self.assertRegex(text, inbox.OWNER_LINE_RE)


if __name__ == "__main__":
    unittest.main()
