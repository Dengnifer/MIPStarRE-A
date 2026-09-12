#!/usr/bin/env python3
"""The owner's live accounts file: validation, atomic writes, the log, the CLI.

`local/bin/accounts_file.py` is the only writer of
``watchdog/accounts.json`` and the only parser of the ``ACCOUNTS:`` directive
form, so the shell CLI and the janitor's GitHub channel cannot disagree about
what a valid entry is.  These cases are the ones the owner will actually hit:
a typo in a field name, a negative ceiling, a duplicate entry, an edit that
must not be half-written, and an audit line that says who changed what.

Nothing here touches ghz: every path is a temporary directory and no ``gh`` or
``codex`` is invoked.
"""

from __future__ import annotations

import contextlib
import io
import json
import os
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "local" / "bin"))

import accounts_file as af  # noqa: E402

BRIEF_ROWS = [
    {"name": "primary", "label": "relay-us7", "endpoint": "relay-us7",
     "codex_home": "~/.codex", "nominal_limit": 5, "external_reserved": 0,
     "enabled": True},
    {"name": "second", "label": "space", "endpoint": "api.finite-dimensional.space",
     "codex_home": "~/.cache/mipstarre-dev/codex-home-yxy", "nominal_limit": 30,
     "external_reserved": 2, "enabled": True},
]


class AccountsHarness(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.cache = Path(self.tmp.name) / "cache"
        (self.cache / "watchdog").mkdir(parents=True)
        environment = mock.patch.dict(os.environ, {
            "MIPSTARRE_CACHE_ROOT": str(self.cache),
            "MIPSTARRE_ACCOUNTS_ACTOR": "tester",
        })
        environment.start()
        self.addCleanup(environment.stop)

    @property
    def path(self) -> Path:
        return self.cache / "watchdog" / "accounts.json"

    def write(self, document) -> None:
        self.path.write_text(json.dumps(document), encoding="utf-8")

    def seed(self) -> None:
        written, _ = af.seed(BRIEF_ROWS, source="test")
        self.assertTrue(written)

    def cli(self, *argv: str, expect: int = 0) -> str:
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = af.main(list(argv))
        self.assertEqual(code, expect, f"argv={argv}\n{out.getvalue()}{err.getvalue()}")
        return out.getvalue() + err.getvalue()

    def log_lines(self) -> list[str]:
        path = self.cache / "watchdog" / "capacity" / "accounts.log"
        if not path.exists():
            return []
        return [line for line in path.read_text(encoding="utf-8").splitlines() if line]


class TestValidation(AccountsHarness):
    def test_absent_file_is_none_not_empty(self) -> None:
        # "No live file" must mean "use the brief", never "no accounts": a
        # missing file that read as an empty list would be zero capacity.
        self.assertIsNone(af.load())

    def test_bad_json_names_the_file(self) -> None:
        self.path.write_text("{not json", encoding="utf-8")
        with self.assertRaises(af.AccountsError) as caught:
            af.load()
        self.assertIn("not valid JSON", str(caught.exception))
        self.assertIn(str(self.path), str(caught.exception))

    def test_unknown_field_is_rejected_by_name(self) -> None:
        # `cieling: 40` must not read as "ceiling unchanged".
        self.write({"schema": af.SCHEMA, "accounts": [
            dict(name="primary", endpoint="relay-us7", codex_home="~/.codex",
                 ceiling=5, cieling=40)]})
        with self.assertRaises(af.AccountsError) as caught:
            af.load()
        self.assertIn("cieling", str(caught.exception))

    def test_negative_ceiling_is_rejected(self) -> None:
        self.write({"schema": af.SCHEMA, "accounts": [
            dict(name="primary", endpoint="relay-us7", codex_home="~/.codex",
                 ceiling=-1)]})
        with self.assertRaises(af.AccountsError) as caught:
            af.load()
        self.assertIn("ceiling", str(caught.exception))

    def test_duplicate_name_is_rejected(self) -> None:
        row = dict(name="primary", endpoint="relay-us7", codex_home="~/.codex", ceiling=5)
        self.write({"schema": af.SCHEMA, "accounts": [row, dict(row)]})
        with self.assertRaises(af.AccountsError) as caught:
            af.load()
        self.assertIn("listed twice", str(caught.exception))

    def test_reserved_above_ceiling_is_rejected_but_equal_is_legal(self) -> None:
        base = dict(name="primary", endpoint="relay-us7", codex_home="~/.codex",
                    ceiling=5)
        self.write({"schema": af.SCHEMA, "accounts": [dict(base, external_reserved=6)]})
        with self.assertRaises(af.AccountsError):
            af.load()
        # Equal is the admin having taken every slot for now — an honest state
        # during a run, and different from `enabled: false`, which is a decision.
        self.write({"schema": af.SCHEMA, "accounts": [dict(base, external_reserved=5)]})
        self.assertEqual(af.load()[0]["external_reserved"], 5)

    def test_empty_account_list_is_rejected(self) -> None:
        self.write({"schema": af.SCHEMA, "accounts": []})
        with self.assertRaises(af.AccountsError) as caught:
            af.load()
        self.assertIn("at least one account", str(caught.exception))

    def test_bare_array_is_accepted(self) -> None:
        self.write([dict(name="only", endpoint="e", codex_home="~/.codex", ceiling=4)])
        self.assertEqual([entry["name"] for entry in af.load()], ["only"])

    def test_account_name_class(self) -> None:
        self.write({"schema": af.SCHEMA, "accounts": [
            dict(name="Not Valid", endpoint="e", codex_home="~/.codex", ceiling=4)]})
        with self.assertRaises(af.AccountsError) as caught:
            af.load()
        self.assertIn("does not match", str(caught.exception))


class TestSeeding(AccountsHarness):
    def test_seed_maps_nominal_limit_to_ceiling(self) -> None:
        self.seed()
        entries = {entry["name"]: entry for entry in af.load()}
        self.assertEqual(entries["second"]["ceiling"], 30)
        self.assertEqual(entries["second"]["external_reserved"], 2)
        self.assertEqual(entries["primary"]["label"], "relay-us7")

    def test_seed_never_overwrites_an_existing_file(self) -> None:
        # The brief is one-shot; the accounts file is live.  Re-applying a brief
        # to change the speed tier must not undo an hour of ceiling edits.
        self.seed()
        entries = af.load()
        af.apply_fields(entries, "second", {"ceiling": "11"})
        af.save(entries, actor="tester", action="set", detail="second ceiling 30 -> 11")
        written, _ = af.seed(BRIEF_ROWS, source="second apply")
        self.assertFalse(written)
        self.assertEqual(af.load_map()["second"]["ceiling"], 11)

    def test_as_mode_rows_carries_both_spellings(self) -> None:
        self.seed()
        rows = {row["name"]: row for row in af.as_mode_rows(af.load())}
        self.assertEqual(rows["second"]["nominal_limit"], rows["second"]["ceiling"])
        self.assertTrue(rows["second"]["codex_home_path"].startswith("/"))


class TestWritesAndLog(AccountsHarness):
    def test_write_is_atomic_and_leaves_no_partial_file(self) -> None:
        self.seed()
        before = self.path.read_text(encoding="utf-8")
        entries = af.load()
        entries.append({"name": "third", "label": "t", "endpoint": "api.third",
                        "codex_home": "~/x", "ceiling": -3,
                        "external_reserved": 0, "enabled": True, "note": ""})
        with self.assertRaises(af.AccountsError):
            af.save(entries, actor="tester", action="add", detail="third")
        # Validation precedes the write, so the file on disk is untouched — the
        # controller reading it a millisecond later must never see a half-file.
        self.assertEqual(self.path.read_text(encoding="utf-8"), before)

    def test_every_write_appends_one_log_line(self) -> None:
        self.seed()
        self.cli("set", "second", "ceiling", "20")
        self.cli("disable", "second", "--note", "admin took the slots")
        lines = self.log_lines()
        self.assertEqual(len(lines), 3)
        self.assertIn("action=seed", lines[0])
        self.assertIn("ceiling 30 -> 20", lines[1])
        self.assertIn("actor=tester", lines[1])
        self.assertIn("admin took the slots", lines[2])

    def test_no_key_value_is_ever_stored(self) -> None:
        self.seed()
        self.assertNotIn("sk-", self.path.read_text(encoding="utf-8"))
        self.assertEqual(sorted(af.load()[0]), sorted(af.ENTRY_KEYS))


class TestCli(AccountsHarness):
    def test_list_get_set_enable_disable(self) -> None:
        self.seed()
        self.assertIn("relay-us7", self.cli("list"))
        self.assertEqual(self.cli("get", "second", "ceiling").strip(), "30")
        self.cli("set", "second", "reserved", "4")
        self.assertEqual(af.load_map()["second"]["external_reserved"], 4)
        self.cli("disable", "second")
        self.assertFalse(af.load_map()["second"]["enabled"])
        self.cli("enable", "second")
        self.assertTrue(af.load_map()["second"]["enabled"])

    def test_add_and_remove(self) -> None:
        self.seed()
        self.cli("add", "third", "--endpoint", "api.third.example",
                 "--codex-home", "~/.codex-third", "--ceiling", "8")
        self.assertEqual(af.load_map()["third"]["ceiling"], 8)
        self.cli("remove", "third")
        self.assertNotIn("third", af.load_map())

    def test_removing_the_last_account_is_refused(self) -> None:
        af.seed([BRIEF_ROWS[0]], source="one key")
        self.assertIn("only account", self.cli("remove", "primary", expect=2))

    def test_unknown_account_exits_3(self) -> None:
        self.seed()
        self.assertIn("no account named", self.cli("get", "fourth", expect=3))

    def test_unknown_field_and_bad_value_exit_2_without_writing(self) -> None:
        self.seed()
        before = self.path.read_text(encoding="utf-8")
        self.cli("set", "second", "cieling", "20", expect=2)
        self.cli("set", "second", "ceiling", "twenty", expect=2)
        self.cli("set", "second", "enabled", "maybe", expect=2)
        self.assertEqual(self.path.read_text(encoding="utf-8"), before)

    def test_missing_file_names_the_seeding_command(self) -> None:
        self.assertIn("run_mode.py apply", self.cli("list", expect=2))


class TestDirectives(AccountsHarness):
    def test_parses_one_or_more_lines_and_ignores_prose(self) -> None:
        records = af.parse_directives(
            "Please lower the yxy key, the admin took slots back.\n"
            "ACCOUNTS: second ceiling=20 reserved=4\n"
            "ACCOUNTS: primary enabled=false\n"
            "Thanks!\n")
        self.assertEqual([record["name"] for record in records], ["second", "primary"])
        self.assertEqual(records[0]["fields"], {"ceiling": "20", "reserved": "4"})
        self.assertEqual([record["error"] for record in records], ["", ""])

    def test_a_bad_line_is_reported_not_guessed(self) -> None:
        records = af.parse_directives("ACCOUNTS: second ceiling 20\n")
        self.assertIn("field=value", records[0]["error"])
        records = af.parse_directives("ACCOUNTS: second\n")
        self.assertIn("no field to set", records[0]["error"])
        records = af.parse_directives("ACCOUNTS: Second ceiling=1\n")
        self.assertIn("account name", records[0]["error"])

    def test_paths_may_not_travel_over_github(self) -> None:
        records = af.parse_directives("ACCOUNTS: second codex_home=/etc\n")
        self.assertIn("may not be set from a comment", records[0]["error"])

    def test_apply_directives_writes_once_and_answers_every_line(self) -> None:
        self.seed()
        results = af.apply_directives(
            "ACCOUNTS: second ceiling=20\nACCOUNTS: fourth ceiling=3\n",
            actor="github:owner", origin="#500 comment 7")
        self.assertEqual(len(results), 2)
        self.assertTrue(results[0].startswith("applied: second"))
        self.assertTrue(results[1].startswith("rejected:"))
        self.assertEqual(af.load_map()["second"]["ceiling"], 20)
        self.assertEqual(len(self.log_lines()), 2)  # the seed and one inbox write

    def test_a_rejected_only_comment_writes_nothing(self) -> None:
        self.seed()
        before = self.path.read_text(encoding="utf-8")
        results = af.apply_directives("ACCOUNTS: fourth ceiling=3\n",
                                      actor="github:owner")
        self.assertTrue(results[0].startswith("rejected:"))
        self.assertEqual(self.path.read_text(encoding="utf-8"), before)

    def test_one_bad_field_of_a_directive_changes_nothing_in_that_entry(self) -> None:
        self.seed()
        results = af.apply_directives(
            "ACCOUNTS: second ceiling=20 enabled=perhaps\n", actor="github:owner")
        self.assertTrue(results[0].startswith("rejected:"))
        self.assertEqual(af.load_map()["second"]["ceiling"], 30)


if __name__ == "__main__":
    unittest.main()
