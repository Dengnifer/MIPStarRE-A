#!/usr/bin/env python3
"""Regressions for the blocking findings of PR 552's review round 2.

One test per finding, named after the defect it pins, in the order the review
reported them.  Like `test_pr552_review_fixes.py` they are grouped by review
rather than by work item: they are one review's conclusions and should fail
together if those conclusions are undone.
"""

from __future__ import annotations

import io
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from datetime import datetime, timedelta, timezone
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
BIN_DIR = REPO_ROOT / "local" / "bin"
TOOLS = REPO_ROOT / "results/telemetry/owner-tools"
PROTOCOLS = REPO_ROOT / "local" / "protocols"
sys.path.insert(0, str(BIN_DIR))

import ready_report  # noqa: E402
import run_mode  # noqa: E402

TEMPLATE = TOOLS / "run-brief.template.json"
SHIM_TEMPLATE = TOOLS / "owner-bin-codex"


def text(path: Path) -> str:
    return path.read_text(encoding="utf-8")


class AttrProbe:
    """`git check-attr` against the COMMITTED .gitattributes and nothing else.

    Deliberately not run in this checkout: git gives
    ``$(git rev-parse --git-common-dir)/info/attributes`` precedence over the
    tracked file, and ghz still carries the hand-installed 2026-09-12 globs
    there.  A test that read the live repository would report that host's
    override rather than what this branch ships, and would pass or fail for the
    wrong reason.  A throwaway repository holding one file answers the question
    the review asked: *what does the committed file say?*
    """

    def __init__(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.root = Path(self._tmp.name)
        subprocess.run(["git", "init", "-q", str(self.root)], check=True,
                       capture_output=True)
        (self.root / ".gitattributes").write_text(
            (REPO_ROOT / ".gitattributes").read_text(encoding="utf-8"), encoding="utf-8")

    def close(self) -> None:
        self._tmp.cleanup()

    def merge_driver(self, path: str) -> str:
        done = subprocess.run(["git", "-C", str(self.root), "check-attr", "merge", "--", path],
                              capture_output=True, text=True)
        if done.returncode != 0:
            raise unittest.SkipTest(f"git check-attr failed: {done.stderr.strip()}")
        return done.stdout.rsplit(": ", 1)[-1].strip()


# ---------------------------------------------------------------------------
# Finding 2 — union merge reached the prose beside the append-only records
# ---------------------------------------------------------------------------

class MergeAttributeScopeTestCase(unittest.TestCase):
    """`union` keeps BOTH versions of a replaced line.  Records only."""

    APPEND_ONLY = (
        "results/telemetry/events.md",
        "results/telemetry/events.d/2026-09-12-x.md",
        "results/telemetry/owner-log.md",
        "results/telemetry/design-decisions.md",
        "results/telemetry/sessions.jsonl",
        "results/telemetry/sessions/prover-1.jsonl",
        "results/telemetry/merge-latency-2026-09-13.jsonl",
        "local/protocols/EVOLUTION.md",
    )
    #: Prose under the same directory.  A line here REPLACES another line.
    PROSE = (
        "results/telemetry/owner-tools/README.md",
        "results/telemetry/owner-handoffs/TEMPLATE.md",
        "results/telemetry/owner-handoffs/2026-09-12-main.md",
        "results/telemetry/README.md",
        "results/telemetry/usage-summary.md",
        "results/telemetry/github-migration-map.md",
    )

    def setUp(self) -> None:
        self.probe = AttrProbe()
        self.addCleanup(self.probe.close)

    def test_the_append_only_records_are_union(self) -> None:
        for path in self.APPEND_ONLY:
            with self.subTest(path=path):
                self.assertEqual(self.probe.merge_driver(path), "union")

    def test_the_prose_beside_them_is_not(self) -> None:
        for path in self.PROSE:
            with self.subTest(path=path):
                self.assertNotEqual(
                    self.probe.merge_driver(path), "union",
                    f"{path} is prose: a union merge of two edits to one line keeps "
                    "both versions, and the merge daemon merges without anyone "
                    "reading the result")

    def test_gitattributes_carries_no_markdown_wildcard(self) -> None:
        body = text(REPO_ROOT / ".gitattributes")
        for line in body.splitlines():
            stripped = line.strip()
            if stripped.startswith("#") or "merge=union" not in stripped:
                continue
            pattern = stripped.split()[0]
            self.assertNotIn(
                "**", pattern.replace("**/*.jsonl", ""),
                f"{pattern} is a wildcard over Markdown; name the record instead")

    def test_worktree_setup_asserts_both_directions(self) -> None:
        body = text(BIN_DIR / "worktree-setup.sh")
        self.assertIn("MERGE_UNION_NEVER_PROBES", body)
        self.assertIn("results/telemetry/owner-tools/README.md", body)


# ---------------------------------------------------------------------------
# Finding 3 — watchdog/account-mode was a second file holding a capacity decision
# ---------------------------------------------------------------------------

class RunModeCase(unittest.TestCase):
    """A temporary cache root and repo with the committed template as the brief."""

    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        root = Path(self._tmp.name)
        self.cache, self.repo = root / "cache", root / "repo"
        (self.repo / "results/telemetry/owner-tools").mkdir(parents=True)
        shutil.copy(TEMPLATE, self.repo / "results/telemetry/owner-tools/run-brief.template.json")
        shutil.copy(SHIM_TEMPLATE, self.repo / "results/telemetry/owner-tools/owner-bin-codex")
        (self.cache / "owner-bin").mkdir(parents=True)
        shim = self.cache / "owner-bin" / "codex"
        shutil.copy(SHIM_TEMPLATE, shim)
        shim.chmod(0o755)
        self._env = dict(os.environ)
        os.environ["MIPSTARRE_CACHE_ROOT"] = str(self.cache)
        os.environ["MIPSTARRE_REPO_ROOT"] = str(self.repo)
        os.environ.pop("MIPSTARRE_OWNER_BIN", None)
        self.brief = self.cache / "watchdog" / "run-brief.json"
        self.brief.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy(TEMPLATE, self.brief)

    def tearDown(self) -> None:
        os.environ.clear()
        os.environ.update(self._env)
        self._tmp.cleanup()

    def run_cli(self, argv: list[str]) -> tuple[int, str, str]:
        out, err = io.StringIO(), io.StringIO()
        with redirect_stdout(out), redirect_stderr(err):
            code = run_mode.main(argv)
        return code, out.getvalue(), err.getvalue()

    def write_brief(self, mutate) -> None:
        doc = json.loads(text(TEMPLATE))
        mutate(doc)
        self.brief.write_text(json.dumps(doc), encoding="utf-8")

    @property
    def account_mode_file(self) -> Path:
        return self.cache / "watchdog" / "account-mode"


class AccountModeTestCase(RunModeCase):
    def test_apply_writes_both_when_two_accounts_are_enabled(self) -> None:
        self.write_brief(lambda doc: [a.update(enabled=True) for a in doc["accounts"]])
        code, out, err = self.run_cli(["apply"])
        self.assertEqual(code, 0, err)
        self.assertEqual(text(self.account_mode_file).strip(), "both",
                         "an enabled second account whose CODEX_HOME is not ~/.codex "
                         "cannot dispatch at all while this file says 'primary'")
        self.assertIn("account-mode", out)

    def test_apply_writes_primary_when_only_one_account_is_enabled(self) -> None:
        self.write_brief(lambda doc: doc["accounts"][1].update(enabled=False))
        self.assertEqual(self.run_cli(["apply"])[0], 0)
        self.assertEqual(text(self.account_mode_file).strip(), "primary")

    def test_the_file_is_queryable_and_shown(self) -> None:
        self.write_brief(lambda doc: [a.update(enabled=True) for a in doc["accounts"]])
        self.assertEqual(self.run_cli(["apply"])[0], 0)
        self.assertEqual(self.run_cli(["get", "account_mode"])[1].strip(), "both")
        self.assertIn("account mode     both", self.run_cli(["show"])[1])

    def test_pause_and_resume_keep_the_file_in_step_with_the_brief(self) -> None:
        self.write_brief(lambda doc: [a.update(enabled=True) for a in doc["accounts"]])
        self.assertEqual(self.run_cli(["apply"])[0], 0)
        self.account_mode_file.write_text("primary\n", encoding="utf-8")
        self.assertEqual(self.run_cli(["pause"])[0], 0)
        self.assertEqual(text(self.account_mode_file).strip(), "both")
        self.account_mode_file.unlink()
        self.assertEqual(self.run_cli(["resume"])[0], 0)
        self.assertEqual(text(self.account_mode_file).strip(), "both")

    def test_a_dry_run_writes_nothing_but_names_the_file(self) -> None:
        self.account_mode_file.parent.mkdir(parents=True, exist_ok=True)
        code, out, err = self.run_cli(["apply", "--dry-run"])
        self.assertEqual(code, 0, err)
        self.assertIn("account-mode", out)
        self.assertFalse(self.account_mode_file.exists())

    def test_owner_resume_fails_when_the_file_and_the_brief_disagree(self) -> None:
        body = text(TOOLS / "owner-resume.sh")
        self.assertIn("get account_mode", body)
        block = body.split('AM_WANT=', 1)
        self.assertEqual(len(block), 2, "owner-resume.sh must read the derived mode")
        # The comparison and its exit-5 must be in the same block, or the check
        # reports and resumes anyway.
        self.assertIn('[ "$AM" != "$AM_WANT" ]', block[1])
        self.assertIn("RC=5", block[1][:900])

    def test_the_shim_no_longer_invents_a_model(self) -> None:
        body = text(SHIM_TEMPLATE)
        self.assertNotIn("model=gpt-6-astra", body,
                         "full-speed-mode.md section 5: a hard-coded model anywhere "
                         "else is a defect; every caller names the model")
        self.assertNotIn('exec "$REAL_CODEX" -m "$model"', body)
        self.assertIn("MODEL_ARGS", body)


# ---------------------------------------------------------------------------
# Finding 6 — `show --oneline` did not exist, and two callers rendered from it
# ---------------------------------------------------------------------------

class ShowOnelineTestCase(RunModeCase):
    def test_show_oneline_is_one_line_and_carries_the_run(self) -> None:
        self.assertEqual(self.run_cli(["apply"])[0], 0)
        code, out, err = self.run_cli(["show", "--oneline"])
        self.assertEqual(code, 0, err)
        self.assertEqual(len(out.strip().splitlines()), 1, out)
        mode = run_mode.load_mode()
        run = mode["run"]
        for token in (f"speed={run['speed']}",
                      f"progress=#{run['progress_issue']}",
                      f"estimate=#{run['estimate_issue']}",
                      f"inbox=#{run['owner_inbox_issue']}",
                      f"floor={run_mode.value_for(mode, 'floor')}",
                      f"accounts={run_mode.account_mode(mode)}"):
            with self.subTest(token=token):
                self.assertIn(token, out)

    def test_the_one_liner_names_the_effective_override(self) -> None:
        self.write_brief(lambda doc: (doc["run"].update(speed="fast"),
                                      doc["models"].update(override=None)))
        self.assertEqual(self.run_cli(["apply"])[0], 0)
        self.assertIn("model=astra-all", self.run_cli(["show", "--oneline"])[1])

    def test_a_paused_run_says_so(self) -> None:
        self.assertEqual(self.run_cli(["apply"])[0], 0)
        self.assertEqual(self.run_cli(["pause"])[0], 0)
        self.assertIn("PAUSED", self.run_cli(["show", "--oneline"])[1])

    def test_json_and_oneline_are_exclusive(self) -> None:
        self.assertEqual(self.run_cli(["apply"])[0], 0)
        code, _, err = self.run_cli(["show", "--json", "--oneline"])
        self.assertNotEqual(code, 0)
        self.assertIn("not both", err)

    def test_both_shipped_callers_still_call_it(self) -> None:
        for name in ("goal-keeper.sh", "owner-resume.sh"):
            with self.subTest(tool=name):
                self.assertIn("show --oneline", text(TOOLS / name))


# ---------------------------------------------------------------------------
# Findings 4 and 5 — the hourly comment carries the residue and the model census
# ---------------------------------------------------------------------------

class HourlyCensusTestCase(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        root = Path(self._tmp.name)
        self.cache, self.repo = root / "cache", root / "repo"
        (self.repo / "results" / "telemetry").mkdir(parents=True)
        (self.cache / "watchdog" / "janitor").mkdir(parents=True)
        self.now = datetime.now(timezone.utc)
        self.since = self.now - timedelta(minutes=60)

    def tearDown(self) -> None:
        self._tmp.cleanup()

    def sessions(self, rows: list[dict]) -> None:
        path = self.repo / "results" / "telemetry" / "sessions.jsonl"
        with path.open("w", encoding="utf-8") as handle:
            for row in rows:
                handle.write(json.dumps(row) + "\n")

    def actions(self, rows: list[dict]) -> None:
        path = self.cache / "watchdog" / "janitor" / "actions.jsonl"
        with path.open("w", encoding="utf-8") as handle:
            for row in rows:
                handle.write(json.dumps(row) + "\n")

    def stamp(self, minutes_ago: int) -> str:
        return (self.now - timedelta(minutes=minutes_ago)).strftime("%Y-%m-%dT%H:%M:%SZ")

    # -- finding 5: W9(5), the per-resolved-model count -------------------

    def test_the_census_groups_by_the_model_that_actually_ran(self) -> None:
        self.sessions([
            {"start": self.stamp(10), "model": "gpt-6-astra", "role": "reviewer"},
            {"start": self.stamp(20), "model": "gpt-6-astra", "role": "prover"},
            {"start": self.stamp(30), "model": "gpt-5.6-sol", "role": "reviewer"},
            {"start": self.stamp(600), "model": "gpt-5.6-sol", "role": "orc"},
        ])
        census = ready_report.model_census(self.repo, self.since)
        self.assertEqual(census["total"], 3, "only the window counts")
        self.assertEqual(census["by_model"], {"gpt-6-astra": 2, "gpt-5.6-sol": 1})

    def test_off_policy_counts_rows_that_disagree_with_the_override(self) -> None:
        self.sessions([
            {"start": self.stamp(5), "model": "gpt-6-astra", "role": "prover"},
            {"start": self.stamp(6), "model": "gpt-5.6-sol", "role": "reviewer"},
        ])
        census = dict(ready_report.model_census(self.repo, self.since))
        census.update(override="astra-all", expected="gpt-6-astra")
        census["off_policy"] = sum(count for name, count in census["by_model"].items()
                                   if name != census["expected"])
        body = ready_report.render([], 0, window_min=60, ts="t", unexplained=0,
                                   models=census)
        self.assertIn("off-policy 1", body)
        self.assertIn("alarm", body, "a wrong model must be flagged the way "
                                     "`unexplained` is, not merely printed")

    def test_no_override_means_no_expectation_and_no_alarm(self) -> None:
        census = {"override": "none", "expected": None, "total": 2,
                  "by_model": {"gpt-5.6-sol": 2}, "off_policy": 0}
        body = ready_report.render([], 0, window_min=60, ts="t", unexplained=0,
                                   models=census)
        self.assertIn("gpt-5.6-sol 2", body)
        self.assertNotIn("off-policy", body)

    def test_the_census_reaches_the_latency_records(self) -> None:
        census = {"override": "astra-all", "expected": "gpt-6-astra", "total": 1,
                  "by_model": {"gpt-5.6-sol": 1}, "off_policy": 1}
        rows = ready_report.latency_rows([], 0, 0, "t", census, None)
        events = [row["event"] for row in rows]
        self.assertIn("models", events)
        record = next(row for row in rows if row["event"] == "models")
        self.assertIn("off_policy=1", record["reason"])

    # -- finding 4: the janitor's residue reaches the owner's channel ------

    def test_dead_sessions_not_redispatched_are_counted_per_role(self) -> None:
        self.actions([
            {"ts": self.stamp(5), "pass": "dead-sessions", "action": "mark-failed",
             "role": "prover", "residue": "role-not-auto-re-dispatched", "dry_run": "0"},
            {"ts": self.stamp(6), "pass": "dead-sessions", "action": "mark-failed",
             "role": "prover", "residue": "role-not-auto-re-dispatched", "dry_run": "0"},
            {"ts": self.stamp(7), "pass": "dead-sessions", "action": "mark-failed",
             "role": "orc", "residue": "role-not-auto-re-dispatched", "dry_run": "0"},
            {"ts": self.stamp(8), "pass": "dead-sessions", "action": "redispatch",
             "role": "reviewer", "dry_run": "0"},
            {"ts": self.stamp(9), "pass": "dead-sessions", "action": "mark-failed",
             "role": "prover", "dry_run": "1"},
            {"ts": self.stamp(400), "pass": "dead-sessions", "action": "mark-failed",
             "role": "prover", "dry_run": "0"},
        ])
        dead = ready_report.dead_session_residue(self.cache, self.since)
        self.assertEqual(dead["by_role"], {"prover": 2, "orc": 1},
                         "a re-dispatch is not residue, a dry run is not an action, "
                         "and the window is the window")
        self.assertEqual(dead["total"], 3)

    def test_the_residue_line_names_the_roles_and_the_scope(self) -> None:
        dead = {"by_role": {"prover": 2, "orc": 1}, "total": 3,
                "redispatched_roles": ["reviewer"]}
        body = ready_report.render([], 0, window_min=60, ts="t", unexplained=0,
                                   dead=dead)
        self.assertIn("prover 2", body)
        self.assertIn("orc 1", body)
        self.assertIn("reviewer", body)

    def test_no_residue_adds_no_line(self) -> None:
        dead = {"by_role": {}, "total": 0, "redispatched_roles": ["reviewer"]}
        body = ready_report.render([], 0, window_min=60, ts="t", unexplained=0,
                                   dead=dead)
        self.assertNotIn("NOT re-dispatched", body)

    def test_the_janitor_records_the_residue_it_leaves(self) -> None:
        body = text(BIN_DIR / "janitor.sh")
        self.assertIn("residue role-not-auto-re-dispatched", body)
        self.assertIn("residue retry-cap-reached", body)
        self.assertIn("residue no-pr-on-the-row", body)

    def test_the_documents_no_longer_claim_every_role_is_re_dispatched(self) -> None:
        evolution = text(PROTOCOLS / "EVOLUTION.md")
        self.assertIn("A dead prover, orc or fixer is NOT re-dispatched", evolution)
        speed = text(PROTOCOLS / "full-speed-mode.md")
        self.assertIn("re-dispatches **`reviewer` only**", speed)
        self.assertIn("dead sessions marked failed and NOT re-dispatched", speed)


if __name__ == "__main__":
    unittest.main()
