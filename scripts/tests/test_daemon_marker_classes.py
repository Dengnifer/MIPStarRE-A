#!/usr/bin/env python3
"""Regression tests for the merge daemon's failure markers and parallelism.

The marker record and its clearing rules exist because on 2026-09-12 05:44Z
eleven unrelated PRs stayed blocked by 2 h ``touch``ed ``pr<N>.failed`` files
after the systemic lane bugs had already been fixed, and were freed by hand
with ``rm`` and with ``( sleep 1500; rm -f ... )``.  The tests below pin:

* each documented lane-log string maps to its class;
* a marker parses and each class produces its documented backoff;
* a newer installed tools-version clears preflight and build markers ONLY;
* a head change clears every class, and elapsed time alone clears nothing
  except the two classes whose backoff IS the documented retry;
* PAR follows clamp(1, floor((nproc - load1) / cores_per_build), free_slots)
  and the daemon logs the inputs it used;
* the daemon refuses to start when its installed dependencies cannot be
  verified, instead of failing per PR at merge time.
"""

from __future__ import annotations

import importlib.util
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
TOOLS = REPO_ROOT / "results" / "telemetry" / "owner-tools"
SCAN = TOOLS / "daemon-scan.py"
DAEMON = TOOLS / "merge-daemon.sh"
MERGE = TOOLS / "merge.sh"
CONF = TOOLS / "daemon.conf"


def _code(text: str) -> str:
    """The script without its comment-only lines (headers cite historical paths)."""
    return "\n".join(line for line in text.splitlines() if not line.lstrip().startswith("#"))


def _load_scan():
    spec = importlib.util.spec_from_file_location("daemon_scan", SCAN)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


scan = _load_scan()


class ClassifyTests(unittest.TestCase):
    def test_documented_lane_strings(self) -> None:
        cases = {
            "== merging github/main conflicted in /w/issue-342-x": "conflict",
            "lake build before push failed (see 342.build.log)": "build",
            "lake build of changed modules failed (see 342.build.log)": "build",
            "pre-push gate failed (see 342.push.log)": "preflight",
            "codex: Reconnecting... 5/5": "infra",
            "gh: HTTP 503 Service Unavailable": "infra",
            "Concurrency limit exceeded": "infra",
            "merge of github/main left paths missing that main carries (issue #222): a.lean":
                "gate",
        }
        for line, expected in cases.items():
            with self.subTest(line=line):
                cls, reason = scan.classify_text(line)
                self.assertEqual(cls, expected)
                self.assertIn(line.strip()[:20], reason)

    def test_needs_attention_reason_slugs(self) -> None:
        for slug, expected in (("no-slot", "infra"), ("worktree-mismatch", "gate"),
                               ("build-failed", "build"), ("merge-conflicted", "conflict"),
                               ("pr-open-failed", "preflight")):
            with self.subTest(slug=slug):
                line = f"2026-09-12T05:44:00Z lane.sh version=abc reason={slug}: something"
                self.assertEqual(scan.classify_text(line)[0], expected)

    def test_last_failure_classifies(self) -> None:
        log = "\n".join([
            "== codex: Reconnecting... 5/5",
            "== recovered",
            "== lake build before push failed (see log)",
        ])
        self.assertEqual(scan.classify_text(log)[0], "build")

    def test_unknown_output_is_retried_not_parked(self) -> None:
        self.assertEqual(scan.classify_text("something nobody has seen before")[0], "infra")

    def test_merge_log_source(self) -> None:
        self.assertEqual(scan.classify_text("MERGE_FAILED rc=3", source="merge")[0], "gate")
        self.assertEqual(scan.classify_text("REBASE_FAILED", source="merge")[0], "conflict")


class MarkerRecordTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.tmp, True)

    def _write(self, cls: str, **kwargs) -> dict:
        path = self.tmp / "pr342.failed"
        args = ["--path", str(path), "--pr", "342", "--head", kwargs.get("head", "aaaa"),
                "--class", cls, "--reason", kwargs.get("reason", "because"),
                "--tools-version", kwargs.get("tools_version", "v1"),
                "--tools-ts", str(kwargs.get("tools_ts", 1000)),
                "--ts", str(kwargs.get("ts", 10_000))]
        subprocess.run([sys.executable, str(SCAN), "marker-write", *args],
                       check=True, capture_output=True, text=True)
        return json.loads(path.read_text(encoding="utf-8"))

    def test_record_parses_with_every_field(self) -> None:
        record = self._write("build")
        for key in ("pr", "head", "ts", "class", "reason", "attempts", "lane_log",
                    "tools_version"):
            self.assertIn(key, record)
        self.assertEqual(record["class"], "build")
        self.assertEqual(record["attempts"], 1)

    def test_attempts_increment_on_the_same_head(self) -> None:
        self._write("infra")
        self.assertEqual(self._write("infra")["attempts"], 2)

    def test_documented_backoff_per_class(self) -> None:
        now = 10_000
        expectations = {
            # class: (decision at +0s, at +600s, at +100000s), nothing else
            # about the world having changed
            "infra": ("block", "clear", "clear"),        # 5 min, then retried
            "preflight": ("block", "block", "clear"),    # 15 min, then retried
            "conflict": ("block", "block", "block"),     # until the repair ends
            "build": ("block", "block", "block"),        # until the repair ends
            "gate": ("block", "block", "block"),         # until the head changes
            "adjudication": ("block", "block", "block"),
        }
        for cls, (early, mid, late) in expectations.items():
            record = {"class": cls, "head": "aaaa", "ts": now, "attempts": 1,
                      "tools_version": "v1", "tools_ts": 1000}
            with self.subTest(cls=cls):
                self.assertEqual(scan.decide(record, head="aaaa", now=now)[0], early)
                self.assertEqual(scan.decide(record, head="aaaa", now=now + 600)[0], mid)
                self.assertEqual(scan.decide(record, head="aaaa", now=now + 100_000)[0], late)

    def test_class_backoff_boundaries(self) -> None:
        for cls, wait in (("infra", 300), ("preflight", 900)):
            record = {"class": cls, "head": "aaaa", "ts": 0, "attempts": 1}
            with self.subTest(cls=cls):
                self.assertEqual(scan.decide(record, head="aaaa", now=wait - 1)[0], "block")
                self.assertEqual(scan.decide(record, head="aaaa", now=wait),
                                 ("clear", "backoff-elapsed", 0))

    def test_repair_states_drive_conflict_and_build(self) -> None:
        for cls in ("conflict", "build"):
            record = {"class": cls, "head": "aaaa", "ts": 0, "attempts": 1}
            with self.subTest(cls=cls):
                self.assertEqual(scan.decide(record, head="aaaa", repair_state="none")[1],
                                 "awaiting-repair")
                self.assertEqual(scan.decide(record, head="aaaa", repair_state="running")[0],
                                 "block")
                self.assertEqual(scan.decide(record, head="aaaa", repair_state="done"),
                                 ("clear", "repair-finished", 0))
                self.assertEqual(scan.decide(record, head="aaaa", repair_state="exhausted")[1],
                                 "repair-exhausted")

    def test_head_change_clears_every_class(self) -> None:
        for cls in scan.CLASSES:
            record = {"class": cls, "head": "aaaa", "ts": 0, "attempts": 1}
            with self.subTest(cls=cls):
                self.assertEqual(scan.decide(record, head="bbbb")[1], "head-changed")

    def test_newer_tools_version_clears_preflight_and_build_only(self) -> None:
        for cls in scan.CLASSES:
            record = {"class": cls, "head": "aaaa", "ts": 0, "attempts": 1,
                      "tools_version": "v1", "tools_ts": 1000}
            decision, why, _ = scan.decide(record, head="aaaa", tools_version="v2",
                                           tools_ts=2000, now=10)
            with self.subTest(cls=cls):
                if cls in ("preflight", "build"):
                    self.assertEqual((decision, why), ("clear", "tools-version"))
                else:
                    self.assertNotEqual(why, "tools-version")

    def test_older_or_equal_tools_version_clears_nothing(self) -> None:
        record = {"class": "build", "head": "aaaa", "ts": 0, "attempts": 1,
                  "tools_version": "v2", "tools_ts": 2000}
        self.assertEqual(scan.decide(record, head="aaaa", tools_version="v1",
                                     tools_ts=1000)[0], "block")

    def test_conflict_clears_when_the_reason_is_gone(self) -> None:
        record = {"class": "conflict", "head": "aaaa", "ts": 0, "attempts": 1}
        self.assertEqual(scan.decide(record, head="aaaa", reason_gone=True)[1], "reason-gone")

    def test_legacy_touched_marker_is_infra_and_self_clears(self) -> None:
        path = self.tmp / "pr99.failed"
        path.touch()
        record = scan.load_marker(path)
        self.assertEqual(record["class"], "infra")
        self.assertEqual(record["pr"], 99)
        # no tools_version recorded: an upgrade must not be claimed
        self.assertEqual(scan.decide(record, tools_version="v9")[0], "block")
        self.assertEqual(scan.decide(record, now=record["ts"] + 301)[1], "backoff-elapsed")

    def test_unbounded_infra_retry_is_bounded(self) -> None:
        record = {"class": "infra", "head": "aaaa", "ts": 0, "attempts": 99}
        self.assertEqual(scan.decide(record, head="aaaa", now=10_000)[1],
                         "infra-attempts-exhausted")

    def test_marker_check_exit_codes(self) -> None:
        path = self.tmp / "pr342.failed"
        self._write("gate")
        blocked = subprocess.run([sys.executable, str(SCAN), "marker-check", "--path", str(path),
                                  "--head", "aaaa"], capture_output=True, text=True)
        self.assertEqual(blocked.returncode, 0)
        self.assertTrue(blocked.stdout.startswith("block "))
        cleared = subprocess.run([sys.executable, str(SCAN), "marker-check", "--path", str(path),
                                  "--head", "bbbb"], capture_output=True, text=True)
        self.assertEqual(cleared.returncode, 10)
        self.assertTrue(cleared.stdout.startswith("clear "))

    def test_marker_list_is_one_line_per_marker(self) -> None:
        self._write("build")
        out = self.tmp / "markers.json"
        proc = subprocess.run([sys.executable, str(SCAN), "marker-list", "--dir", str(self.tmp),
                               "--json-out", str(out)], capture_output=True, text=True, check=True)
        self.assertEqual(len(proc.stdout.strip().splitlines()), 1)
        self.assertIn("reason=because", proc.stdout)
        self.assertEqual(len(json.loads(out.read_text())["markers"]), 1)


class LatencyRowTests(unittest.TestCase):
    def test_one_row_per_transition(self) -> None:
        tmp = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, tmp, True)
        path = tmp / "merge-latency.jsonl"
        for event in scan.LATENCY_EVENTS:
            subprocess.run([sys.executable, str(SCAN), "latency", "--file", str(path),
                            "--pr", "342", "--head", "aaaa", "--event", event,
                            "--seconds", "12", "--par", "3"], check=True, capture_output=True)
        rows = [json.loads(line) for line in path.read_text().splitlines()]
        self.assertEqual([row["event"] for row in rows], list(scan.LATENCY_EVENTS))
        self.assertEqual(rows[0]["par"], 3)
        self.assertEqual(rows[0]["seconds"], 12)

    def test_unknown_event_is_refused(self) -> None:
        tmp = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, tmp, True)
        proc = subprocess.run([sys.executable, str(SCAN), "latency", "--file",
                               str(tmp / "x.jsonl"), "--pr", "1", "--event", "invented"],
                              capture_output=True, text=True)
        self.assertEqual(proc.returncode, 2)


class AdaptiveParTests(unittest.TestCase):
    def test_formula(self) -> None:
        # ghz: 128 cores, load 90 from other users' jobs, 16 cores per build
        self.assertEqual(scan.adaptive_par(128, 90.0, 16, 4), 2)
        # free worker slots are the upper clamp
        self.assertEqual(scan.adaptive_par(128, 0, 16, 3), 3)
        self.assertEqual(scan.adaptive_par(128, 0, 16, 99), 8)
        # an overloaded host still makes progress, one refresh at a time
        self.assertEqual(scan.adaptive_par(128, 200, 16, 4), 1)
        self.assertEqual(scan.adaptive_par(128, 0, 16, 0), 1)


@unittest.skipUnless(shutil.which("bash") and shutil.which("git"), "bash and git are required")
class DaemonScriptTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.tmp, True)
        self.tools = self.tmp / "tools"
        self.tools.mkdir()
        for path in (DAEMON, MERGE, SCAN, CONF):
            shutil.copy(path, self.tools / path.name)
        self.checkout = self.tmp / "checkout"
        (self.checkout / "local" / "bin").mkdir(parents=True)
        for name in ("lane.sh", "worktree_resolve.sh"):
            source = REPO_ROOT / "local" / "bin" / name
            if source.exists():
                shutil.copy(source, self.checkout / "local" / "bin" / name)
        for args in (["init", "-q", "."], ["add", "-A"],
                     ["-c", "user.email=t@example.invalid", "-c", "user.name=test",
                      "commit", "-qm", "init", "--allow-empty"]):
            subprocess.run(["git", *args], cwd=str(self.checkout), capture_output=True)
        self.cache = self.tmp / "cache"
        (self.cache / "watchdog" / "daemon").mkdir(parents=True)

    def _env(self, **extra) -> dict:
        env = dict(os.environ)
        env.update({
            "MIPSTARRE_CACHE_ROOT": str(self.cache),
            "MIPSTARRE_CHECKOUT": str(self.checkout),
            "MIPSTARRE_OWNER_BIN": str(self.tmp / "owner-bin"),
        })
        env.update({k: str(v) for k, v in extra.items()})
        return env

    def test_shell_syntax(self) -> None:
        for script in (DAEMON, MERGE, CONF):
            with self.subTest(script=script.name):
                proc = subprocess.run(["bash", "-n", str(script)], capture_output=True, text=True)
                self.assertEqual(proc.returncode, 0, proc.stderr)

    def test_no_tmp_paths_and_honest_names(self) -> None:
        """Operator scripts run from the repo or owner-bin, never from /tmp."""
        for path in (DAEMON, MERGE, SCAN, CONF):
            with self.subTest(script=path.name):
                self.assertNotIn("/tmp/", _code(path.read_text(encoding="utf-8")))
        daemon = _code(DAEMON.read_text(encoding="utf-8"))
        # the honest names of the two files the daemon calls
        self.assertIn('dep_path merge.sh', daemon)
        self.assertIn('dep_path daemon-scan.py', daemon)
        self.assertIn('dep_path fix-lane.sh', daemon)
        self.assertIn('$CHECKOUT/local/bin/lane.sh', daemon)
        for historical in ("merge-v2.sh", "lane-v17.sh", "merge-daemon-v9h.sh"):
            self.assertNotIn(historical, daemon)

    def test_merge_path_is_pr_merge_only(self) -> None:
        merge = MERGE.read_text(encoding="utf-8")
        self.assertIn("local/bin/pr_merge.py", merge)
        self.assertNotIn("--no-verify", merge)
        self.assertNotIn("MIPSTARRE_SKIP_HOOKS", merge)
        daemon = _code(DAEMON.read_text(encoding="utf-8"))
        # the daemon merges through merge.sh; it reads pr_merge only for the
        # gate-2b freshness predicate, and never runs the gate itself.
        self.assertIn('bash "$MERGE_SH" "$PR"', daemon)
        self.assertIn("head_is_fresh", daemon)
        self.assertNotIn('pr_merge.py "$PR"', daemon)

    def test_dry_loop_chooses_par_from_a_synthetic_load_and_logs_its_inputs(self) -> None:
        fixture = self.tmp / "scan.txt"
        fixture.write_text(
            "525:525:issue-525-pauli:pauli:clean:aaaaaaaa\n"
            "342:342:issue-342-games:games:clean:cccccccc\n"
            "263:263:issue-263-lift:lift:clean:dddddddd\n"
            "530:530:issue-530-old:old:retire:bbbbbbbb\n"
            "999:-:wip/experiment:-:offconv:eeeeeeee\n", encoding="utf-8")
        subprocess.run([sys.executable, str(SCAN), "marker-write",
                        "--path", str(self.cache / "watchdog" / "daemon" / "pr342.failed"),
                        "--pr", "342", "--head", "cccccccc", "--class", "conflict",
                        "--reason", "merging github/main conflicted", "--tools-version", "v1"],
                       check=True, capture_output=True)
        proc = subprocess.run(["bash", str(self.tools / "merge-daemon.sh"), "--dry-run"],
                              capture_output=True, text=True,
                              env=self._env(MIPSTARRE_DAEMON_SCAN_FIXTURE=fixture,
                                            MIPSTARRE_DAEMON_NPROC=128,
                                            MIPSTARRE_DAEMON_LOAD1="90.0",
                                            MIPSTARRE_DAEMON_FREE_SLOTS=4))
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        out = proc.stdout
        self.assertIn("par=2 (nproc=128 load1=90.0 cores_per_build=16 free_slots=4)", out)
        self.assertIn("would hand PR 530 to pr_janitor.py", out)
        self.assertIn("off-convention", out)
        self.assertIn("PR 342 held by its failure marker", out)
        self.assertIn("class=conflict", out)          # the hourly marker line
        # PAR bounds the launches: two refreshes, never three
        self.assertEqual(out.count("would refresh"), 2)
        # nothing was written outside the runtime cache
        self.assertFalse((self.checkout / "results").exists())

    def test_refuses_to_start_without_a_verified_dependency(self) -> None:
        proc = subprocess.run(["bash", str(self.tools / "merge-daemon.sh"), "--once"],
                              capture_output=True, text=True, env=self._env())
        self.assertEqual(proc.returncode, 3)
        self.assertIn("refusing to start", proc.stdout)
        self.assertIn("manifest", proc.stdout + proc.stderr)

    def test_conf_defaults_are_overridable_by_the_environment(self) -> None:
        text = CONF.read_text(encoding="utf-8")
        for key in ("cores_per_build", "train_max", "repair_attempts_per_head",
                    "backoff_infra_s", "backoff_preflight_s", "daemon_deps"):
            self.assertIn(f': "${{{key}:=', text)


if __name__ == "__main__":
    unittest.main()
