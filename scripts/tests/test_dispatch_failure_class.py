#!/usr/bin/env python3
"""Regression tests for local/bin/telemetry.py failure classification.

Covers the machine-readable half of the 2026-09-12 run: a provider refusal has
a class, a class has an endpoint, a refusal is not a failed attempt, both
accounts carry a key label, and the incident log is sharded so two sessions
never write one path.
"""

from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
BIN_DIR = REPO_ROOT / "local" / "bin"
sys.path.insert(0, str(BIN_DIR))

import telemetry  # noqa: E402


# ── fixtures ────────────────────────────────────────────────────────────────


def _stream(*lines: str) -> list[dict]:
    """A capture whose events carry the given provider text."""
    events: list[dict] = [{"type": "thread.started", "thread_id": "t-0001"}]
    for line in lines:
        events.append({"type": "error", "message": line})
    return events


def _finished_stream(text: str = "done") -> list[dict]:
    return [
        {"type": "thread.started", "thread_id": "t-0002"},
        {"type": "turn.completed", "usage": {"input_tokens": 10, "output_tokens": 5}},
        {"type": "item.completed", "item": {"item_type": "assistant_message", "text": text}},
    ]


CONCURRENCY = _stream(
    "stream error: Concurrency limit exceeded for account; retrying",
    "Reconnecting... 5/5",
)
FIVE_HUNDRED_THREE = _stream(
    "stream error: unexpected status 503 Service Unavailable from "
    "https://relay-us7.example/v1/responses",
    "Reconnecting... 5/5",
)
RECONNECTS = _stream("stream disconnected; Reconnecting... 5/5")
TIMEOUT = _stream("upstream request timed out after 600s")
TASK_FAILURE = _finished_stream("could not close the goal")
# A capture that just stops: no known wording, no model turn.  This is the case
# the controller must treat as neutral.
UNKNOWN_ENDING = [{"type": "thread.started", "thread_id": "t-0003"},
                  {"type": "item.started", "item": {"item_type": "command_execution"}}]


def _repo(root: Path) -> Path:
    (root / "local" / "bin").mkdir(parents=True)
    (root / "results" / "telemetry").mkdir(parents=True)
    return root


# ── classify_failure ────────────────────────────────────────────────────────


class ClassifyFailureTests(unittest.TestCase):
    def test_each_recorded_pattern_gets_its_class(self) -> None:
        cases = {
            "concurrency_limit": CONCURRENCY,
            "endpoint_5xx": FIVE_HUNDRED_THREE,
            "retries_exhausted": RECONNECTS,
            "timeout": TIMEOUT,
        }
        for expected, events in cases.items():
            with self.subTest(expected):
                self.assertEqual(
                    telemetry.classify_failure(
                        events, patterns=telemetry.DEFAULT_FAILURE_PATTERNS
                    )["failure_class"],
                    expected,
                )

    def test_unknown_ending_is_the_safe_default(self) -> None:
        result = telemetry.classify_failure(
            UNKNOWN_ENDING, patterns=telemetry.DEFAULT_FAILURE_PATTERNS
        )
        self.assertEqual(result["failure_class"], "unknown")
        self.assertEqual(result["retries_seen"], 0)

    def test_clean_nonzero_exit_with_model_output_is_a_task_failure(self) -> None:
        result = telemetry.classify_failure(
            TASK_FAILURE, exit_code=1, patterns=telemetry.DEFAULT_FAILURE_PATTERNS
        )
        self.assertEqual(result["failure_class"], "task_failure")

    def test_exit_zero_is_no_failure(self) -> None:
        result = telemetry.classify_failure(
            _finished_stream(), exit_code=0, patterns=telemetry.DEFAULT_FAILURE_PATTERNS
        )
        self.assertEqual(result["failure_class"], "none")

    def test_concurrency_wins_over_the_exhausted_reconnect_it_causes(self) -> None:
        # Both wordings appear in the same capture; the controller must act on
        # the cause, not on the symptom.
        result = telemetry.classify_failure(
            CONCURRENCY, patterns=telemetry.DEFAULT_FAILURE_PATTERNS
        )
        self.assertEqual(result["failure_class"], "concurrency_limit")
        self.assertEqual(result["retries_seen"], 5)

    def test_endpoint_is_read_off_the_stream(self) -> None:
        result = telemetry.classify_failure(
            FIVE_HUNDRED_THREE, patterns=telemetry.DEFAULT_FAILURE_PATTERNS
        )
        self.assertEqual(result["failure_endpoint"], "relay-us7.example")

    def test_session_guard_kill_is_a_timeout_not_a_refusal(self) -> None:
        result = telemetry.classify_failure(
            UNKNOWN_ENDING, exit_code=124, patterns=telemetry.DEFAULT_FAILURE_PATTERNS
        )
        self.assertEqual(result["failure_class"], "timeout")
        self.assertNotIn("timeout", telemetry.TRANSIENT_FAILURE_CLASSES)


class PatternKnobTests(unittest.TestCase):
    def test_patterns_come_from_capacity_policy_when_present(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = _repo(Path(tmp))
            (root / "local" / "capacity-policy.json").write_text(
                json.dumps({"failure_patterns": {"concurrency_limit": ["OVER QUOTA"]}}),
                encoding="utf-8",
            )
            patterns = telemetry.load_failure_patterns(root)
            self.assertEqual(patterns["concurrency_limit"], ["OVER QUOTA"])
            # classes the file is silent about keep their built-in wording
            self.assertEqual(
                patterns["endpoint_5xx"],
                telemetry.DEFAULT_FAILURE_PATTERNS["endpoint_5xx"],
            )
            result = telemetry.classify_failure(_stream("over quota"), patterns=patterns)
            self.assertEqual(result["failure_class"], "concurrency_limit")

    def test_a_malformed_knob_degrades_to_the_built_in_table(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = _repo(Path(tmp))
            (root / "local" / "capacity-policy.json").write_text("{ not json",
                                                                encoding="utf-8")
            self.assertEqual(
                telemetry.load_failure_patterns(root),
                telemetry.DEFAULT_FAILURE_PATTERNS,
            )


# ── the session row ─────────────────────────────────────────────────────────


def _summarize(root: Path, events: list[dict], **kwargs) -> dict:
    capture = root / "results" / "telemetry" / "sessions" / "s.jsonl"
    capture.parent.mkdir(parents=True, exist_ok=True)
    capture.write_text("".join(json.dumps(e) + "\n" for e in events), encoding="utf-8")
    registry = root / "results" / "telemetry" / "sessions.jsonl"
    argv = ["--repo-root", str(root), "session-summarize", str(capture),
            "--name", "prover-42-20260913-01", "--role", "prover", "--issue", "42",
            "--append-to", str(registry), "--no-rollout-scan"]
    for key, value in kwargs.items():
        argv += ["--" + key.replace("_", "-"), str(value)]
    telemetry.main(argv)
    rows = [json.loads(line) for line in
            registry.read_text(encoding="utf-8").splitlines() if line.strip()]
    return rows[-1]


class SessionRowTests(unittest.TestCase):
    def test_a_refusal_is_not_scored_as_a_failed_attempt(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            row = _summarize(_repo(Path(tmp)), CONCURRENCY, exit_code=1,
                             key_label="space", endpoint="api.finite-dimensional.space")
            self.assertEqual(row["status"], "refused")
            self.assertIn("refused", telemetry.KNOWN_STATUSES)
            self.assertEqual(row["failure_class"], "concurrency_limit")
            self.assertEqual(row["retries_seen"], 5)
            self.assertEqual(row["endpoint"], "api.finite-dimensional.space")
            self.assertEqual(row["key_label"], "space")

    def test_a_real_task_failure_still_fails(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            row = _summarize(_repo(Path(tmp)), TASK_FAILURE, exit_code=1,
                             key_label="relay-1")
            self.assertEqual(row["status"], "failed")
            self.assertEqual(row["failure_class"], "task_failure")

    def test_every_row_carries_an_endpoint(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            row = _summarize(_repo(Path(tmp)), _finished_stream(), exit_code=0)
            self.assertEqual(row["endpoint"], "unknown")
            self.assertEqual(row["failure_class"], "none")
            self.assertEqual(row["status"], "done")

    def test_historical_key_labels_stay_valid(self) -> None:
        for label in ("relay-1", "space", "unknown"):
            with self.subTest(label), tempfile.TemporaryDirectory() as tmp:
                row = _summarize(_repo(Path(tmp)), _finished_stream(), exit_code=0,
                                 key_label=label)
                self.assertEqual(row["key_label"], label)

    def test_a_label_outside_the_class_fails_closed(self) -> None:
        for bad in ("Relay US7", "relay_us7", "a" * 41, "relay/us7"):
            with self.subTest(bad), tempfile.TemporaryDirectory() as tmp:
                with self.assertRaises(SystemExit) as caught:
                    _summarize(_repo(Path(tmp)), _finished_stream(), exit_code=0,
                               key_label=bad)
                self.assertNotEqual(caught.exception.code, 0)

    def test_a_long_dotted_label_is_accepted(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            row = _summarize(_repo(Path(tmp)), _finished_stream(), exit_code=0,
                             key_label="api.finite-dimensional.space")
            self.assertEqual(row["key_label"], "api.finite-dimensional.space")


# ── events.d sharding ───────────────────────────────────────────────────────


class EventShardTests(unittest.TestCase):
    def test_two_sessions_never_touch_one_path(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = _repo(Path(tmp))
            for session in ("orc-1-20260913-01", "prover-2-20260913-01"):
                telemetry.main(["--repo-root", str(root), "event", "--date", "2026-09-13",
                                "--session", session, "--text", f"{session} said something"])
            shards = sorted(p.name for p in (root / "results" / "telemetry" / "events.d")
                            .glob("*.md"))
            self.assertEqual(shards, ["2026-09-13-orc-1-20260913-01.md",
                                      "2026-09-13-prover-2-20260913-01.md"])
            # events.md is never rewritten by a shard write
            self.assertFalse((root / "results" / "telemetry" / "events.md").exists())

    def test_events_since_reads_the_history_and_the_shards(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = _repo(Path(tmp))
            (root / "results" / "telemetry" / "events.md").write_text(
                "# Incident and observation log\n\n"
                "## 2026-09-11\n\n- older incident\n\n"
                "## 2026-09-12T08:33:00Z — Pause of track A\n\n- the pause\n",
                encoding="utf-8",
            )
            telemetry.main(["--repo-root", str(root), "event", "--date", "2026-09-13",
                            "--session", "orc-1", "--text", "sharded incident"])
            rows = telemetry.collect_events(root / "results" / "telemetry")
            self.assertEqual([row["date"] for row in rows],
                             ["2026-09-11", "2026-09-12", "2026-09-13"])
            self.assertIn("the pause", rows[1]["body"])
            self.assertIn("sharded incident", rows[2]["body"])
            since = telemetry.collect_events(root / "results" / "telemetry",
                                             since="2026-09-12")
            self.assertEqual([row["date"] for row in since], ["2026-09-12", "2026-09-13"])

    def test_shard_paths_are_inside_the_tolerated_telemetry_allowlist(self) -> None:
        # pr_merge gate 2b tolerates passive telemetry paths; the shard must be
        # one of them or sharding would perturb the merge gate.
        sys.path.insert(0, str(BIN_DIR))
        import pr_merge  # noqa: E402

        self.assertTrue(pr_merge._is_tolerated_telemetry_path(
            "results/telemetry/events.d/2026-09-13-orc-1.md"))


if __name__ == "__main__":
    unittest.main()
