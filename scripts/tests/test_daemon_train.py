#!/usr/bin/env python3
"""Offline routing and preparation fixtures for daemon-owned reviewed trains."""

from __future__ import annotations

import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest import mock

import daemon_train
from pr_merge import GateFailure


def git(repo: Path, *args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=repo, text=True).strip()


class DaemonTrainTests(unittest.TestCase):
    def setUp(self) -> None:
        holder = tempfile.TemporaryDirectory()
        self.addCleanup(holder.cleanup)
        self.repo = Path(holder.name) / "primary"
        self.remote = Path(holder.name) / "remote.git"
        self.repo.mkdir()
        git(self.repo, "init", "-q", "--initial-branch=main", "--template=")
        git(self.repo, "config", "user.name", "Offline fixture")
        git(self.repo, "config", "user.email", "fixture@example.invalid")
        git(self.repo, "config", "commit.gpgsign", "false")
        (self.repo / "README").write_text("base\n")
        git(self.repo, "add", "README")
        git(self.repo, "commit", "-qm", "base")
        self.base = git(self.repo, "rev-parse", "HEAD")
        git(self.repo, "init", "-q", "--bare", str(self.remote))
        git(self.remote, "fetch", "-q", str(self.repo), "main")
        git(self.remote, "update-ref", "refs/heads/main", git(self.remote, "rev-parse", "FETCH_HEAD"))
        git(self.repo, "remote", "add", "github", str(self.remote))
        git(self.repo, "fetch", "-q", "github", "main")
        self.first = "a" * 40
        self.second = "b" * 40
        self.batch = Path(holder.name) / "approved.json"
        self.batch.write_text(json.dumps({"members": [
            {"number": 580, "head": self.first}, {"number": 587, "head": self.second}]}))
        self.scan = (f"580:580:issue-580-one:one:clean:{self.first}\n"
                     f"587:587:issue-587-two:two:clean:{self.second}\n"
                     f"260:260:issue-260-adj:adj:adj:{'c' * 40}\n")

    def select(self, scan: str | None = None) -> list[int]:
        with mock.patch.object(daemon_train.pr_merge, "head_is_fresh", return_value=False), \
             mock.patch.object(daemon_train.pr_train, "claim_call", return_value=(0, "free")):
            return daemon_train.select(self.repo, daemon_train.pinned_batch(self.batch),
                                       self.scan if scan is None else scan)

    def test_only_pinned_clean_stale_heads_route_to_train(self) -> None:
        self.assertEqual(self.select(), [580, 587])

    def test_head_change_or_adjudication_refuses_batch(self) -> None:
        for scan in (self.scan.replace(self.first, "d" * 40),
                     self.scan.replace(":clean:", ":adj:", 1),
                     self.scan.replace("587:587", "588:588")):
            with self.subTest(scan=scan), self.assertRaises(GateFailure):
                self.select(scan)

    def test_fresh_member_and_active_claim_refuse_before_preparation(self) -> None:
        with mock.patch.object(daemon_train.pr_merge, "head_is_fresh",
                               side_effect=[False, True]), \
             mock.patch.object(daemon_train.pr_train, "claim_call", return_value=(0, "free")):
            with self.assertRaisesRegex(GateFailure, "fresh"):
                daemon_train.select(self.repo, daemon_train.pinned_batch(self.batch), self.scan)
        with mock.patch.object(daemon_train.pr_merge, "head_is_fresh", return_value=False), \
             mock.patch.object(daemon_train.pr_train, "claim_call",
                               return_value=(3, "opus-fix 580 claimed")):
            with self.assertRaisesRegex(GateFailure, "opus-fix 580 claimed"):
                daemon_train.select(self.repo, daemon_train.pinned_batch(self.batch), self.scan)

    def test_malformed_scan_and_bad_pins_fail_closed(self) -> None:
        with self.assertRaisesRegex(GateFailure, "malformed"):
            self.select(self.scan + "garbage\n")
        self.batch.write_text(json.dumps({"members": [
            {"number": 580, "head": self.first}, {"number": 580, "head": self.second}]}))
        with self.assertRaisesRegex(GateFailure, "distinct"):
            daemon_train.pinned_batch(self.batch)

    def test_preparation_retains_local_telemetry_and_uses_existing_sync(self) -> None:
        telemetry = self.repo / "results/telemetry"
        telemetry.mkdir(parents=True)
        (telemetry / "events.md").write_text("existing record\n")
        git(self.repo, "add", "results/telemetry/events.md")
        git(self.repo, "commit", "-qm", "chore(telemetry): previous record")
        prior = git(self.repo, "rev-parse", "HEAD")
        (telemetry / "builds.jsonl").write_text('{"event":"pending"}\n')
        calls = []

        real_run = subprocess.run

        def sync(args: list[str], **kwargs: object) -> subprocess.CompletedProcess:
            if args[0] != str(self.repo / "local/bin/github-sync.sh"):
                return real_run(args, **kwargs)
            calls.append(args)
            # Fixture-only fetch/ref update: no receive-pack or publisher.
            git(self.remote, "fetch", "-q", str(self.repo), "main")
            git(self.remote, "update-ref", "refs/heads/main", git(self.remote, "rev-parse", "FETCH_HEAD"))
            return subprocess.CompletedProcess(args, 0)

        with mock.patch.object(daemon_train.subprocess, "run", side_effect=sync):
            daemon_train.prepare_primary(self.repo)
        self.assertEqual(calls, [[str(self.repo / "local/bin/github-sync.sh"), "main"]])
        self.assertEqual(git(self.repo, "rev-parse", "HEAD"), git(self.repo, "rev-parse", "github/main"))
        self.assertEqual(git(self.repo, "rev-parse", "HEAD^"), prior)
        self.assertIn("existing record", (telemetry / "events.md").read_text())
        self.assertEqual(git(self.repo, "status", "--porcelain"), "")

    def test_nontelemetry_dirt_or_divergence_refuses_without_sync(self) -> None:
        (self.repo / "README").write_text("uncommitted code\n")
        real_run = subprocess.run

        def forbid_sync(args: list[str], **kwargs: object) -> subprocess.CompletedProcess:
            if args[0] != "git":
                self.fail(f"publisher invoked: {args}")
            return real_run(args, **kwargs)

        with mock.patch.object(daemon_train.subprocess, "run", side_effect=forbid_sync):
            with self.assertRaisesRegex(GateFailure, "outside telemetry"):
                daemon_train.prepare_primary(self.repo)
        git(self.repo, "restore", "README")
        (self.repo / "README").write_text("committed code\n")
        git(self.repo, "commit", "-qam", "change code")
        with mock.patch.object(daemon_train.subprocess, "run", side_effect=forbid_sync):
            with self.assertRaisesRegex(GateFailure, "telemetry-only"):
                daemon_train.prepare_primary(self.repo)

    def test_train_failure_is_not_described_as_a_merge(self) -> None:
        with mock.patch.object(daemon_train, "select", return_value=[580, 587]), \
             mock.patch.object(daemon_train, "prepare_primary"), \
             mock.patch.object(daemon_train.subprocess, "run",
                               return_value=subprocess.CompletedProcess([], 1)) as train:
            self.assertEqual(daemon_train.run(self.repo, self.batch, self.scan), 1)
            self.assertEqual(train.call_args.args[0][-2:], ["580", "587"])


if __name__ == "__main__":
    unittest.main()
