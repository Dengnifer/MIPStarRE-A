#!/usr/bin/env python3
"""End-to-end tests for local/bin/dispatch.sh: branch claim, spool, retry.

These run the real script against a throwaway repository, a throwaway cache
root and a stub `codex` on PATH.  Nothing here touches the network, ghz, or the
operator's cache.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
BIN_DIR = REPO_ROOT / "local" / "bin"
DISPATCH = BIN_DIR / "dispatch.sh"

COPIED = ("dispatch.sh", "telemetry.py", "model_policy.py", "account_router.py")

CODEX_STUB = r"""#!/usr/bin/env bash
# Stub codex: emits a recorded event stream chosen by MIPSTARRE_TEST_CODEX_MODE.
printf 'ran\n' >> "$MIPSTARRE_TEST_CODEX_MARKER"
printf '{"type":"thread.started","thread_id":"t-stub-0001"}\n'
case "${MIPSTARRE_TEST_CODEX_MODE:-ok}" in
  concurrency)
    printf '{"type":"error","message":"stream error: Concurrency limit exceeded for account"}\n'
    printf '{"type":"error","message":"Reconnecting... 5/5"}\n'
    exit 1
    ;;
  task-failure)
    printf '{"type":"turn.completed","usage":{"input_tokens":3,"output_tokens":1}}\n'
    printf '{"type":"item.completed","item":{"item_type":"assistant_message"}}\n'
    exit 1
    ;;
  *)
    printf '{"type":"turn.completed","usage":{"input_tokens":3,"output_tokens":1}}\n'
    printf '{"type":"item.completed","item":{"item_type":"assistant_message"}}\n'
    exit 0
    ;;
esac
"""

HOOK_STUB = "#!/usr/bin/env bash\nexit 0\n"

MODEL_POLICY = {
    "schema_version": 2,
    "default_model": "gpt-5.6-sol",
    "hard_model": "gpt-6-astra",
    "main_model": "gpt-6-astra",
    "effort": "ultra",
    "override": None,
}


def _git(repo: Path, *args: str) -> None:
    subprocess.run(["git", "-C", str(repo), *args], check=True,
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)


class DispatchFixture:
    """A repository, a cache root, a branch and a stub codex."""

    def __init__(self, tmp: Path) -> None:
        self.root = tmp
        self.repo = tmp / "repo"
        self.cache = tmp / "cache"
        self.bin = tmp / "bin"
        (self.repo / "local" / "bin").mkdir(parents=True)
        (self.repo / "local" / "personas").mkdir(parents=True)
        (self.repo / "scripts").mkdir(parents=True)
        (self.repo / "results" / "telemetry").mkdir(parents=True)
        for name in COPIED:
            shutil.copy2(BIN_DIR / name, self.repo / "local" / "bin" / name)
        os.chmod(self.repo / "local" / "bin" / "dispatch.sh", 0o755)
        (self.repo / "AGENTS.md").write_text("# AGENTS\n", encoding="utf-8")
        (self.repo / "local" / "model-policy.json").write_text(
            json.dumps(MODEL_POLICY), encoding="utf-8")
        for role in ("prover", "reviewer"):
            (self.repo / "local" / "personas" / f"{role}.md").write_text(
                f"You are a {role}.\n", encoding="utf-8")
        hook = self.repo / "scripts" / "install_git_hooks.sh"
        hook.write_text(HOOK_STUB, encoding="utf-8")
        os.chmod(hook, 0o755)

        _git(self.repo, "init", "-b", "main")
        _git(self.repo, "config", "user.email", "test@localhost")
        _git(self.repo, "config", "user.name", "test")
        _git(self.repo, "add", "-A")
        _git(self.repo, "commit", "-m", "fixture")
        _git(self.repo, "checkout", "-b", "issue-42-slug")

        self.bin.mkdir()
        codex = self.bin / "codex"
        codex.write_text(CODEX_STUB, encoding="utf-8")
        os.chmod(codex, 0o755)
        self.marker = tmp / "codex-ran.txt"

        (self.cache / "watchdog").mkdir(parents=True)
        (self.cache / "watchdog" / "max-codex-primary").write_text("2\n", encoding="utf-8")
        (self.cache / "watchdog" / "max-codex-second").write_text("0\n", encoding="utf-8")

    # -- helpers ------------------------------------------------------------

    def env(self, **extra: str) -> dict[str, str]:
        env = dict(os.environ)
        env.update({
            "PATH": f"{self.bin}:{env.get('PATH', '')}",
            "MIPSTARRE_CACHE_ROOT": str(self.cache),
            "MIPSTARRE_TEST_CODEX_MARKER": str(self.marker),
            "MIPSTARRE_SESSION": "test-operator",
            "MIPSTARRE_DISPATCH_BACKOFF_S": "1",
            "MIPSTARRE_DISPATCH_BACKOFF_MAX_S": "1",
            "MIPSTARRE_DISPATCH_ATTEMPTS": "1",
            "HOME": str(self.root / "home"),
        })
        for key in ("MIPSTARRE_KEY_LABEL", "MIPSTARRE_CODEX_MODEL", "MIPSTARRE_JOB_CLASS",
                    "MIPSTARRE_HARDNESS_REASON", "MIPSTARRE_DISPATCH_CUTOFF",
                    "MIPSTARRE_SESSION_TIMEOUT", "CODEX_HOME"):
            env.pop(key, None)
        env.update(extra)
        (self.root / "home").mkdir(exist_ok=True)
        return env

    def run(self, *args: str, **extra: str) -> subprocess.CompletedProcess:
        return subprocess.run(
            ["bash", str(self.repo / "local" / "bin" / "dispatch.sh"), *args],
            capture_output=True, text=True, env=self.env(**extra), cwd=str(self.repo))

    def dry_run(self, *args: str, **extra: str) -> subprocess.CompletedProcess:
        return self.run("--role", "prover", "--issue", "42", "--worktree", str(self.repo),
                        "--skip-hook-check", "--dry-run", *args, "--", "close the goal",
                        **extra)

    def claim_dir(self, branch: str = "issue-42-slug") -> Path:
        return self.cache / "locks" / f"branch-{branch}.claim"

    def plant_claim(self, pid: int, session: str = "prover-9-20260913-01") -> Path:
        claim = self.claim_dir()
        claim.mkdir(parents=True)
        (claim / "pid").write_text(f"{pid}\n", encoding="utf-8")
        (claim / "role").write_text("prover\n", encoding="utf-8")
        (claim / "session").write_text(f"{session}\n", encoding="utf-8")
        return claim

    def registry_rows(self) -> list[dict]:
        path = self.repo / "results" / "telemetry" / "sessions.jsonl"
        if not path.exists():
            return []
        return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines()
                if line.strip()]


class _Base(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.fx = DispatchFixture(Path(self._tmp.name))

    def tearDown(self) -> None:
        self._tmp.cleanup()


# ── the branch claim ────────────────────────────────────────────────────────


class BranchClaimTests(_Base):
    def test_a_dry_run_claims_and_releases_the_branch(self) -> None:
        result = self.fx.dry_run()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("branch: issue-42-slug", result.stdout)
        self.assertIn("branch_claim:", result.stdout)
        self.assertFalse(self.fx.claim_dir().exists(),
                         "the claim must be released in release_locks()")

    def test_a_second_writer_on_one_branch_is_refused_with_exit_5(self) -> None:
        holder = subprocess.Popen(["sleep", "30"])
        try:
            self.fx.plant_claim(holder.pid, session="prover-42-20260913-01")
            result = self.fx.dry_run()
            self.assertEqual(result.returncode, 5, result.stdout + result.stderr)
            self.assertIn("prover-42-20260913-01", result.stderr,
                          "the refusal must name the holding session")
        finally:
            holder.terminate()
            holder.wait()

    def test_a_read_only_session_is_exempt(self) -> None:
        holder = subprocess.Popen(["sleep", "30"])
        try:
            self.fx.plant_claim(holder.pid)
            result = self.fx.run("--role", "reviewer", "--issue", "42",
                                 "--worktree", str(self.fx.repo), "--sandbox", "read-only",
                                 "--skip-hook-check", "--dry-run", "--", "review it")
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        finally:
            holder.terminate()
            holder.wait()

    def test_allow_concurrent_passes_the_claim(self) -> None:
        holder = subprocess.Popen(["sleep", "30"])
        try:
            self.fx.plant_claim(holder.pid)
            result = self.fx.dry_run("--allow-concurrent")
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("--allow-concurrent", result.stderr)
        finally:
            holder.terminate()
            holder.wait()

    def test_a_claim_whose_pid_is_gone_is_broken(self) -> None:
        dead = subprocess.Popen(["true"])
        dead.wait()
        self.fx.plant_claim(dead.pid)
        result = self.fx.dry_run()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("stale branch claim", result.stderr)


# ── the spool and the retry ─────────────────────────────────────────────────


class SpoolAndRetryTests(_Base):
    def test_the_request_is_spooled_before_the_reservation(self) -> None:
        result = self.fx.run("--role", "prover", "--issue", "42",
                             "--worktree", str(self.fx.repo), "--skip-hook-check",
                             "--", "close the goal",
                             MIPSTARRE_TEST_CODEX_MODE="concurrency",
                             MIPSTARRE_DISPATCH_ATTEMPTS="1")
        self.assertEqual(result.returncode, 7, result.stdout + result.stderr)
        spools = sorted((self.fx.cache / "watchdog" / "capacity" / "spool").glob("*.json"))
        self.assertEqual(len(spools), 1, "the spool entry is left for the janitor")
        record = json.loads(spools[0].read_text(encoding="utf-8"))
        for field in ("role", "issue", "worktree", "persona", "effort", "job_class",
                      "prompt_file", "attempt", "max_attempts", "account", "sandbox"):
            self.assertIn(field, record)
        self.assertEqual(record["role"], "prover")
        self.assertEqual(record["issue"], "42")
        self.assertTrue(Path(record["prompt_file"]).exists(),
                        "the janitor must be able to replay the exact prompt")

    def test_a_refused_dispatch_is_retried_and_keeps_one_episode(self) -> None:
        result = self.fx.run("--role", "prover", "--issue", "42",
                             "--worktree", str(self.fx.repo), "--skip-hook-check",
                             "--", "close the goal",
                             MIPSTARRE_TEST_CODEX_MODE="concurrency",
                             MIPSTARRE_DISPATCH_ATTEMPTS="2")
        self.assertEqual(result.returncode, 7, result.stdout + result.stderr)
        self.assertIn("failure_class: concurrency_limit", result.stdout)
        self.assertIn("attempts: 2", result.stdout)
        rows = self.fx.registry_rows()
        self.assertEqual(len(rows), 2, rows)
        names = [row["name"] for row in rows]
        self.assertTrue(names[1].startswith(names[0]),
                        f"the retry must reuse the episode name: {names}")
        self.assertTrue(names[1].endswith("-a2"), names)
        for row in rows:
            # A transient-class retry never scores a failed attempt.
            self.assertEqual(row["status"], "refused")
            self.assertEqual(row["failure_class"], "concurrency_limit")

    def test_a_task_failure_is_not_retried(self) -> None:
        result = self.fx.run("--role", "prover", "--issue", "42",
                             "--worktree", str(self.fx.repo), "--skip-hook-check",
                             "--", "close the goal",
                             MIPSTARRE_TEST_CODEX_MODE="task-failure",
                             MIPSTARRE_DISPATCH_ATTEMPTS="3")
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("failure_class: task_failure", result.stdout)
        rows = self.fx.registry_rows()
        self.assertEqual(len(rows), 1, "a real failure is one attempt, not three")
        self.assertEqual(rows[0]["status"], "failed")

    def test_a_clean_run_clears_the_spool_and_labels_both_accounts(self) -> None:
        (self.fx.cache / "watchdog" / "run-mode.json").write_text(json.dumps({
            "accounts": [
                {"name": "primary", "label": "relay-us7", "endpoint": "relay-us7"},
                {"name": "second", "label": "space",
                 "endpoint": "api.finite-dimensional.space"},
            ]}), encoding="utf-8")
        result = self.fx.run("--role", "prover", "--issue", "42",
                             "--worktree", str(self.fx.repo), "--skip-hook-check",
                             "--", "close the goal")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("key_label: relay-us7", result.stdout)
        self.assertIn("endpoint: relay-us7", result.stdout)
        self.assertFalse(list((self.fx.cache / "watchdog" / "capacity" / "spool")
                              .glob("*.json")),
                         "a delivered dispatch leaves no spool entry")
        rows = self.fx.registry_rows()
        self.assertEqual(rows[-1]["key_label"], "relay-us7")
        self.assertEqual(rows[-1]["endpoint"], "relay-us7")

    def test_a_label_outside_the_class_fails_closed(self) -> None:
        (self.fx.cache / "watchdog" / "run-mode.json").write_text(json.dumps({
            "accounts": [{"name": "primary", "label": "Relay US7; rm -rf /",
                          "endpoint": "relay-us7"}]}), encoding="utf-8")
        result = self.fx.dry_run()
        self.assertEqual(result.returncode, 4, result.stdout + result.stderr)
        self.assertIn("outside", result.stderr)


# ── endpoint preflight ──────────────────────────────────────────────────────


class EndpointPreflightTests(_Base):
    def _mark_down(self, account: str = "primary") -> None:
        health = self.fx.cache / "watchdog" / "capacity"
        health.mkdir(parents=True, exist_ok=True)
        (health / f"health-{account}.json").write_text(
            json.dumps({"state": "down", "since": "2026-09-13T05:30:00Z"}), encoding="utf-8")

    def test_a_down_endpoint_is_never_reserved_on(self) -> None:
        self._mark_down()
        result = self.fx.run("--role", "prover", "--issue", "42", "--account", "primary",
                             "--worktree", str(self.fx.repo), "--skip-hook-check",
                             "--", "close the goal", MIPSTARRE_DISPATCH_ATTEMPTS="1")
        self.assertEqual(result.returncode, 7, result.stdout + result.stderr)
        self.assertIn("failure_class: endpoint_down", result.stdout)
        self.assertFalse(self.fx.marker.exists(),
                         "codex must not run against an endpoint known to be down")

    def test_a_missing_health_file_means_healthy(self) -> None:
        result = self.fx.run("--role", "prover", "--issue", "42", "--account", "primary",
                             "--worktree", str(self.fx.repo), "--skip-hook-check",
                             "--", "close the goal")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertTrue(self.fx.marker.exists())

    def test_a_half_open_endpoint_may_be_probed(self) -> None:
        health = self.fx.cache / "watchdog" / "capacity"
        health.mkdir(parents=True, exist_ok=True)
        (health / "health-primary.json").write_text(
            json.dumps({"state": "half_open"}), encoding="utf-8")
        result = self.fx.run("--role", "prover", "--issue", "42", "--account", "primary",
                             "--worktree", str(self.fx.repo), "--skip-hook-check",
                             "--", "close the goal")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


# ── the dispatch cutoff ─────────────────────────────────────────────────────


class CutoffTests(_Base):
    def test_no_new_dispatch_starts_after_the_cutoff(self) -> None:
        past = time.strftime("%Y-%m-%dT%H:%M:%S+00:00", time.gmtime(time.time() - 3600))
        result = self.fx.run("--role", "prover", "--issue", "42",
                             "--worktree", str(self.fx.repo), "--skip-hook-check",
                             "--", "close the goal", MIPSTARRE_DISPATCH_CUTOFF=past)
        self.assertEqual(result.returncode, 7, result.stdout + result.stderr)
        self.assertFalse(self.fx.marker.exists())

    def test_until_my_word_means_no_cutoff(self) -> None:
        result = self.fx.run("--role", "prover", "--issue", "42",
                             "--worktree", str(self.fx.repo), "--skip-hook-check",
                             "--", "close the goal",
                             MIPSTARRE_DISPATCH_CUTOFF="until my word")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    sys.exit(unittest.main())
