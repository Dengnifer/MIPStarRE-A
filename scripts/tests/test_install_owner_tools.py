"""Regression tests for the operator-tools installer and the owner controls.

The tools under ``results/telemetry/owner-tools/`` are deployed to
``~/.cache/mipstarre-dev/owner-bin/`` and never edited on the host.  These tests pin the
guarantees that make that checkable — the manifest, the hand-patch refusal, the attic, the
compat symlinks, the regenerated PATH shim — plus the two owner controls whose failures on
2026-09-12 are the reason the design was written: the crontab generation (a ``sed``
delimiter bug wiped the crontab) and the pause phase plan (four ``/tmp`` variants with a
hard-coded deadline timestamp).

Everything runs against a temporary cache root with stub ``run_mode.py`` and ``crontab``
executables; nothing here touches the host's crontab, tmux or the real cache root.
"""

from __future__ import annotations

import hashlib
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest


REPO_ROOT = Path(__file__).resolve().parents[2]
TOOLS = REPO_ROOT / "results" / "telemetry" / "owner-tools"
INSTALL = TOOLS / "install.sh"
INSTALL_CRONS = TOOLS / "install-crons.sh"
OWNER_PAUSE = TOOLS / "owner-pause.sh"
OWNER_RESUME = TOOLS / "owner-resume.sh"
OWNER_SAY = TOOLS / "owner-say.sh"
GOAL_KEEPER = TOOLS / "goal-keeper.sh"
ESTIMATE = TOOLS / "estimate.sh"
SHIM_TEMPLATE = TOOLS / "owner-bin-codex"
MAIN_SESSION = REPO_ROOT / "local" / "bin" / "main-session.sh"

def code_of(path: Path) -> str:
    """The script with its comment lines removed, so a quoted example in the header cannot
    satisfy (or break) an assertion about what the script actually does."""
    return "\n".join(line for line in path.read_text(encoding="utf-8").splitlines()
                     if not line.lstrip().startswith("#"))


REQUIRED_TOOLS = (
    "install.sh", "install-crons.sh", "owner-pause.sh", "owner-resume.sh",
    "owner-say.sh", "goal-keeper.sh", "estimate.sh", "status-snapshot.sh", "codex",
)

RUN_MODE_STUB = """#!/usr/bin/env python3
import json, sys
VALUES = {
    "speed": "fast",
    "estimate_cadence_min": "30",
    "pause_deadline_min": "15",
    "turn_max_min": "8",
    "ready_report_cron": "17 * * * *",
    "cron.watchdog": "off",
    "cron.heartbeat": "off",
    "cron.astra_poll": "off",
    "estimate_issue": "168",
    "progress_issue": "27",
    "floor": "21",
    "accounts": "primary\\nsecond",
    "cap.primary": "5",
    "cap.second": "22",
}
if len(sys.argv) >= 3 and sys.argv[1] == "get":
    value = VALUES.get(sys.argv[2], "")
    if value:
        print(value)
    raise SystemExit(0)
if len(sys.argv) >= 2 and sys.argv[1] == "show":
    if "--json" in sys.argv:
        print(json.dumps({"speed": "fast", "caps": {"primary": 5, "second": 22}}))
    elif "--oneline" in sys.argv:
        print("speed=fast caps primary=5 second=22 floor=21")
    raise SystemExit(0)
raise SystemExit(0)
"""

CRONTAB_STUB = """#!/usr/bin/env bash
# stub crontab: -l prints the table, a file argument installs it and is logged
set -u
TABLE="$CRONTAB_STUB_TABLE"
if [ "${1:-}" = "-l" ]; then
  [ -s "$TABLE" ] || exit 1
  cat "$TABLE"
  exit 0
fi
[ -r "${1:-}" ] || exit 1
cp "$1" "$TABLE"
printf '%s\\n' "$1" >> "$TABLE.installs"
exit 0
"""


def sha256_of(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


class OwnerToolsFixture(unittest.TestCase):
    """A temporary cache root plus stub run_mode.py / crontab executables."""

    def setUp(self) -> None:
        self.tmp = Path(tempfile.mkdtemp(prefix="owner-tools-test-"))
        self.addCleanup(shutil.rmtree, self.tmp, True)
        self.cache = self.tmp / "cache"
        self.dest = self.cache / "owner-bin"
        self.compat = self.tmp / "compat"
        (self.cache / "watchdog").mkdir(parents=True)
        self.run_mode = self.tmp / "run_mode.py"
        self.run_mode.write_text(RUN_MODE_STUB, encoding="utf-8")
        self.crontab_table = self.tmp / "crontab.table"
        self.crontab_table.write_text(
            "0 */6 * * * /home/drx/bin/estimate.sh >> /dev/null 2>&1\n"
            "5 4 * * * /home/drx/bin/unrelated-backup.sh\n",
            encoding="utf-8",
        )
        self.crontab = self.tmp / "crontab-stub"
        self.crontab.write_text(CRONTAB_STUB, encoding="utf-8")
        self.crontab.chmod(0o755)

    def env(self, **extra: str) -> dict:
        env = dict(os.environ)
        env.update(
            MIPSTARRE_CACHE_ROOT=str(self.cache),
            MIPSTARRE_OWNER_BIN=str(self.dest),
            MIPSTARRE_REPO_ROOT=str(REPO_ROOT),
            MIPSTARRE_RUN_MODE=str(self.run_mode),
            MIPSTARRE_CRONTAB=str(self.crontab),
            CRONTAB_STUB_TABLE=str(self.crontab_table),
            MIPSTARRE_COMPAT_DIR=str(self.compat),
        )
        env.update(extra)
        return env

    def run_script(self, script: Path, *args: str, **kwargs) -> subprocess.CompletedProcess:
        return subprocess.run(
            ["bash", str(script), *args],
            capture_output=True, text=True, env=self.env(**kwargs.pop("extra_env", {})),
            cwd=str(REPO_ROOT), timeout=120, check=False,
        )

    def install(self, *args: str) -> subprocess.CompletedProcess:
        return self.run_script(INSTALL, "--dest", str(self.dest), *args)


class InstallerTests(OwnerToolsFixture):
    def test_install_writes_manifest_version_and_repo_root(self) -> None:
        result = self.install()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue(result.stdout.startswith("tool=install.sh version="), result.stdout)

        manifest = (self.dest / "manifest.sha256").read_text(encoding="utf-8")
        rows = dict(
            (line.split()[1], line.split()[0]) for line in manifest.splitlines() if line.strip()
        )
        for name in REQUIRED_TOOLS:
            with self.subTest(tool=name):
                self.assertIn(name, rows, f"{name} missing from manifest.sha256")
                deployed = self.dest / name
                self.assertTrue(deployed.exists(), f"{name} was not deployed")
                self.assertEqual(rows[name], sha256_of(deployed))

        version = (self.dest / "tools-version").read_text(encoding="utf-8")
        for key in ("describe=", "sha=", "short=", "installed_at=", "source=", "installer="):
            self.assertIn(key, version)
        self.assertEqual((self.dest / "repo-root").read_text(encoding="utf-8").strip(),
                         str(REPO_ROOT))
        self.assertEqual(self.install().returncode, 0, "a second install must be idempotent")

    def test_hand_patched_copy_is_refused_and_left_alone(self) -> None:
        self.assertEqual(self.install().returncode, 0)
        patched = self.dest / "owner-say.sh"
        original = patched.read_text(encoding="utf-8")
        patched.write_text(original + "\n# hand patch on the host\n", encoding="utf-8")
        before = sha256_of(patched)

        result = self.install()
        self.assertEqual(result.returncode, 4, result.stdout + result.stderr)
        self.assertIn("REFUSING owner-say.sh", result.stderr)
        self.assertIn("hand patch", result.stderr)
        self.assertEqual(sha256_of(patched), before,
                         "a refused install must not touch the deployed copy")
        self.assertFalse((self.dest / "attic").exists(),
                         "a refusal must not attic anything either")

    def test_force_moves_the_previous_copy_to_the_attic(self) -> None:
        self.assertEqual(self.install().returncode, 0)
        patched = self.dest / "owner-say.sh"
        patch_text = patched.read_text(encoding="utf-8") + "\n# hand patch\n"
        patched.write_text(patch_text, encoding="utf-8")

        result = self.install("--force")
        self.assertEqual(result.returncode, 0, result.stderr)
        attics = sorted((self.dest / "attic").iterdir())
        self.assertEqual(len(attics), 1, "exactly one attic directory for this run")
        kept = attics[0] / "owner-say.sh"
        self.assertTrue(kept.exists(), "the hand patch must be kept, not deleted")
        self.assertEqual(kept.read_text(encoding="utf-8"), patch_text)
        self.assertEqual(sha256_of(patched), sha256_of(OWNER_SAY),
                         "--force must restore the released copy")
        self.assertTrue((attics[0] / "manifest.sha256").exists(),
                        "the attic keeps the manifest that described the replaced copy")

    def test_compat_tmp_creates_symlinks_not_copies(self) -> None:
        result = self.install("--compat-tmp", "--compat-dir", str(self.compat))
        self.assertEqual(result.returncode, 0, result.stderr)
        for alias, target in (("owner-say.sh", "owner-say.sh"),
                              ("owner-say-v3.sh", "owner-say.sh"),
                              ("goal-keeper-v2.sh", "goal-keeper.sh"),
                              ("owner-pause-fast.sh", "owner-pause.sh"),
                              ("final-pause.sh", "owner-pause.sh")):
            with self.subTest(alias=alias):
                link = self.compat / alias
                self.assertTrue(link.is_symlink(), f"{alias} must be a symlink, not a copy")
                self.assertEqual(os.path.realpath(link),
                                 os.path.realpath(self.dest / target))

    def test_compat_tmp_does_not_clobber_a_regular_file(self) -> None:
        self.compat.mkdir(parents=True)
        victim = self.compat / "owner-say.sh"
        victim.write_text("someone else's file\n", encoding="utf-8")
        result = self.install("--compat-tmp", "--compat-dir", str(self.compat))
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertFalse(victim.is_symlink())
        self.assertEqual(victim.read_text(encoding="utf-8"), "someone else's file\n")

    def test_verify_is_the_daemon_gate(self) -> None:
        self.assertEqual(self.install().returncode, 0)
        ok = self.install("--verify")
        self.assertEqual(ok.returncode, 0, ok.stderr)

        (self.dest / "goal-keeper.sh").write_text("# replaced\n", encoding="utf-8")
        bad = self.install("--verify")
        self.assertEqual(bad.returncode, 3)
        self.assertIn("goal-keeper.sh", bad.stderr)

        (self.dest / "estimate.sh").unlink()
        missing = self.install("--verify")
        self.assertEqual(missing.returncode, 3)
        self.assertIn("missing", missing.stderr)

    def test_the_shim_is_rendered_and_both_speeds_are_accepted(self) -> None:
        self.assertEqual(self.install("--speed", "fast").returncode, 0)
        fast = (self.dest / "codex").read_text(encoding="utf-8")
        self.assertIn('service_tier="priority"', fast)
        self.assertIn("@speed-args@", fast)
        accepted = (self.dest / "manifest.accepted").read_text(encoding="utf-8")
        codex_rows = [line for line in accepted.splitlines() if line.split()[1:] == ["codex"]]
        self.assertGreaterEqual(len(codex_rows), 2,
                                "both renderings of the shim must be released versions")

        speed_lines = [line for line in fast.splitlines() if line.startswith("SPEED_ARGS=")]
        self.assertEqual(len(speed_lines), 1,
                         "exactly one line is rewritten; a documented example must not be")
        self.assertIn('service_tier="priority"', speed_lines[0])

        # what `run_mode.py set speed default` does: rewrite that one line, then --record
        default_line = "SPEED_ARGS=()   #" + speed_lines[0].split("#", 1)[1]
        default_render = "\n".join(
            default_line if line.startswith("SPEED_ARGS=") else line
            for line in fast.splitlines()) + "\n"
        self.assertNotIn("service_tier", default_line)
        (self.dest / "codex").write_text(default_render, encoding="utf-8")
        recorded = self.install("--record", "codex")
        self.assertEqual(recorded.returncode, 0, recorded.stderr)
        self.assertEqual(self.install("--verify").returncode, 0,
                         "a regenerated shim must verify after --record")

        (self.dest / "codex").write_text(default_render + "\n# hand patch\n", encoding="utf-8")
        refused = self.install("--record", "codex")
        self.assertEqual(refused.returncode, 4)


class CrontabGenerationTests(OwnerToolsFixture):
    def test_dry_run_generates_the_thirty_minute_estimate_row_when_speed_is_fast(self) -> None:
        self.assertEqual(self.install().returncode, 0)
        result = self.run_script(INSTALL_CRONS, "--dry-run")
        self.assertEqual(result.returncode, 0, result.stderr)
        body = result.stdout
        self.assertIn("*/30 * * * *", body)
        self.assertIn(f"{self.dest}/estimate.sh", body)
        self.assertIn("17 * * * *", body)
        self.assertIn("ready_report.py", body)
        # the nudging crons are off in the mode file, so they appear as comments only
        self.assertNotIn("qpbt-watchdog.sh >>", body)
        self.assertIn("watchdog: off (run-mode)", body)
        # a foreign row survives; the historical 6-hourly estimate row does not
        self.assertIn("unrelated-backup.sh", body)
        self.assertNotIn("0 */6 * * *", body)
        self.assertFalse((self.crontab_table.parent / "crontab.table.installs").exists(),
                         "--dry-run must not install anything")

    def test_a_six_hour_row_when_the_speed_is_default(self) -> None:
        self.run_mode.write_text(
            RUN_MODE_STUB.replace('"speed": "fast"', '"speed": "default"')
                         .replace('"estimate_cadence_min": "30"', '"estimate_cadence_min": "360"'),
            encoding="utf-8")
        self.assertEqual(self.install("--speed", "default").returncode, 0)
        result = self.run_script(INSTALL_CRONS, "--dry-run")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("0 */6 * * *", result.stdout)
        self.assertNotIn("*/30 * * * *", result.stdout)

    def test_an_empty_crontab_is_refused(self) -> None:
        self.assertEqual(self.install().returncode, 0)
        self.crontab_table.write_text("", encoding="utf-8")
        result = self.run_script(INSTALL_CRONS)
        self.assertEqual(result.returncode, 3, result.stdout)
        self.assertIn("returned nothing", result.stderr)

    def test_install_backs_up_first_and_installs_from_a_file_under_w(self) -> None:
        self.assertEqual(self.install().returncode, 0)
        result = self.run_script(INSTALL_CRONS)
        self.assertEqual(result.returncode, 0, result.stderr)
        watchdog = self.cache / "watchdog"
        backups = sorted(watchdog.glob("crontab.*.bak"))
        installed = sorted(watchdog.glob("crontab.*.new"))
        self.assertEqual(len(backups), 1, "the previous crontab is backed up verbatim")
        self.assertEqual(len(installed), 1, "the new crontab is installed from a file under $W")
        self.assertIn("unrelated-backup.sh", backups[0].read_text(encoding="utf-8"))
        installs = Path(str(self.crontab_table) + ".installs").read_text(encoding="utf-8")
        self.assertIn(str(installed[0]), installs)
        # The invariant is "installed from a file under $W", not "not under
        # /tmp": on a host whose TMPDIR is /tmp the test's own cache root is a
        # /tmp path, and the substring check then fails a correct install.
        for line in installs.splitlines():
            if line.strip():
                self.assertTrue(
                    line.strip().startswith(str(watchdog)),
                    f"the crontab is installed from $W, not from {line.strip()!r}")

    def test_no_script_edits_the_live_crontab_with_sed(self) -> None:
        for script in (INSTALL_CRONS, OWNER_PAUSE, OWNER_RESUME):
            text = script.read_text(encoding="utf-8")
            for line in text.splitlines():
                if line.lstrip().startswith("#"):
                    continue
                self.assertNotRegex(
                    line, r"crontab -l.*\|.*sed",
                    f"{script.name} pipes the live crontab through sed")


class OwnerPausePlanTests(OwnerToolsFixture):
    def phases(self, text: str) -> list[int]:
        """The offsets of the phase rows only, in order (not the header or footer line)."""
        offsets = []
        for line in text.splitlines():
            match = re.match(r"\s+T\+(\d+):(\d\d)\s", line)
            if match:
                offsets.append(int(match.group(1)) * 60 + int(match.group(2)))
        return offsets

    def test_dry_run_prints_a_plan_whose_last_phase_is_within_the_deadline(self) -> None:
        result = self.run_script(OWNER_PAUSE, "--dry-run")
        self.assertEqual(result.returncode, 0, result.stderr)
        body = result.stdout
        self.assertIn("phase plan (deadline 15 min = T+15:00", body)
        offsets = self.phases(body)
        self.assertTrue(offsets, "the plan must print T+mm:ss offsets")
        self.assertLessEqual(max(offsets), 15 * 60,
                             "no phase may be scheduled after the deadline")
        for phase in ("stop admission", "release waiters", "one message", "crontab",
                      "kill leftovers", "confirm/record"):
            self.assertIn(phase, body)
        self.assertIn("last phase T+15:00 <= deadline T+15:00", body)
        self.assertIn("nothing was stopped, written or sent", body)
        self.assertFalse((self.cache / "watchdog" / "drain").exists())
        self.assertFalse((self.cache / "watchdog" / "pause-state.json").exists())

    def test_the_deadline_flag_overrides_the_run_mode(self) -> None:
        result = self.run_script(OWNER_PAUSE, "--deadline", "8m", "--dry-run")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("deadline 8 min = T+8:00", result.stdout)
        self.assertLessEqual(max(self.phases(result.stdout)), 8 * 60)

    def test_a_short_deadline_clamps_every_phase_onto_it(self) -> None:
        # a deadline shorter than the nominal plan must collapse the later phases onto the
        # deadline, not run past it: "pause within N minutes" is the whole instruction
        for minutes in (1, 2, 3, 5, 15):
            with self.subTest(deadline=minutes):
                result = self.run_script(OWNER_PAUSE, "--deadline", f"{minutes}m", "--dry-run")
                self.assertEqual(result.returncode, 0, result.stderr)
                offsets = self.phases(result.stdout)
                self.assertEqual(len(offsets), 6, "all six phases must be printed")
                self.assertEqual(offsets, sorted(offsets), "phases must stay in order")
                self.assertLessEqual(max(offsets), minutes * 60,
                                     "no phase may be scheduled after the deadline")

    def test_the_pause_script_carries_no_literal_timestamp_or_cap(self) -> None:
        code = code_of(OWNER_PAUSE)
        self.assertNotRegex(code, r"20\d\d-\d\d-\d\dT\d\d:\d\d",
                            "the pause deadline must come from run-mode, not a timestamp")
        self.assertNotRegex(code, r"echo\s+\d+\s*>\s*[^ ]*max-codex-",
                            "caps are written by run_mode.py, never by the pause script")
        self.assertNotRegex(code, r"git\s+clean\b\s*-",
                            "partial work stays in the workers' worktrees")
        self.assertIn("--mode terminal", code, "the closing order must not auto-resume")

    def test_the_resume_script_restores_from_the_record_only(self) -> None:
        code = code_of(OWNER_RESUME)
        self.assertIn("pause-state.json", code)
        self.assertNotIn("caps-before-pause", code,
                         "the clobberable caps file is replaced by pause-state.json")
        self.assertNotRegex(code, r"sed.*PAUSED-",
                            "the crontab is restored verbatim, never un-commented by sed")

    def test_resume_without_a_record_refuses(self) -> None:
        result = self.run_script(OWNER_RESUME, "--dry-run")
        self.assertEqual(result.returncode, 3)
        self.assertIn("no pause record", result.stderr)


class OwnerSayAndKeeperTests(OwnerToolsFixture):
    def test_the_three_modes_and_the_terminal_hold(self) -> None:
        dry = self.run_script(OWNER_SAY, "--mode", "terminal", "--dry-run", "stop now")
        self.assertEqual(dry.returncode, 0, dry.stderr)
        self.assertIn("mode=terminal", dry.stdout)
        self.assertIn("hold=yes", dry.stdout)

        bad = self.run_script(OWNER_SAY, "--mode", "whenever", "hello")
        self.assertEqual(bad.returncode, 2)

        text = OWNER_SAY.read_text(encoding="utf-8")
        self.assertIn('if [ "$MODE" = terminal ]; then', text)
        self.assertIn('"$W/goal-hold"', text)
        resume_line = [line for line in text.splitlines() if "/goal resume" in line
                       and not line.lstrip().startswith("#")]
        self.assertTrue(resume_line, "interrupt mode must still resume the goal")
        guard = [line for line in text.splitlines()
                 if 'MODE" = interrupt' in line and "INTERRUPTED" in line]
        self.assertTrue(guard, "the resume must be guarded by --mode interrupt")

    def test_the_idle_rule_is_the_last_four_non_empty_lines(self) -> None:
        text = OWNER_SAY.read_text(encoding="utf-8")
        self.assertIn("tail -n 4", text)
        self.assertIn("esc to interrupt", text)

    def test_the_keeper_renders_its_goal_and_limit_from_run_mode(self) -> None:
        code = code_of(GOAL_KEEPER)
        self.assertIn("show --oneline", code)
        self.assertIn("turn_max_min", code)
        self.assertIn("goal-hold", code)
        self.assertIn("main-inbox", code)
        self.assertNotRegex(code, r"primary \d+, second \d+",
                            "no literal caps may appear in the goal text")
        self.assertNotRegex(code, r"TURN_MAX=\"\$\{TURN_MAX:-\d+\}\"",
                            "the turn cap comes from run-mode, not from the environment")


class EstimateAndLauncherTests(OwnerToolsFixture):
    def test_estimate_reads_the_committed_snapshot_and_uses_a_throwaway_worktree(self) -> None:
        code = code_of(ESTIMATE)
        self.assertIn("results/telemetry/github-snapshot", code)
        self.assertIn("open-pulls.json", code)
        self.assertNotIn("gh pr list", code)
        self.assertNotIn("gh pr view", code)
        self.assertIn("git worktree add --detach", code)
        self.assertIn("estimate_post.py", code)
        self.assertIn("DENOM=197", code)
        self.assertIn("<sub>", code)
        self.assertIn("timeout", code)
        self.assertNotIn("/tmp/estimate", code, "no scratch files in /tmp")

    def test_estimate_refuses_to_no_op_without_an_issue(self) -> None:
        empty = self.tmp / "run_mode_empty.py"
        empty.write_text("#!/usr/bin/env python3\nraise SystemExit(0)\n", encoding="utf-8")
        result = self.run_script(ESTIMATE, "--no-timeout",
                                 extra_env={"MIPSTARRE_RUN_MODE": str(empty)})
        self.assertEqual(result.returncode, 3, result.stdout)
        self.assertIn("is NOT posted", result.stderr)

    def test_the_launcher_goes_through_the_shim(self) -> None:
        code = code_of(MAIN_SESSION)
        self.assertIn("owner-bin", code)
        self.assertIn("run_mode.py", code)
        self.assertNotIn("$HOME/.local/bin/codex", code,
                         "the launcher must not exec an absolute codex path")
        self.assertNotIn("/home/drx", code)
        for key in ("main.model", "main.effort", "main.codex_home", "speed"):
            self.assertIn(key, code)

    def test_launch_qpbt_main_is_a_retirement_stub(self) -> None:
        stub = TOOLS / "launch_qpbt_main.sh"
        result = self.run_script(stub)
        self.assertEqual(result.returncode, 2)
        self.assertIn("main-session.sh", result.stderr)
        self.assertNotIn("tmux send-keys", code_of(stub),
                         "the stub must not start or drive a session")


class ShellSyntaxTests(unittest.TestCase):
    def test_bash_n_on_every_owner_tool(self) -> None:
        scripts = [INSTALL, INSTALL_CRONS, OWNER_PAUSE, OWNER_RESUME, OWNER_SAY,
                   GOAL_KEEPER, ESTIMATE, SHIM_TEMPLATE, MAIN_SESSION,
                   TOOLS / "launch_qpbt_main.sh"]
        for script in scripts:
            with self.subTest(script=script.name):
                result = subprocess.run(["bash", "-n", str(script)],
                                        capture_output=True, text=True, check=False)
                self.assertEqual(result.returncode, 0, result.stderr)

    def test_every_tool_prints_its_version_as_the_first_log_line(self) -> None:
        for script in (INSTALL, INSTALL_CRONS, OWNER_PAUSE, OWNER_RESUME, OWNER_SAY,
                       GOAL_KEEPER, ESTIMATE):
            with self.subTest(script=script.name):
                text = script.read_text(encoding="utf-8")
                self.assertRegex(
                    text, r'echo "tool=\$PROG version=\$\{VERSION:-unreleased\}"',
                    f"{script.name} must name the release that produced its log")


if __name__ == "__main__":
    unittest.main()
