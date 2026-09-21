#!/usr/bin/env python3
"""Unit tests for the session machinery in ``local/bin/session/``.

Everything here runs offline: no tmux, no codex, no gh, no network.  The tests
put stub executables (``tmux``, ``sleep``, ``curl``, ``setsid``) first on PATH,
point the state directory at a temporary tree, and use the scripts' own
``--dry-run`` modes where a real side effect would otherwise be needed.

This module also holds the shared harness the other ``test_session_*`` modules
import.
"""

from __future__ import annotations

import re
import stat
import subprocess
import sys
import time
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

REPO = Path(__file__).resolve().parents[2]
SESSION = REPO / "local" / "bin" / "session"
TEMPLATES = REPO / "local" / "templates"

# Scripts this module owns; config.sh belongs to the configuration loader and is
# tested there, so it is deliberately not in this list.
SCRIPTS = [
    "lib.sh", "probe-key.sh", "say.sh", "main-tui.sh", "goal-keeper.sh",
    "key-watch.sh", "pause.sh", "pause-watch.sh", "resume.sh", "standdown.sh",
    "timer.sh", "status.sh",
]

FAKE_TMUX = r"""#!/usr/bin/env bash
# Stub tmux for the session tests: records every call and replays canned panes.
# The "phase" selects which pane file capture-pane prints; it advances whenever
# a call matches FAKE_TMUX_ADVANCE_ON, so a test can script what the pane shows
# before and after a keystroke.
set -u
printf '%s\n' "$*" >> "${FAKE_TMUX_LOG:-/dev/null}"
dir="${FAKE_TMUX_PANES:-}"
phase=1
[ -n "$dir" ] && phase="$(cat "$dir/.phase" 2>/dev/null || echo 1)"
rc=0
case "${1:-}" in
  capture-pane)
    if [ -n "$dir" ]; then
      f="$dir/pane-$phase.txt"
      [ -f "$f" ] || f="$(ls "$dir"/pane-*.txt 2>/dev/null | sort -V | tail -n 1)"
      [ -n "${f:-}" ] && [ -f "$f" ] && cat "$f"
    fi
    ;;
  has-session) rc="${FAKE_TMUX_HAS_SESSION:-0}" ;;
  load-buffer)
    last=""
    for a in "$@"; do last="$a"; done
    if [ -n "${FAKE_TMUX_BUFFER:-}" ] && [ -f "$last" ]; then cp "$last" "$FAKE_TMUX_BUFFER"; fi
    ;;
esac
if [ -n "$dir" ] && [ -n "${FAKE_TMUX_ADVANCE_ON:-}" ]; then
  printf '%s' "$*" | grep -q -E "$FAKE_TMUX_ADVANCE_ON" && printf '%s' "$((phase+1))" > "$dir/.phase"
fi
exit "$rc"
"""

FAKE_SLEEP = "#!/bin/sh\nexit 0\n"
FAKE_SETSID = '#!/bin/sh\nprintf \'%s\\n\' "$*" >> "${FAKE_SETSID_LOG:-/dev/null}"\nexit 0\n'
FAKE_GH = '#!/bin/sh\nprintf \'%s\\n\' "$*" >> "${FAKE_GH_LOG:-/dev/null}"\nexit 0\n'
FAKE_SAY = '#!/bin/sh\nprintf \'%s\\n\' "$*" >> "${KIT_SAY_LOG:-/dev/null}"\nexit "${KIT_SAY_RC:-0}"\n'

FAKE_CURL = r"""#!/usr/bin/env bash
# Stub curl: prints the n-th canned reply, where n counts the calls.  Each reply
# file already ends in the "HTTP<code>" line the real curl would append through
# its -w format, so the caller's parsing is exercised unchanged.
set -u
printf '%s\n' "$*" >> "${FAKE_CURL_LOG:-/dev/null}"
n=1
if [ -n "${FAKE_CURL_STATE:-}" ]; then
  n="$(cat "$FAKE_CURL_STATE" 2>/dev/null || echo 0)"; n=$((n+1)); printf '%s' "$n" > "$FAKE_CURL_STATE"
fi
dir="${FAKE_CURL_DIR:-}"
[ -n "$dir" ] || exit 0
f="$dir/reply-$n.txt"
[ -f "$f" ] || f="$(ls "$dir"/reply-*.txt 2>/dev/null | sort -V | tail -n 1)"
[ -n "${f:-}" ] && [ -f "$f" ] && cat "$f"
exit 0
"""

SECRET = "sk-test-0123456789-never-print-me"


class SessionHarness(unittest.TestCase):
    """Temporary state directory plus stub executables first on PATH."""

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self._tmp.cleanup)
        self.root = Path(self._tmp.name)
        self.home = self.root / "home"
        self.cache = self.root / "cache"
        self.state = self.cache / "watchdog"
        self.binstub = self.root / "stubbin"
        self.panes = self.root / "panes"
        self.replies = self.root / "replies"
        self.tmpdir = self.root / "tmp"
        for d in (self.home, self.state, self.binstub, self.panes, self.replies, self.tmpdir):
            d.mkdir(parents=True, exist_ok=True)
        self.tmux_log = self.root / "tmux.log"
        self.curl_log = self.root / "curl.log"
        self.say_log = self.root / "say.log"
        self.setsid_log = self.root / "setsid.log"
        self.buffer = self.root / "buffer.txt"
        self.stub("tmux", FAKE_TMUX)
        self.stub("sleep", FAKE_SLEEP)
        self.stub("setsid", FAKE_SETSID)
        self.stub("curl", FAKE_CURL)
        self.stub("gh", FAKE_GH)
        self.say_stub = self.root / "say-stub.sh"
        self.say_stub.write_text(FAKE_SAY)
        self.say_stub.chmod(0o755)

    # -- helpers ---------------------------------------------------------
    def stub(self, name: str, body: str) -> Path:
        path = self.binstub / name
        path.write_text(body)
        path.chmod(path.stat().st_mode | stat.S_IEXEC | stat.S_IXGRP | stat.S_IXOTH)
        return path

    def pane(self, number: int, text: str) -> None:
        (self.panes / f"pane-{number}.txt").write_text(text if text.endswith("\n") else text + "\n")

    def reply(self, number: int, body: str, code: int) -> None:
        (self.replies / f"reply-{number}.txt").write_text(f"{body}\nHTTP{code}")

    def key_home(self, name: str = "testkey", base_url: str = "https://example.invalid/v1",
                 secret: str = SECRET) -> Path:
        home = self.root / f"codex-home-{name}"
        home.mkdir(parents=True, exist_ok=True)
        (home / "config.toml").write_text(f'base_url = "{base_url}"\n')
        (home / "auth.json").write_text('{"OPENAI_API_KEY": "%s"}\n' % secret)
        return home

    def env(self, **extra) -> dict:
        base = {
            "PATH": f"{self.binstub}:/usr/bin:/bin:/usr/local/bin",
            "HOME": str(self.home),
            "TMPDIR": str(self.tmpdir),
            # no configuration loader in this tree: exercise the env fallback
            "KIT_CONFIG_SH": str(self.root / "there-is-no-config.sh"),
            "KIT_REPO_ROOT": str(REPO),
            "KIT_CACHE_ROOT": str(self.cache),
            "KIT_STATE_DIR": str(self.state),
            "KIT_TMUX": "kittest",
            "KIT_MAIN_KEY": "testkey",
            "KIT_PROGRESS_ISSUE": "",
            "KIT_MAIN_PID_CMD": "echo ''",
            "FAKE_TMUX_LOG": str(self.tmux_log),
            "FAKE_TMUX_PANES": str(self.panes),
            "FAKE_TMUX_BUFFER": str(self.buffer),
            "FAKE_CURL_LOG": str(self.curl_log),
            "FAKE_CURL_DIR": str(self.replies),
            "FAKE_CURL_STATE": str(self.root / "curl.n"),
            "FAKE_SETSID_LOG": str(self.setsid_log),
            "FAKE_GH_LOG": str(self.root / "gh.log"),
            "KIT_SAY_LOG": str(self.say_log),
        }
        base.update({k: str(v) for k, v in extra.items()})
        return base

    def run_script(self, script: str, *args: str, timeout: int = 120, **envextra):
        return subprocess.run(
            ["bash", str(SESSION / script), *args],
            capture_output=True, text=True, timeout=timeout,
            cwd=str(REPO), env=self.env(**envextra),
        )

    def tmux_calls(self) -> list[str]:
        if not self.tmux_log.exists():
            return []
        return [line for line in self.tmux_log.read_text().splitlines() if line.strip()]

    def say_calls(self) -> list[str]:
        if not self.say_log.exists():
            return []
        return [line for line in self.say_log.read_text().splitlines() if line.strip()]


class ScriptHygieneTests(unittest.TestCase):
    def test_every_script_exists_and_parses(self):
        for name in SCRIPTS:
            path = SESSION / name
            with self.subTest(script=name):
                self.assertTrue(path.exists(), f"{path} is missing")
                result = subprocess.run(["bash", "-n", str(path)], capture_output=True, text=True)
                self.assertEqual(result.returncode, 0, f"{name}: {result.stderr}")

    def test_every_script_is_set_u_and_self_documenting(self):
        for name in SCRIPTS:
            text = (SESSION / name).read_text()
            with self.subTest(script=name):
                self.assertTrue(text.startswith("#!/usr/bin/env bash"), f"{name} has no bash shebang")
                if name != "lib.sh":
                    self.assertIn("\nset -u\n", text, f"{name} does not run under set -u")
                header = [l for l in text.splitlines()[1:8] if l.startswith("#")]
                self.assertGreaterEqual(len(header), 2, f"{name} has no header comment")
                self.assertIn(name, header[0], f"{name}'s first comment line should name the script")

    def test_nothing_is_nailed_to_one_machine_one_account_or_one_project(self):
        # These are the shapes that make an operator script unusable anywhere but
        # the machine it was written on.  Every one of them has to come from the
        # configuration instead.
        patterns = [
            (r"/home/[A-Za-z0-9_.-]+", "an absolute path into somebody's home directory"),
            (r"/Users/[A-Za-z0-9_.-]+", "an absolute path into somebody's home directory"),
            (r"~/\.cache/", "a hard-coded cache directory (use $KIT_CACHE_ROOT)"),
            (r"codex-home-", "a hard-coded key-home name (use kit_key_home)"),
            (r"\b(gpt|claude|llama|gemini)-[0-9]", "a pinned model id (models come from the configuration)"),
            (r"gh issue comment [0-9]", "a hard-coded issue number (use kit_issue_comment)"),
            (r"tmux [a-z-]+ (-[a-z] )*-[ts] (?!\"\$)", "a hard-coded tmux session (use $KIT_TMUX)"),
        ]
        owned = [SESSION / n for n in SCRIPTS]
        owned += [TEMPLATES / "standdown.md", TEMPLATES / "handover-section.md"]
        for path in owned:
            text = path.read_text()
            for pattern, why in patterns:
                with self.subTest(file=path.name, pattern=pattern):
                    found = re.search(pattern, text)
                    self.assertIsNone(found, f"{path.name} contains {why}: {found.group(0) if found else ''!r}")

    def test_the_directory_readme_names_every_tool(self):
        readme = SESSION / "README.md"
        self.assertTrue(readme.exists(), f"{readme} is missing")
        text = readme.read_text()
        for name in SCRIPTS:
            if name in ("lib.sh", "config.sh"):
                continue   # sourced, never run by hand
            with self.subTest(script=name):
                self.assertIn(name, text, f"the README does not mention {name}")

    def test_the_two_templates_carry_the_placeholders_the_tools_fill(self):
        standdown = (TEMPLATES / "standdown.md").read_text()
        for key in ("{{REASON}}", "{{NEXT_LAYOUT}}", "{{DEADLINE_MIN}}", "{{DONE_MARKER}}"):
            self.assertIn(key, standdown, f"standdown.md is missing {key}")
        handover = (TEMPLATES / "handover-section.md").read_text()
        for key in ("{{TIMESTAMP}}", "{{TITLE}}", "{{REASON}}", "{{LAYOUT}}"):
            self.assertIn(key, handover, f"handover-section.md is missing {key}")


class ConfigFallbackTests(SessionHarness):
    """lib.sh must work before the configuration loader exists."""

    def source_lib(self, snippet: str, **envextra):
        script = self.root / "probe-lib.sh"
        script.write_text(f'set -u\n. "{SESSION}/lib.sh"\n{snippet}\n')
        return subprocess.run(["bash", str(script)], capture_output=True, text=True,
                              cwd=str(REPO), env=self.env(**envextra), timeout=60)

    def test_defaults_apply_when_there_is_no_config_sh(self):
        env = dict(self.env())
        for name in ("KIT_CACHE_ROOT", "KIT_STATE_DIR", "KIT_TMUX", "KIT_MAIN_KEY"):
            env.pop(name, None)
        script = self.root / "defaults.sh"
        script.write_text(
            f'set -u\n. "{SESSION}/lib.sh"\n'
            'printf "%s|%s|%s|%s|%s|%s\\n" "$KIT_NAME" "$KIT_TMUX" "$KIT_TURN_MAX" '
            '"$KIT_MAIN_KEY" "$KIT_CACHE_ROOT" "$KIT_STATE_DIR"\n')
        result = subprocess.run(["bash", str(script)], capture_output=True, text=True,
                                cwd=str(REPO), env=env, timeout=60)
        self.assertEqual(result.returncode, 0, result.stderr)
        name, tmux, turn, key, cache, state = result.stdout.strip().split("|")
        self.assertEqual(name, "PaperLib")
        self.assertEqual(tmux, "paperlib")
        self.assertEqual(turn, "25")
        self.assertEqual(key, "default")
        self.assertEqual(cache, f"{self.home}/.cache/paperlib-dev")
        self.assertEqual(state, f"{cache}/watchdog")

    def test_config_sh_wins_over_the_defaults_once_it_exists(self):
        config = self.root / "config.sh"
        config.write_text(
            'export KIT_NAME=WidgetLib\nexport KIT_TMUX=widgetlib\n'
            'export KIT_TURN_MAX=45\nexport KIT_MAIN_KEY=blue\n')
        env = dict(self.env(KIT_CONFIG_SH=str(config)))
        for name in ("KIT_TMUX", "KIT_MAIN_KEY"):
            env.pop(name, None)
        script = self.root / "fromconfig.sh"
        script.write_text(f'set -u\n. "{SESSION}/lib.sh"\n'
                          'printf "%s|%s|%s|%s\\n" "$KIT_NAME" "$KIT_TMUX" "$KIT_TURN_MAX" "$KIT_MAIN_KEY"\n')
        result = subprocess.run(["bash", str(script)], capture_output=True, text=True,
                                cwd=str(REPO), env=env, timeout=60)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.strip(), "WidgetLib|widgetlib|45|blue")

    def test_a_key_home_comes_from_the_environment_then_the_project_file(self):
        result = self.source_lib('kit_key_home blue', KIT_KEY_HOME_BLUE="/tmp/blue-home")
        self.assertEqual(result.stdout.strip(), "/tmp/blue-home", result.stderr)

        project = self.root / "project.json"
        project.write_text('{"schema": 1, "keys": {"green": {"codex_home": "~/green-home", "limit": 3}}}')
        result = self.source_lib('kit_key_home green', KIT_PROJECT_JSON=str(project))
        self.assertEqual(result.stdout.strip(), f"{self.home}/green-home", result.stderr)
        result = self.source_lib('kit_key_limit green', KIT_PROJECT_JSON=str(project))
        self.assertEqual(result.stdout.strip(), "3", result.stderr)

        result = self.source_lib('kit_key_home unknown')
        self.assertEqual(result.stdout.strip(), f"{self.home}/.codex", result.stderr)

    def test_the_idle_detector_uses_the_repository_basename_not_a_fixed_name(self):
        repo = self.root / "widgetlib"
        repo.mkdir()
        self.pane(1, "some output\n\ngpt-x  ultra  ·  ~/widgetlib\nAsk Codex to do anything")
        ok = self.source_lib('kit_idle && echo IDLE || echo BUSY', KIT_REPO_ROOT=str(repo))
        self.assertEqual(ok.stdout.strip(), "IDLE", ok.stderr)
        other = self.root / "someotherproject"
        other.mkdir()
        no = self.source_lib('kit_idle && echo IDLE || echo BUSY', KIT_REPO_ROOT=str(other))
        self.assertEqual(no.stdout.strip(), "BUSY", no.stderr)


class ProbeKeyTests(SessionHarness):
    def test_a_healthy_key_exits_zero_and_never_prints_the_key(self):
        self.key_home("testkey")
        self.reply(1, '{"output":[{"content":[{"text":"ok"}]}]}', 200)
        result = self.run_script("probe-key.sh", "testkey",
                                 KIT_KEY_HOME_TESTKEY=str(self.root / "codex-home-testkey"))
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        self.assertIn("HTTP200", result.stdout)
        self.assertNotIn(SECRET, result.stdout)
        self.assertIn(f"keylen={len(SECRET)}", result.stdout)

    def test_a_refused_key_exits_seventy_five(self):
        self.key_home("testkey")
        self.reply(1, '{"error":{"message":"quota exhausted"}}', 403)
        result = self.run_script("probe-key.sh", "testkey",
                                 KIT_KEY_HOME_TESTKEY=str(self.root / "codex-home-testkey"))
        self.assertEqual(result.returncode, 75, result.stdout)
        self.assertIn("HTTP403", result.stdout)
        self.assertIn("quota exhausted", result.stdout)

    def test_a_key_echoed_back_by_the_endpoint_is_redacted(self):
        self.key_home("testkey")
        self.reply(1, '{"error":{"message":"invalid_api_key ' + SECRET + ' rejected"}}', 401)
        result = self.run_script("probe-key.sh", "testkey",
                                 KIT_KEY_HOME_TESTKEY=str(self.root / "codex-home-testkey"))
        self.assertEqual(result.returncode, 75)
        self.assertNotIn(SECRET, result.stdout)
        self.assertIn("<redacted>", result.stdout)

    def test_the_probe_never_goes_through_a_proxy(self):
        self.key_home("testkey")
        self.reply(1, "{}", 200)
        self.run_script("probe-key.sh", "testkey",
                        KIT_KEY_HOME_TESTKEY=str(self.root / "codex-home-testkey"))
        self.assertIn("--noproxy", self.curl_log.read_text())

    def test_a_missing_key_home_is_a_configuration_error_not_a_dead_key(self):
        result = self.run_script("probe-key.sh", "nosuchkey",
                                 KIT_KEY_HOME_NOSUCHKEY=str(self.root / "absent"))
        self.assertEqual(result.returncode, 2, result.stdout)

    def test_dry_run_touches_nothing(self):
        result = self.run_script("probe-key.sh", "testkey", "--dry-run")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("DRY probe", result.stdout)
        self.assertFalse(self.curl_log.exists())


class MainTuiTests(SessionHarness):
    def setUp(self):
        super().setUp()
        self.key_home("testkey")
        self.reply(1, "{}", 200)
        self.keyenv = {"KIT_KEY_HOME_TESTKEY": str(self.root / "codex-home-testkey")}

    def test_dry_run_shows_the_command_it_would_launch(self):
        result = self.run_script("main-tui.sh", "start", "--dry-run", **self.keyenv)
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        self.assertIn("DRY launch command:", result.stdout)
        self.assertIn("main-tui.sh __exec", result.stdout)
        self.assertIn(f"CODEX_HOME={self.root}/codex-home-testkey", result.stdout)
        self.assertIn("danger-full-access", result.stdout)
        self.assertEqual(self.tmux_calls(), [], "a dry run must not touch tmux")

    def test_default_permissions_leaves_the_sandbox_alone(self):
        result = self.run_script("main-tui.sh", "start", "--default-permissions", "--dry-run",
                                 **self.keyenv)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("KIT_FULL_ACCESS=0", result.stdout)
        self.assertIn("codex defaults", result.stdout)

    def test_zero_delegates_turns_multi_agent_off(self):
        result = self.run_script("main-tui.sh", "start", "--delegates", "0", "--dry-run",
                                 **self.keyenv)
        self.assertIn("KIT_EXEC_DELEGATES=0", result.stdout)
        self.assertIn("multi_agent off", result.stdout)

    def test_a_dead_key_stops_the_launch(self):
        self.reply(1, '{"error":"insufficient_quota"}', 429)
        result = self.run_script("main-tui.sh", "start", **self.keyenv)
        self.assertEqual(result.returncode, 75, result.stdout)
        self.assertEqual(self.tmux_calls(), [], "nothing may be launched when the key is dead")

    def test_start_refuses_to_run_a_second_main_session(self):
        result = self.run_script("main-tui.sh", "start", KIT_MAIN_PID_CMD="echo 4242", **self.keyenv)
        self.assertEqual(result.returncode, 3, result.stdout)
        self.assertIn("already running", result.stdout)
        self.assertEqual(self.tmux_calls(), [])

    def test_an_unknown_action_is_a_usage_error(self):
        result = self.run_script("main-tui.sh", "frobnicate", **self.keyenv)
        self.assertEqual(result.returncode, 3)


class TimerTests(SessionHarness):
    def test_a_time_in_the_past_runs_the_command_now(self):
        marker = self.root / "fired.txt"
        result = self.run_script("timer.sh", "1", "--name", "t1", "--",
                                 "touch", str(marker))
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        self.assertTrue(marker.exists(), "the command did not run")
        self.assertTrue((self.state / "timer-t1.pid").exists())

    def test_a_cancelled_timer_never_runs_its_command(self):
        marker = self.root / "never.txt"
        env = self.env()
        env["PATH"] = "/usr/bin:/bin"   # a real sleep, so the wait loop does not spin
        armed = subprocess.Popen(
            ["bash", str(SESSION / "timer.sh"), "9999999999", "--name", "t2",
             "--poll", "1", "--", "touch", str(marker)],
            cwd=str(REPO), env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        self.addCleanup(armed.kill)
        pidfile = self.state / "timer-t2.pid"
        for _ in range(100):
            if pidfile.exists():
                break
            time.sleep(0.05)
        self.assertTrue(pidfile.exists(), "the timer never armed")
        stop = subprocess.run(["bash", str(SESSION / "timer.sh"), "stop", "t2"],
                              cwd=str(REPO), env=env, capture_output=True, text=True, timeout=30)
        self.assertEqual(stop.returncode, 0, stop.stderr)
        armed.wait(timeout=30)
        self.assertFalse(marker.exists(), "a cancelled timer ran its command")

    def test_dry_run_prints_the_plan_only(self):
        result = self.run_script("timer.sh", "9999999999", "--dry-run", "--", "echo", "hello")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("DRY timer", result.stdout)
        self.assertIn("echo hello", result.stdout)

    def test_usage_errors(self):
        self.assertEqual(self.run_script("timer.sh", "notanepoch", "--", "true").returncode, 3)
        self.assertEqual(self.run_script("timer.sh", "123").returncode, 3)


class PauseTests(SessionHarness):
    def test_a_graceful_landing_kills_nothing(self):
        result = self.run_script("pause.sh", "graceful", "1", "--reason", "wind off by noon")
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        self.assertTrue((self.state / "daemon" / "stop").exists())
        self.assertTrue((self.state / "auto-merge.stop").exists())
        self.assertFalse((self.state / "paused").exists(),
                         "a landing must not write the paused marker")
        self.assertIn("Nothing was killed", result.stdout)

    def test_the_hard_pause_says_that_it_is_the_hard_one(self):
        result = self.run_script("pause.sh", "now", "--dry-run", "--reason", "owner said stop")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("HARD pause", result.stdout)
        self.assertIn("graceful", result.stdout)
        self.assertFalse((self.state / "paused").exists())

    def test_the_hard_pause_stops_the_helpers_and_latches_their_stop_files(self):
        result = self.run_script("pause.sh", "now", "--reason", "owner said stop",
                                 KIT_MAIN_PID_CMD="echo ''")
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        self.assertTrue((self.state / "paused").exists())
        self.assertTrue((self.state / "goal-keeper.stop").exists())
        self.assertTrue((self.state / "key-watch.stop").exists())
        self.assertEqual((self.state / "max-codex").read_text().strip(), "0")

    def test_a_dry_run_writes_no_event_log_and_arms_no_timer(self):
        future = "9999999999"
        result = self.run_script("pause.sh", "graceful", future, "--dry-run", "--reason", "later")
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        self.assertIn("nothing is armed", result.stdout)
        self.assertFalse((self.state / "events-meta.log").exists(),
                         "a dry run wrote to the event log")
        self.assertFalse((self.state / "timer-landing.pid").exists())

    def test_status_reads_the_markers(self):
        (self.state / "cutoff").write_text("2026-01-01T00:00:00Z the key died\n")
        result = self.run_script("pause.sh", "status")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("the key died", result.stdout)
        self.assertIn("paused:   no", result.stdout)

    def test_the_pause_watch_acts_on_the_cutoff_marker(self):
        (self.state / "cutoff").write_text("2026-01-01T00:00:00Z the main key failed\n")
        result = self.run_script("pause-watch.sh", "--once", KIT_MAIN_PID_CMD="echo ''")
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        self.assertTrue((self.state / "paused").exists())
        self.assertIn("cutoff marker", (self.state / "paused").read_text())

    def test_the_pause_watch_does_nothing_without_a_trigger(self):
        result = self.run_script("pause-watch.sh", "--once")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertFalse((self.state / "paused").exists())


class StanddownTemplateTests(SessionHarness):
    def test_the_message_is_rendered_with_every_placeholder_filled(self):
        result = self.run_script("standdown.sh", "--dry-run", "--minutes", "20",
                                 "--reason", "the operator is switching the layout",
                                 "--next-layout", "one main session, two workers")
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        out = result.stdout
        self.assertNotIn("{{", out, "an unfilled placeholder is left in the message")
        self.assertIn("the operator is switching the layout", out)
        self.assertIn("one main session, two workers", out)
        self.assertIn("within 20 minutes", out)
        self.assertIn(str(self.state / "main-standdown.done"), out)
        self.assertIn("handover-section.md", out)

    def test_without_a_progress_issue_the_message_says_to_skip_that_step(self):
        result = self.run_script("standdown.sh", "--dry-run")
        self.assertIn("skip this step", result.stdout)

    def test_with_a_progress_issue_the_message_names_it(self):
        result = self.run_script("standdown.sh", "--dry-run",
                                 KIT_PROGRESS_ISSUE="42", KIT_GITHUB_SLUG="OWNER/REPO")
        self.assertIn("OWNER/REPO#42", result.stdout)

    def test_a_missing_main_session_is_not_an_error(self):
        result = self.run_script("standdown.sh", KIT_MAIN_PID_CMD="echo ''")
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        self.assertIn("nothing to hand over", result.stdout)
        self.assertEqual(self.say_calls(), [])


class StatusTests(SessionHarness):
    def test_status_prints_one_screen_of_the_things_that_matter(self):
        (self.state / "main-key").write_text("testkey\n")
        (self.state / "max-codex").write_text("2\n")
        (self.state / "goal-text").write_text("/goal do the work\n")
        (self.state / "events-meta.log").write_text("2026-01-01T00:00:00Z something happened\n")
        (self.state / "key-disabled").mkdir(exist_ok=True)
        (self.state / "key-disabled" / "oldkey").write_text("2026-01-01T00:00:00Z out of quota\n")
        result = self.run_script("status.sh")
        self.assertEqual(result.returncode, 0, result.stderr)
        for needle in ("main session", "testkey", "goal keeper", "merge queue",
                       "retired keys", "oldkey", "something happened", "/goal do the work",
                       "default home", "worker models"):
            self.assertIn(needle, result.stdout, f"status.sh does not report {needle!r}")

    def test_status_reports_the_shim_guard_and_the_model_allowlist(self):
        result = self.run_script("status.sh")
        self.assertIn("default home usable as a fallback", result.stdout)
        self.assertIn("worker models any (no allowlist)", result.stdout)
        # keyrot-install.sh writes these two; status.sh only reads them.
        (self.state / "no-default-home").write_text(
            "2026-01-01T00:00:00Z the default CODEX_HOME is not one of the configured keys\n")
        (self.state / "models-allowed").write_text("model-a\nmodel-b\n")
        result = self.run_script("status.sh")
        self.assertIn("default home REFUSED as a fallback", result.stdout)
        self.assertIn("model-a model-b", result.stdout)


class ResumeTests(SessionHarness):
    def test_resume_refuses_and_clears_nothing_when_the_key_is_dead(self):
        self.key_home("testkey")
        self.reply(1, '{"error":"API_KEY_DISABLED"}', 401)
        (self.state / "paused").write_text("2026-01-01T00:00:00Z stopped\n")
        result = self.run_script("resume.sh", "--key", "testkey",
                                 KIT_KEY_HOME_TESTKEY=str(self.root / "codex-home-testkey"))
        self.assertEqual(result.returncode, 75, result.stdout)
        self.assertTrue((self.state / "paused").exists(),
                        "a refused resume must leave the markers alone")

    def test_dry_run_describes_the_whole_bring_up_order(self):
        self.key_home("testkey")
        self.reply(1, "{}", 200)
        result = self.run_script("resume.sh", "--key", "testkey", "--lanes", "2", "--dry-run",
                                 KIT_KEY_HOME_TESTKEY=str(self.root / "codex-home-testkey"))
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        for needle in ("DRY resume on key testkey", "key-watch.sh", "pause-watch.sh",
                       "merge-daemon.sh", "handover section", "main-tui.sh start"):
            self.assertIn(needle, result.stdout)


if __name__ == "__main__":
    unittest.main()
