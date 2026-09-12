#!/usr/bin/env python3
"""The chsh build farm: the mode gate, the dry run and the fallback (issue #553).

Three properties are worth a regression test, and they are exactly the three
that would cost a run if they broke.

* **The gate.** chsh is used in full speed mode and never otherwise, so
  ``run_mode.py get offload`` must answer ``yes`` only for a fast, unpaused
  brief that lists the host — and ``no`` for a default-speed run, a brief
  without the field, a paused run and a mode document that predates the field.
* **The dry run.** ``build-on-chsh.sh --dry-run`` must print every command and
  contact chsh not at all, so an operator can read the plan on a host that has
  no route to the farm.  The stubs here fail loudly if they are executed.
* **The fallback.** A lane must never fail because chsh is unreachable.  With
  the offload script failing the way an unreachable host makes it fail (exit
  64), ``offload_lake_build`` must run the local build and return ITS exit
  code — and with a build that genuinely failed (any other code) it must pass
  that through instead of silently spending the build lease twice.

Everything runs against a temporary cache root and a temporary repository root.
No test contacts a network host: the ssh and rsync stubs record their own
invocation and exit nonzero.
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
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
BIN_DIR = REPO_ROOT / "local" / "bin"
sys.path.insert(0, str(BIN_DIR))

import run_mode  # noqa: E402

TEMPLATE = REPO_ROOT / "results/telemetry/owner-tools/run-brief.template.json"
SHIM_TEMPLATE = REPO_ROOT / "results/telemetry/owner-tools/owner-bin-codex"
OFFLOAD_SH = REPO_ROOT / "results/telemetry/owner-tools/build-on-chsh.sh"
HELPER_SH = BIN_DIR / "offload-build.sh"

#: A `run_mode.py` stand-in for the shell tests: `get offload` is the only
#: question build-on-chsh.sh asks, and these tests fix the answer directly so
#: the shell side is tested without a whole briefing.
RUN_MODE_STUB = """#!/usr/bin/env python3
import sys
print("{answer}" if sys.argv[1:3] == ["get", "offload"] else "")
"""

#: A stub that fails if it is ever run, and says so in a file the test reads.
NEVER_STUB = """#!/usr/bin/env bash
printf '%s %s\\n' "$0" "$*" >> "{marker}"
exit 255
"""


def run_mode_main(argv: list[str]) -> tuple[int, str, str]:
    out, err = io.StringIO(), io.StringIO()
    with redirect_stdout(out), redirect_stderr(err):
        code = run_mode.main(argv)
    return code, out.getvalue(), err.getvalue()


class OffloadGateTest(unittest.TestCase):
    """`run_mode.py get offload` is the ONE answer to "may this run use chsh"."""

    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        root = Path(self._tmp.name)
        self.cache = root / "cache"
        self.repo = root / "repo"
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

    def write_brief(self, mutate) -> None:
        doc = json.loads(TEMPLATE.read_text(encoding="utf-8"))
        mutate(doc)
        self.brief.write_text(json.dumps(doc), encoding="utf-8")

    def get(self, key: str) -> str:
        code, out, err = run_mode_main(["get", key])
        self.assertEqual(code, 0, err)
        return out.strip()

    def apply(self) -> None:
        code, out, err = run_mode_main(["apply"])
        self.assertEqual(code, 0, out + err)

    # -- the four "no" cases and the one "yes" ---------------------------

    def test_template_is_a_full_speed_brief_that_uses_chsh(self) -> None:
        self.apply()
        self.assertEqual(self.get("offload"), "yes")
        self.assertEqual(self.get("offload_hosts"), "chsh")
        self.assertIn("chsh", self.get("offload_reason"))

    def test_default_speed_never_uses_chsh(self) -> None:
        self.write_brief(lambda d: d["run"].update(speed="default"))
        self.apply()
        self.assertEqual(self.get("offload"), "no")
        self.assertIn("fast", self.get("offload_reason"))

    def test_absent_compute_block_is_no(self) -> None:
        self.write_brief(lambda d: d["run"].pop("compute"))
        self.apply()
        self.assertEqual(self.get("offload"), "no")
        self.assertEqual(self.get("offload_hosts"), "none")

    def test_empty_host_list_is_no(self) -> None:
        self.write_brief(lambda d: d["run"].update(compute={"offload_hosts": []}))
        self.apply()
        self.assertEqual(self.get("offload"), "no")

    def test_pause_disables_the_offload_and_resume_restores_it(self) -> None:
        self.apply()
        self.assertEqual(self.get("offload"), "yes")
        code, _, err = run_mode_main(["pause", "--reason", "owner word"])
        self.assertEqual(code, 0, err)
        self.assertEqual(self.get("offload"), "no")
        self.assertIn("paused", self.get("offload_reason"))
        code, _, err = run_mode_main(["resume"])
        self.assertEqual(code, 0, err)
        self.assertEqual(self.get("offload"), "yes")

    def test_speed_switch_moves_the_offload_with_it(self) -> None:
        self.apply()
        code, _, err = run_mode_main(["set", "speed", "default"])
        self.assertEqual(code, 0, err)
        self.assertEqual(self.get("offload"), "no")
        code, _, err = run_mode_main(["set", "speed", "fast"])
        self.assertEqual(code, 0, err)
        self.assertEqual(self.get("offload"), "yes")

    def test_unknown_host_is_a_briefing_time_error(self) -> None:
        self.write_brief(lambda d: d["run"].update(compute={"offload_hosts": ["gpu-box"]}))
        code, _, err = run_mode_main(["apply"])
        self.assertEqual(code, 2)
        self.assertIn("offload_hosts", err)
        self.assertIn("gpu-box", err)

    def test_unknown_key_under_compute_is_an_error(self) -> None:
        self.write_brief(lambda d: d["run"].update(compute={"offload_host": ["chsh"]}))
        code, _, err = run_mode_main(["apply"])
        self.assertEqual(code, 2)
        self.assertIn("run.compute", err)

    def test_a_mode_document_without_the_field_is_no(self) -> None:
        """An older run-mode.json must read as "do not use chsh", not as a crash."""
        self.apply()
        mode = json.loads((self.cache / "watchdog" / "run-mode.json").read_text("utf-8"))
        mode["run"].pop("compute")
        (self.cache / "watchdog" / "run-mode.json").write_text(
            json.dumps(mode), encoding="utf-8")
        self.assertFalse(run_mode.offload_enabled(mode))
        self.assertEqual(self.get("offload"), "no")

    def test_show_states_the_offload(self) -> None:
        self.apply()
        code, out, err = run_mode_main(["show"])
        self.assertEqual(code, 0, err)
        self.assertRegex(out, r"offload\s+yes")


class ShellTestCase(unittest.TestCase):
    """Shared scaffolding: a tmp cache root, stub binaries, a fake worktree."""

    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.root = Path(self._tmp.name)
        self.cache = self.root / "cache"
        (self.cache / "watchdog" / "chsh").mkdir(parents=True)
        self.marker = self.root / "contacted-chsh.txt"
        self.worktree = self.root / "issue-553-chsh-build-farm"
        self.worktree.mkdir()
        (self.worktree / "lakefile.toml").write_text("name = \"MIPStarRE\"\n", encoding="utf-8")
        (self.worktree / "lean-toolchain").write_text("leanprover/lean4:v4.32.0\n", encoding="utf-8")

    def tearDown(self) -> None:
        self._tmp.cleanup()

    def stub(self, name: str, body: str, mode: int = 0o755) -> Path:
        path = self.root / name
        path.write_text(body, encoding="utf-8")
        path.chmod(mode)
        return path

    def never_stub(self, name: str) -> Path:
        return self.stub(name, NEVER_STUB.format(marker=self.marker))

    def run_mode_stub(self, answer: str) -> Path:
        return self.stub(f"run_mode_{answer}.py", RUN_MODE_STUB.format(answer=answer))

    def env(self, **extra: str) -> dict:
        env = dict(os.environ)
        env.update({
            "MIPSTARRE_CACHE_ROOT": str(self.cache),
            "HOME": str(self.root),
        })
        env.update(extra)
        return env

    def assertNeverContacted(self) -> None:
        self.assertFalse(self.marker.exists(),
                         f"chsh was contacted: {self.marker.read_text() if self.marker.exists() else ''}")


class DryRunTest(ShellTestCase):
    """`--dry-run` prints the plan and touches no network."""

    def test_dry_run_prints_every_command_and_contacts_nothing(self) -> None:
        done = subprocess.run(
            ["bash", str(OFFLOAD_SH), "--dry-run", str(self.worktree), "MIPStarRE.QPBT"],
            capture_output=True, text=True,
            env=self.env(CHSH_SSH_BIN=str(self.never_stub("ssh")),
                         CHSH_RSYNC_BIN=str(self.never_stub("rsync")),
                         MIPSTARRE_RUN_MODE=str(self.run_mode_stub("no"))))
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertNeverContacted()
        for expected in ("lean-toolchain", "cp -al", "rsync", "lake build MIPStarRE.QPBT",
                         "--exclude=/results/telemetry", ".offload-stamp"):
            self.assertIn(expected, done.stdout, f"the dry run never mentions {expected!r}")
        self.assertIn("DISABLED", done.stdout,
                      "the dry run must say that a real run would not have offloaded")

    def test_dry_run_of_the_seed_refresh(self) -> None:
        checkout = self.root / "MIPStarRE-qpbt"
        checkout.mkdir()
        (checkout / "lakefile.toml").write_text("name = \"MIPStarRE\"\n", encoding="utf-8")
        done = subprocess.run(
            ["bash", str(OFFLOAD_SH), "--dry-run", "--seed-refresh"],
            capture_output=True, text=True,
            env=self.env(CHSH_SSH_BIN=str(self.never_stub("ssh")),
                         CHSH_RSYNC_BIN=str(self.never_stub("rsync")),
                         MIPSTARRE_CHECKOUT=str(checkout),
                         MIPSTARRE_RUN_MODE=str(self.run_mode_stub("yes"))))
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertNeverContacted()
        self.assertIn("lake build MIPStarRE.QPBT", done.stdout)
        self.assertIn("seed", done.stdout)


class GateEnforcementTest(ShellTestCase):
    """The script refuses to contact chsh when the run mode says no."""

    def test_disabled_run_mode_exits_unusable_without_touching_the_host(self) -> None:
        done = subprocess.run(
            ["bash", str(OFFLOAD_SH), str(self.worktree)],
            capture_output=True, text=True,
            env=self.env(CHSH_SSH_BIN=str(self.never_stub("ssh")),
                         CHSH_RSYNC_BIN=str(self.never_stub("rsync")),
                         MIPSTARRE_RUN_MODE=str(self.run_mode_stub("no"))))
        self.assertEqual(done.returncode, 64, done.stdout + done.stderr)
        self.assertNeverContacted()

    def test_missing_known_hosts_is_unusable_not_an_insecure_connection(self) -> None:
        done = subprocess.run(
            ["bash", str(OFFLOAD_SH), str(self.worktree)],
            capture_output=True, text=True,
            env=self.env(CHSH_SSH_BIN=str(self.never_stub("ssh")),
                         CHSH_RSYNC_BIN=str(self.never_stub("rsync")),
                         MIPSTARRE_RUN_MODE=str(self.run_mode_stub("yes"))))
        self.assertEqual(done.returncode, 64, done.stdout + done.stderr)
        self.assertIn("known-hosts", done.stderr)
        self.assertNeverContacted()

    def test_ssh_failure_is_reported_as_unusable(self) -> None:
        (self.cache / "watchdog" / "chsh" / "known_hosts").write_text("|1|x\n", encoding="utf-8")
        done = subprocess.run(
            ["bash", str(OFFLOAD_SH), str(self.worktree)],
            capture_output=True, text=True,
            env=self.env(CHSH_SSH_BIN=str(self.never_stub("ssh")),
                         CHSH_RSYNC_BIN=str(self.never_stub("rsync")),
                         MIPSTARRE_RUN_MODE=str(self.run_mode_stub("yes"))))
        self.assertEqual(done.returncode, 64, done.stdout + done.stderr)
        self.assertTrue(self.marker.exists(), "the stub ssh should have been tried")

    def test_check_reports_the_gate(self) -> None:
        for answer, code in (("yes", 0), ("no", 1)):
            done = subprocess.run(
                ["bash", str(OFFLOAD_SH), "--check"], capture_output=True, text=True,
                env=self.env(MIPSTARRE_RUN_MODE=str(self.run_mode_stub(answer))))
            self.assertEqual(done.returncode, code, done.stdout + done.stderr)


#: Driver for the fallback tests: source the helper, stub the local build, run.
DRIVER = """#!/usr/bin/env bash
set -u
. "{helper}"
offload_local_build() {{ printf 'LOCAL %s\\n' "$*" >> "{built}"; return {local_rc}; }}
offload_lake_build "{worktree}" "lane-553" MIPStarRE.QPBT
printf 'RC=%s\\n' "$?"
"""

#: An offload script whose exit code the test chooses.  It records that it ran.
FAKE_OFFLOAD = """#!/usr/bin/env bash
if [ "${{1:-}}" = --check ]; then exit {check_rc}; fi
printf 'OFFLOAD %s\\n' "$*" >> "{ran}"
exit {rc}
"""


class FallbackTest(ShellTestCase):
    """A lane never fails because chsh is unreachable — and never builds twice."""

    def drive(self, *, offload_rc: int, check_rc: int = 0, local_rc: int = 0) -> str:
        ran = self.root / "offload-ran.txt"
        built = self.root / "local-built.txt"
        script = self.stub("fake-offload.sh",
                           FAKE_OFFLOAD.format(rc=offload_rc, check_rc=check_rc, ran=ran))
        driver = self.stub("driver.sh", DRIVER.format(
            helper=HELPER_SH, built=built, worktree=self.worktree, local_rc=local_rc))
        done = subprocess.run(
            ["bash", str(driver)], capture_output=True, text=True,
            # The run mode is asked independently of MIPSTARRE_OFFLOAD_SCRIPT, so
            # these tests state it: without it the helper answers "not a full
            # speed run" and never reaches the script at all.
            env=self.env(MIPSTARRE_OFFLOAD_SCRIPT=str(script),
                         MIPSTARRE_RUN_MODE=str(self.run_mode_stub("yes"))))
        self.ran = ran
        self.built = built
        return done.stdout + done.stderr

    def test_unreachable_chsh_falls_back_to_the_local_build(self) -> None:
        out = self.drive(offload_rc=64, local_rc=0)
        self.assertIn("RC=0", out)
        self.assertIn("host=ghz", out)
        self.assertTrue(self.ran.exists(), "the offload should have been attempted")
        self.assertTrue(self.built.exists(), "the local build must have run")

    def test_returned_artifacts_failure_also_falls_back(self) -> None:
        out = self.drive(offload_rc=65, local_rc=0)
        self.assertIn("RC=0", out)
        self.assertTrue(self.built.exists())

    def test_the_local_build_verdict_is_the_lane_verdict(self) -> None:
        out = self.drive(offload_rc=64, local_rc=1)
        self.assertIn("RC=1", out)

    def test_a_real_build_failure_is_passed_through_not_retried(self) -> None:
        out = self.drive(offload_rc=1)
        self.assertIn("RC=1", out)
        self.assertIn("host=chsh", out)
        self.assertFalse(self.built.exists(),
                         "a failed proof must not be rebuilt locally in the hope of "
                         "a different answer")

    def test_a_successful_offload_skips_the_local_build(self) -> None:
        out = self.drive(offload_rc=0)
        self.assertIn("RC=0", out)
        self.assertIn("host=chsh", out)
        self.assertFalse(self.built.exists())

    def test_a_disabled_gate_never_runs_the_offload(self) -> None:
        out = self.drive(offload_rc=0, check_rc=1)
        self.assertIn("RC=0", out)
        self.assertIn("host=ghz", out)
        self.assertFalse(self.ran.exists(), "a disabled run must not contact chsh at all")
        self.assertTrue(self.built.exists())

    def test_the_kill_switch_wins_over_an_enabled_mode(self) -> None:
        ran = self.root / "offload-ran.txt"
        built = self.root / "local-built.txt"
        script = self.stub("fake-offload.sh", FAKE_OFFLOAD.format(rc=0, check_rc=0, ran=ran))
        driver = self.stub("driver.sh", DRIVER.format(
            helper=HELPER_SH, built=built, worktree=self.worktree, local_rc=0))
        done = subprocess.run(["bash", str(driver)], capture_output=True, text=True,
                              env=self.env(MIPSTARRE_OFFLOAD_SCRIPT=str(script),
                                           MIPSTARRE_RUN_MODE=str(self.run_mode_stub("yes")),
                                           MIPSTARRE_OFFLOAD="0"))
        self.assertIn("host=ghz", done.stdout)
        self.assertFalse(ran.exists())

    def test_a_default_speed_run_never_reaches_the_script(self) -> None:
        """MIPSTARRE_OFFLOAD_SCRIPT can redirect the offload; it cannot enable it."""
        ran = self.root / "offload-ran.txt"
        built = self.root / "local-built.txt"
        script = self.stub("fake-offload.sh", FAKE_OFFLOAD.format(rc=0, check_rc=0, ran=ran))
        driver = self.stub("driver.sh", DRIVER.format(
            helper=HELPER_SH, built=built, worktree=self.worktree, local_rc=0))
        done = subprocess.run(["bash", str(driver)], capture_output=True, text=True,
                              env=self.env(MIPSTARRE_OFFLOAD_SCRIPT=str(script),
                                           MIPSTARRE_RUN_MODE=str(self.run_mode_stub("no"))))
        self.assertIn("host=ghz", done.stdout)
        self.assertFalse(ran.exists(),
                         "a run whose mode says no must not run the offload script, "
                         "however friendly that script's --check is")
        self.assertTrue(built.exists())


class ShellSyntaxTest(unittest.TestCase):
    def test_bash_n(self) -> None:
        for path in (OFFLOAD_SH, HELPER_SH, BIN_DIR / "lane.sh", BIN_DIR / "ci.sh",
                     REPO_ROOT / "results/telemetry/owner-tools/install.sh",
                     REPO_ROOT / "results/telemetry/owner-tools/merge-daemon.sh"):
            with self.subTest(script=path.name):
                done = subprocess.run(["bash", "-n", str(path)],
                                      capture_output=True, text=True)
                self.assertEqual(done.returncode, 0, done.stderr)

    def test_the_offload_script_is_installed_by_the_installer(self) -> None:
        installer = (REPO_ROOT / "results/telemetry/owner-tools/install.sh").read_text("utf-8")
        self.assertIn("build-on-chsh.sh|build-on-chsh.sh|755", installer)
        self.assertIn("known_hosts", installer)

    def test_the_merge_daemon_refreshes_the_seed_after_a_merge(self) -> None:
        daemon = (REPO_ROOT / "results/telemetry/owner-tools/merge-daemon.sh").read_text("utf-8")
        self.assertIn("chsh_seed_refresh", daemon)
        self.assertIn("--seed-refresh", daemon)

    def test_the_pre_push_per_file_gate_stays_on_this_host(self) -> None:
        """`lake env lean` is never offloaded: the push gate runs where we push.

        Asserted on the GATE'S CALL SITES rather than on the absence of the
        string "build-on-chsh" from lane.sh: lane.sh reaches the farm by sourcing
        offload-build.sh, so that assertion passed for the wrong reason and would
        have gone on passing if the `lake env lean` gate itself were offloaded.
        """
        hook = (REPO_ROOT / ".githooks" / "pre-push").read_text("utf-8")
        self.assertNotIn("chsh", hook)
        self.assertNotIn("offload", hook)
        gate_lines = [line for line in hook.splitlines()
                      if "lake env lean" in line and not line.strip().startswith("#")]
        self.assertTrue(gate_lines,
                        "the pre-push hook must still run `lake env lean` per changed file")
        for body, where in ((hook, ".githooks/pre-push"),
                            ((BIN_DIR / "lane.sh").read_text("utf-8"), "lane.sh"),
                            ((BIN_DIR / "ci.sh").read_text("utf-8"), "ci.sh")):
            for number, line in enumerate(body.splitlines(), 1):
                if "lake env lean" not in line or line.strip().startswith("#"):
                    continue
                with self.subTest(where=f"{where}:{number}"):
                    self.assertNotIn("offload", line)
                    self.assertNotIn("chsh", line)

    def test_the_offload_returns_the_whole_closure_not_the_delta(self) -> None:
        """The post-condition is the local .lake/build, not chsh's own delta.

        `find lib ir -newer .offload-stamp` returns what chsh rebuilt relative to
        ITS seed, which tracks `main`, while a ghz worktree is warmed from the
        hot-main snapshot and lags it.  Every module that moved in that gap has
        an olean on chsh and none here, the offload reports success, nothing
        falls back, and the lane dies at the per-file push gate.
        """
        body = OFFLOAD_SH.read_text("utf-8")
        self.assertNotIn("--files-from", body,
                         "the artifact return must not be a file list built from "
                         "chsh's own stamp")
        self.assertIn('"$CHSH_HOST:$LANE/.lake/build/" "$SRC/.lake/build/"', body,
                      "the whole .lake/build tree is what comes back")
        self.assertIn("--timeout=", body.replace('--timeout="$RSYNC_TIMEOUT_S"',
                                                 "--timeout=X"),
                      "every rsync needs an I/O timeout: ssh's ServerAlive only "
                      "notices a link that is dead, not one that is slow")
        for line in body.splitlines():
            if line.strip().startswith("#") or '"$RSYNC_BIN"' not in line:
                continue
            with self.subTest(line=line.strip()[:60]):
                self.assertIn("--timeout=", line)

    def test_the_seed_stamp_is_written_after_the_rebuild(self) -> None:
        body = OFFLOAD_SH.read_text("utf-8")
        rebuild = body.index("seed refresh: the rebuild on")
        stamp = body.index(': > "$stamp"')
        self.assertGreater(stamp, rebuild,
                           "a refresh that fails must not rate-limit its own retries "
                           "for an hour; after a toolchain bump that is an hour of "
                           "silently unused farm")

    def test_the_offload_has_a_wall_clock(self) -> None:
        helper = HELPER_SH.read_text("utf-8")
        self.assertIn("MIPSTARRE_OFFLOAD_TIMEOUT_S", helper)
        self.assertIn("OFFLOAD_TIMED_OUT=124", helper)
        self.assertIn('rc="$OFFLOAD_UNUSABLE"', helper,
                      "a stalled offload is 'chsh is unusable', never a verdict "
                      "on the proof")

    def test_the_script_variable_cannot_turn_the_farm_on(self) -> None:
        helper = HELPER_SH.read_text("utf-8")
        gate = helper.split("offload_enabled_for_run()", 1)[1]
        self.assertIn("offload_run_mode_says_yes", gate.split("offload_script", 1)[0],
                      "full-speed-mode.md section 5.1 claims there is no environment "
                      "variable that turns the offload on; the run mode must be asked "
                      "before MIPSTARRE_OFFLOAD_SCRIPT is honoured")


if __name__ == "__main__":
    unittest.main()
