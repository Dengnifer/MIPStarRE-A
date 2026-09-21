#!/usr/bin/env python3
"""Unit tests for the service layer (``local/bin/service``) and the operator tools
(``results/telemetry/owner-tools``).

Everything here is offline: no tmux, no codex, no gh, no network.  Temporary git
repositories, stub executables on PATH and ``--dry-run`` entry points stand in for the
machine.  Three things are pinned:

* every shell script parses and every Python tool compiles;
* no origin-project name, path, host, key or model id survives in these files;
* the behaviours that were paid for in incidents — the record path filter, the worker
  routing rules of the shim, and a status screen that still works on a fresh project.

The gate's decision table lives in ``test_service_gate.py`` and the train member rules in
``test_service_trains.py``.
"""

from __future__ import annotations

import json
import os
import py_compile
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
from project_config import PLACEHOLDER_SLUG  # noqa: E402

SERVICE = ROOT / "local" / "bin" / "service"
OWNER_TOOLS = ROOT / "results" / "telemetry" / "owner-tools"


def files_of(directory: Path) -> list[Path]:
    return sorted(p for p in directory.iterdir() if p.is_file() and not p.name.startswith("."))


def is_python(path: Path) -> bool:
    if path.suffix == ".py":
        return True
    head = path.read_bytes()[:80]
    return head.startswith(b"#!") and b"python" in head.splitlines()[0]


def is_shell(path: Path) -> bool:
    if path.suffix == ".sh":
        return True
    head = path.read_bytes()[:80]
    return head.startswith(b"#!") and (b"bash" in head.splitlines()[0] or b" sh" in head.splitlines()[0])


def run(*cmd: str, **kwargs) -> subprocess.CompletedProcess:
    return subprocess.run(list(cmd), capture_output=True, text=True, **kwargs)


class SyntaxTests(unittest.TestCase):
    """Nothing ships that does not parse — a service script fails at 3 a.m. or never."""

    def test_every_service_shell_script_parses(self) -> None:
        checked = 0
        for path in files_of(SERVICE) + files_of(OWNER_TOOLS):
            if not is_shell(path) or is_python(path):
                continue
            with self.subTest(script=path.name):
                proc = run("bash", "-n", str(path))
                self.assertEqual(proc.returncode, 0, proc.stderr)
            checked += 1
        self.assertGreaterEqual(checked, 12, "expected the service and operator shell tools")

    def test_every_service_python_tool_compiles(self) -> None:
        checked = 0
        with tempfile.TemporaryDirectory() as tmp:
            for path in files_of(SERVICE) + files_of(OWNER_TOOLS):
                if not is_python(path):
                    continue
                with self.subTest(tool=path.name):
                    py_compile.compile(str(path), doraise=True,
                                       cfile=str(Path(tmp) / (path.name + "c")))
                checked += 1
        self.assertGreaterEqual(checked, 5)

    def test_the_named_service_tools_all_exist(self) -> None:
        expected = {
            "merge-daemon.sh", "daemon-scan.py", "lane.sh", "merge.sh", "gate.py",
            "stage-train.py", "stage-when-quiet.sh", "train-precheck.sh", "train-recover.sh",
            "records.sh", "auto-merge.py", "codex-shim", "keyrot-install.sh",
        }
        present = {p.name for p in files_of(SERVICE)}
        self.assertEqual(expected - present, set())

    def test_every_executable_service_tool_is_executable(self) -> None:
        for path in files_of(SERVICE):
            if path.name.endswith(("-lib.sh", "_env.py")):
                continue  # sourced / imported, not run
            with self.subTest(tool=path.name):
                self.assertTrue(os.access(path, os.X_OK), f"{path.name} is not executable")


class NoOriginLeakTests(unittest.TestCase):
    """The kit is paper-agnostic: no origin name, path, host, key or model id remains.

    The env prefix ``MIPSTARRE_``, the cache-directory default name and the
    ``mipstarre-review`` comment marker are deliberately kept (a documented decision),
    so only the mixed-case library token and the origin's own names are forbidden.
    """

    FORBIDDEN = (
        "MIPStarRE", "QPBT", "Dengnifer", "/home/", "gpt-6-astra", "gpt-5.6-sol",
        "space-d", "space-3", "relay-1", "relay-3", "codex-home-space", "erkki",
    )

    def test_no_origin_token_survives(self) -> None:
        for path in files_of(SERVICE) + files_of(OWNER_TOOLS):
            text = path.read_text(encoding="utf-8", errors="replace")
            for token in self.FORBIDDEN:
                with self.subTest(file=path.name, token=token):
                    self.assertNotIn(token, text)

    def test_no_absolute_home_path_is_hard_coded(self) -> None:
        pattern = re.compile(r"(?<![\w$])/(?:home|Users)/[a-z]")
        for path in files_of(SERVICE) + files_of(OWNER_TOOLS):
            text = path.read_text(encoding="utf-8", errors="replace")
            with self.subTest(file=path.name):
                self.assertIsNone(pattern.search(text))


class TempRepo:
    """A throwaway git repository with a `github` remote, for the record tools."""

    def __init__(self, tmp: Path) -> None:
        self.root = tmp / "repo"
        self.bare = tmp / "remote.git"
        self.state = tmp / "state"
        self.root.mkdir(parents=True)
        self.state.mkdir(parents=True)
        run("git", "init", "-q", "-b", "main", str(self.root))
        run("git", "init", "-q", "--bare", str(self.bare))
        self.git("config", "user.email", "test@localhost")
        self.git("config", "user.name", "test")
        self.git("remote", "add", "github", str(self.bare))
        for relative in ("results/telemetry", "local/bin/service", "local/registry"):
            (self.root / relative).mkdir(parents=True, exist_ok=True)
        (self.root / "results/telemetry/events.md").write_text("# log\n", encoding="utf-8")
        sync = self.root / "local/bin/github-sync.sh"
        sync.write_text('#!/usr/bin/env bash\nexec git push -q github "${1:-main}"\n', encoding="utf-8")
        sync.chmod(0o755)
        for name in ("service-lib.sh", "records.sh"):
            shutil.copy2(SERVICE / name, self.root / "local/bin/service" / name)
        (self.root / "local/bin/service/records.sh").chmod(0o755)
        self.git("add", "-A")
        self.git("commit", "-q", "-m", "init")
        self.git("push", "-q", "github", "main")

    def git(self, *args: str) -> subprocess.CompletedProcess:
        return run("git", "-C", str(self.root), *args)

    def records(self, *args: str) -> subprocess.CompletedProcess:
        env = dict(os.environ, KIT_STATE_DIR=str(self.state), KIT_CACHE_ROOT=str(self.state.parent),
                   KIT_REPO_ROOT=str(self.root), HOME=str(self.state.parent),
                   KIT_CONFIG_SOURCED="1")
        return run("bash", str(self.root / "local/bin/service/records.sh"), *args, env=env)


class RecordsFilterTests(unittest.TestCase):
    """records.sh commits records, and nothing else, ever."""

    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.repo = TempRepo(Path(self.tmp.name))

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def test_markdown_and_jsonl_records_are_committed(self) -> None:
        (self.repo.root / "results/telemetry/sessions.jsonl").write_text('{"a":1}\n', encoding="utf-8")
        (self.repo.root / "results/telemetry/events.md").write_text("# log\n- a thing\n", encoding="utf-8")
        proc = self.repo.records("a note")
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        self.assertIn("committed", proc.stdout)
        self.assertEqual(self.repo.git("status", "--porcelain").stdout.strip(), "")

    def test_a_script_under_telemetry_is_refused_and_unstaged(self) -> None:
        (self.repo.root / "results/telemetry/sneaky.sh").write_text("echo hi\n", encoding="utf-8")
        proc = self.repo.records("a note")
        self.assertEqual(proc.returncode, 4)
        self.assertIn("not a record", proc.stdout)
        self.assertIn("sneaky.sh", proc.stdout)
        # The index must be left clean, so the next tool is not surprised.
        self.assertEqual(self.repo.git("diff", "--cached", "--name-only").stdout.strip(), "")

    def test_a_dirty_path_outside_telemetry_is_refused(self) -> None:
        (self.repo.root / "source.txt").write_text("edit\n", encoding="utf-8")
        proc = self.repo.records("a note")
        self.assertEqual(proc.returncode, 4)
        self.assertIn("outside results/telemetry", proc.stdout)

    def test_a_staged_train_blocks_any_record_commit(self) -> None:
        daemon = self.repo.state / "daemon"
        daemon.mkdir(parents=True)
        (daemon / "train-approved.json").write_text("{}", encoding="utf-8")
        (self.repo.root / "results/telemetry/sessions.jsonl").write_text('{"a":1}\n', encoding="utf-8")
        proc = self.repo.records("a note")
        self.assertEqual(proc.returncode, 3)
        self.assertIn("train marker", proc.stdout)

    def test_helper_spool_rows_are_folded_into_the_registry(self) -> None:
        (self.repo.state / "helper-sessions-spool.jsonl").write_text('{"who":"helper"}\n', encoding="utf-8")
        (self.repo.root / "results/telemetry/owner-sessions.jsonl").write_text("", encoding="utf-8")
        proc = self.repo.records("a note")
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        folded = (self.repo.root / "results/telemetry/owner-sessions.jsonl").read_text(encoding="utf-8")
        self.assertIn('{"who":"helper"}', folded)
        self.assertEqual((self.repo.state / "helper-sessions-spool.jsonl").read_text(encoding="utf-8"), "")


class StatusSnapshotTests(unittest.TestCase):
    """The operating session runs this every turn, including on turn one."""

    def _run(self, state: Path, *args: str) -> subprocess.CompletedProcess:
        with tempfile.TemporaryDirectory() as tmp:
            tree = Path(tmp)
            (tree / "results/telemetry/owner-tools").mkdir(parents=True)
            (tree / "local/bin/service").mkdir(parents=True)
            shutil.copy2(OWNER_TOOLS / "status-snapshot.sh", tree / "results/telemetry/owner-tools")
            env = dict(os.environ, KIT_REPO_ROOT=str(tree), KIT_STATE_DIR=str(state),
                       KIT_CACHE_ROOT=str(state.parent), HOME=str(tree),
                       KIT_CONFIG_SOURCED="1")
            return run("bash", str(tree / "results/telemetry/owner-tools/status-snapshot.sh"),
                       *args, env=env)

    def test_an_absent_state_directory_still_exits_zero(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            proc = self._run(Path(tmp) / "never-created")
            self.assertEqual(proc.returncode, 0, proc.stderr)
            self.assertIn("does not exist yet", proc.stdout)

    def test_an_empty_state_directory_still_exits_zero(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            state = Path(tmp) / "state"
            state.mkdir()
            proc = self._run(state)
            self.assertEqual(proc.returncode, 0, proc.stderr)
            self.assertIn("(none)", proc.stdout)
            self.assertIn("merge daemon: not running", proc.stdout)

    def test_it_names_the_recovery_tool_after_a_refused_train(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            state = Path(tmp) / "state"
            (state / "daemon").mkdir(parents=True)
            (state / "daemon" / "train-approved.running.json").write_text("{}", encoding="utf-8")
            proc = self._run(state)
            self.assertEqual(proc.returncode, 0, proc.stderr)
            self.assertIn("train-recover.sh", proc.stdout)


class CodexShimTests(unittest.TestCase):
    """Worker routing: least loaded, limit respected, dead markers cleaned, no fallback
    onto a retired default home."""

    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        base = Path(self.tmp.name)
        self.cache = base / "cache"
        self.state = self.cache / "watchdog"
        self.rot = self.cache / "keyrot"
        self.owner_bin = self.cache / "owner-bin"
        self.fake_bin = base / "fakebin"
        for directory in (self.state, self.rot, self.owner_bin, self.fake_bin):
            directory.mkdir(parents=True)
        self.shim = self.owner_bin / "codex"
        shutil.copy2(SERVICE / "codex-shim", self.shim)
        self.shim.chmod(0o755)
        self.record = base / "invocation.txt"
        real = self.fake_bin / "codex"
        real.write_text(
            "#!/usr/bin/env bash\n"
            f'printf "HOME=%s\\n" "${{CODEX_HOME:-none}}" > "{self.record}"\n'
            f'printf "ARGS=%s\\n" "$*" >> "{self.record}"\n'
            "exit 0\n", encoding="utf-8")
        real.chmod(0o755)
        self.home = base / "home"
        self.home.mkdir()

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def key(self, name: str, limit: int) -> Path:
        directory = self.rot / name
        directory.mkdir(parents=True, exist_ok=True)
        (directory / ".limit").write_text(f"{limit}\n", encoding="utf-8")
        home = self.cache / f"home-{name}"
        home.mkdir(exist_ok=True)
        (directory / "home").write_text(f"{home}\n", encoding="utf-8")
        return directory

    @staticmethod
    def dead_pid() -> int:
        for candidate in range(60000, 40000, -1):
            try:
                os.kill(candidate, 0)
            except ProcessLookupError:
                return candidate
            except PermissionError:
                continue
        raise unittest.SkipTest("no free pid found for the dead-marker test")

    def call(self, *args: str, **extra) -> subprocess.CompletedProcess:
        env = dict(os.environ, HOME=str(self.home),
                   PATH=f"{self.owner_bin}:{self.fake_bin}:{os.environ['PATH']}",
                   MIPSTARRE_CACHE_ROOT=str(self.cache), KIT_STATE_DIR=str(self.state))
        env.pop("CODEX_HOME", None)
        env.update(extra)
        return run(str(self.shim), *args, env=env)

    def result(self) -> dict[str, str]:
        out = {}
        for line in self.record.read_text(encoding="utf-8").splitlines():
            name, _, value = line.partition("=")
            out[name] = value
        return out

    def test_it_finds_the_real_codex_on_path_and_forces_the_fan_out_guard(self) -> None:
        proc = self.call("exec", "--", "do a thing")
        self.assertEqual(proc.returncode, 0, proc.stderr)
        args = self.result()["ARGS"]
        self.assertIn("features.multi_agent=false", args)
        self.assertIn("agents.max_concurrent_threads_per_session=1", args)
        self.assertIn("Do not use collaboration tools", args)

    def test_re_enabling_fan_out_is_refused(self) -> None:
        proc = self.call("exec", "--enable", "multi_agent", "--", "task")
        self.assertEqual(proc.returncode, 4)
        self.assertIn("fan-out", proc.stderr)

    def test_a_whole_feature_table_override_is_refused(self) -> None:
        proc = self.call("exec", "-c", 'features={"multi_agent":true}', "--", "task")
        self.assertEqual(proc.returncode, 4)

    def test_it_picks_the_least_loaded_home(self) -> None:
        busy = self.key("alpha", 2)
        free = self.key("beta", 2)
        (busy / str(os.getpid())).write_text("", encoding="utf-8")
        proc = self.call("exec", "--", "task")
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertEqual(self.result()["HOME"], str(self.cache / "home-beta"))
        self.assertTrue(any(p.name.isdigit() for p in free.iterdir()))

    def test_a_home_at_its_limit_is_skipped(self) -> None:
        full = self.key("alpha", 1)
        self.key("beta", 1)
        (full / str(os.getpid())).write_text("", encoding="utf-8")
        proc = self.call("exec", "--", "task")
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertEqual(self.result()["HOME"], str(self.cache / "home-beta"))

    def test_a_dead_marker_frees_its_slot(self) -> None:
        only = self.key("alpha", 1)
        stale = only / str(self.dead_pid())
        stale.write_text("", encoding="utf-8")
        proc = self.call("exec", "--", "task")
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertFalse(stale.exists(), "a marker of a dead pid must be cleaned up")
        self.assertEqual(self.result()["HOME"], str(self.cache / "home-alpha"))

    def test_the_no_default_home_guard_exits_75(self) -> None:
        full = self.key("alpha", 1)
        (full / str(os.getpid())).write_text("", encoding="utf-8")
        (self.state / "no-default-home").write_text("retired\n", encoding="utf-8")
        proc = self.call("exec", "--", "task")
        self.assertEqual(proc.returncode, 75)
        self.assertFalse(self.record.exists(), "nothing may start on the retired default home")

    def test_an_unlisted_model_is_refused_when_an_allowlist_exists(self) -> None:
        self.key("alpha", 1)
        (self.state / "models-allowed").write_text("approved-model\n", encoding="utf-8")
        self.assertEqual(self.call("exec", "-m", "some-other-model", "--", "t").returncode, 4)
        self.assertEqual(self.call("exec", "-m", "approved-model", "--", "t").returncode, 0)

    def test_primary_only_mode_refuses_a_foreign_home(self) -> None:
        (self.state / "account-mode").write_text("primary\n", encoding="utf-8")
        proc = self.call("exec", "--", "task", CODEX_HOME=str(self.cache / "elsewhere"))
        self.assertEqual(proc.returncode, 4)

    def test_the_model_and_effort_come_from_the_configuration(self) -> None:
        proc = self.call("exec", "--", "task",
                         KIT_WORKER_MODEL="configured-model", KIT_WORKER_EFFORT="high")
        self.assertEqual(proc.returncode, 0, proc.stderr)
        args = self.result()["ARGS"]
        self.assertIn("-m configured-model", args)
        self.assertIn('model_reasoning_effort="high"', args)


class KeyrotInstallTests(unittest.TestCase):
    def test_the_dry_run_reports_what_it_would_install(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            cache = Path(tmp) / "cache"
            cache.mkdir()
            env = dict(os.environ, KIT_CACHE_ROOT=str(cache), KIT_STATE_DIR=str(cache / "watchdog"),
                       HOME=str(Path(tmp)), KIT_CONFIG_SOURCED="1")
            proc = run("bash", str(SERVICE / "keyrot-install.sh"), "--dry-run", env=env)
            self.assertEqual(proc.returncode, 0, proc.stderr)
            self.assertIn("would install", proc.stdout)
            self.assertFalse((cache / "owner-bin" / "codex").exists())

    def test_it_installs_the_shim_and_keeps_the_previous_copy(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            cache = Path(tmp) / "cache"
            (cache / "owner-bin").mkdir(parents=True)
            previous = cache / "owner-bin" / "codex"
            previous.write_text("#!/usr/bin/env bash\nexit 0\n", encoding="utf-8")
            env = dict(os.environ, KIT_CACHE_ROOT=str(cache), KIT_STATE_DIR=str(cache / "watchdog"),
                       HOME=str(Path(tmp)), KIT_CONFIG_SOURCED="1")
            proc = run("bash", str(SERVICE / "keyrot-install.sh"), env=env)
            self.assertEqual(proc.returncode, 0, proc.stderr)
            installed = previous.read_text(encoding="utf-8")
            self.assertIn("codex-shim", installed)
            backups = list((cache / "owner-bin").glob("codex.before-*"))
            self.assertEqual(len(backups), 1, "the running copy must be versioned, not overwritten")


class SessionInterfaceTests(unittest.TestCase):
    """The two files the session layer and the service layer share.

    `local/bin/session/pause.sh` writes `<state>/daemon/stop` and
    `<state>/auto-merge.stop`; `resume.sh` and `status.sh` read
    `<state>/daemon/daemon.pid`.  Both halves are tested separately, so this is
    the only place that says the two halves agree on the names.
    """

    def test_the_merge_daemon_writes_its_pid_and_exits_on_the_stop_file(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            tmp = Path(directory)
            repo = tmp / "repo"
            repo.mkdir()
            run("git", "init", "-q", "-b", "main", str(repo))
            state = tmp / "state"
            (state / "daemon").mkdir(parents=True)
            (state / "daemon" / "stop").touch()
            env = dict(os.environ, KIT_REPO_ROOT=str(repo), KIT_STATE_DIR=str(state),
                       KIT_CACHE_ROOT=str(tmp / "cache"), KIT_GITHUB_SLUG="someone/demo",
                       KIT_CONFIG_SOURCED="1", HOME=str(tmp))
            proc = subprocess.run(["bash", str(SERVICE / "merge-daemon.sh")], env=env,
                                  capture_output=True, text=True, timeout=120)
            self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
            self.assertIn("stop file present", proc.stdout)
            pid = (state / "daemon" / "daemon.pid").read_text(encoding="utf-8").strip()
            self.assertTrue(pid.isdigit(), f"daemon.pid holds {pid!r}, not a process id")

    def test_the_between_turn_loop_stops_on_its_own_stop_file(self) -> None:
        import importlib.util
        from unittest import mock

        spec = importlib.util.spec_from_file_location("kit_auto_merge", SERVICE / "auto-merge.py")
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        with tempfile.TemporaryDirectory() as directory:
            tmp = Path(directory)
            state = tmp / "state"
            state.mkdir()
            loop = module.Loop(tmp, state, interval=1)
            (state / "auto-merge.stop").touch()
            with mock.patch.object(module.Loop, "one_pass") as one_pass:
                self.assertEqual(loop.run(hours=1.0, once=False), 0)
            self.assertEqual(one_pass.call_count, 1,
                             "the stop file must end the loop after the pass in flight")


class KeyrotStateFileTests(unittest.TestCase):
    """`keyrot-install.sh` renders two machine facts into the state directory.

    `models-allowed` is `session.workers.models_allowed` of `local/project.json`
    (the shim reads the rendered file, never the checkout), and `no-default-home`
    is the guard that stops a worker with no free rotation slot from falling back
    to a CODEX_HOME this project never named.  Nothing in `local/bin/session/`
    writes either file.
    """

    def project(self, tmp: Path, *, key_home: Path, models: list[str]) -> Path:
        repo = tmp / "repo"
        (repo / "scripts").mkdir(parents=True, exist_ok=True)
        (repo / "local").mkdir(parents=True, exist_ok=True)
        shutil.copy2(ROOT / "scripts" / "project_config.py", repo / "scripts")
        (repo / "local" / "project.json").write_text(json.dumps({
            "schema": 1,
            "session": {"main": {"key": "worker"},
                        "workers": {"models_allowed": models}},
            "keys": {"worker": {"codex_home": str(key_home), "limit": 1}},
        }), encoding="utf-8")
        return repo

    def install(self, tmp: Path, repo: Path, cache: Path) -> subprocess.CompletedProcess:
        env = dict(os.environ, KIT_CACHE_ROOT=str(cache), KIT_STATE_DIR=str(cache / "watchdog"),
                   KIT_REPO_ROOT=str(repo), HOME=str(tmp), KIT_CONFIG_SOURCED="1")
        return run("bash", str(SERVICE / "keyrot-install.sh"), env=env)

    def test_an_allowlist_is_rendered_and_an_empty_one_removes_the_file(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            tmp = Path(directory)
            key_home = tmp / "keyhome"
            key_home.mkdir()
            cache = tmp / "cache"
            state = cache / "watchdog"
            repo = self.project(tmp, key_home=key_home, models=["model-a", "model-b"])
            proc = self.install(tmp, repo, cache)
            self.assertEqual(proc.returncode, 0, proc.stderr)
            self.assertEqual((state / "models-allowed").read_text(encoding="utf-8").split(),
                             ["model-a", "model-b"])
            repo = self.project(tmp, key_home=key_home, models=[])
            proc = self.install(tmp, repo, cache)
            self.assertEqual(proc.returncode, 0, proc.stderr)
            self.assertFalse((state / "models-allowed").exists(),
                             "an empty allowlist must mean no restriction, not an empty file")

    def test_the_guard_follows_whether_the_default_home_is_a_configured_key(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            tmp = Path(directory)
            cache = tmp / "cache"
            state = cache / "watchdog"
            other = tmp / "keyhome"
            other.mkdir()
            proc = self.install(tmp, self.project(tmp, key_home=other, models=[]), cache)
            self.assertEqual(proc.returncode, 0, proc.stderr)
            self.assertTrue((state / "no-default-home").exists(),
                            "the default home is not one of the keys: the guard must be on")
            default = tmp / ".codex"
            default.mkdir()
            proc = self.install(tmp, self.project(tmp, key_home=default, models=[]), cache)
            self.assertEqual(proc.returncode, 0, proc.stderr)
            self.assertFalse((state / "no-default-home").exists(),
                             "the default home is a configured key: the guard must be off")

    def test_the_dry_run_says_what_it_would_do_with_both_files(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            tmp = Path(directory)
            cache = tmp / "cache"
            other = tmp / "keyhome"
            other.mkdir()
            repo = self.project(tmp, key_home=other, models=["model-a"])
            env = dict(os.environ, KIT_CACHE_ROOT=str(cache),
                       KIT_STATE_DIR=str(cache / "watchdog"), KIT_REPO_ROOT=str(repo),
                       HOME=str(tmp), KIT_CONFIG_SOURCED="1")
            proc = run("bash", str(SERVICE / "keyrot-install.sh"), "--dry-run", env=env)
            self.assertEqual(proc.returncode, 0, proc.stderr)
            self.assertIn("would write", proc.stdout)
            self.assertIn("models-allowed", proc.stdout)
            self.assertIn("no-default-home", proc.stdout)
            self.assertFalse((cache / "watchdog" / "no-default-home").exists())


class SlugResolutionTests(unittest.TestCase):
    """``kit_slug`` turns the checkout's GitHub remote into ``owner/repo``.

    POSIX ERE has no lazy quantifier, so the obvious one-line sed leaves the ``.git``
    suffix on and every later `gh api repos/<slug>/...` call 404s.
    """

    def slug_for(self, url: str) -> str:
        with tempfile.TemporaryDirectory() as tmp:
            tree = Path(tmp)
            (tree / "local/bin/service").mkdir(parents=True)
            shutil.copy2(SERVICE / "service-lib.sh", tree / "local/bin/service/service-lib.sh")
            run("git", "init", "-q", "-b", "main", str(tree))
            run("git", "-C", str(tree), "remote", "add", "github", url)
            env = dict(os.environ, KIT_REPO_ROOT=str(tree), KIT_CONFIG_SOURCED="1",
                       KIT_GITHUB_SLUG="", KIT_STATE_DIR=str(tree / "state"),
                       KIT_CACHE_ROOT=str(tree / "cache"), HOME=str(tree))
            proc = run("bash", "-c",
                       f'. "{tree}/local/bin/service/service-lib.sh"; kit_slug', env=env)
            return proc.stdout.strip()

    def test_an_ssh_remote_with_a_git_suffix(self) -> None:
        self.assertEqual(self.slug_for("git@github.com:acme/widget.git"), "acme/widget")

    def test_an_https_remote_without_a_suffix(self) -> None:
        self.assertEqual(self.slug_for("https://github.com/acme/widget"), "acme/widget")

    def test_a_configured_slug_wins_over_the_remote(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tree = Path(tmp)
            (tree / "local/bin/service").mkdir(parents=True)
            shutil.copy2(SERVICE / "service-lib.sh", tree / "local/bin/service/service-lib.sh")
            env = dict(os.environ, KIT_REPO_ROOT=str(tree), KIT_CONFIG_SOURCED="1",
                       KIT_GITHUB_SLUG="someone/else", KIT_STATE_DIR=str(tree / "state"),
                       KIT_CACHE_ROOT=str(tree / "cache"), HOME=str(tree))
            proc = run("bash", "-c",
                       f'. "{tree}/local/bin/service/service-lib.sh"; kit_slug', env=env)
            self.assertEqual(proc.stdout.strip(), "someone/else")

    def test_the_placeholder_slug_is_not_used(self) -> None:
        """The kit's placeholder slug is "no slug", not a repository.

        The constant, never the literal: `bootstrap_project.py` rewrites the
        literal across the tree, including this file.
        """
        with tempfile.TemporaryDirectory() as tmp:
            tree = Path(tmp)
            (tree / "local/bin/service").mkdir(parents=True)
            shutil.copy2(SERVICE / "service-lib.sh", tree / "local/bin/service/service-lib.sh")
            env = dict(os.environ, KIT_REPO_ROOT=str(tree), KIT_CONFIG_SOURCED="1",
                       KIT_GITHUB_SLUG=PLACEHOLDER_SLUG, KIT_STATE_DIR=str(tree / "state"),
                       KIT_CACHE_ROOT=str(tree / "cache"), HOME=str(tree))
            proc = run("bash", "-c",
                       f'. "{tree}/local/bin/service/service-lib.sh"; kit_slug', env=env)
            self.assertNotEqual(proc.returncode, 0)
            self.assertEqual(proc.stdout.strip(), "")


if __name__ == "__main__":
    unittest.main()
