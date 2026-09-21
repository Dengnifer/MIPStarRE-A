#!/usr/bin/env python3
"""Unit tests for ``scripts/project_config.py`` and ``local/bin/session/config.sh``.

Every case builds its own repository root in a temporary directory, so nothing
here depends on the configuration this checkout happens to carry.  The shell
tests run ``config.sh`` in a stub tree (real ``project_config.py``, no other tool)
and check that sourcing it exports what the inherited tools read.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "scripts"))

import project_config as pc  # noqa: E402

CONFIG_SH = REPO_ROOT / "local/bin/session/config.sh"
LOADER = REPO_ROOT / "scripts/project_config.py"

SAMPLE = {
    "schema": 1,
    "project": {
        "name": "Widget",
        "lean_root": "Widget",
        "track": "core",
        "title": "A widget",
        "arxiv": ["https://arxiv.org/abs/1234.56789"],
        "github_slug": "someone/widget",
        "comparator_slug": "someone/widget-comparator",
    },
    "paths": {
        "cache_root": "~/.cache/widget-dev",
        "full_build_lock": "~/.cache/lean-full-build.lock",
    },
    "issues": {"progress": 12, "owner_inbox": 13, "tracker_root": 47},
    "session": {
        "tmux": "widget",
        "turn_max_minutes": 30,
        "main": {"model": "m", "effort": "high", "key": "default", "native_delegates": 2},
        "workers": {"model": "w", "hard_model": "h", "effort": "low", "lanes": 3,
                    "models_allowed": ["w", "h"]},
    },
    "keys": {"default": {"codex_home": "~/.codex", "limit": 2}},
    "paper_mirrors": ["widget"],
    "tracks": {
        "core": {
            "name": "core",
            "lean_root": "Widget/Core",
            "headline": [["Widget.Core.main", "thm:main"]],
            "gap_register": "docs/paper-gaps/core-gap-register.md",
            "axiom_audit": "Widget/Core/Test/AxiomAudit.lean",
            "blueprint_chapters": ["blueprint/src/chapter/ch01_core.tex"],
            "leanok_exemptions": "docs/completion/core-leanok-exemptions.md",
            "comparator_doc": "docs/comparator.md",
            "expected_challenge": "scripts/comparator/expected/ChallengeCore.lean.expected",
            "truthful_docs": ["README.md"],
            "artifact_files": ["README.md", "LICENSE"],
            "artifact_script": "scripts/make_artifact.sh",
        }
    },
}


def write_config(root: Path, config: dict | str) -> Path:
    path = root / pc.CONFIG_RELPATH
    path.parent.mkdir(parents=True, exist_ok=True)
    text = config if isinstance(config, str) else json.dumps(config, indent=2)
    path.write_text(text, encoding="utf-8")
    return path


class TemporaryRootTestCase(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)


class LoadTests(TemporaryRootTestCase):
    def test_a_tree_without_a_config_file_gets_the_placeholder_defaults(self) -> None:
        config = pc.load(self.root)
        # The placeholder CONSTANTS, never the literals: bootstrap_project.py
        # rewrites the literals across the tree, including this file.
        self.assertEqual(pc.get(config, "project.lean_root"), pc.PLACEHOLDER_LEAN_ROOT)
        self.assertEqual(pc.get(config, "project.github_slug"), pc.PLACEHOLDER_SLUG)
        self.assertEqual(pc.track_names(config), [])
        self.assertEqual(config["_root"], str(self.root))

    def test_a_missing_config_is_an_error_only_when_the_caller_requires_one(self) -> None:
        with self.assertRaises(pc.ConfigError) as caught:
            pc.load(self.root, required=True)
        self.assertIn("local/project.json", str(caught.exception))

    def test_values_from_the_file_win_and_unmentioned_keys_keep_their_default(self) -> None:
        write_config(self.root, {"schema": 1, "project": {"name": "Widget"}})
        config = pc.load(self.root)
        self.assertEqual(pc.get(config, "project.name"), "Widget")
        self.assertEqual(pc.get(config, "project.lean_root"), pc.PLACEHOLDER_LEAN_ROOT)
        self.assertEqual(pc.get(config, "session.tmux"), "paperlib")

    def test_paths_are_expanded_but_other_strings_are_left_alone(self) -> None:
        write_config(self.root, SAMPLE)
        config = pc.load(self.root)
        home = os.path.expanduser("~")
        self.assertEqual(pc.get(config, "paths.cache_root"), f"{home}/.cache/widget-dev")
        self.assertEqual(pc.get(config, "keys.default.codex_home"), f"{home}/.codex")
        self.assertEqual(pc.get(config, "project.github_slug"), "someone/widget")

    def test_get_returns_the_default_for_absent_and_for_null(self) -> None:
        config = pc.load(self.root)
        self.assertIsNone(pc.get(config, "issues.progress"))
        self.assertEqual(pc.get(config, "issues.progress", 0), 0)
        self.assertEqual(pc.get(config, "no.such.key", "fallback"), "fallback")
        self.assertEqual(pc.get(config, "session.main.native_delegates"), 1)

    def test_the_state_directory_hangs_under_the_cache_root(self) -> None:
        write_config(self.root, SAMPLE)
        config = pc.load(self.root)
        self.assertEqual(
            pc.state_dir(config), os.path.expanduser("~/.cache/widget-dev/watchdog")
        )

    def test_paper_mirror_names_become_reference_directories(self) -> None:
        write_config(self.root, SAMPLE)
        self.assertEqual(
            pc.paper_mirror_dirs(pc.load(self.root)), ["references/widget-paper"]
        )

    def test_the_placeholder_slug_is_recognised_as_not_filled_in(self) -> None:
        self.assertFalse(pc.has_github_slug(pc.load(self.root)))
        write_config(self.root, SAMPLE)
        self.assertTrue(pc.has_github_slug(pc.load(self.root)))

    def test_loading_creates_nothing_on_disk(self) -> None:
        pc.load(self.root)
        self.assertEqual(list(self.root.iterdir()), [])


class WorkerModelTests(TemporaryRootTestCase):
    """The models a worker may run, and the allowlist the rotation shim enforces."""

    def test_no_model_is_configured_by_default(self) -> None:
        models = pc.models(pc.load(self.root))
        self.assertEqual(models, {"main": "", "default": "", "hard": ""})
        self.assertEqual(pc.models_allowed(pc.load(self.root)), [])

    def test_an_empty_hard_model_falls_back_to_the_routine_one(self) -> None:
        write_config(self.root, {"schema": 1, "session": {"workers": {"model": "w"}}})
        self.assertEqual(pc.models(pc.load(self.root))["hard"], "w")

    def test_the_three_names_come_from_the_session_section(self) -> None:
        write_config(self.root, SAMPLE)
        self.assertEqual(pc.models(pc.load(self.root)),
                         {"main": "m", "default": "w", "hard": "h"})

    def test_the_allowlist_drops_empty_entries(self) -> None:
        write_config(self.root, {"schema": 1, "session": {"workers": {
            "models_allowed": ["a", "", "b"]}}})
        self.assertEqual(pc.models_allowed(pc.load(self.root)), ["a", "b"])

    def test_the_allowlist_must_be_a_list_of_strings(self) -> None:
        write_config(self.root, {"schema": 1, "session": {"workers": {
            "models_allowed": "a"}}})
        with self.assertRaises(pc.ConfigError) as error:
            pc.load(self.root)
        self.assertIn("session.workers.models_allowed", str(error.exception))


class LeanScanTargetTests(TemporaryRootTestCase):
    """Which subtrees carry this project's Lean code."""

    def test_a_fresh_kit_scans_the_library_root(self) -> None:
        self.assertEqual(pc.lean_scan_targets(self.root), [pc.PLACEHOLDER_LEAN_ROOT])

    def test_a_track_subdirectory_wins_when_it_is_there(self) -> None:
        (self.root / pc.PLACEHOLDER_LEAN_ROOT / "main").mkdir(parents=True)
        self.assertEqual(pc.lean_scan_targets(self.root),
                         [f"{pc.PLACEHOLDER_LEAN_ROOT}/main"])

    def test_registered_tracks_name_their_own_roots(self) -> None:
        write_config(self.root, SAMPLE)
        self.assertEqual(pc.lean_scan_targets(self.root), ["Widget/Core"])


class TrackTests(TemporaryRootTestCase):
    def test_an_unknown_track_is_none_rather_than_an_exception(self) -> None:
        write_config(self.root, SAMPLE)
        config = pc.load(self.root)
        self.assertIsNone(pc.track(config, "nope"))

    def test_the_default_track_is_the_one_named_by_the_project(self) -> None:
        write_config(self.root, SAMPLE)
        entry = pc.track(pc.load(self.root))
        self.assertIsNotNone(entry)
        self.assertEqual(entry["lean_root"], "Widget/Core")
        self.assertEqual(entry["headline"], [["Widget.Core.main", "thm:main"]])

    def test_a_half_filled_track_gets_every_field_with_an_empty_value(self) -> None:
        write_config(
            self.root,
            {"schema": 1, "project": {"track": "core"}, "tracks": {"core": {"lean_root": "L"}}},
        )
        entry = pc.track(pc.load(self.root))
        self.assertEqual(entry["name"], "core")
        self.assertEqual(entry["headline"], [])
        self.assertEqual(entry["gap_register"], "")
        self.assertEqual(sorted(entry), sorted(pc.TRACK_FIELDS))

    def test_the_track_fields_are_exactly_the_gate_dataclass_fields(self) -> None:
        import dataclasses

        import completion_gate as gate

        self.assertEqual(
            sorted(f.name for f in dataclasses.fields(gate.Track)), sorted(pc.TRACK_FIELDS)
        )


class ValidationTests(TemporaryRootTestCase):
    def assert_refused(self, config: dict | str, needle: str) -> None:
        write_config(self.root, config)
        with self.assertRaises(pc.ConfigError) as caught:
            pc.load(self.root)
        self.assertIn(needle, str(caught.exception))

    def test_broken_json_names_the_file(self) -> None:
        self.assert_refused("{not json", "not valid JSON")

    def test_an_unknown_schema_version_is_refused(self) -> None:
        self.assert_refused({"schema": 99}, "this kit understands 1")

    def test_a_wrong_type_names_the_key_and_both_types(self) -> None:
        self.assert_refused({"schema": 1, "session": {"turn_max_minutes": "soon"}},
                            "session.turn_max_minutes must be a whole number, got a string")

    def test_an_empty_lean_root_is_refused(self) -> None:
        self.assert_refused({"schema": 1, "project": {"lean_root": ""}},
                            "project.lean_root must not be empty")

    def test_a_file_that_lists_keys_replaces_the_placeholder_key(self) -> None:
        """`keys` is a registry, not a set of defaults to extend.

        Inheriting the placeholder `default` key would leave a phantom entry
        pointing at `~/.codex`, which the rotation shim's fallback guard would
        then treat as one of this project's keys.
        """
        write_config(self.root, {"schema": 1, "keys": {"worker": {"codex_home": "/tmp/k"}},
                                 "session": {"main": {"key": "worker"}}})
        config = pc.load(self.root)
        self.assertEqual(sorted(config["keys"]), ["worker"])

    def test_the_main_key_must_name_a_configured_key(self) -> None:
        self.assert_refused({"schema": 1, "session": {"main": {"key": "second"}}},
                            "which is not in keys")

    def test_an_unknown_track_field_lists_the_allowed_ones(self) -> None:
        self.assert_refused({"schema": 1, "tracks": {"core": {"lean_roots": "L"}}},
                            "unknown field(s) lean_roots")

    def test_a_headline_entry_must_be_a_pair(self) -> None:
        self.assert_refused({"schema": 1, "tracks": {"core": {"headline": ["thm"]}}},
                            'must be ["Full.Theorem.Name", "blueprint:label"]')

    def test_an_issue_number_must_be_a_number_or_null(self) -> None:
        self.assert_refused({"schema": 1, "issues": {"progress": "27"}},
                            "must be an issue number or null")

    def test_the_tracker_root_is_an_issue_number_too(self) -> None:
        self.assert_refused({"schema": 1, "issues": {"tracker_root": "~/somewhere"}},
                            "issues.tracker_root must be an issue number or null")


class ShippedConfigTests(unittest.TestCase):
    """The file this repository actually ships must load and stay generic."""

    def test_the_repository_config_loads(self) -> None:
        config = pc.load(REPO_ROOT)
        self.assertEqual(config["schema"], pc.SCHEMA)
        self.assertTrue(pc.get(config, "project.lean_root"))

    def test_every_documented_export_is_produced_exactly_once(self) -> None:
        names = [name for name, _ in pc.exports(pc.load(REPO_ROOT))]
        self.assertEqual(len(names), len(set(names)))
        self.assertEqual(
            names,
            [
                "KIT_REPO_ROOT", "KIT_NAME", "KIT_LEAN_ROOT", "KIT_TRACK",
                "KIT_GITHUB_SLUG", "KIT_COMPARATOR_SLUG", "KIT_CACHE_ROOT",
                "KIT_STATE_DIR", "KIT_TMUX", "KIT_TURN_MAX", "KIT_PROGRESS_ISSUE",
                "KIT_OWNER_INBOX_ISSUE", "KIT_TRACKER_ROOT", "KIT_MAIN_MODEL",
                "KIT_MAIN_EFFORT", "KIT_MAIN_KEY", "KIT_MAIN_DELEGATES",
                "KIT_WORKER_MODEL", "KIT_WORKER_EFFORT", "KIT_LANES",
            ],
        )


class CommandLineTests(TemporaryRootTestCase):
    def run_cli(self, *args: str, root: Path | None = None):
        return subprocess.run(
            [sys.executable, str(LOADER), "--root", str(root or self.root), *args],
            capture_output=True,
            text=True,
        )

    def test_get_prints_one_value(self) -> None:
        write_config(self.root, SAMPLE)
        result = self.run_cli("get", "session.tmux")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.strip(), "widget")

    def test_get_prints_the_fallback_for_a_null_value(self) -> None:
        write_config(self.root, SAMPLE)
        self.assertEqual(self.run_cli("get", "project.title").stdout.strip(), "A widget")
        self.assertEqual(
            self.run_cli("get", "no.such.key", "--default", "none").stdout.strip(), "none"
        )

    def test_get_prints_json_for_a_container(self) -> None:
        write_config(self.root, SAMPLE)
        self.assertEqual(
            json.loads(self.run_cli("get", "paper_mirrors").stdout), ["widget"]
        )

    def test_shell_quotes_values_that_would_otherwise_split(self) -> None:
        awkward = json.loads(json.dumps(SAMPLE))
        awkward["project"]["title"] = "one two; rm -rf /"
        awkward["session"]["tmux"] = "a b"
        write_config(self.root, awkward)
        result = self.run_cli("shell")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("export KIT_TMUX='a b'\n", result.stdout)
        for line in result.stdout.splitlines():
            self.assertRegex(line, r"^export KIT_[A-Z_]+=")

    def test_validate_reports_a_fresh_kit_as_having_no_track(self) -> None:
        write_config(self.root, {"schema": 1})
        result = self.run_cli("validate")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("none registered", result.stdout)

    def test_validate_fails_loudly_when_the_file_is_absent(self) -> None:
        result = self.run_cli("validate")
        self.assertEqual(result.returncode, 2)
        self.assertIn("no local/project.json", result.stderr)

    def test_a_broken_file_fails_with_a_message_and_no_traceback(self) -> None:
        write_config(self.root, "{")
        result = self.run_cli("get", "project.name")
        self.assertEqual(result.returncode, 2)
        self.assertIn("not valid JSON", result.stderr)
        self.assertNotIn("Traceback", result.stderr)


class ConfigShellTests(TemporaryRootTestCase):
    """`config.sh` in a stub tree: only the loader and the shell script exist."""

    def setUp(self) -> None:
        super().setUp()
        (self.root / "scripts").mkdir(parents=True)
        shutil.copyfile(LOADER, self.root / "scripts/project_config.py")
        (self.root / "local/bin/session").mkdir(parents=True)
        self.script = self.root / "local/bin/session/config.sh"
        shutil.copyfile(CONFIG_SH, self.script)
        self.script.chmod(0o755)

    def source(self, *, script: Path | None = None, cwd: Path | None = None, env=None):
        command = f'. "{script or self.script}" && env | sort'
        return subprocess.run(
            ["bash", "-c", command],
            capture_output=True,
            text=True,
            cwd=str(cwd or self.root),
            env=env or {k: v for k, v in os.environ.items() if k != "MIPSTARRE_CACHE_ROOT"},
        )

    def environment(self, **kwargs) -> dict:
        result = self.source(**kwargs)
        self.assertEqual(result.returncode, 0, result.stderr)
        out = {}
        for line in result.stdout.splitlines():
            name, _, value = line.partition("=")
            out[name] = value
        return out

    def test_it_exports_the_kit_variables_from_the_configuration(self) -> None:
        write_config(self.root, SAMPLE)
        env = self.environment()
        self.assertEqual(env["KIT_REPO_ROOT"], str(self.root))
        self.assertEqual(env["KIT_NAME"], "Widget")
        self.assertEqual(env["KIT_LEAN_ROOT"], "Widget")
        self.assertEqual(env["KIT_TRACK"], "core")
        self.assertEqual(env["KIT_TMUX"], "widget")
        self.assertEqual(env["KIT_TURN_MAX"], "30")
        self.assertEqual(env["KIT_LANES"], "3")
        self.assertEqual(env["KIT_PROGRESS_ISSUE"], "12")
        self.assertEqual(env["KIT_TRACKER_ROOT"], "47")

    def test_it_exports_the_three_inherited_variables(self) -> None:
        write_config(self.root, SAMPLE)
        env = self.environment()
        home = os.path.expanduser("~")
        self.assertEqual(env["MIPSTARRE_CACHE_ROOT"], f"{home}/.cache/widget-dev")
        self.assertEqual(env["KIT_STATE_DIR"], f"{home}/.cache/widget-dev/watchdog")
        self.assertEqual(env["MIPSTARRE_FULL_BUILD_LOCK"], f"{home}/.cache/lean-full-build.lock")
        self.assertEqual(env["MIPSTARRE_GITHUB_REPO"], "someone/widget")

    def test_the_placeholder_slug_leaves_the_github_variable_unset(self) -> None:
        write_config(self.root, {"schema": 1})
        env = self.environment()
        self.assertNotIn("MIPSTARRE_GITHUB_REPO", env)
        self.assertEqual(env["KIT_GITHUB_SLUG"], pc.PLACEHOLDER_SLUG)

    def test_the_configuration_overrides_a_cache_root_left_by_another_project(self) -> None:
        write_config(self.root, SAMPLE)
        stale = dict(os.environ, MIPSTARRE_CACHE_ROOT="/tmp/some-other-project")
        env = self.environment(env=stale)
        self.assertEqual(
            env["MIPSTARRE_CACHE_ROOT"], os.path.expanduser("~/.cache/widget-dev")
        )

    def test_the_root_comes_from_the_script_not_from_the_working_directory(self) -> None:
        write_config(self.root, SAMPLE)
        elsewhere = Path(self.temporary.name).parent
        env = self.environment(cwd=elsewhere)
        self.assertEqual(env["KIT_REPO_ROOT"], str(self.root))

    def test_it_follows_a_symlink_back_to_the_repository(self) -> None:
        write_config(self.root, SAMPLE)
        link = Path(self.temporary.name) / "config-link.sh"
        link.symlink_to(self.script)
        env = self.environment(script=link)
        self.assertEqual(env["KIT_REPO_ROOT"], str(self.root))
        self.assertEqual(env["KIT_NAME"], "Widget")

    def test_it_creates_nothing_on_disk(self) -> None:
        write_config(self.root, SAMPLE)
        before = sorted(str(p) for p in self.root.rglob("*"))
        self.environment()
        after = sorted(str(p) for p in self.root.rglob("*") if "__pycache__" not in str(p))
        self.assertEqual([p for p in before if "__pycache__" not in p], after)
        self.assertFalse(Path(os.path.expanduser("~/.cache/widget-dev")).exists())

    def test_an_already_prepared_environment_is_left_alone(self) -> None:
        """`KIT_CONFIG_SOURCED=1` means "do not read local/project.json".

        Without it no tool could be driven against a temporary tree: sourcing
        config.sh would put the real cache root back.  The flag is never set or
        exported by config.sh itself, so a child process of another project
        cannot inherit it.
        """
        write_config(self.root, SAMPLE)
        prepared = dict(os.environ, KIT_CONFIG_SOURCED="1",
                        KIT_CACHE_ROOT="/tmp/prepared-cache",
                        KIT_NAME="Prepared", MIPSTARRE_CACHE_ROOT="/tmp/prepared-cache")
        env = self.environment(env=prepared)
        self.assertEqual(env["KIT_CACHE_ROOT"], "/tmp/prepared-cache")
        self.assertEqual(env["KIT_NAME"], "Prepared")
        self.assertEqual(env["MIPSTARRE_CACHE_ROOT"], "/tmp/prepared-cache")

    def test_the_flag_is_not_exported_so_it_cannot_leak_into_a_child(self) -> None:
        write_config(self.root, SAMPLE)
        env = self.environment()
        self.assertNotIn("KIT_CONFIG_SOURCED", env)

    def test_the_per_run_knobs_of_the_session_tools_survive_sourcing(self) -> None:
        """config.sh owns the spec's KIT_* names and touches nothing else."""
        write_config(self.root, SAMPLE)
        knobs = {
            "KIT_DRY_RUN": "1", "KIT_SAY": "/tmp/say.sh", "KIT_MAIN_PID_CMD": "echo 7",
            "KIT_KEY_HOME_TESTKEY": "/tmp/keyhome", "KIT_KEY_LIMIT_TESTKEY": "3",
            "KIT_PROJECT_JSON": "/tmp/other.json", "KIT_EXEC_PREFIX": "nice",
            "KIT_KEYWATCH_INTERVAL": "60", "KIT_SAY_GRACE": "30", "KIT_TIMER_POLL": "5",
            "KIT_STANDDOWN_MINUTES": "45", "KIT_RECORDS_CMD": "/tmp/records.sh",
            "KIT_TMUX_WIDTH": "200", "KIT_TMUX_HEIGHT": "50",
        }
        env = self.environment(env=dict(os.environ, **knobs))
        for name, value in knobs.items():
            self.assertEqual(env.get(name), value, f"config.sh clobbered {name}")
        # and it still overwrote the names it does own
        self.assertEqual(env["KIT_NAME"], "Widget")

    def test_a_broken_configuration_fails_the_sourcing_script(self) -> None:
        write_config(self.root, "{")
        result = self.source()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("could not read local/project.json", result.stderr)


if __name__ == "__main__":
    unittest.main()
