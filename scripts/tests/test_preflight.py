#!/usr/bin/env python3
"""Regression tests for scripts/preflight.py.

Offline: every external tool is a small shell stub on a temporary PATH, HOME
points at a temporary directory, and the repository root is a fake tree, so
the checks see a machine the test controls.
"""

from __future__ import annotations

import io
import json
import os
import sys
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path
from unittest import mock

SCRIPT_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPT_DIR))

import preflight  # noqa: E402

TOOLCHAIN = "leanprover/lean4:v4.32.0"

STUBS = {
    "git": """#!/bin/sh
case "$1 $2" in
  "--version ") echo "git version 2.43.0" ;;
  "config --get") case "$3" in
      user.name) echo "Kit Tester" ;;
      user.email) echo "tester@example.invalid" ;;
    esac ;;
  "remote get-url") [ "$3" = "github" ] && echo "git@github.com:someone/demo.git" || exit 2 ;;
  "ls-remote --heads") echo "deadbeef refs/heads/main" ;;
  *) exit 0 ;;
esac
""",
    "tmux": '#!/bin/sh\necho "tmux 3.3a"\n',
    "elan": """#!/bin/sh
case "$1" in
  --version) echo "elan 3.1.1" ;;
  toolchain) echo "%(toolchain)s" ;;
esac
""" % {"toolchain": TOOLCHAIN},
    "lake": '#!/bin/sh\necho "Lake version 5.0"\n',
    "latexmk": '#!/bin/sh\necho "Latexmk 4.79"\n',
    "xelatex": '#!/bin/sh\necho "XeTeX 3.14"\n',
    "leanblueprint": '#!/bin/sh\necho "leanblueprint 0.0.13"\n',
    "texra-blueprint": '#!/bin/sh\necho "texra-blueprint 0.3.8"\n',
    "codex": '#!/bin/sh\necho "codex-cli 0.151.0"\n',
    "ssh": '#!/bin/sh\necho "Hi! You have successfully authenticated." >&2\nexit 1\n',
    "gh": """#!/bin/sh
case "$1 $2" in
  "--version ") echo "gh version 2.40.1" ;;
  "auth status") exit 0 ;;
  "api user") echo "kit-tester" ;;
  "api repos/someone/demo") echo "someone/demo" ;;
  *) exit 1 ;;
esac
""",
}


def write_stubs(bindir: Path, names: list[str]) -> None:
    bindir.mkdir(parents=True, exist_ok=True)
    for name in names:
        path = bindir / name
        path.write_text(STUBS[name], encoding="utf-8")
        path.chmod(0o755)


def fake_root(root: Path, cache: Path, slug: str = "someone/demo") -> Path:
    (root / ".github").mkdir(parents=True, exist_ok=True)
    (root / "local").mkdir(parents=True, exist_ok=True)
    (root / "lean-toolchain").write_text(TOOLCHAIN + "\n", encoding="utf-8")
    (root / "lake-manifest.json").write_text('{"packages": []}\n', encoding="utf-8")
    (root / ".github" / "allowed-tools.json").write_text(json.dumps({
        "blueprint-auto-fix": "Bash(pip install leanblueprint plastex "
                              "git+https://example.invalid/texra-blueprint@v0.3.8)",
    }) + "\n", encoding="utf-8")
    (root / "local" / "project.json").write_text(json.dumps({
        "schema": 1,
        "project": {"name": "Demo", "lean_root": "Demo", "github_slug": slug},
        "paths": {"cache_root": str(cache)},
        "session": {"main": {"key": "default"}},
    }) + "\n", encoding="utf-8")
    return root


def results(root: Path, **kwargs) -> dict[str, preflight.Check]:
    return {check.ident: check for check in preflight.run_checks(root, **kwargs)}


class PreflightTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.base = Path(self.tmp.name)
        self.addCleanup(self.tmp.cleanup)
        self.home = self.base / "home"
        self.bin = self.base / "bin"
        self.cache = self.base / "cache"
        self.cache.mkdir(parents=True)
        (self.home / ".local" / "bin").mkdir(parents=True)
        self.root = fake_root(self.base / "repo", self.cache)
        write_stubs(self.bin, list(STUBS))
        self.env = {"PATH": str(self.bin), "HOME": str(self.home),
                    "ELAN_HOME": str(self.home / ".elan")}

    def patched(self, extra: dict | None = None):
        return mock.patch.dict(os.environ, {**self.env, **(extra or {})}, clear=True)

    def test_a_complete_machine_passes_every_tool_check(self) -> None:
        with self.patched():
            found = results(self.root, probe=False)
        for ident in ("python", "git", "git-identity", "tmux", "elan", "toolchain",
                      "lake", "cache-root", "latex", "texra-blueprint", "codex",
                      "gh", "gh-auth", "gh-repo", "ssh-github", "proxy"):
            with self.subTest(check=ident):
                self.assertEqual(found[ident].status, preflight.PASS,
                                 f"{ident}: {found[ident].detail}")

    def test_the_report_names_every_check_once(self) -> None:
        with self.patched():
            found = results(self.root, probe=False)
        self.assertEqual(len(found), len(preflight.CHECKS))
        self.assertIn("mathlib-cache", found)
        self.assertIn("machine", found)
        self.assertIn("disk", found)

    def test_a_missing_tool_fails_and_says_how_to_install_it(self) -> None:
        (self.bin / "tmux").unlink()
        (self.bin / "codex").unlink()
        with self.patched():
            found = results(self.root, probe=False)
        self.assertEqual(found["tmux"].status, preflight.FAIL)
        self.assertIn("install tmux", found["tmux"].fix)
        self.assertEqual(found["codex"].status, preflight.FAIL)
        self.assertIn("install the codex CLI", found["codex"].fix)

    def test_a_tool_installed_outside_PATH_is_found_and_reported_as_unusable(self) -> None:
        """Installed but invisible to scripts is a different report from missing."""
        write_stubs(self.home / ".local" / "bin", ["gh"])
        (self.bin / "gh").unlink()
        with self.patched():
            found = results(self.root, probe=False)
        self.assertEqual(found["gh"].status, preflight.WARN)
        self.assertIn("not on PATH", found["gh"].detail)
        self.assertIn("export PATH=", found["gh"].fix)

    def test_lean_tools_are_also_looked_for_in_the_elan_bin_directory(self) -> None:
        elan_bin = self.home / ".elan" / "bin"
        write_stubs(elan_bin, ["elan", "lake"])
        (self.bin / "elan").unlink()
        (self.bin / "lake").unlink()
        with self.patched():
            found = results(self.root, probe=False)
        for ident in ("elan", "lake"):
            with self.subTest(check=ident):
                self.assertEqual(found[ident].status, preflight.WARN)
                self.assertIn("not on PATH", found[ident].detail)

    def test_api_authentication_and_git_transport_are_separate_checks(self) -> None:
        """A deploy key authenticates git, never the API — and the other way round."""
        (self.bin / "gh").write_text("""#!/bin/sh
case "$1 $2" in
  "--version ") echo "gh version 2.40.1" ;;
  *) echo "gh: not authenticated" >&2; exit 1 ;;
esac
""", encoding="utf-8")
        (self.bin / "gh").chmod(0o755)
        with self.patched():
            found = results(self.root, probe=False)
        self.assertEqual(found["gh"].status, preflight.PASS)
        self.assertEqual(found["gh-auth"].status, preflight.FAIL)
        self.assertIn("gh auth login", found["gh-auth"].fix)
        self.assertEqual(found["ssh-github"].status, preflight.PASS)

    def test_a_wrong_repository_is_reported_against_the_configured_slug(self) -> None:
        fake_root(self.root, self.cache, slug="someone/other-repo")
        with self.patched():
            found = results(self.root, probe=False)
        self.assertEqual(found["gh-repo"].status, preflight.FAIL)
        self.assertIn("someone/other-repo", found["gh-repo"].fix)

    def test_an_uninstantiated_checkout_only_warns_about_the_repository(self) -> None:
        fake_root(self.root, self.cache, slug="OWNER/REPO")
        with self.patched():
            found = results(self.root, probe=False)
        self.assertEqual(found["gh-repo"].status, preflight.WARN)
        self.assertIn("bootstrap_project.py", found["gh-repo"].fix)

    def test_proxy_variables_are_named_and_their_values_are_never_printed(self) -> None:
        secret = "http://user:hunter2@proxy.example.invalid:3128"
        with self.patched({"HTTPS_PROXY": secret}):
            found = results(self.root, probe=False)
        check = found["proxy"]
        self.assertEqual(check.status, preflight.WARN)
        self.assertIn("HTTPS_PROXY", check.detail)
        self.assertNotIn("hunter2", check.detail + check.fix)

    def test_the_pinned_blueprint_tool_version_is_read_from_the_repository(self) -> None:
        with self.patched():
            found = results(self.root, probe=False)
        self.assertIn("0.3.8", found["texra-blueprint"].detail)
        (self.bin / "texra-blueprint").write_text(
            '#!/bin/sh\necho "texra-blueprint 0.1.0"\n', encoding="utf-8")
        (self.bin / "texra-blueprint").chmod(0o755)
        with self.patched():
            found = results(self.root, probe=False)
        self.assertEqual(found["texra-blueprint"].status, preflight.WARN)
        self.assertIn("pip install", found["texra-blueprint"].fix)

    def test_the_toolchain_check_uses_the_pin_in_the_repository(self) -> None:
        (self.root / "lean-toolchain").write_text("leanprover/lean4:v9.99.9\n",
                                                  encoding="utf-8")
        with self.patched():
            found = results(self.root, probe=False)
        self.assertEqual(found["toolchain"].status, preflight.WARN)
        self.assertIn("elan toolchain install leanprover/lean4:v9.99.9",
                      found["toolchain"].fix)

    def test_an_unwritable_state_directory_fails(self) -> None:
        fake_root(self.root, Path("/proc/kit-state-does-not-exist"))
        with self.patched():
            found = results(self.root, probe=False)
        self.assertEqual(found["cache-root"].status, preflight.FAIL)
        self.assertIn("mkdir -p", found["cache-root"].fix)


class ProbeTests(unittest.TestCase):
    """The functional key probe is delegated, and only run when it is there."""

    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.base = Path(self.tmp.name)
        self.addCleanup(self.tmp.cleanup)
        self.cache = self.base / "cache"
        self.cache.mkdir()
        self.root = fake_root(self.base / "repo", self.cache)
        self.env = {"PATH": str(self.base / "bin"), "HOME": str(self.base / "home")}

    def write_probe(self, body: str) -> None:
        path = self.root / "local" / "bin" / "session" / "probe-key.sh"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(body, encoding="utf-8")
        path.chmod(0o755)

    def test_without_a_probe_script_the_check_only_warns(self) -> None:
        with mock.patch.dict(os.environ, self.env, clear=True):
            found = results(self.root)
        self.assertEqual(found["codex-probe"].status, preflight.WARN)
        self.assertIn("probe-key.sh", found["codex-probe"].detail)

    def test_a_probe_that_answers_passes(self) -> None:
        self.write_probe('#!/bin/sh\necho "key $1 answered"\nexit 0\n')
        with mock.patch.dict(os.environ, self.env, clear=True):
            found = results(self.root)
        self.assertEqual(found["codex-probe"].status, preflight.PASS)
        self.assertIn("default", found["codex-probe"].detail)

    def test_a_probe_that_fails_is_a_FAIL_naming_the_command_to_repeat(self) -> None:
        self.write_probe('#!/bin/sh\necho "quota exhausted" >&2\nexit 3\n')
        with mock.patch.dict(os.environ, self.env, clear=True):
            found = results(self.root)
        self.assertEqual(found["codex-probe"].status, preflight.FAIL)
        self.assertIn("quota exhausted", found["codex-probe"].detail)
        self.assertIn("probe-key.sh default", found["codex-probe"].fix)

    def test_no_probe_skips_the_call(self) -> None:
        self.write_probe('#!/bin/sh\nexit 3\n')
        with mock.patch.dict(os.environ, self.env, clear=True):
            found = results(self.root, probe=False)
        self.assertEqual(found["codex-probe"].status, preflight.WARN)
        self.assertIn("--no-probe", found["codex-probe"].detail)


class ReportTests(unittest.TestCase):
    """Exit code and rendering, independent of any machine."""

    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.addCleanup(self.tmp.cleanup)

    def run_with(self, checks, *argv: str) -> tuple[int, str]:
        out = io.StringIO()
        with mock.patch.object(preflight, "CHECKS", checks), redirect_stdout(out):
            rc = preflight.main(["--root", str(self.root), *argv])
        return rc, out.getvalue()

    def test_warnings_alone_still_exit_zero(self) -> None:
        checks = (lambda env: preflight.Check("a", "A", preflight.PASS, "fine"),
                  lambda env: preflight.Check("b", "B", preflight.WARN, "later", "do b"))
        rc, text = self.run_with(checks)
        self.assertEqual(rc, 0)
        self.assertIn("fix: do b", text)
        self.assertIn("1 pass, 1 warn, 0 fail", text)

    def test_one_failure_exits_one_and_says_what_to_do(self) -> None:
        checks = (lambda env: preflight.Check("a", "A", preflight.FAIL, "broken",
                                              "install a"),)
        rc, text = self.run_with(checks)
        self.assertEqual(rc, 1)
        self.assertIn("fix: install a", text)
        self.assertIn("Not ready", text)

    def test_json_output_is_machine_readable(self) -> None:
        checks = (lambda env: preflight.Check("a", "A", preflight.FAIL, "broken", "fix a"),)
        rc, text = self.run_with(checks, "--json")
        payload = json.loads(text)
        self.assertEqual(rc, 1)
        self.assertFalse(payload["ok"])
        self.assertEqual(payload["summary"]["fail"], 1)
        self.assertEqual(payload["checks"][0]["fix"], "fix a")

    def test_a_check_that_raises_does_not_hide_the_others(self) -> None:
        def broken(env):
            raise RuntimeError("boom")

        checks = (broken, lambda env: preflight.Check("b", "B", preflight.PASS))
        rc, text = self.run_with(checks)
        self.assertEqual(rc, 0)
        self.assertIn("boom", text)


if __name__ == "__main__":
    unittest.main()
