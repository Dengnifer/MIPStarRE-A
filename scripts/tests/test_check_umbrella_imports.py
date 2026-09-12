#!/usr/bin/env python3
"""Regression tests for scripts/check_umbrella_imports.py."""

from __future__ import annotations

import contextlib
import io
import os
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPT_DIR))

from check_umbrella_imports import (  # noqa: E402
    EXIT_FINDINGS,
    EXIT_OK,
    EXIT_USAGE,
    analyse,
    main,
    parse_imports,
    read_lean,
    reexport_file_for,
    strip_comments,
)

# chmod-based unreadability is meaningless for root.
_IS_ROOT = hasattr(os, "geteuid") and os.geteuid() == 0


# ── fixtures ────────────────────────────────────────────────────────────────


def _write(root: Path, rel: str, *imports: str, body: str = "") -> Path:
    """Write a Lean file with the given imports and an optional body."""

    path = root / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    text = "".join(f"import {name}\n" for name in imports)
    if body:
        text += body if body.endswith("\n") else body + "\n"
    path.write_text(text, encoding="utf-8")
    return path


def _reachable_tree(root: Path) -> None:
    """A tree in which every module is reachable from the re-export roots."""

    _write(root, "MIPStarRE.lean", "MIPStarRE.QPBT")
    _write(
        root,
        "MIPStarRE/QPBT.lean",
        "MIPStarRE.QPBT.Algebra.Lines",
        "MIPStarRE.QPBT.Combining.Points",
    )
    _write(root, "MIPStarRE/QPBT/Algebra/Lines.lean")
    _write(
        root,
        "MIPStarRE/QPBT/Combining/Points.lean",
        "MIPStarRE.QPBT.Combining.Points.Absorption",
        "MIPStarRE.QPBT.Combining.Points.MarginalContraction",
    )
    _write(root, "MIPStarRE/QPBT/Combining/Points/Absorption.lean")
    _write(root, "MIPStarRE/QPBT/Combining/Points/MarginalContraction.lean")


def _orphan_tree(root: Path) -> None:
    """The 2026-09-12 shape: Points.lean does not import its split-out children."""

    _reachable_tree(root)
    _write(root, "MIPStarRE/QPBT/Combining/Points.lean")  # imports dropped


def _run(argv: list[str]) -> tuple[int, str]:
    """Run ``main(argv)`` capturing stdout."""

    buffer = io.StringIO()
    with contextlib.redirect_stdout(buffer):
        status = main(argv)
    return status, buffer.getvalue()


# ── strip_comments / parse_imports ──────────────────────────────────────────


class ImportHeaderTests(unittest.TestCase):
    def test_line_comment_is_stripped(self) -> None:
        visible, depth = strip_comments("import Foo.Bar -- why", 0)
        self.assertEqual(visible.strip(), "import Foo.Bar")
        self.assertEqual(depth, 0)

    def test_block_comment_spans_lines(self) -> None:
        visible, depth = strip_comments("/- copyright", 0)
        self.assertEqual(visible, "")
        self.assertEqual(depth, 1)
        visible, depth = strip_comments("still inside -/ import Foo", depth)
        self.assertEqual(visible.strip(), "import Foo")
        self.assertEqual(depth, 0)

    def test_nested_block_comment(self) -> None:
        _, depth = strip_comments("/- outer /- inner -/", 0)
        self.assertEqual(depth, 1)
        _, depth = strip_comments("-/", depth)
        self.assertEqual(depth, 0)

    def test_imports_after_copyright_block(self) -> None:
        text = "/- Copyright\n   two lines -/\nimport A.B\nimport C.D  -- note\n"
        self.assertEqual(parse_imports(text), ("A.B", "C.D"))

    def test_scan_stops_at_first_command(self) -> None:
        text = "import A.B\n\nnamespace Foo\n\nimport C.D\n"
        self.assertEqual(parse_imports(text), ("A.B",))

    def test_import_word_in_a_docstring_is_not_an_import(self) -> None:
        text = "import A.B\n\n/-!\nimport C.D is what this module needs\n-/\n"
        self.assertEqual(parse_imports(text), ("A.B",))

    def test_prelude_does_not_end_the_header(self) -> None:
        text = "prelude\nimport A.B\n"
        self.assertEqual(parse_imports(text), ("A.B",))

    def test_empty_file_has_no_imports(self) -> None:
        self.assertEqual(parse_imports(""), ())


# ── reachability ────────────────────────────────────────────────────────────


class ReachableTreeTests(unittest.TestCase):
    def test_fully_reachable_tree_exits_zero(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _reachable_tree(root)
            status, out = _run(["--root", str(root)])
            self.assertEqual(status, EXIT_OK)
            self.assertIn("are reachable from the re-export roots", out)

    def test_roots_are_the_top_level_reexport_files(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _reachable_tree(root)
            report = analyse(root)
            self.assertEqual(report.roots, ["MIPStarRE", "MIPStarRE.QPBT"])
            self.assertEqual(report.unreachable, [])


class OrphanTreeTests(unittest.TestCase):
    def test_orphan_is_reported_with_import_line_and_reexport_file(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _orphan_tree(root)
            status, out = _run(["--root", str(root)])
            self.assertEqual(status, EXIT_FINDINGS)
            self.assertIn("MIPStarRE/QPBT/Combining/Points/Absorption.lean", out)
            self.assertIn("import MIPStarRE.QPBT.Combining.Points.Absorption", out)
            self.assertIn("import MIPStarRE.QPBT.Combining.Points.MarginalContraction", out)
            self.assertIn("add to        MIPStarRE/QPBT/Combining/Points.lean", out)

    def test_warn_only_exits_zero_but_still_reports(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _orphan_tree(root)
            status, out = _run(["--root", str(root), "--warn-only"])
            self.assertEqual(status, EXIT_OK)
            self.assertIn("import MIPStarRE.QPBT.Combining.Points.Absorption", out)
            self.assertIn("--warn-only", out)

    def test_ci_emits_one_annotation_per_module_to_fix(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _orphan_tree(root)
            status, out = _run(["--root", str(root), "--ci"])
            self.assertEqual(status, EXIT_FINDINGS)
            annotations = [line for line in out.splitlines() if line.startswith("::error")]
            self.assertEqual(len(annotations), 2)

    def test_the_check_never_edits_a_reexport_file(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _orphan_tree(root)
            target = root / "MIPStarRE" / "QPBT" / "Combining" / "Points.lean"
            before = target.read_bytes()
            _run(["--root", str(root)])
            self.assertEqual(target.read_bytes(), before)

    def test_fixing_the_reexport_file_clears_the_finding(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _orphan_tree(root)
            _write(
                root,
                "MIPStarRE/QPBT/Combining/Points.lean",
                "MIPStarRE.QPBT.Combining.Points.Absorption",
                "MIPStarRE.QPBT.Combining.Points.MarginalContraction",
            )
            status, _ = _run(["--root", str(root)])
            self.assertEqual(status, EXIT_OK)


class SubgraphTests(unittest.TestCase):
    def test_an_unimported_reexport_file_is_itself_reported(self) -> None:
        """A deeper re-export file is not a root: unimported, its subtree has no olean."""

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _reachable_tree(root)
            _write(root, "MIPStarRE/QPBT.lean", "MIPStarRE.QPBT.Algebra.Lines")
            report = analyse(root)
            self.assertIn("MIPStarRE.QPBT.Combining.Points", report.primary)
            # The children are fixed for free once Points.lean is imported again.
            self.assertIn("MIPStarRE.QPBT.Combining.Points.Absorption", report.fixed_by)
            status, out = _run(["--root", str(root)])
            self.assertEqual(status, EXIT_FINDINGS)
            self.assertIn("add to        MIPStarRE/QPBT.lean", out)
            self.assertIn("follows from", out)

    def test_import_cycle_among_orphans_reports_every_member(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _reachable_tree(root)
            _write(root, "MIPStarRE/QPBT/Loop/A.lean", "MIPStarRE.QPBT.Loop.B")
            _write(root, "MIPStarRE/QPBT/Loop/B.lean", "MIPStarRE.QPBT.Loop.A")
            report = analyse(root)
            self.assertEqual(
                report.primary, {"MIPStarRE.QPBT.Loop.A", "MIPStarRE.QPBT.Loop.B"}
            )


class TestTargetTests(unittest.TestCase):
    def test_test_modules_are_never_reported(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _reachable_tree(root)
            _write(root, "MIPStarRE/QPBT/Test/Soundness.lean")
            status, _ = _run(["--root", str(root)])
            self.assertEqual(status, EXIT_OK)

    def test_module_reachable_only_from_a_test_root_is_unreachable(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _reachable_tree(root)
            _write(root, "MIPStarRE/QPBT/Combining/Helper.lean")
            _write(root, "MIPStarRE/QPBT/Test/Soundness.lean", "MIPStarRE.QPBT.Combining.Helper")
            status, out = _run(["--root", str(root)])
            self.assertEqual(status, EXIT_FINDINGS)
            self.assertIn("MIPStarRE/QPBT/Combining/Helper.lean", out)
            self.assertIn("imported only from a */Test/* module", out)


# ── failure modes ───────────────────────────────────────────────────────────


class FailureModeTests(unittest.TestCase):
    def test_read_lean_reports_an_os_error_instead_of_raising(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            text, reason, warning = read_lean(Path(tmp) / "does-not-exist.lean")
            self.assertIsNone(text)
            self.assertIsNotNone(reason)
            self.assertIsNone(warning)

    @unittest.skipIf(_IS_ROOT, "chmod 000 does not stop root from reading")
    def test_unreadable_file_is_reported_not_crashed_on(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _reachable_tree(root)
            broken = root / "MIPStarRE" / "QPBT" / "Broken.lean"
            broken.write_text("import MIPStarRE.QPBT\n", encoding="utf-8")
            broken.chmod(0o000)
            try:
                status, out = _run(["--root", str(root)])
            finally:
                broken.chmod(0o644)
            self.assertEqual(status, EXIT_FINDINGS)
            self.assertIn("UNREADABLE", out)
            self.assertIn("MIPStarRE/QPBT/Broken.lean", out)

    def test_non_utf8_file_is_a_warning_and_still_parsed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _reachable_tree(root)
            path = root / "MIPStarRE" / "QPBT" / "Combining" / "Points.lean"
            path.write_bytes(
                b"import MIPStarRE.QPBT.Combining.Points.Absorption\n"
                b"import MIPStarRE.QPBT.Combining.Points.MarginalContraction\n"
                b"\n/-! \xff\xfe not utf-8 -/\n"
            )
            status, out = _run(["--root", str(root)])
            self.assertEqual(status, EXIT_OK)
            self.assertIn("WARNING", out)
            self.assertIn("not valid UTF-8", out)

    def test_malformed_lean_does_not_crash_the_walk(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _reachable_tree(root)
            path = root / "MIPStarRE" / "QPBT" / "Combining" / "Points.lean"
            path.write_text(
                "/- unterminated block comment\n"
                "import MIPStarRE.QPBT.Combining.Points.Absorption\n",
                encoding="utf-8",
            )
            status, out = _run(["--root", str(root)])
            self.assertEqual(status, EXIT_FINDINGS)
            self.assertIn("MIPStarRE/QPBT/Combining/Points/Absorption.lean", out)

    def test_wrong_root_is_a_usage_error(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            buffer = io.StringIO()
            with contextlib.redirect_stderr(buffer):
                status = main(["--root", tmp])
            self.assertEqual(status, EXIT_USAGE)
            self.assertIn("not a MIPStarRE worktree", buffer.getvalue())


# ── re-export file resolution ───────────────────────────────────────────────


class ReexportFileTests(unittest.TestCase):
    def test_nearest_existing_ancestor_wins(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _orphan_tree(root)
            report = analyse(root)
            self.assertEqual(
                reexport_file_for("MIPStarRE.QPBT.Combining.Points.Absorption", report.modules),
                "MIPStarRE/QPBT/Combining/Points.lean",
            )

    def test_falls_back_past_a_missing_ancestor(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _reachable_tree(root)
            _write(root, "MIPStarRE/QPBT/Games/Defs.lean")  # no MIPStarRE/QPBT/Games.lean
            report = analyse(root)
            self.assertEqual(
                reexport_file_for("MIPStarRE.QPBT.Games.Defs", report.modules),
                "MIPStarRE/QPBT.lean",
            )

    def test_an_ancestor_the_module_already_imports_is_skipped(self) -> None:
        """Importing back a parent the child imports would be a cycle."""

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _orphan_tree(root)
            # Absorption imports its own parent, as a split-out file often does.
            _write(
                root,
                "MIPStarRE/QPBT/Combining/Points/Absorption.lean",
                "MIPStarRE.QPBT.Combining.Points",
            )
            report = analyse(root)
            self.assertEqual(
                report.targets["MIPStarRE.QPBT.Combining.Points.Absorption"],
                "MIPStarRE/QPBT.lean",
            )
            self.assertEqual(
                report.targets["MIPStarRE.QPBT.Combining.Points.MarginalContraction"],
                "MIPStarRE/QPBT/Combining/Points.lean",
            )

    def test_no_usable_reexport_file_is_said_so(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _reachable_tree(root)
            _write(root, "MIPStarRE/QPBT.lean", "MIPStarRE.QPBT.Algebra.Lines")
            # Points.lean is now unreachable and imports every ancestor above it.
            _write(
                root,
                "MIPStarRE/QPBT/Combining/Points.lean",
                "MIPStarRE",
                "MIPStarRE.QPBT",
                "MIPStarRE.QPBT.Combining.Points.Absorption",
                "MIPStarRE.QPBT.Combining.Points.MarginalContraction",
            )
            report = analyse(root)
            self.assertIsNone(report.targets["MIPStarRE.QPBT.Combining.Points"])
            status, out = _run(["--root", str(root)])
            self.assertEqual(status, EXIT_FINDINGS)
            self.assertIn("no usable re-export file", out)


if __name__ == "__main__":
    unittest.main()
