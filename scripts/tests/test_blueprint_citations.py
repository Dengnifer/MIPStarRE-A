#!/usr/bin/env python3
"""Regression tests for ``scripts/blueprint_citations.py``."""

from __future__ import annotations

import contextlib
import io
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPT_DIR))

from blueprint_citations import (  # noqa: E402
    LabelLocation,
    build_label_index,
    collect_input_files,
    find_citation_uses,
    main,
    rewrite_text,
)


def _write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


class BlueprintCitationTests(unittest.TestCase):
    def setUp(self) -> None:
        holder = tempfile.TemporaryDirectory()
        self.addCleanup(holder.cleanup)
        self.root = Path(holder.name)
        self.chapter = self.root / "blueprint" / "src" / "chapter"
        _write(
            self.chapter / "ch12_example.tex",
            """\\section{Example}\\label{sec:example}

\\begin{lemma}[Alpha]\\label{lem:alpha}
  Alpha statement.
\\end{lemma}
\\begin{proof}
  Alpha proof.
\\end{proof}

% \\label{lem:commented-out}
\\begin{definition}
  \\label{def:beta}
  Beta definition.
\\end{definition}
""",
        )

    def test_index_resolves_statement_and_following_proof(self) -> None:
        index = build_label_index(self.root)

        self.assertEqual(index["lem:alpha"][0].locator,
                         "blueprint/src/chapter/ch12_example.tex:3-8")
        self.assertEqual(index["def:beta"][0].locator,
                         "blueprint/src/chapter/ch12_example.tex:11-14")
        self.assertEqual(index["sec:example"][0].locator,
                         "blueprint/src/chapter/ch12_example.tex:1")
        self.assertNotIn("lem:commented-out", index)

    def test_duplicate_labels_remain_visible_to_resolver(self) -> None:
        _write(
            self.chapter / "ch13_duplicate.tex",
            "\\begin{lemma}\\label{lem:alpha}Duplicate.\\end{lemma}\n",
        )

        index = build_label_index(self.root)

        self.assertEqual(len(index["lem:alpha"]), 2)

    def test_scan_finds_known_tokens_and_unknown_blueprint_labels(self) -> None:
        lean = self.root / "MIPStarRE" / "Example.lean"
        _write(
            lean,
            "/-- See blueprint `lem:alpha`, `def:missing`, and bare "
            "`rem:missing`; ignore Lean name `Example.value`. -/\n",
        )
        index = build_label_index(self.root)

        uses, unknown = find_citation_uses([lean], self.root, index)

        self.assertEqual([(use.label, use.line) for use in uses], [("lem:alpha", 1)])
        self.assertEqual(
            [(use.label, use.line) for use in unknown],
            [("def:missing", 1), ("rem:missing", 1)],
        )

    def test_rewrite_uses_label_named_in_same_docstring(self) -> None:
        text = (
            "/-- Lean support for `lem:alpha`, blueprint "
            "`blueprint/src/chapter/ch12_example.tex:20-26`. -/\n"
        )

        rewritten, unresolved = rewrite_text(text, build_label_index(self.root))

        self.assertEqual(unresolved, [])
        self.assertEqual(rewritten, "/-- Lean support for blueprint `lem:alpha`. -/\n")

    def test_rewrite_prefers_an_exact_node_to_a_nearby_label(self) -> None:
        text = (
            "/-- Lean support for `lem:alpha`, blueprint "
            "`blueprint/src/chapter/ch12_example.tex:11-14`. -/\n"
        )

        rewritten, unresolved = rewrite_text(text, build_label_index(self.root))

        self.assertEqual(unresolved, [])
        self.assertEqual(
            rewritten,
            "/-- Lean support for `lem:alpha`, blueprint `def:beta`. -/\n",
        )

    def test_rewrite_can_use_an_exact_current_span(self) -> None:
        text = "/-- See `blueprint/src/chapter/ch12_example.tex:11-14`. -/\n"

        rewritten, unresolved = rewrite_text(text, build_label_index(self.root))

        self.assertEqual(unresolved, [])
        self.assertEqual(rewritten, "/-- See `def:beta`. -/\n")

    def test_rewrite_accepts_a_single_line_locator(self) -> None:
        text = "/-- See `blueprint/src/chapter/ch12_example.tex:1`. -/\n"

        rewritten, unresolved = rewrite_text(text, build_label_index(self.root))

        self.assertEqual(unresolved, [])
        self.assertEqual(rewritten, "/-- See `sec:example`. -/\n")

    def test_rewrite_collapses_duplicate_parenthetical_label(self) -> None:
        text = (
            "/-- The source is `lem:alpha` "
            "(`blueprint/src/chapter/ch12_example.tex:20-26`). -/\n"
        )

        rewritten, unresolved = rewrite_text(text, build_label_index(self.root))

        self.assertEqual(unresolved, [])
        self.assertEqual(rewritten, "/-- The source is blueprint `lem:alpha`. -/\n")

    def test_rewrite_refuses_an_unanchored_stale_locator(self) -> None:
        text = "/-- See `blueprint/src/chapter/ch12_example.tex:80-90`. -/\n"

        rewritten, unresolved = rewrite_text(text, build_label_index(self.root))

        self.assertEqual(rewritten, text)
        self.assertEqual(
            unresolved,
            ["`blueprint/src/chapter/ch12_example.tex:80-90`"],
        )

    def test_rewrite_refuses_containment_in_a_current_span(self) -> None:
        text = "/-- See `blueprint/src/chapter/ch12_example.tex:4-6`. -/\n"

        rewritten, unresolved = rewrite_text(text, build_label_index(self.root))

        self.assertEqual(rewritten, text)
        self.assertEqual(
            unresolved,
            ["`blueprint/src/chapter/ch12_example.tex:4-6`"],
        )

    def test_rewrite_does_not_guess_from_decoding_docstring_proximity(self) -> None:
        index = {
            "lem:qld-decoder-linearity": [LabelLocation(
                "lem:qld-decoder-linearity", "blueprint/src/chapter/ch16_qpbt_analysis.tex",
                30, 30, 46,
            )],
            "lem:qld-construct-the-paulis": [LabelLocation(
                "lem:qld-construct-the-paulis", "blueprint/src/chapter/ch16_qpbt_analysis.tex",
                193, 193, 261,
            )],
        }
        text = (
            "/-- This is blueprint `lem:qld-decoder-linearity`, used in the symmetry "
            "step at blueprint `ch16_qpbt_analysis.tex:239-244`. -/\n"
        )

        rewritten, unresolved = rewrite_text(text, index)

        self.assertIn("`ch16_qpbt_analysis.tex:239-244`", rewritten)
        self.assertEqual(rewritten.count("`lem:qld-decoder-linearity`"), 1)
        self.assertEqual(unresolved, ["`ch16_qpbt_analysis.tex:239-244`"])

    def test_rewrite_uses_exact_given_strategy_support_node(self) -> None:
        index = {
            "lem:symmetric-strat": [LabelLocation(
                "lem:symmetric-strat", "blueprint/src/chapter/ch12_qpbt_games.tex",
                116, 116, 134,
            )],
            "lem:symmetric-strat-given-strategy": [LabelLocation(
                "lem:symmetric-strat-given-strategy",
                "blueprint/src/chapter/ch12_qpbt_games.tex", 140, 140, 154,
            )],
        }
        text = (
            "/-- Formalization-only form of `lem:symmetric-strat`; blueprint "
            "`ch12_qpbt_games.tex:140-154`. -/\n"
        )

        rewritten, unresolved = rewrite_text(text, index)

        self.assertEqual(unresolved, [])
        self.assertEqual(
            rewritten,
            "/-- Formalization-only form of `lem:symmetric-strat`; blueprint\n"
            "`lem:symmetric-strat-given-strategy`. -/\n",
        )

    def test_rewrite_wraps_long_blueprint_citation_lines_idempotently(self) -> None:
        text = (
            "/-- The source-facing nodes are blueprint `def:one`, blueprint `def:two`, "
            "blueprint `lem:three`, and blueprint `def:a-very-long-fourth-label`. -/\n"
        )

        rewritten, unresolved = rewrite_text(text, {})
        second, second_unresolved = rewrite_text(rewritten, {})

        self.assertEqual(unresolved, [])
        self.assertEqual(second_unresolved, [])
        self.assertEqual(second, rewritten)
        self.assertTrue(all(len(line) <= 100 for line in rewritten.splitlines()))

    def test_resolve_scan_fails_for_bare_and_list_unknown_labels(self) -> None:
        lean = self.root / "MIPStarRE" / "Example.lean"
        _write(
            lean,
            "/-- Blueprint `lem:alpha`, `def:missing`; bare `rem:missing`. -/\n",
        )
        stdout = io.StringIO()

        with contextlib.redirect_stdout(stdout):
            result = main([
                "--root", str(self.root), "resolve", "--path",
                "MIPStarRE/Example.lean", "--format", "plain",
            ])

        self.assertEqual(result, 1)
        self.assertIn("def:missing\tUNRESOLVED", stdout.getvalue())
        self.assertIn("rem:missing\tUNRESOLVED", stdout.getvalue())

    def test_rewrite_refuses_proximity_with_multiple_labels(self) -> None:
        text = (
            "/-- Compare `lem:alpha` with `def:beta`. The first source is "
            "`blueprint/src/chapter/ch12_example.tex:80-90`; the second is "
            "`blueprint/src/chapter/ch12_example.tex:91-100`. -/\n"
        )

        rewritten, unresolved = rewrite_text(text, build_label_index(self.root))

        self.assertEqual(
            rewritten,
            "/-- Compare `lem:alpha` with `def:beta`. The first source is\n"
            "`blueprint/src/chapter/ch12_example.tex:80-90`; the second is\n"
            "`blueprint/src/chapter/ch12_example.tex:91-100`. -/\n",
        )
        self.assertEqual(
            unresolved,
            [
                "`blueprint/src/chapter/ch12_example.tex:80-90`",
                "`blueprint/src/chapter/ch12_example.tex:91-100`",
            ],
        )

    def test_rewrite_pairs_multiple_parenthetical_labels(self) -> None:
        text = (
            "/-- See `lem:alpha` "
            "(`blueprint/src/chapter/ch12_example.tex:80-90`) and `def:beta`; "
            "blueprint `blueprint/src/chapter/ch12_example.tex:91-100`. -/\n"
        )

        rewritten, unresolved = rewrite_text(text, build_label_index(self.root))

        self.assertEqual(unresolved, [])
        self.assertEqual(
            rewritten,
            "/-- See blueprint `lem:alpha` and blueprint `def:beta`. -/\n",
        )

    def test_rewrite_pairs_a_following_parenthetical_label(self) -> None:
        text = (
            "/-- See `blueprint/src/chapter/ch12_example.tex:80-90` "
            "(`lem:alpha`) and `def:beta`. -/\n"
        )

        rewritten, unresolved = rewrite_text(text, build_label_index(self.root))

        self.assertEqual(unresolved, [])
        self.assertEqual(
            rewritten,
            "/-- See blueprint `lem:alpha` and `def:beta`. -/\n",
        )

    def test_rewrite_refuses_a_multi_range_locator(self) -> None:
        text = (
            "/-- See `lem:alpha`, blueprint "
            "`blueprint/src/chapter/ch12_example.tex:3-8,11-14`. -/\n"
        )

        rewritten, unresolved = rewrite_text(text, build_label_index(self.root))

        self.assertEqual(rewritten, text)
        self.assertEqual(
            unresolved,
            ["`blueprint/src/chapter/ch12_example.tex:3-8,11-14`"],
        )

    def test_input_paths_cannot_escape_root(self) -> None:
        with self.assertRaisesRegex(ValueError, "escapes repository root"):
            collect_input_files(self.root, ["../outside"], None)

    def test_resolve_cli_reports_current_location(self) -> None:
        stdout = io.StringIO()
        with contextlib.redirect_stdout(stdout):
            result = main([
                "--root", str(self.root), "resolve", "lem:alpha", "--format", "plain"
            ])

        self.assertEqual(result, 0)
        self.assertEqual(
            stdout.getvalue(),
            "lem:alpha\tblueprint/src/chapter/ch12_example.tex:3-8\n",
        )

    def test_resolve_cli_fails_for_unknown_label(self) -> None:
        stdout = io.StringIO()
        with contextlib.redirect_stdout(stdout):
            result = main([
                "--root", str(self.root), "resolve", "lem:missing", "--format", "plain"
            ])

        self.assertEqual(result, 1)
        self.assertEqual(stdout.getvalue(), "lem:missing\tUNRESOLVED\n")

    def test_rewrite_cli_refuses_partial_writes_without_opt_in(self) -> None:
        lean = self.root / "MIPStarRE" / "Example.lean"
        original = (
            "/-- See `lem:alpha`, blueprint "
            "`blueprint/src/chapter/ch12_example.tex:80-90`. -/\n"
            "/-- See `blueprint/src/chapter/ch12_example.tex:91-100`. -/\n"
        )
        _write(lean, original)
        stderr = io.StringIO()

        with contextlib.redirect_stderr(stderr):
            refused = main([
                "--root", str(self.root), "rewrite", "MIPStarRE/Example.lean", "--write"
            ])

        self.assertEqual(refused, 1)
        self.assertEqual(lean.read_text(encoding="utf-8"), original)
        self.assertIn("refusing partial rewrite", stderr.getvalue())

        stderr = io.StringIO()
        with contextlib.redirect_stderr(stderr):
            accepted = main([
                "--root", str(self.root), "rewrite", "MIPStarRE/Example.lean",
                "--write", "--allow-unresolved",
            ])

        self.assertEqual(accepted, 0)
        self.assertEqual(
            lean.read_text(encoding="utf-8"),
            "/-- See blueprint `lem:alpha`. -/\n"
            "/-- See `blueprint/src/chapter/ch12_example.tex:91-100`. -/\n",
        )
        self.assertIn("rewrote 1 file(s); 1 unresolved locator(s)", stderr.getvalue())

    def test_location_locator_uses_one_line_form(self) -> None:
        location = LabelLocation("sec:x", "blueprint/src/chapter/ch.tex", 7, 7, 7)
        self.assertEqual(location.locator, "blueprint/src/chapter/ch.tex:7")


if __name__ == "__main__":
    unittest.main()
