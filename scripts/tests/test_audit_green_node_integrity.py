#!/usr/bin/env python3
"""Regression tests for scripts/audit_green_node_integrity.py."""

from __future__ import annotations

import contextlib
import io
import json
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path
from unittest import mock

SCRIPT_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPT_DIR))

import audit_green_node_integrity as audit  # noqa: E402


class GreenNodeIntegrityAuditTests(unittest.TestCase):
    def test_endpoint_prose_does_not_close_namespace(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            lean_file = root / "PaperLib" / "Foo.lean"
            lean_file.parent.mkdir(parents=True)
            lean_file.write_text(
                textwrap.dedent(
                    """
                    namespace PaperLib.Core

                    /--
                    end point
                    endpoint prose in a mathematical docstring is not a Lean `end`
                    command, and therefore must not change the namespace stack.
                    -/
                    theorem afterEndpointProse (h : P) : Q := by
                      sorry

                    end PaperLib.Core
                    """
                ).strip()
                + "\n",
                encoding="utf-8",
            )

            headers = audit.declaration_headers(root)

        self.assertIn("PaperLib.Core.afterEndpointProse", headers)
        self.assertIsNone(audit.EVENT_RE.search("endpoint"))
        self.assertTrue(audit.EVENT_RE.search("end point"))

    def test_line_comments_do_not_close_namespace(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            lean_file = root / "PaperLib" / "Foo.lean"
            lean_file.parent.mkdir(parents=True)
            lean_file.write_text(
                textwrap.dedent(
                    """
                    namespace PaperLib.Core

                    -- end point
                    theorem afterLineComment (h : P) : Q := by
                      sorry

                    end PaperLib.Core
                    """
                ).strip()
                + "\n",
                encoding="utf-8",
            )

            headers = audit.declaration_headers(root)

        self.assertIn("PaperLib.Core.afterLineComment", headers)

    def test_tex_comment_does_not_mark_node_green(self) -> None:
        block = textwrap.dedent(
            r"""
            \begin{theorem}\label{thm:commented}
              \lean{Foo.bar}
              % This source theorem is not marked \leanok.
            \end{theorem}
            """
        )

        masked = audit.mask_tex_comments(block)

        self.assertNotIn(r"\leanok", masked)
        self.assertIn(r"\lean{Foo.bar}", masked)

    def test_unfaithful_docstring_is_indexed(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            lean_file = root / "PaperLib" / "Foo.lean"
            lean_file.parent.mkdir(parents=True)
            lean_file.write_text(
                textwrap.dedent(
                    """
                    namespace PaperLib.Core

                    /--
                    A source-shaped declaration.

                    **Unfaithful:** This proof still depends on a tracked
                    obligation.
                    -/
                    theorem sourceStatement (h : P) : Q := by
                      sorry

                    end PaperLib.Core
                    """
                ).strip()
                + "\n",
                encoding="utf-8",
            )

            docstrings = audit.declaration_docstrings(root)

        self.assertTrue(
            audit.has_unfaithful_marker("PaperLib.Core.sourceStatement", docstrings)
        )

    def test_plain_block_comment_does_not_reuse_previous_docstring(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            lean_file = root / "PaperLib" / "Foo.lean"
            lean_file.parent.mkdir(parents=True)
            lean_file.write_text(
                textwrap.dedent(
                    """
                    namespace PaperLib.Core

                    /--
                    **Unfaithful:** This marker belongs only to the first
                    declaration.
                    -/
                    theorem firstSourceStatement (h : P) : Q := by
                      sorry

                    /- A plain implementation note immediately before the next
                    declaration is not a docstring. -/
                    theorem secondStatement (h : P) : Q := by
                      sorry

                    end PaperLib.Core
                    """
                ).strip()
                + "\n",
                encoding="utf-8",
            )

            docstrings = audit.declaration_docstrings(root)

        self.assertTrue(
            audit.has_unfaithful_marker("PaperLib.Core.firstSourceStatement", docstrings)
        )
        self.assertFalse(
            audit.has_unfaithful_marker("PaperLib.Core.secondStatement", docstrings)
        )

    def test_nested_block_comment_inside_docstring_is_indexed(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            lean_file = root / "PaperLib" / "Foo.lean"
            lean_file.parent.mkdir(parents=True)
            lean_file.write_text(
                textwrap.dedent(
                    """
                    namespace PaperLib.Core

                    /--
                    A source-shaped declaration whose docstring contains a
                    nested implementation aside: /- nested note -/.

                    **Unfaithful:** The marker still belongs to this declaration.
                    -/
                    theorem nestedDocstringStatement (h : P) : Q := by
                      sorry

                    end PaperLib.Core
                    """
                ).strip()
                + "\n",
                encoding="utf-8",
            )

            docstrings = audit.declaration_docstrings(root)

        self.assertTrue(
            audit.has_unfaithful_marker(
                "PaperLib.Core.nestedDocstringStatement", docstrings
            )
        )


if __name__ == "__main__":
    unittest.main()


class ExemptionRegisterTests(unittest.TestCase):
    """The per-declaration exemptions are data, not code, and start empty."""

    def _repo(self, root: Path) -> None:
        lean = root / "PaperLib" / "Foo.lean"
        lean.parent.mkdir(parents=True)
        lean.write_text(
            "namespace PaperLib\n\n"
            "theorem someBridge (h : P) : Q := by\n  sorry\n\n"
            "end PaperLib\n",
            encoding="utf-8",
        )
        chapter = root / "blueprint" / "src" / "chapter" / "ch01.tex"
        chapter.parent.mkdir(parents=True)
        chapter.write_text(
            "\\begin{theorem}\\label{thm:paper}\n"
            "  \\lean{PaperLib.someBridge}\n"
            "  \\leanok\n"
            "\\end{theorem}\n",
            encoding="utf-8",
        )

    def _run(self, root: Path) -> tuple[int, str]:
        out = io.StringIO()
        with mock.patch.object(sys, "argv", ["audit", "--root", str(root), "--ci"]):
            with contextlib.redirect_stdout(out):
                code = audit.main()
        return code, out.getvalue()

    def test_a_repository_without_a_register_file_exempts_nothing(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            self.assertEqual(audit._load_register(root, "allowed_source_warnings"), set())
            self._repo(root)
            code, text = self._run(root)
            self.assertEqual(code, 1)
            self.assertIn("unexpected source-like warning links", text)

    def test_a_registered_pair_is_classified_as_allowed(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            self._repo(root)
            (root / "local").mkdir()
            (root / audit.REGISTER_PATH).write_text(
                json.dumps({
                    audit.REGISTER_SECTION: {
                        "allowed_source_warnings": [
                            ["thm:paper", "PaperLib.someBridge"],
                        ]
                    }
                }),
                encoding="utf-8",
            )
            self.assertEqual(
                audit._load_register(root, "allowed_source_warnings"),
                {("thm:paper", "PaperLib.someBridge")},
            )
            code, text = self._run(root)
            self.assertEqual(code, 0)
            self.assertIn("OK:", text)

    def test_a_malformed_register_entry_is_refused(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "local").mkdir()
            (root / audit.REGISTER_PATH).write_text(
                json.dumps({audit.REGISTER_SECTION: {"allowed_source_warnings": ["thm:paper"]}}),
                encoding="utf-8",
            )
            with self.assertRaises(SystemExit):
                audit._load_register(root, "allowed_source_warnings")
