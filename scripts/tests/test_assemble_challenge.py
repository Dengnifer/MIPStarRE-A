#!/usr/bin/env python3
"""Regression tests for comparator challenge assembly."""

from __future__ import annotations

import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
COMPARATOR = REPO_ROOT / "scripts" / "comparator"
ASSEMBLER = COMPARATOR / "assemble_challenge.py"

# the assembler imports its sibling `challenge_config`, which a script run
# finds on `sys.path[0]` and a file-location import does not
if str(COMPARATOR) not in sys.path:
    sys.path.insert(0, str(COMPARATOR))

_spec = importlib.util.spec_from_file_location("assemble_challenge", ASSEMBLER)
assert _spec is not None and _spec.loader is not None
assemble_challenge = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(assemble_challenge)


class AssembleChallengeTests(unittest.TestCase):
    def assemble_split_fixture(
        self, root: Path, *, header: str | None, footer: str | None
    ) -> dict[str, str]:
        source = root / "MIPStarRE" / "Example.lean"
        source.parent.mkdir(parents=True)
        source.write_text(
            "namespace Example\ndef value : Nat := 1\nend Example\n",
            encoding="utf-8",
        )
        tsv = root / "closure.tsv"
        tsv.write_text(
            "Example.value\tMIPStarRE/Example.lean\t2\t2\n",
            encoding="utf-8",
        )
        challenge = assemble_challenge.ChallengeConfig(
            name="test",
            path=root / "test.json",
            description="split fixture",
            imports=("MIPStarRE.Example",),
            targets=("Example.value",),
            header=header,
            footer=footer,
            expected="expected/test",
            require_expected=False,
            split=True,
            common_opens=(),
            extras={},
            module_preludes={},
        )
        return assemble_challenge.assemble_split(challenge, root, tsv)

    def test_preserves_declaration_scoped_open_command(self) -> None:
        lines = [
            "namespace Example",
            "open scoped Classical in",
            "/-- A definition needing declaration-scoped context. -/",
            "def value := 1",
            "end Example",
        ]

        start, source = assemble_challenge.source_range_with_context(lines, 3, 4)

        self.assertEqual(start, 2)
        self.assertEqual(source[0], "open scoped Classical in")
        self.assertEqual(source[-1], "def value := 1")

    def test_leaves_ordinary_declaration_range_unchanged(self) -> None:
        lines = ["namespace Example", "/-- Ordinary. -/", "def value := 1", "end Example"]

        start, source = assemble_challenge.source_range_with_context(lines, 2, 3)

        self.assertEqual(start, 2)
        self.assertEqual(source, lines[1:3])

    def test_split_assembly_omits_unconfigured_parts(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            files = self.assemble_split_fixture(
                Path(td), header=None, footer=None
            )

        self.assertTrue(files["Challenge.lean"].startswith(
            "import Mathlib\nimport Challenge.MIPStarRE.Example\n"
        ))

    def test_split_assembly_omits_missing_configured_header(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            footer = root / "footer.lean"
            footer.write_text("\n-- footer sentinel\n", encoding="utf-8")
            files = self.assemble_split_fixture(
                root, header="missing-header.lean", footer="footer.lean"
            )

        root_module = files["Challenge.lean"]
        self.assertTrue(root_module.startswith(
            "import Mathlib\nimport Challenge.MIPStarRE.Example\n"
        ))
        self.assertIn("-- footer sentinel", root_module)

    def test_split_assembly_omits_missing_configured_footer(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            header = root / "header.lean"
            header.write_text(
                "import Mathlib\n\n-- header sentinel\n", encoding="utf-8"
            )
            files = self.assemble_split_fixture(
                root, header="header.lean", footer="missing-footer.lean"
            )

        root_module = files["Challenge.lean"]
        self.assertIn("import Challenge.MIPStarRE.Example", root_module)
        self.assertIn("-- header sentinel", root_module)


if __name__ == "__main__":
    unittest.main()
