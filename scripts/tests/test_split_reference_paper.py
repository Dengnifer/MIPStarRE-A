#!/usr/bin/env python3
"""Regression tests for scripts/split_reference_paper.py.

The splitter is the one bootstrap tool the origin project shipped untested,
and its byte-identity check is the whole reason the mirrors can be trusted, so
that check is exercised in both directions: a good split, and a split that has
lost a line.
"""

from __future__ import annotations

import io
import sys
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path
from unittest import mock

SCRIPT_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPT_DIR))

import split_reference_paper as splitter  # noqa: E402

FIXTURE = Path(__file__).resolve().parent / "fixtures" / "kit" / "sample-paper.tex"


def split(source: Path, outdir: Path, *extra: str) -> int:
    argv = ["split_reference_paper.py", str(source), str(outdir),
            "--arxiv", "0000.00000", "--title", "A miniature paper", *extra]
    with mock.patch.object(sys, "argv", argv), redirect_stdout(io.StringIO()):
        return splitter.main()


class SlugTests(unittest.TestCase):
    def test_a_title_becomes_a_file_name_stem(self) -> None:
        self.assertEqual(splitter.slugify("The main estimate"), "the_main_estimate")
        # TeX commands are dropped, not transliterated: `\eps` leaves no trace.
        self.assertEqual(splitter.slugify(r"$\eps$-nets \& friends"), "nets_friends")
        self.assertEqual(splitter.slugify("!!!"), "section")

    def test_a_section_title_is_brace_balanced(self) -> None:
        line = r"\section{A \textbf{bold} title}"
        self.assertEqual(splitter.section_title(line), r"A \textbf{bold} title")


class SplitTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.addCleanup(self.tmp.cleanup)
        self.source = self.root / "paper.tex"
        self.source.write_bytes(FIXTURE.read_bytes())
        self.out = self.root / "out"

    def test_every_byte_of_the_source_survives_the_split(self) -> None:
        self.assertEqual(split(self.source, self.out), 0)
        pieces = sorted(self.out.glob("*.tex"))
        joined = b"".join(piece.read_bytes() for piece in pieces)
        self.assertEqual(joined, self.source.read_bytes())

    def test_the_pieces_are_preamble_frontmatter_sections_bibliography(self) -> None:
        split(self.source, self.out)
        names = [p.name for p in sorted(self.out.glob("*.tex"))]
        self.assertEqual(names, [
            "00_preamble.tex",
            "01_frontmatter.tex",
            "02_introduction.tex",
            "03_the_main_estimate.tex",
            "04_deferred_proofs.tex",
            "05_bibliography.tex",
        ])

    def test_an_appendix_switch_opens_the_section_that_follows_it(self) -> None:
        split(self.source, self.out)
        deferred = (self.out / "04_deferred_proofs.tex").read_text(encoding="utf-8")
        estimate = (self.out / "03_the_main_estimate.tex").read_text(encoding="utf-8")
        self.assertIn("\\appendix", deferred)
        self.assertNotIn("\\appendix", estimate)

    def test_the_manifest_records_the_line_ranges(self) -> None:
        split(self.source, self.out)
        manifest = (self.out / "README.md").read_text(encoding="utf-8")
        self.assertIn("arXiv:0000.00000", manifest)
        self.assertIn("| File | Kind | Source lines |", manifest)
        self.assertIn("`02_introduction.tex` | section |", manifest)

    def test_crlf_input_is_normalized_once_and_said_so_in_the_manifest(self) -> None:
        crlf = self.root / "crlf.tex"
        crlf.write_bytes(self.source.read_bytes().replace(b"\n", b"\r\n"))
        out = self.root / "crlf-out"
        self.assertEqual(split(crlf, out), 0)
        joined = b"".join(p.read_bytes() for p in sorted(out.glob("*.tex")))
        self.assertEqual(joined, self.source.read_bytes())
        self.assertNotIn(b"\r\n", joined)
        self.assertIn("CRLF", (out / "README.md").read_text(encoding="utf-8"))

    def test_a_split_that_loses_a_line_fails_and_removes_its_output(self) -> None:
        """The verifier must catch a lossy split, not just report success."""
        real = splitter.split_lines

        def lossy(text: str):
            pieces = real(text)
            kind, hint, start, end = pieces[2]
            pieces[2] = (kind, hint, start, end - 1)  # drop one line
            return pieces

        with mock.patch.object(splitter, "split_lines", lossy):
            with self.assertRaises(SystemExit) as caught:
                split(self.source, self.out)
        self.assertIn("byte-identity", str(caught.exception))
        self.assertEqual(list(self.out.glob("*.tex")), [])

    def test_a_non_empty_outdir_needs_force(self) -> None:
        split(self.source, self.out)
        with self.assertRaises(SystemExit) as caught:
            split(self.source, self.out)
        self.assertIn("--force", str(caught.exception))
        self.assertEqual(split(self.source, self.out, "--force"), 0)

    def test_a_source_without_a_document_is_refused(self) -> None:
        bad = self.root / "bad.tex"
        bad.write_text("\\documentclass{article}\n% and nothing else\n", encoding="utf-8")
        with self.assertRaises(SystemExit) as caught:
            split(bad, self.root / "bad-out")
        self.assertIn("begin{document}", str(caught.exception))


if __name__ == "__main__":
    unittest.main()
