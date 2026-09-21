#!/usr/bin/env python3
"""Regression tests for scripts/fetch_arxiv_source.py.

Every case runs offline from ``--from-archive`` with a fixture archive built
in the test's temporary directory, so nothing here reaches arxiv.org.
"""

from __future__ import annotations

import gzip
import hashlib
import io
import sys
import tarfile
import tempfile
import unittest
from contextlib import redirect_stdout, redirect_stderr
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPT_DIR))

import fetch_arxiv_source as fetcher  # noqa: E402

MAIN_TEX = """\\documentclass{article}
\\usepackage{graphicx}
\\begin{document}
\\section{Introduction}
\\includegraphics[width=0.5\\textwidth]{fig1}
\\input{sections/sec1}
\\end{document}
"""

SEC_TEX = "Some prose in a section.\n"
BIB = "@article{x, title={A title}}\n"
BBL = "\\begin{thebibliography}{1}\\end{thebibliography}\n"


def add(tar: tarfile.TarFile, name: str, payload: bytes) -> None:
    info = tarfile.TarInfo(name)
    info.size = len(payload)
    tar.addfile(info, io.BytesIO(payload))


def build_tgz(path: Path) -> bytes:
    with tarfile.open(path, "w:gz") as tar:
        add(tar, "main.tex", MAIN_TEX.encode())
        add(tar, "sections/sec1.tex", SEC_TEX.encode())
        add(tar, "refs.bib", BIB.encode())
        add(tar, "main.bbl", BBL.encode())
        add(tar, "fig1.pdf", b"%PDF-1.4 pretend figure\n")
        add(tar, "unused.png", b"\x89PNG not referenced\n")
        add(tar, "main.log", b"build log, dropped\n")
        add(tar, "../escape.tex", b"\\documentclass{article}\n")
    return path.read_bytes()


def fetch(*argv: str) -> tuple[int, str, str]:
    out, err = io.StringIO(), io.StringIO()
    with redirect_stdout(out), redirect_stderr(err):
        rc = fetcher.main(list(argv))
    return rc, out.getvalue(), err.getvalue()


class IdentifierTests(unittest.TestCase):
    def test_every_shape_of_identifier_is_accepted(self) -> None:
        cases = {
            "1234.56789": "1234.56789",
            "arXiv:1234.56789v3": "1234.56789v3",
            "https://arxiv.org/abs/1234.56789": "1234.56789",
            "https://arxiv.org/abs/1234.56789v2": "1234.56789v2",
            "http://arxiv.org/pdf/1234.56789v2.pdf": "1234.56789v2",
            "https://arxiv.org/e-print/1234.56789": "1234.56789",
            "math-ph/0000001": "math-ph/0000001",
            "https://arxiv.org/abs/quant-ph/0000001v1": "quant-ph/0000001v1",
        }
        for text, want in cases.items():
            with self.subTest(text=text):
                self.assertEqual(fetcher.parse_arxiv_id(text), want)

    def test_nonsense_is_refused_with_an_explanation(self) -> None:
        with self.assertRaises(fetcher.FetchError) as caught:
            fetcher.parse_arxiv_id("the paper about quantum things")
        self.assertIn("arXiv identifier", str(caught.exception))

    def test_the_version_is_split_off(self) -> None:
        self.assertEqual(fetcher.split_version("1234.56789v3"), ("1234.56789", "v3"))
        self.assertEqual(fetcher.split_version("1234.56789"), ("1234.56789", ""))


class TarballTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.addCleanup(self.tmp.cleanup)
        self.archive = self.root / "eprint.tar.gz"
        self.blob = build_tgz(self.archive)
        self.dest = self.root / "references" / "demo-paper"
        self.rc, self.out, self.err = fetch(
            "1234.56789v2", "--dest", str(self.dest),
            "--from-archive", str(self.archive), "--title", "A demo paper")
        self.source = self.dest / fetcher.SOURCE_SUBDIR

    def test_it_keeps_the_text_and_the_referenced_figure(self) -> None:
        self.assertEqual(self.rc, 0, self.err)
        kept = sorted(p.relative_to(self.source).as_posix()
                      for p in self.source.rglob("*") if p.is_file())
        self.assertEqual(kept, ["fig1.pdf", "main-arxiv.bbl", "main.tex",
                                "refs.bib", "sections/sec1.tex"])

    def test_it_drops_figures_nothing_includes_and_build_droppings(self) -> None:
        names = {p.name for p in self.source.rglob("*")}
        self.assertNotIn("unused.png", names)
        self.assertNotIn("main.log", names)

    def test_a_member_pointing_outside_the_directory_is_not_unpacked(self) -> None:
        self.assertFalse((self.root / "escape.tex").exists())
        self.assertFalse((self.dest.parent / "escape.tex").exists())

    def test_the_precompiled_bibliography_is_moved_out_of_harms_way(self) -> None:
        """A bibtex run would overwrite <main>.bbl, and arXiv ships no .bib."""
        self.assertTrue((self.source / "main-arxiv.bbl").is_file())
        self.assertFalse((self.source / "main.bbl").exists())

    def test_source_md_records_what_was_fetched(self) -> None:
        text = (self.dest / "SOURCE.md").read_text(encoding="utf-8")
        self.assertIn("`1234.56789`", text)
        self.assertIn("`v2`", text)
        self.assertIn(hashlib.sha256(self.blob).hexdigest(), text)
        self.assertIn(fetcher.UNKNOWN_LICENCE, text)
        self.assertIn("Copyright remains with the authors.", text)
        self.assertIn("arxiv-source/main.tex", text)
        self.assertIn("main.bbl -> main-arxiv.bbl", text)

    def test_it_prints_the_split_command(self) -> None:
        self.assertIn("split_reference_paper.py", self.out)
        self.assertIn("--arxiv 1234.56789", self.out)
        self.assertIn('--title "A demo paper"', self.out)

    def test_a_second_run_needs_force(self) -> None:
        rc, _, err = fetch("1234.56789v2", "--dest", str(self.dest),
                           "--from-archive", str(self.archive))
        self.assertEqual(rc, 2)
        self.assertIn("--force", err)
        rc, _, _ = fetch("1234.56789v2", "--dest", str(self.dest),
                         "--from-archive", str(self.archive), "--force")
        self.assertEqual(rc, 0)


class SingleFileTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.addCleanup(self.tmp.cleanup)

    def test_a_single_gzipped_tex_file_is_a_valid_submission(self) -> None:
        archive = self.root / "eprint.gz"
        archive.write_bytes(gzip.compress(MAIN_TEX.encode()))
        dest = self.root / "mirror"
        rc, out, err = fetch("1234.56789", "--dest", str(dest),
                             "--from-archive", str(archive))
        self.assertEqual(rc, 0, err)
        self.assertEqual((dest / fetcher.SOURCE_SUBDIR / "main.tex").read_text(
            encoding="utf-8"), MAIN_TEX)
        self.assertIn("split_reference_paper.py", out)

    def test_a_pdf_only_submission_stops_with_a_clear_message(self) -> None:
        archive = self.root / "eprint.pdf"
        archive.write_bytes(b"%PDF-1.5\nno source here\n")
        rc, _, err = fetch("1234.56789", "--dest", str(self.root / "m1"),
                           "--from-archive", str(archive))
        self.assertEqual(rc, 2)
        self.assertIn("PDF", err)
        self.assertIn("TeX source", err)
        self.assertIn("owner", err)

    def test_a_gzipped_pdf_only_submission_is_caught_too(self) -> None:
        archive = self.root / "eprint.gz"
        archive.write_bytes(gzip.compress(b"%PDF-1.5\nno source here\n"))
        rc, _, err = fetch("1234.56789", "--dest", str(self.root / "m2"),
                           "--from-archive", str(archive))
        self.assertEqual(rc, 2)
        self.assertIn("TeX source", err)

    def test_an_archive_without_tex_is_refused(self) -> None:
        archive = self.root / "eprint.tar.gz"
        with tarfile.open(archive, "w:gz") as tar:
            add(tar, "notes.txt", b"nothing useful\n")
        rc, _, err = fetch("1234.56789", "--dest", str(self.root / "m3"),
                           "--from-archive", str(archive))
        self.assertEqual(rc, 2)
        self.assertIn("no .tex", err)


if __name__ == "__main__":
    unittest.main()
