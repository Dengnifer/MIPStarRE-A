#!/usr/bin/env python3
"""Smoke tests for scripts/make_artifact.sh.

The script is driven against a throwaway git repository built in a temporary
directory, so these tests are fast, offline, and independent of the state of
the real repository. What they pin down is the behaviour a release depends on:
the allow-list actually excludes the workflow layer, the leak scan actually
fails the run, and `--anonymize` actually rewrites.
"""

from __future__ import annotations

import json
import shutil
import subprocess
import tarfile
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "make_artifact.sh"

LEAN_MAIN = """import MIPStarRE.Bar

/-- A doc comment: this line does not count as code.
    Neither does this one. -/
theorem foo : True := trivial
"""

LEAN_BAR = "theorem bar : True := trivial\n"


def git(repo: Path, *args: str) -> str:
    """Run git in *repo* with a fixed identity, returning stripped stdout."""
    proc = subprocess.run(
        ["git", "-C", str(repo), "-c", "user.name=Test", "-c", "user.email=test@example.invalid",
         "-c", "commit.gpgsign=false", *args],
        capture_output=True, text=True, check=True,
    )
    return proc.stdout.strip()


def write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def minimal_pdf(text: str) -> bytes:
    """A one-page PDF whose only visible content is *text*, built by hand.

    Short enough to keep in the test, and real enough that pdftotext reads it.
    Its job is to put a binary into the snapshot: the leak scan skips binaries
    by construction, so a PDF is the one shipped file that could otherwise
    carry a home path past it.
    """
    stream = ("BT /F1 12 Tf 20 100 Td (%s) Tj ET" % text).encode("ascii")
    objects = [
        b"<< /Type /Catalog /Pages 2 0 R >>",
        b"<< /Type /Pages /Kids [3 0 R] /Count 1 >>",
        b"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 300 200]"
        b" /Resources << /Font << /F1 5 0 R >> >> /Contents 4 0 R >>",
        b"<< /Length %d >>\nstream\n%s\nendstream" % (len(stream), stream),
        b"<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica >>",
    ]
    out = bytearray(b"%PDF-1.4\n")
    offsets = []
    for number, body in enumerate(objects, start=1):
        offsets.append(len(out))
        out += b"%d 0 obj\n" % number + body + b"\nendobj\n"
    xref = len(out)
    out += b"xref\n0 %d\n" % (len(objects) + 1)
    out += b"0000000000 65535 f \n"
    for offset in offsets:
        out += b"%010d 00000 n \n" % offset
    out += b"trailer\n<< /Size %d /Root 1 0 R >>\nstartxref\n%d\n%%%%EOF\n" % (
        len(objects) + 1, xref)
    return bytes(out)


class MakeArtifactTests(unittest.TestCase):
    """Each test gets its own repository; they mutate it freely."""

    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.tmp = Path(self._tmp.name)
        self.addCleanup(self._tmp.cleanup)
        self.repo = self.tmp / "repo"
        self.out = self.tmp / "out"
        self.repo.mkdir()
        git(self.repo, "init", "-q", "-b", "main")

        write(self.repo / "MIPStarRE.lean", "import MIPStarRE.Foo\n")
        write(self.repo / "MIPStarRE" / "Foo.lean", LEAN_MAIN)
        write(self.repo / "MIPStarRE" / "Bar.lean", LEAN_BAR)
        write(self.repo / "lean-toolchain", "leanprover/lean4:v4.32.0\n")
        write(self.repo / "lakefile.toml", 'name = "MIPStarRE"\n')
        write(self.repo / "lake-manifest.json", json.dumps(
            {"packages": [{"name": "mathlib", "rev": "deadbeefcafe"}]}))
        write(self.repo / "README.md", "See https://github.com/Dengnifer/MIPStarRE-A\n")
        write(self.repo / "docs" / "comparator.md", "trust model\n")
        # Third-party paper sources: they ship (owner decision, 2026-09-19).
        write(self.repo / "references" / "qpbt-paper" / "frontmatter.tex",
              "\\title{A paper}\n")
        # The workflow layer: excluded by the allow-list, and carrying exactly
        # the kind of home path the leak scan exists to catch.
        write(self.repo / "local" / "bin" / "tool.sh", "cd /home/somebody/checkout\n")
        write(self.repo / "results" / "telemetry" / "builds.jsonl", '{"ok":true}\n')
        self.commit()

    def commit(self, message: str = "test") -> str:
        git(self.repo, "add", "-A")
        git(self.repo, "commit", "-q", "--no-verify", "-m", message)
        return git(self.repo, "rev-parse", "HEAD")

    def run_script(self, *args: str) -> subprocess.CompletedProcess:
        return subprocess.run(
            ["bash", str(SCRIPT), *args, "HEAD", str(self.out)],
            capture_output=True, text=True,
            env={"PATH": "/usr/bin:/bin:/usr/local/bin", "HOME": str(self.tmp),
                 "MIPSTARRE_REPO_ROOT": str(self.repo)},
        )

    def members(self) -> list[str]:
        """Snapshot-relative paths inside the one tarball in the out directory."""
        tarballs = sorted(self.out.glob("*.tar.gz"))
        self.assertEqual(len(tarballs), 1, f"expected one tarball, got {tarballs}")
        with tarfile.open(tarballs[0]) as archive:
            return [name.split("/", 1)[1] for name in archive.getnames() if "/" in name]

    # -- what ships ---------------------------------------------------------

    def test_packages_the_development_and_drops_the_workflow_layer(self) -> None:
        head = git(self.repo, "rev-parse", "HEAD")
        result = self.run_script()
        self.assertEqual(result.returncode, 0, result.stderr)
        names = self.members()
        for shipped in ("MIPStarRE/Foo.lean", "MIPStarRE/Bar.lean", "MIPStarRE.lean",
                        "lean-toolchain", "README.md", "MANIFEST.txt"):
            self.assertIn(shipped, names)
        for excluded in ("local/bin/tool.sh", "results/telemetry/builds.jsonl"):
            self.assertNotIn(excluded, names)
        self.assertIn(head, result.stdout)
        self.assertIn("sha256", result.stdout)

    def test_the_paper_sources_ship(self) -> None:
        """They are what the docstring `file.tex:lines` locators point at."""
        self.assertEqual(self.run_script().returncode, 0)
        self.assertIn("references/qpbt-paper/frontmatter.tex", self.members())

    def test_manifest_records_toolchain_mathlib_and_lean_code_lines(self) -> None:
        self.assertEqual(self.run_script().returncode, 0)
        manifest = next(self.out.glob("*.MANIFEST.txt")).read_text(encoding="utf-8")
        self.assertIn("leanprover/lean4:v4.32.0", manifest)
        self.assertIn("deadbeefcafe", manifest)
        self.assertIn("Lean files        : 3", manifest)
        # Foo.lean: import + theorem are code, the two doc-comment lines and the
        # blank lines are not; Bar.lean and MIPStarRE.lean are one line each.
        self.assertIn("Lean code lines   : 4 ", manifest)

    def test_reports_an_import_that_is_not_in_the_snapshot(self) -> None:
        (self.repo / "MIPStarRE" / "Bar.lean").unlink()
        self.commit("drop Bar")
        self.assertEqual(self.run_script().returncode, 0)
        manifest = next(self.out.glob("*.MANIFEST.txt")).read_text(encoding="utf-8")
        self.assertIn("self-contained    : NO", manifest)
        self.assertIn("MIPStarRE.Bar", manifest)

    # -- the leak scan ------------------------------------------------------

    def test_a_home_path_in_a_shipped_file_fails_the_run(self) -> None:
        write(self.repo / "docs" / "notes.md", "built under /home/somebody/checkout\n")
        self.commit("plant a leak")
        result = self.run_script()
        self.assertEqual(result.returncode, 2, result.stdout)
        self.assertIn("LEAK SCAN FAILED", result.stderr)
        self.assertIn("docs/notes.md", result.stderr)
        self.assertEqual(sorted(self.out.glob("*.tar.gz")), [],
                         "a leaking snapshot must not be packaged")

    def test_a_key_shaped_string_fails_the_run(self) -> None:
        write(self.repo / "docs" / "notes.md", "token ghp_0123456789abcdefghijklmnopqrst\n")
        self.commit("plant a key")
        self.assertEqual(self.run_script().returncode, 2)

    def test_the_allow_list_forgives_a_placeholder_address(self) -> None:
        write(self.repo / "docs" / "notes.md", "write to nobody@example.invalid\n")
        self.commit("placeholder address")
        self.assertEqual(self.run_script().returncode, 0)

    def test_an_author_address_is_forgiven_in_the_paper_sources_only(self) -> None:
        """The `references/` forgiveness must be scoped by path, not blanket.

        The papers print their corresponding authors' addresses; an address in a
        file of ours is still a leak, and the scan has to keep catching it.
        """
        write(self.repo / "references" / "qpbt-paper" / "frontmatter.tex",
              "\\email{someone@some-university.edu}\n")
        self.commit("an address in the paper source")
        self.assertEqual(self.run_script().returncode, 0)

        write(self.repo / "docs" / "notes.md", "write to someone@some-university.edu\n")
        self.commit("the same address in a page of ours")
        result = self.run_script()
        self.assertEqual(result.returncode, 2, result.stdout)
        self.assertIn("docs/notes.md", result.stderr)
        self.assertNotIn("references/qpbt-paper/frontmatter.tex", result.stderr)

    def test_a_home_path_in_the_paper_sources_still_fails_the_run(self) -> None:
        """The forgiveness is scoped by content too: only addresses."""
        write(self.repo / "references" / "qpbt-paper" / "frontmatter.tex",
              "%% typeset in /home/somebody/tex\n")
        self.commit("a home path in the paper source")
        result = self.run_script()
        self.assertEqual(result.returncode, 2, result.stdout)
        self.assertIn("references/qpbt-paper/frontmatter.tex", result.stderr)

    def test_a_home_path_inside_a_pdf_fails_the_run(self) -> None:
        """The scan must read the PDFs it ships, not skip them as binaries."""
        if shutil.which("pdftotext") is None:
            self.skipTest("pdftotext (poppler-utils) is not installed")
        pdf = self.repo / "docs" / "paper-gaps" / "note.pdf"
        pdf.parent.mkdir(parents=True, exist_ok=True)
        pdf.write_bytes(minimal_pdf("/home/somebody/checkout"))
        self.commit("plant a leak inside a PDF")
        result = self.run_script()
        self.assertEqual(result.returncode, 2, result.stdout)
        self.assertIn("LEAK SCAN FAILED", result.stderr)
        self.assertIn("docs/paper-gaps/note.pdf", result.stderr)
        self.assertEqual(sorted(self.out.glob("*.tar.gz")), [],
                         "a snapshot leaking through a PDF must not be packaged")

    # -- shipped pages ------------------------------------------------------

    def test_the_manifest_reports_a_link_to_a_page_that_does_not_ship(self) -> None:
        write(self.repo / "docs" / "notes.md", "see [the plan](plan.md)\n")
        self.commit("link a page that is not in the snapshot")
        self.assertEqual(self.run_script().returncode, 0)
        manifest = next(self.out.glob("*.MANIFEST.txt")).read_text(encoding="utf-8")
        self.assertIn("internal links    : 1 dead of 1 checked", manifest)

    # -- anonymization ------------------------------------------------------

    def test_anonymize_rewrites_the_owner_name_and_tags_the_tarball(self) -> None:
        result = self.run_script("--anonymize")
        self.assertEqual(result.returncode, 0, result.stderr)
        tarball = next(self.out.glob("*.tar.gz"))
        self.assertIn("-anon", tarball.name)
        with tarfile.open(tarball) as archive:
            member = next(m for m in archive.getnames() if m.endswith("README.md"))
            text = archive.extractfile(member).read().decode("utf-8")
        self.assertNotIn("Dengnifer", text)
        self.assertIn("ANONYMIZED", text)

    def test_an_unresolvable_ref_is_a_usage_error(self) -> None:
        result = subprocess.run(
            ["bash", str(SCRIPT), "no-such-ref", str(self.out)],
            capture_output=True, text=True,
            env={"PATH": "/usr/bin:/bin:/usr/local/bin", "HOME": str(self.tmp),
                 "MIPSTARRE_REPO_ROOT": str(self.repo)},
        )
        self.assertEqual(result.returncode, 1)
        self.assertIn("cannot resolve git ref", result.stderr)


if __name__ == "__main__":
    unittest.main()
