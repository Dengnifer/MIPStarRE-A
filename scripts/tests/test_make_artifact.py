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
import sys
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

    The header carries the binary-marker comment that real PDF writers emit,
    with a NUL byte in it, and that byte is what makes this a binary at all: a
    hand-built PDF is otherwise plain ASCII, which the script would classify as
    text and happily rewrite in place, so a test built on one would exercise
    the text path and prove nothing about binaries. A comment is ignored by
    every reader, so the file stays valid.
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
    out = bytearray(b"%PDF-1.4\n%\xe2\xe3\xcf\xd3\x00\n")
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
        write(self.repo / "README.md", "See https://github.com/Dengnifer/MIPStarRE-QPBT\n")
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
        # Start from an empty output directory every time.  A test that runs the
        # script twice commits in between, so the second run writes a tarball and
        # a MANIFEST under a *different* commit-derived name beside the first
        # ones; `self.out.glob(...)` then returns them in an unspecified order
        # and an assertion about the second run may read the first run's file.
        shutil.rmtree(self.out, ignore_errors=True)
        return subprocess.run(
            ["bash", str(SCRIPT), *args, "HEAD", str(self.out)],
            capture_output=True, text=True,
            env={"PATH": "/usr/bin:/bin:/usr/local/bin", "HOME": str(self.tmp),
                 "MIPSTARRE_REPO_ROOT": str(self.repo)},
        )

    def install_packaging_script(self, suffix: str = "") -> Path:
        """Install the real packaging script in the fixture repository."""
        shipped = self.repo / "scripts" / "make_artifact.sh"
        write(shipped, SCRIPT.read_text(encoding="utf-8") + suffix)
        return shipped

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

    def test_blueprint_audit_runs_from_extracted_snapshot(self) -> None:
        """The shipped entry point must import its helpers through both export guards."""
        shutil.copyfile(SCRIPT.parent.parent / ".gitattributes",
                        self.repo / ".gitattributes")
        for name in ("blueprint_leanok_axioms.py", "blueprint_lean_sync.py", "tex_utils.py"):
            write(self.repo / "scripts" / name,
                  (SCRIPT.parent / name).read_text(encoding="utf-8"))
        write(self.repo / "blueprint" / "src" / "chapter" / "test.tex",
              "\\begin{theorem}\\label{thm:foo}\n"
              "\\lean{foo}\\leanok % \\lean{not_a_declaration}\n"
              "\\end{theorem}\n")
        self.commit("ship the blueprint audit and its Python helpers")

        for args in ((), ("--anonymize",)):
            with self.subTest(args=args):
                result = self.run_script("--no-pdf", *args)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                unpacked = self.out / "unpacked"
                unpacked.mkdir()
                subprocess.run(
                    ["tar", "-xzf", str(next(self.out.glob("*.tar.gz"))),
                     "-C", str(unpacked)], check=True,
                )
                snapshot = next(unpacked.iterdir())
                audit = subprocess.run(
                    [sys.executable, "-E", "-s", "-B", "scripts/blueprint_leanok_axioms.py",
                     "--ci", "--skip-axiom-check"],
                    cwd=snapshot, capture_output=True, text=True, timeout=30,
                )
                self.assertEqual(audit.returncode, 0, audit.stdout + audit.stderr)
                self.assertIn("Parsed 1 blueprint", audit.stdout)
                self.assertIn("1 carry at least one \\leanok tag.", audit.stdout)
                self.assertIn("Axiom check skipped (--skip-axiom-check).", audit.stdout)

    def test_manifest_records_toolchain_mathlib_and_lean_code_lines(self) -> None:
        self.assertEqual(self.run_script().returncode, 0)
        manifest = next(self.out.glob("*.MANIFEST.txt")).read_text(encoding="utf-8")
        self.assertIn("leanprover/lean4:v4.32.0", manifest)
        self.assertIn("deadbeefcafe", manifest)
        self.assertIn("source repository : Dengnifer/MIPStarRE-QPBT", manifest)
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

    def test_the_allow_list_forgives_exact_placeholder_addresses(self) -> None:
        for domain in ("example.com", "example.org", "example.invalid"):
            with self.subTest(domain=domain):
                write(self.repo / "docs" / "notes.md", f"write to nobody@{domain}\n")
                self.commit(f"placeholder address {domain}")
                self.assertEqual(self.run_script().returncode, 0)

    def test_placeholder_domain_suffix_is_rejected_in_both_modes(self) -> None:
        """A reserved-domain prefix does not make the complete address safe."""
        contact = "ruixuan.deng@icloud.com"
        unrelated = "reviewer@example.com.private-mail.net"
        self.install_packaging_script(
            f"\n# planted mixed address line: {contact} {unrelated}\n")
        self.commit("plant placeholder-domain suffix address")

        for args in ((), ("--anonymize",)):
            with self.subTest(args=args):
                result = self.run_script(*args)
                self.assertEqual(result.returncode, 2, result.stdout)
                self.assertIn("LEAK SCAN FAILED", result.stderr)
                self.assertIn(unrelated, result.stderr)
                self.assertEqual(sorted(self.out.glob("*.tar.gz")), [],
                                 "a suffix address must not be packaged")

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

    def test_an_unrelated_address_in_the_shipped_script_fails_the_run(self) -> None:
        """Only the configured rule contact, not every script address, is safe."""
        unrelated = "unrelated.person@private.example"
        self.install_packaging_script(f"\n# planted unrelated address: {unrelated}\n")
        self.commit("plant an unrelated address in the shipped script")

        result = self.run_script()
        self.assertEqual(result.returncode, 2, result.stdout)
        self.assertIn("LEAK SCAN FAILED", result.stderr)
        self.assertIn(unrelated, result.stderr)
        self.assertEqual(sorted(self.out.glob("*.tar.gz")), [],
                         "an unrelated script address must not be packaged")

    def test_anonymize_rejects_an_unrelated_address_beside_the_rule_contact(self) -> None:
        """One permitted match on a line must not launder another address."""
        contact = "ruixuan.deng@icloud.com"
        unrelated = "unrelated.person@private.example"
        self.install_packaging_script(
            f"\n# planted mixed address line: {contact} {unrelated}\n")
        self.commit("plant mixed addresses in the shipped script")

        result = self.run_script("--anonymize")
        self.assertEqual(result.returncode, 2, result.stdout)
        self.assertIn("LEAK SCAN FAILED", result.stderr)
        self.assertIn(unrelated, result.stderr)
        self.assertNotIn(contact, result.stderr)
        self.assertEqual(sorted(self.out.glob("*.tar.gz")), [],
                         "an unrelated script address must not be packaged anonymously")

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

    # -- the gap-note PDF build ---------------------------------------------

    def test_the_latexmk_intermediates_are_pruned(self) -> None:
        """Only the PDFs are part of the artifact.

        `.fls` and `.fdb_latexmk` also record the absolute path of the directory
        the build ran in, so shipping them would put the build host's home
        directory into a release cut with TMPDIR under a home.  A stand-in
        Makefile stands for latexmk here: what is under test is the pruning.
        """
        if shutil.which("pdftotext") is None:
            self.skipTest("pdftotext (poppler-utils) is not installed")
        gaps = self.repo / "docs" / "paper-gaps"
        (gaps / "note.pdf").parent.mkdir(parents=True, exist_ok=True)
        (gaps / "note.pdf").write_bytes(minimal_pdf("a gap note"))
        # The stand-in writes a plain `.fls`: a real one would name the build
        # directory's absolute path, which the scan would catch here rather than
        # letting the assertion below do the work.
        write(gaps / "Makefile",
              "all:\n\tmkdir -p build\n\tcp note.pdf build/note.pdf\n"
              "\tprintf 'INPUT note.tex\\n' > build/note.fls\n")
        self.commit("a gap-note build that leaves intermediates")
        result = self.run_script()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        names = self.members()
        self.assertIn("docs/paper-gaps/build/note.pdf", names)
        self.assertNotIn("docs/paper-gaps/build/note.fls", names)
        self.assertIn("docs/paper-gaps/note.pdf", names)

    # -- shipped pages ------------------------------------------------------

    def test_the_manifest_reports_a_link_to_a_page_that_does_not_ship(self) -> None:
        write(self.repo / "docs" / "notes.md", "see [the plan](plan.md)\n")
        self.commit("link a page that is not in the snapshot")
        self.assertEqual(self.run_script().returncode, 0)
        manifest = next(self.out.glob("*.MANIFEST.txt")).read_text(encoding="utf-8")
        self.assertIn("internal links    : 1 dead of 1 checked", manifest)

    def test_the_manifest_reports_a_paper_locator_that_does_not_resolve(self) -> None:
        """A docstring locator is now a path a reviewer can open."""
        write(self.repo / "MIPStarRE" / "Bar.lean",
              "/-- Paper origin: `references/qpbt-paper/frontmatter.tex`. -/\n"
              "theorem bar : True := trivial\n")
        self.commit("a locator that resolves")
        self.assertEqual(self.run_script().returncode, 0)
        manifest = next(self.out.glob("*.MANIFEST.txt")).read_text(encoding="utf-8")
        self.assertIn("paper locators    : all 1 cited files are in the snapshot",
                      manifest)

        write(self.repo / "MIPStarRE" / "Bar.lean",
              "/-- Paper origin: `references/qpbt-paper/no-such-section.tex`. -/\n"
              "theorem bar : True := trivial\n")
        self.commit("a locator that does not resolve")
        self.assertEqual(self.run_script().returncode, 0)
        manifest = next(self.out.glob("*.MANIFEST.txt")).read_text(encoding="utf-8")
        self.assertIn("1 of 1 cited files absent", manifest)
        self.assertIn("references/qpbt-paper/no-such-section.tex", manifest)

    # -- anonymization ------------------------------------------------------

    def test_anonymize_rewrites_the_owner_name_and_tags_the_tarball(self) -> None:
        # Historical links remain in evidence; both aliases must anonymize.
        write(self.repo / "README.md", "\n".join(
            f"https://{host}/{slug}/issues/705"
            for host in ("github.com/Dengnifer", "dengnifer.github.io")
            for slug in ("MIPStarRE-A", "MIPStarRE-QPBT")
        ) + "\n")
        self.commit("exercise current and historical repository aliases")
        result = self.run_script("--anonymize")
        self.assertEqual(result.returncode, 0, result.stderr)
        tarball = next(self.out.glob("*.tar.gz"))
        self.assertIn("-anon", tarball.name)
        with tarfile.open(tarball) as archive:
            member = next(m for m in archive.getnames() if m.endswith("README.md"))
            text = archive.extractfile(member).read().decode("utf-8")
        self.assertNotIn("Dengnifer", text)
        self.assertNotIn("dengnifer.github.io", text)
        self.assertIn("ANONYMIZED", text)
        self.assertIn("anonymized.example.invalid", text)
        manifest = next(self.out.glob("*.MANIFEST.txt")).read_text(encoding="utf-8")
        self.assertIn("source repository : ANONYMIZED/MIPStarRE-QPBT", manifest)
        self.assertNotIn("Dengnifer", manifest)

    def test_anonymize_rewrites_the_rules_inside_the_shipped_script(self) -> None:
        """The script ships, so the pass runs over its own rules block.

        The rules used to be stored pre-escaped for `sed`, which meant each one
        matched the plain string everywhere else in the tree and never its own
        spelling here: the address the rule exists to remove rode out in the
        rules list of the shipped copy, and nothing said so.
        """
        self.install_packaging_script()
        self.commit("ship the packaging script, as the real repository does")
        # Plain run first: the rules name the owner's address literally now, so
        # the path-scoped allow-list entry for this one file has to hold, or no
        # release could be cut at all.
        self.assertEqual(self.run_script().returncode, 0)
        result = self.run_script("--anonymize")
        self.assertEqual(result.returncode, 0, result.stderr)
        with tarfile.open(next(self.out.glob("*.tar.gz"))) as archive:
            member = next(m for m in archive.getnames()
                          if m.endswith("scripts/make_artifact.sh"))
            text = archive.extractfile(member).read().decode("utf-8")
        for rule_text in ("Dengnifer", "dengnifer.github.io", "LionSR", "Ruixuan Deng",
                          "ruixuan.deng@icloud.com", "sirui-lu.com"):
            self.assertNotIn(rule_text, text, f"{rule_text!r} survived in the shipped script")
            escaped = rule_text.replace(".", r"\.")
            self.assertNotIn(escaped, text,
                             f"escaped spelling {escaped!r} survived in the shipped script")

    def test_anonymize_rejects_an_escaped_rule_in_the_shipped_script(self) -> None:
        """A regex-escaped identity is still readable and must fail the run."""
        rule_text = "ruixuan.deng@icloud.com"
        escaped = rule_text.replace(".", r"\.")
        self.install_packaging_script(f"\n# planted escaped rule spelling: {escaped}\n")
        self.commit("plant an escaped anonymization rule in the shipped script")

        result = self.run_script("--anonymize")
        self.assertEqual(result.returncode, 2, result.stdout)
        self.assertIn("ANONYMIZATION INCOMPLETE", result.stderr)
        self.assertIn("scripts/make_artifact.sh", result.stderr)
        self.assertIn(escaped, result.stderr)
        self.assertEqual(sorted(self.out.glob("*.tar.gz")), [],
                         "an escaped rule spelling must not be packaged")

    def test_a_rule_string_surviving_in_a_pdf_fails_the_run(self) -> None:
        """`sed` cannot reach inside a binary, so the check has to catch it.

        A tracked PDF is the one shipped file the anonymization pass cannot
        rewrite. Before this guard the run packaged it anyway; the leak scan
        would not have caught it either, since a name is neither address- nor
        key-shaped.
        """
        if shutil.which("pdftotext") is None:
            self.skipTest("pdftotext (poppler-utils) is not installed")
        pdf = self.repo / "docs" / "paper-gaps" / "note.pdf"
        pdf.parent.mkdir(parents=True, exist_ok=True)
        for identity in ("Ruixuan Deng", "Dengnifer/MIPStarRE-A",
                         "Dengnifer/MIPStarRE-QPBT", "dengnifer.github.io"):
            with self.subTest(identity=identity):
                pdf.write_bytes(minimal_pdf(identity))
                self.commit("an identity baked into a binary")
                self.assertEqual(self.run_script().returncode, 0,
                                 "without --anonymize the identity is not a leak")
                result = self.run_script("--anonymize")
                self.assertEqual(result.returncode, 2, result.stdout)
                self.assertIn("ANONYMIZATION INCOMPLETE", result.stderr)
                self.assertIn("docs/paper-gaps/note.pdf", result.stderr)
                self.assertEqual(sorted(self.out.glob("*.tar.gz")), [],
                                 "an incompletely anonymized snapshot must not be packaged")

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
