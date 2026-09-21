#!/usr/bin/env python3
"""Regression tests for scripts/bootstrap_project.py.

Everything runs on a miniature kit tree built in a temporary directory: the
placeholder token in files that must change and in the two directories that
must not, the environment prefix that must survive, the blueprint and
paper-gap identity, and the refusal to bootstrap the same checkout twice.
No network, no git, no GitHub (`--keep-git` keeps the git step out).
"""

from __future__ import annotations

import io
import json
import sys
import tempfile
import unittest
from contextlib import redirect_stdout, redirect_stderr
from pathlib import Path
from unittest import mock

SCRIPT_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPT_DIR))

import bootstrap_project as bootstrap  # noqa: E402

#: The kit's placeholders, taken from the script, never spelled as literals:
#: `bootstrap_project.py` rewrites the literals across the whole tree, this file
#: included, so a fixture or an assertion that spelled them would silently talk
#: about the instantiated project's own names instead of the placeholders.
ROOT_TOKEN = bootstrap.PLACEHOLDER_ROOT
SLUG_TOKEN = bootstrap.PLACEHOLDER_SLUG
COMPARATOR_TOKEN = bootstrap.PLACEHOLDER_COMPARATOR
OWNER_TOKEN, REPO_TOKEN = SLUG_TOKEN.split("/", 1)


def fill(text: str) -> str:
    """Put the placeholder tokens into a fixture written with @@NAME@@ marks."""
    for mark, value in (("@@ROOT@@", ROOT_TOKEN), ("@@COMPARATOR@@", COMPARATOR_TOKEN),
                        ("@@SLUG@@", SLUG_TOKEN), ("@@OWNER@@", OWNER_TOKEN),
                        ("@@REPO@@", REPO_TOKEN)):
        text = text.replace(mark, value)
    return text


WEB_TEX = """% Web version of the blueprint.
\\documentclass{report}
\\home{https://EXAMPLE.github.io/@@ROOT@@}
\\github{https://github.com/EXAMPLE/@@ROOT@@}
\\dochome{https://EXAMPLE.github.io/@@ROOT@@/docs}

\\title{Blueprint for arXiv:0000.00000\\\\
\\textit{The placeholder paper}}
\\author{@@ROOT@@ Project}

\\begin{document}
\\input{content}
\\end{document}
"""

TEXRA_TOML = """# Configuration for the shared texra-blueprint tooling.

[paper_gaps]
dir         = "docs/paper-gaps"
site_base   = "https://example.invalid/@@ROOT@@"
blob_base   = "https://github.com/EXAMPLE/@@ROOT@@/blob/main/docs/paper-gaps"
bib_author  = "The {@@ROOT@@} contributors"
institution = "@@ROOT@@"
title       = "@@ROOT@@ paper-gap notes"
scan_roots  = ["@@ROOT@@", "blueprint/src", "docs"]
skip        = ["command.tex", "template.tex"]

# A long comment about the previous project's source keys, which describes
# notes that are not in this tree any more.
[paper_gaps.sources]
stale = "arXiv:0000.00000 (a paper this repository does not carry)"
proof-gap = "protocol for source-faithful formalization (instructional document)"

[paper_gaps.aliases]
stale = "stale-old-name"
"""

SITE_YML = """# placeholders until the project is instantiated
title: "@@ROOT@@"
description: A formal verification in Lean 4 using Mathlib
baseurl: "/REPO"
url: "https://@@OWNER@@.github.io"
github_username: @@OWNER@@
repository: @@SLUG@@
remote_theme: pages-themes/cayman@v0.2.0
"""

KEEP_PY = """#!/usr/bin/env python3
'''A tool that mentions the Lean root and the environment prefix.'''
import os
ROOT = "@@ROOT@@"
CACHE = os.environ.get("MIPSTARRE_CACHE_ROOT", "~/.cache/mipstarre-dev")
SLUG = "@@SLUG@@"
COMPARATOR = "@@COMPARATOR@@"
"""


def build_tree(root: Path) -> Path:
    def write(relative: str, text: str) -> None:
        path = root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    write("lean-toolchain", "leanprover/lean4:v4.32.0\n")
    write("lakefile.toml", fill('name = "@@ROOT@@"\ndefaultTargets = ["@@ROOT@@"]\n'))
    write(f"{ROOT_TOKEN}.lean", fill("import @@ROOT@@.Basic\n"))
    write(f"{ROOT_TOKEN}/Basic.lean", "theorem stub : True := trivial\n")
    write("scripts/keep.py", fill(KEEP_PY))
    write("local/project.json", json.dumps(bootstrap.default_config(), indent=2) + "\n")
    write("local/kit/extract.sh", fill("# how @@ROOT@@ and @@SLUG@@ were stripped\n"))
    write("docs/origin/EVOLUTION-origin.md",
          fill("The @@ROOT@@ origin ledger, @@SLUG@@.\n"))
    write("docs/CONTRIBUTING.md",
          fill("Work on @@ROOT@@ happens at @@SLUG@@; the comparator is "
               "@@COMPARATOR@@.\n"))
    write("docs/paper-gaps/proof-gap-protocol.tex", "% the instructional note\n")
    write("README.md", "# The formalization kit\n\nClone this and bootstrap it.\n")
    write("blueprint/src/web.tex", fill(WEB_TEX))
    write("blueprint/src/print.tex", fill(WEB_TEX).replace("Web version", "PDF version"))
    write("texra-blueprint.toml", fill(TEXRA_TOML))
    write("home_page/_config.yml", fill(SITE_YML))
    (root / "blueprint" / "src" / "logo.png").write_bytes(
        b"\x00\x01" + ROOT_TOKEN.encode() + b"\x00")
    return root


def snapshot(root: Path) -> dict[str, bytes]:
    return {p.relative_to(root).as_posix(): p.read_bytes()
            for p in sorted(root.rglob("*")) if p.is_file()}


def run(*argv: str) -> tuple[int, str, str]:
    out, err = io.StringIO(), io.StringIO()
    with redirect_stdout(out), redirect_stderr(err):
        with mock.patch.object(bootstrap, "fetch_and_split", lambda *a, **k: None):
            rc = bootstrap.main(list(argv))
    return rc, out.getvalue(), err.getvalue()


class ValidationTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.root = build_tree(Path(self.tmp.name) / "kit")
        self.addCleanup(self.tmp.cleanup)

    def bootstrap(self, *extra: str) -> tuple[int, str, str]:
        return run("--lean-root", "Demo", "--github-slug", "someone/demo-paper",
                   "--root", str(self.root), "--keep-git", *extra)

    def test_a_name_that_is_not_a_lean_identifier_is_refused(self) -> None:
        for name in ("demo", "My.Paper", "2Demo", "My Paper"):
            with self.subTest(name=name):
                rc, _, err = run("--lean-root", name, "--github-slug", "a/b",
                                 "--root", str(self.root), "--keep-git")
                self.assertEqual(rc, 2)
                self.assertIn("Lean library root", err)

    def test_a_lean_or_mathlib_namespace_is_refused(self) -> None:
        for name in ("Mathlib", "Std", "Lean", "Set", ROOT_TOKEN):
            with self.subTest(name=name):
                rc, _, err = run("--lean-root", name, "--github-slug", "a/b",
                                 "--root", str(self.root), "--keep-git")
                self.assertEqual(rc, 2)
                self.assertIn("Pick a name", err)

    def test_a_malformed_slug_is_refused(self) -> None:
        rc, _, err = run("--lean-root", "Demo", "--github-slug", "not-a-slug",
                         "--root", str(self.root), "--keep-git")
        self.assertEqual(rc, 2)
        self.assertIn("owner/repo", err)

    def test_a_directory_that_is_not_the_kit_is_refused(self) -> None:
        rc, _, err = run("--lean-root", "Demo", "--github-slug", "a/b",
                         "--root", str(self.root.parent), "--keep-git")
        self.assertEqual(rc, 2)
        self.assertIn("kit checkout", err)

    def test_dry_run_changes_nothing_and_counts_what_it_would_change(self) -> None:
        before = snapshot(self.root)
        rc, out, _ = self.bootstrap("--dry-run")
        self.assertEqual(rc, 0)
        self.assertEqual(snapshot(self.root), before)
        self.assertIn(f"{ROOT_TOKEN} -> Demo", out)
        self.assertIn("files rewritten", out)
        self.assertIn(f"{ROOT_TOKEN}.lean -> Demo.lean", out)
        self.assertIn("dry run: nothing was written", out)

    def test_bootstrapping_twice_is_refused_unless_forced(self) -> None:
        self.assertEqual(self.bootstrap()[0], 0)
        rc, _, err = self.bootstrap()
        self.assertEqual(rc, 2)
        self.assertIn("already the project 'Demo'", err)
        self.assertEqual(self.bootstrap("--force")[0], 0)


class RenameTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.root = build_tree(Path(self.tmp.name) / "kit")
        self.addCleanup(self.tmp.cleanup)
        self.rc, self.out, self.err = run(
            "--lean-root", "Demo", "--github-slug", "someone/demo-paper",
            "--arxiv", "https://arxiv.org/abs/1234.56789v2",
            "--title", "A demo paper", "--root", str(self.root), "--keep-git")

    def read(self, relative: str) -> str:
        return (self.root / relative).read_text(encoding="utf-8")

    def test_it_succeeds(self) -> None:
        self.assertEqual(self.rc, 0, self.err)

    def test_the_lean_root_is_renamed_in_files_and_in_paths(self) -> None:
        self.assertFalse((self.root / f"{ROOT_TOKEN}.lean").exists())
        self.assertFalse((self.root / ROOT_TOKEN).exists())
        self.assertEqual(self.read("Demo.lean"), "import Demo.Basic\n")
        self.assertTrue((self.root / "Demo" / "Basic.lean").is_file())
        self.assertIn('name = "Demo"', self.read("lakefile.toml"))

    def test_the_environment_prefix_and_cache_name_are_left_alone(self) -> None:
        """They are per-machine, not per-project; projects differ by cache_root."""
        keep = self.read("scripts/keep.py")
        self.assertIn("MIPSTARRE_CACHE_ROOT", keep)
        self.assertIn("mipstarre-dev", keep)
        self.assertIn('ROOT = "Demo"', keep)

    def test_both_slugs_are_rewritten_longest_first(self) -> None:
        contributing = self.read("docs/CONTRIBUTING.md")
        self.assertIn("someone/demo-paper-comparator", contributing)
        self.assertIn("at someone/demo-paper;", contributing)
        # The placeholder CONSTANT, never the literal: this file is rewritten too.
        self.assertNotIn(SLUG_TOKEN, contributing)

    def test_the_origin_ledger_and_the_kit_record_are_never_rewritten(self) -> None:
        ledger = self.read("docs/origin/EVOLUTION-origin.md")
        self.assertIn(ROOT_TOKEN, ledger)
        self.assertIn(SLUG_TOKEN, ledger)
        self.assertIn(ROOT_TOKEN, self.read("local/kit/extract.sh"))

    def test_binary_files_are_not_touched(self) -> None:
        self.assertEqual((self.root / "blueprint" / "src" / "logo.png").read_bytes(),
                         b"\x00\x01" + ROOT_TOKEN.encode() + b"\x00")

    def test_project_json_describes_the_project(self) -> None:
        config = json.loads(self.read("local/project.json"))
        self.assertEqual(config["project"]["name"], "Demo")
        self.assertEqual(config["project"]["lean_root"], "Demo")
        self.assertEqual(config["project"]["github_slug"], "someone/demo-paper")
        self.assertEqual(config["project"]["comparator_slug"],
                         "someone/demo-paper-comparator")
        self.assertEqual(config["project"]["arxiv"], ["1234.56789"])
        self.assertEqual(config["project"]["title"], "A demo paper")
        self.assertEqual(config["paths"]["cache_root"], "~/.cache/demo-dev")
        self.assertEqual(config["session"]["tmux"], "demo")
        self.assertEqual(config["paper_mirrors"], ["demo"])
        self.assertIsNone(config["issues"]["tracker_root"])

    def test_the_track_carries_the_completion_gate_fields(self) -> None:
        track = json.loads(self.read("local/project.json"))["tracks"]["main"]
        self.assertEqual(sorted(track), [
            "artifact_files", "artifact_script", "axiom_audit", "blueprint_chapters",
            "comparator_doc", "expected_challenge", "gap_register", "headline",
            "lean_root", "leanok_exemptions", "name", "truthful_docs",
        ])
        self.assertEqual(track["lean_root"], "Demo")
        self.assertEqual(track["axiom_audit"], "Demo/Test/AxiomAudit.lean")
        self.assertEqual(track["headline"], [])
        self.assertEqual(track["blueprint_chapters"], [])
        self.assertEqual(track["expected_challenge"],
                         "scripts/comparator/expected/Challenge.lean.expected")

    def test_the_blueprint_carries_this_project_s_identity(self) -> None:
        for relative in ("blueprint/src/web.tex", "blueprint/src/print.tex"):
            with self.subTest(file=relative):
                text = self.read(relative)
                self.assertIn("\\home{https://someone.github.io/demo-paper}", text)
                self.assertIn("\\github{https://github.com/someone/demo-paper}", text)
                self.assertIn("\\dochome{https://someone.github.io/demo-paper/docs}", text)
                self.assertIn("Blueprint for arXiv:1234.56789", text)
                self.assertIn("\\textit{A demo paper}", text)
                self.assertIn("\\author{The Demo contributors}", text)
                self.assertNotIn("0000.00000", text)

    def test_the_paper_gap_registry_describes_this_paper_only(self) -> None:
        text = self.read("texra-blueprint.toml")
        self.assertIn('site_base   = "https://someone.github.io/demo-paper"', text)
        self.assertIn('blob_base   = "https://github.com/someone/demo-paper'
                      '/blob/main/docs/paper-gaps"', text)
        self.assertIn('bib_author  = "The {Demo} contributors"', text)
        self.assertIn('title       = "Demo paper-gap notes"', text)
        self.assertIn('scan_roots  = ["Demo", "blueprint/src", "docs"]', text)
        self.assertIn('demo = "arXiv:1234.56789 (A demo paper)"', text)
        # kept: its note is still in the tree.  dropped: nothing carries it.
        self.assertIn("proof-gap =", text)
        self.assertNotIn("stale", text)

    def test_the_pages_site_names_this_project(self) -> None:
        text = self.read("home_page/_config.yml")
        self.assertIn('title: "A demo paper"', text)
        self.assertIn('baseurl: "/demo-paper"', text)
        self.assertIn('url: "https://someone.github.io"', text)
        self.assertIn("github_username: someone", text)
        self.assertIn("repository: someone/demo-paper", text)
        self.assertNotIn(OWNER_TOKEN, text)
        # untouched keys stay as they are
        self.assertIn("remote_theme: pages-themes/cayman@v0.2.0", text)

    def test_the_kit_readme_becomes_docs_kit_md_and_a_project_readme_is_written(self):
        self.assertIn("The formalization kit", self.read("docs/KIT.md"))
        readme = self.read("README.md")
        self.assertTrue(readme.startswith("# Demo\n"))
        self.assertIn("arXiv:1234.56789", readme)
        self.assertIn("references/demo-paper/", readme)
        self.assertIn("no mathematics is formalized yet", readme)
        self.assertIn("leanprover/lean4:v4.32.0", readme)

    def test_it_prints_the_two_commands_that_need_the_owner_s_word(self) -> None:
        self.assertIn("gh repo create someone/demo-paper", self.out)
        self.assertIn("git push -u github main", self.out)
        self.assertIn("Nothing was created on GitHub", self.out)


class MirrorFailureTests(unittest.TestCase):
    def test_a_failed_paper_mirror_leaves_the_project_instantiated_and_says_so(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        root = build_tree(Path(tmp.name) / "kit")

        def explode(*_a, **_k):
            raise bootstrap.Refused("no network; run: python3 scripts/"
                                    "fetch_arxiv_source.py 1234.56789 --dest X")

        out = io.StringIO()
        with redirect_stdout(out), mock.patch.object(bootstrap, "fetch_and_split", explode):
            rc = bootstrap.main(["--lean-root", "Demo", "--github-slug", "someone/demo",
                                 "--arxiv", "1234.56789", "--root", str(root),
                                 "--keep-git"])
        self.assertEqual(rc, 5)
        self.assertIn("the paper mirror is MISSING", out.getvalue())
        self.assertIn("fetch_arxiv_source.py", out.getvalue())
        self.assertEqual(json.loads((root / "local" / "project.json").read_text(
            encoding="utf-8"))["project"]["lean_root"], "Demo")


if __name__ == "__main__":
    unittest.main()
