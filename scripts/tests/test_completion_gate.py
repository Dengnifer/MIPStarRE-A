#!/usr/bin/env python3
"""Unit tests for ``scripts/completion_gate.py``.

Each criterion of ``local/protocols/completion.md`` gets a small fixture tree
that passes, and one mutation of it that must fail.  One test additionally
cross-checks the gate's sorry counting against the real
``results/telemetry/owner-tools/estimate.sh`` rather than against a copy of the
rule, since the protocol requires a single implementation of that rule.
"""

from __future__ import annotations

import contextlib
import dataclasses
import io
import json
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "scripts"))

import completion_gate as gate  # noqa: E402


ESTIMATE = REPO_ROOT / "results/telemetry/owner-tools/estimate.sh"

GOOD_LEAN = """\
import Mathlib

namespace Fixture

/-- A docstring that discusses a `sorry` it does not contain. -/
theorem good : True := trivial

end Fixture
"""

BAD_LEAN = """\
import Mathlib

namespace Fixture

theorem holed : True := sorry

theorem other : True := by
  admit

axiom assumed : True

theorem fast : True := by native_decide

end Fixture
"""

GOOD_CHAPTER = r"""
\begin{theorem}[Headline]\label{thm:fixture}
  \lean{Fixture.good}
  \leanok
  True holds.
\end{theorem}

\begin{lemma}[Unlinked]\label{lem:fixture-unlinked}
  No Lean link here.
\end{lemma}
"""

UNMARKED_CHAPTER = r"""
\begin{theorem}[Headline]\label{thm:fixture}
  \lean{Fixture.good}
  \begin{align*} 1 = 1 \end{align*}
  True holds.
\end{theorem}
"""

# An ``example`` node is a node: the shared parser of
# ``scripts/blueprint_lean_sync.py`` counts it, so C4 must too.
UNMARKED_EXAMPLE_CHAPTER = r"""
\begin{theorem}[Headline]\label{thm:fixture}
  \lean{Fixture.good}
  \leanok
  True holds.
\end{theorem}

\begin{example}[Worked]\label{exa:fixture}
  \lean{Fixture.worked}
  An example carrying a Lean link and no marker.
\end{example}
"""

# A chapter shared with another track: only the node whose ``\lean{}`` names a
# declaration under this track's Lean root is this track's to mark.
SHARED_CHAPTER = r"""
\begin{lemma}[Shared chapter, this track]\label{lem:shared-track}
  \lean{PaperLib.Fixture.shared}
  A node of this track living outside the track's own chapters.
\end{lemma}
"""

MARKED_SHARED_CHAPTER = SHARED_CHAPTER.replace(
    "\\lean{PaperLib.Fixture.shared}",
    "\\lean{PaperLib.Fixture.shared}\n  \\leanok",
)

FOREIGN_CHAPTER = r"""
\begin{lemma}[Shared chapter, another track]\label{lem:shared-foreign}
  \lean{PaperLib.Other.shared}
  Another track's node, unmarked; not this track's criterion.
\end{lemma}
"""

GOOD_REGISTER = """\
# Fixture register

| Note | Source statement | Terminal status | Lean status |
|---|---|---|---|
| `a.tex` | `fact:a` | corrected | proved |
| `b.tex` | `fact:b` | no-difference | proved |
"""

GOOD_AUDIT = """\
import Fixture

assert_standard_axioms Fixture.good
"""

# The shape a generated challenge has: a Mathlib-only prelude whose assembler
# names each declaration of the closure by its fully-qualified name.
EXPECTED_CHALLENGE = """\
import Mathlib

namespace Fixture

-- source: PaperLib/Fixture/Good.lean:6-6  (Fixture.good)
theorem good : True := sorry

end Fixture
"""


def track_for(root: Path) -> gate.Track:
    return gate.Track(
        name="fixture",
        lean_root="PaperLib/Fixture",
        headline=(("Fixture.good", "thm:fixture"),),
        gap_register="docs/paper-gaps/fixture-register.md",
        axiom_audit="PaperLib/Fixture/AxiomAudit.lean",
        blueprint_chapters=("blueprint/src/chapter/ch99_fixture.tex",),
        leanok_exemptions="docs/completion/fixture-leanok-exemptions.md",
        comparator_doc="docs/comparator.md",
        expected_challenge="scripts/comparator/expected/fixture/Challenge.lean.expected",
        truthful_docs=("README.md",),
        artifact_files=("README.md", "docs/ARTIFACT.md", "LICENSE"),
        artifact_script="scripts/make_artifact.sh",
    )


def write(root: Path, rel: str, text: str) -> Path:
    path = root / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")
    return path


def git(root: Path, *args: str) -> str:
    completed = subprocess.run(
        ["git", "-c", "user.name=fixture", "-c", "user.email=fixture@example.invalid", *args],
        cwd=root, check=True, capture_output=True, text=True,
    )
    return completed.stdout.strip()


class GateFixture(unittest.TestCase):
    """A repository tree that passes every criterion, plus helpers."""

    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory(prefix="completion-gate-")
        self.root = Path(self._tmp.name)
        self.addCleanup(self._tmp.cleanup)
        self.track = track_for(self.root)

        (self.root / "results/telemetry/owner-tools").mkdir(parents=True)
        shutil.copy(ESTIMATE, self.root / gate.ESTIMATE_SH)
        write(self.root, "PaperLib/Fixture/Good.lean", GOOD_LEAN)
        write(self.root, "PaperLib/Fixture/AxiomAudit.lean", GOOD_AUDIT)
        write(self.root, "docs/paper-gaps/fixture-register.md", GOOD_REGISTER)
        write(self.root, "blueprint/src/chapter/ch99_fixture.tex", GOOD_CHAPTER)
        write(
            self.root,
            "scripts/comparator/expected/fixture/Challenge.lean.expected",
            EXPECTED_CHALLENGE,
        )
        write(self.root, "README.md", "Fixture track: 0 open sites.\n")
        write(self.root, "docs/ARTIFACT.md", "How to run the artifact.\n")
        write(self.root, "LICENSE", "Apache-2.0 fixture text.\n")
        write(self.root, "scripts/make_artifact.sh", "#!/bin/sh\nexit 0\n")

        if shutil.which("git"):
            git(self.root, "init", "-q")
            git(self.root, "add", "-A")
            git(self.root, "commit", "-q", "-m", "fixture")
            self.pin = git(self.root, "rev-parse", "HEAD")
            git(self.root, "commit", "-q", "--allow-empty", "-m", "later")
            self.head = git(self.root, "rev-parse", "HEAD")
        else:  # pragma: no cover - git is present on every machine we run on
            self.pin = "0" * 40
            self.head = "0" * 40

        self.write_comparator(self.pin)

    def write_comparator(self, pin: str) -> None:
        write(
            self.root,
            "docs/comparator.md",
            "# Comparator\n\n"
            "<!-- completion-gate: track=fixture -->\n"
            "- challenge-repository: https://example.invalid/fixture-comparator\n"
            f"- verified-library-commit: {pin}\n"
            "- expected-challenge: scripts/comparator/expected/fixture/Challenge.lean.expected\n"
            "- drift-check: scripts/comparator/check_challenge_drift.py\n"
            "- covered-theorems: Fixture.good\n",
        )


class SharedRuleTests(GateFixture):
    def test_rule_comes_from_estimate_sh(self) -> None:
        pattern = gate.load_sorry_site_rule(self.root)
        self.assertIn("sorry", pattern)
        matcher = gate.token_rule(pattern, "sorry")
        self.assertTrue(matcher.search("  theorem t : True := sorry"))
        self.assertTrue(matcher.search("  sorry"))
        self.assertFalse(matcher.search("  -- a sorry in prose"))

    def test_missing_rule_is_a_config_error(self) -> None:
        (self.root / gate.ESTIMATE_SH).write_text("#!/bin/sh\n", encoding="utf-8")
        with self.assertRaises(gate.GateConfigError):
            gate.load_sorry_site_rule(self.root)

    def test_unknown_posix_class_is_a_config_error(self) -> None:
        with self.assertRaises(gate.GateConfigError):
            gate.translate_posix_ere("[[:martian:]]sorry")

    @unittest.skipUnless(shutil.which("bash"), "bash is required")
    def test_agrees_with_the_estimate_on_a_plain_file(self) -> None:
        lean = write(self.root, "PaperLib/Fixture/Sites.lean", BAD_LEAN)
        counted = subprocess.run(
            ["bash", str(ESTIMATE), "--count-sorry-sites", str(lean)],
            check=True, capture_output=True, text=True,
        )
        matcher = gate.token_rule(gate.load_sorry_site_rule(self.root), "sorry")
        mine = sum(
            1 for line in gate.strip_lean_comments(BAD_LEAN).splitlines()
            if matcher.search(line)
        )
        self.assertEqual(mine, int(counted.stdout.strip()))

    @unittest.skipUnless(shutil.which("bash"), "bash is required")
    def test_never_counts_more_than_the_estimate(self) -> None:
        """Stronger comment stripping may drop sites; it may never add any."""
        text = GOOD_LEAN + "\n/-\ntheorem commented : True := sorry\n-/\n"
        lean = write(self.root, "PaperLib/Fixture/Commented.lean", text)
        counted = int(
            subprocess.run(
                ["bash", str(ESTIMATE), "--count-sorry-sites", str(lean)],
                check=True, capture_output=True, text=True,
            ).stdout.strip()
        )
        crit = gate.criterion_proof_integrity(self.root, self.track)
        mine = sum(1 for line in crit.evidence if ": sorry:" in line)
        self.assertLessEqual(mine, counted)
        self.assertEqual(mine, 0)


class ProofIntegrityTests(GateFixture):
    def test_clean_tree_passes(self) -> None:
        crit = gate.criterion_proof_integrity(self.root, self.track)
        self.assertEqual(crit.status, gate.PASS, crit.evidence)

    def test_every_kind_of_debt_is_reported_with_file_and_line(self) -> None:
        write(self.root, "PaperLib/Fixture/Sites.lean", BAD_LEAN)
        crit = gate.criterion_proof_integrity(self.root, self.track)
        self.assertEqual(crit.status, gate.FAIL)
        kinds = {line.split(": ")[1] for line in crit.evidence}
        self.assertEqual(kinds, {"sorry", "admit", "native", "axiom declaration"})
        for line in crit.evidence:
            path, number, _ = line.split(":", 2)
            self.assertEqual(path, "PaperLib/Fixture/Sites.lean")
            self.assertGreater(int(number), 0)

    def test_local_name_constant_on_a_continuation_line_is_not_a_declaration(self) -> None:
        write(
            self.root,
            "PaperLib/Fixture/Bounds.lean",
            "theorem bound (constant error : Nat) : 0 ≤ 8 * error +\n"
            "    constant * (error + error) := by\n"
            "  omega\n",
        )
        crit = gate.criterion_proof_integrity(self.root, self.track)
        self.assertEqual(crit.status, gate.PASS, crit.evidence)

    def test_empty_tree_fails_rather_than_passing_vacuously(self) -> None:
        shutil.rmtree(self.root / "PaperLib/Fixture")
        crit = gate.criterion_proof_integrity(self.root, self.track)
        self.assertEqual(crit.status, gate.FAIL)


class HeadlineAxiomTests(GateFixture):
    def test_covered_but_unbuilt_audit_is_delegated_not_passed(self) -> None:
        """No build ran here, so C2 may not claim the axiom values are standard."""
        crit = gate.criterion_headline_axioms(self.root, self.track)
        self.assertEqual(crit.status, gate.DELEGATED, crit.evidence)
        self.assertNotEqual(crit.status, gate.PASS)
        self.assertFalse(crit.counts_against_exit)
        self.assertTrue(crit.notes)

    def test_missing_audit_file_fails(self) -> None:
        (self.root / "PaperLib/Fixture/AxiomAudit.lean").unlink()
        crit = gate.criterion_headline_axioms(self.root, self.track)
        self.assertEqual(crit.status, gate.FAIL)

    def test_uncovered_headline_theorem_fails(self) -> None:
        write(self.root, "PaperLib/Fixture/AxiomAudit.lean", "import Fixture\n")
        crit = gate.criterion_headline_axioms(self.root, self.track)
        self.assertEqual(crit.status, gate.FAIL)
        self.assertIn("Fixture.good", crit.evidence[0])

    def test_the_other_audit_command_spelling_also_counts(self) -> None:
        """Either `assert_standard_axioms` or `audit_standard_axioms` covers it."""
        write(
            self.root,
            "PaperLib/Fixture/AxiomAudit.lean",
            "import Fixture\n\naudit_standard_axioms Fixture.good\n",
        )
        crit = gate.criterion_headline_axioms(self.root, self.track)
        self.assertEqual(crit.status, gate.DELEGATED, crit.evidence)

    def test_commented_assertion_does_not_count(self) -> None:
        write(
            self.root,
            "PaperLib/Fixture/AxiomAudit.lean",
            "-- assert_standard_axioms Fixture.good\n",
        )
        crit = gate.criterion_headline_axioms(self.root, self.track)
        self.assertEqual(crit.status, gate.FAIL)


class PaperGapTests(GateFixture):
    def test_terminal_rows_pass(self) -> None:
        crit = gate.criterion_paper_gaps(self.root, self.track)
        self.assertEqual(crit.status, gate.PASS, crit.evidence)

    def test_missing_terminal_column_fails(self) -> None:
        write(
            self.root,
            "docs/paper-gaps/fixture-register.md",
            "| Note | Lean status |\n|---|---|\n| `a.tex` | proved |\n",
        )
        crit = gate.criterion_paper_gaps(self.root, self.track)
        self.assertEqual(crit.status, gate.FAIL)
        self.assertIn("Terminal status", crit.summary)

    def test_non_terminal_row_fails_with_its_line(self) -> None:
        write(
            self.root,
            "docs/paper-gaps/fixture-register.md",
            GOOD_REGISTER.replace("| no-difference |", "| open proof |"),
        )
        crit = gate.criterion_paper_gaps(self.root, self.track)
        self.assertEqual(crit.status, gate.FAIL)
        self.assertTrue(crit.evidence[0].startswith("docs/paper-gaps/fixture-register.md:6"))


class BlueprintTests(GateFixture):
    def test_marked_nodes_are_delegated(self) -> None:
        crit = gate.criterion_blueprint(self.root, self.track)
        self.assertEqual(crit.status, gate.DELEGATED, crit.evidence)
        self.assertFalse(crit.counts_against_exit)

    def test_environment_list_comes_from_the_shared_parser(self) -> None:
        from blueprint_lean_sync import _TEX_ENV_BEGIN_RE

        rule = gate.blueprint_node_rule()
        for env in ("definition", "theorem", "lemma", "proposition",
                    "corollary", "remark", "example"):
            self.assertIn(env, rule.pattern)
            self.assertIn(env, _TEX_ENV_BEGIN_RE.pattern)

    def test_unmarked_example_node_fails(self) -> None:
        """A `\\lean{}` node in an `example` is a node the blueprint tooling sees."""
        write(self.root, "blueprint/src/chapter/ch99_fixture.tex",
              UNMARKED_EXAMPLE_CHAPTER)
        crit = gate.criterion_blueprint(self.root, self.track)
        self.assertEqual(crit.status, gate.FAIL)
        self.assertIn("exa:fixture", crit.evidence[0])

    def test_unmarked_node_fails(self) -> None:
        write(self.root, "blueprint/src/chapter/ch99_fixture.tex", UNMARKED_CHAPTER)
        crit = gate.criterion_blueprint(self.root, self.track)
        self.assertEqual(crit.status, gate.FAIL)
        self.assertIn("thm:fixture", crit.evidence[0])

    def test_exempted_node_does_not_fail(self) -> None:
        write(self.root, "blueprint/src/chapter/ch99_fixture.tex", UNMARKED_CHAPTER)
        write(
            self.root,
            "docs/completion/fixture-leanok-exemptions.md",
            "| Node | Reason |\n|---|---|\n| `thm:fixture` | printed claim, not asserted |\n",
        )
        crit = gate.criterion_blueprint(self.root, self.track)
        self.assertEqual(crit.status, gate.DELEGATED, crit.evidence)

    def test_track_node_in_an_unregistered_chapter_is_in_scope(self) -> None:
        """A node of the track in a shared chapter may not escape C4."""
        write(self.root, "blueprint/src/chapter/ch03_shared.tex", SHARED_CHAPTER)
        crit = gate.criterion_blueprint(self.root, self.track)
        self.assertEqual(crit.status, gate.FAIL)
        self.assertIn("ch03_shared.tex", crit.evidence[0])
        self.assertIn("lem:shared-track", crit.evidence[0])

    def test_foreign_node_in_an_unregistered_chapter_is_ignored(self) -> None:
        """C4 judges this track's nodes, not another track's."""
        write(self.root, "blueprint/src/chapter/ch03_shared.tex", FOREIGN_CHAPTER)
        crit = gate.criterion_blueprint(self.root, self.track)
        self.assertEqual(crit.status, gate.DELEGATED, crit.evidence)
        self.assertNotIn("ch03_shared", " ".join(crit.evidence))

    def test_marked_track_node_in_an_unregistered_chapter_is_counted(self) -> None:
        write(self.root, "blueprint/src/chapter/ch03_shared.tex",
              MARKED_SHARED_CHAPTER)
        crit = gate.criterion_blueprint(self.root, self.track)
        self.assertEqual(crit.status, gate.DELEGATED, crit.evidence)
        self.assertIn("2 linked nodes", crit.summary)
        self.assertIn("section 6 does not list", crit.summary)

    def test_exemption_without_a_reason_does_not_count(self) -> None:
        write(self.root, "blueprint/src/chapter/ch99_fixture.tex", UNMARKED_CHAPTER)
        write(
            self.root,
            "docs/completion/fixture-leanok-exemptions.md",
            "| Node | Reason |\n|---|---|\n| `thm:fixture` |  |\n",
        )
        crit = gate.criterion_blueprint(self.root, self.track)
        self.assertEqual(crit.status, gate.FAIL)


@unittest.skipUnless(shutil.which("git"), "git is required")
class ComparatorTests(GateFixture):
    def test_recorded_and_pinned_challenge_is_delegated(self) -> None:
        crit = gate.criterion_comparator(self.root, self.track, self.head)
        self.assertEqual(crit.status, gate.DELEGATED, crit.evidence)
        self.assertFalse(crit.counts_against_exit)

    def test_missing_block_fails(self) -> None:
        write(self.root, "docs/comparator.md", "# Comparator\n")
        crit = gate.criterion_comparator(self.root, self.track, self.head)
        self.assertEqual(crit.status, gate.FAIL)
        self.assertIn("completion-gate", crit.evidence[0])

    def test_missing_field_fails(self) -> None:
        doc = self.root / "docs/comparator.md"
        doc.write_text(
            "\n".join(
                line for line in doc.read_text(encoding="utf-8").splitlines()
                if not line.startswith("- covered-theorems")
            ) + "\n",
            encoding="utf-8",
        )
        crit = gate.criterion_comparator(self.root, self.track, self.head)
        self.assertEqual(crit.status, gate.FAIL)
        self.assertIn("covered-theorems", crit.evidence[0])

    def test_uncovered_headline_theorem_fails(self) -> None:
        doc = self.root / "docs/comparator.md"
        doc.write_text(
            doc.read_text(encoding="utf-8").replace("Fixture.good", "Fixture.other"),
            encoding="utf-8",
        )
        crit = gate.criterion_comparator(self.root, self.track, self.head)
        self.assertEqual(crit.status, gate.FAIL)

    def test_record_that_over_claims_coverage_fails(self) -> None:
        """`covered-theorems` is hand-written; the challenge file decides."""
        write(
            self.root,
            "scripts/comparator/expected/fixture/Challenge.lean.expected",
            EXPECTED_CHALLENGE.replace("Fixture.good", "Fixture.other"),
        )
        crit = gate.criterion_comparator(self.root, self.track, self.head)
        self.assertEqual(crit.status, gate.FAIL)
        self.assertTrue(
            any("does not occur in" in line for line in crit.evidence),
            crit.evidence,
        )

    def test_record_naming_another_expected_copy_fails(self) -> None:
        """A record may only name the copy the track registers."""
        doc = self.root / "docs/comparator.md"
        doc.write_text(
            doc.read_text(encoding="utf-8").replace(
                "- expected-challenge: scripts/comparator/expected/fixture/"
                "Challenge.lean.expected",
                "- expected-challenge: scripts/comparator/expected/"
                "Challenge.lean.expected",
            ),
            encoding="utf-8",
        )
        write(self.root, "scripts/comparator/expected/Challenge.lean.expected",
              EXPECTED_CHALLENGE)
        crit = gate.criterion_comparator(self.root, self.track, self.head)
        self.assertEqual(crit.status, gate.FAIL)
        self.assertIn("registered expected copy", crit.evidence[0])

    def test_missing_expected_copy_fails(self) -> None:
        (self.root / "scripts/comparator/expected/fixture/Challenge.lean.expected").unlink()
        crit = gate.criterion_comparator(self.root, self.track, self.head)
        self.assertEqual(crit.status, gate.FAIL)
        self.assertIn("does not exist", crit.evidence[0])

    def test_pin_that_is_not_an_ancestor_fails(self) -> None:
        self.write_comparator(self.head)
        crit = gate.criterion_comparator(self.root, self.track, self.pin)
        self.assertEqual(crit.status, gate.FAIL)
        self.assertIn("ancestor", crit.evidence[0])

    def test_short_pin_is_rejected(self) -> None:
        self.write_comparator(self.head[:12])
        crit = gate.criterion_comparator(self.root, self.track, self.head)
        self.assertEqual(crit.status, gate.FAIL)
        self.assertIn("full commit hash", crit.evidence[0])


class DocsTruthfulTests(GateFixture):
    def test_deferred_while_proof_debt_remains(self) -> None:
        write(self.root, "PaperLib/Fixture/Sites.lean", BAD_LEAN)
        integrity = gate.criterion_proof_integrity(self.root, self.track)
        crit = gate.criterion_docs_truthful(self.root, self.track, integrity)
        self.assertEqual(crit.status, gate.DEFERRED)

    def test_zero_claim_passes(self) -> None:
        integrity = gate.criterion_proof_integrity(self.root, self.track)
        crit = gate.criterion_docs_truthful(self.root, self.track, integrity)
        self.assertEqual(crit.status, gate.PASS, crit.evidence)

    def test_missing_registered_doc_fails(self) -> None:
        """A renamed doc must not leave C6 green with nothing checked."""
        (self.root / "README.md").unlink()
        integrity = gate.criterion_proof_integrity(self.root, self.track)
        crit = gate.criterion_docs_truthful(self.root, self.track, integrity)
        self.assertEqual(crit.status, gate.FAIL)
        self.assertTrue(crit.evidence[0].startswith("README.md:0"))
        self.assertIn("missing", crit.summary)

    def test_stale_nonzero_claim_fails(self) -> None:
        write(self.root, "README.md", "Fixture track: 12 open sites remain.\n")
        integrity = gate.criterion_proof_integrity(self.root, self.track)
        crit = gate.criterion_docs_truthful(self.root, self.track, integrity)
        self.assertEqual(crit.status, gate.FAIL)
        self.assertTrue(crit.evidence[0].startswith("README.md:1"))


class ArtifactReadinessTests(GateFixture):
    def test_complete_bundle_is_delegated_not_passed(self) -> None:
        """No snapshot was built here, so C7 may not claim the leak scan ran."""
        crit = gate.criterion_artifact_readiness(self.root, self.track)
        self.assertEqual(crit.status, gate.DELEGATED, crit.evidence)
        self.assertFalse(crit.counts_against_exit)
        self.assertTrue(crit.notes)

    def test_missing_files_fail_and_are_named(self) -> None:
        (self.root / "docs/ARTIFACT.md").unlink()
        (self.root / "LICENSE").unlink()
        crit = gate.criterion_artifact_readiness(self.root, self.track)
        self.assertEqual(crit.status, gate.FAIL)
        self.assertIn("docs/ARTIFACT.md", crit.summary)
        self.assertIn("LICENSE", crit.summary)
        self.assertEqual(
            {line.split(":")[0] for line in crit.evidence},
            {"docs/ARTIFACT.md", "LICENSE"},
        )

    def test_missing_snapshot_script_fails(self) -> None:
        (self.root / "scripts/make_artifact.sh").unlink()
        crit = gate.criterion_artifact_readiness(self.root, self.track)
        self.assertEqual(crit.status, gate.FAIL)
        self.assertIn("scripts/make_artifact.sh", crit.summary)


@unittest.skipUnless(shutil.which("git"), "git is required")
class DriverTests(GateFixture):
    def setUp(self) -> None:
        super().setUp()
        gate.TRACKS["fixture"] = self.track
        self.addCleanup(gate.TRACKS.pop, "fixture", None)

    def run_gate(self, *argv: str) -> tuple[int, str]:
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = gate.main(list(argv))
        return code, out.getvalue() + err.getvalue()

    def test_passing_tree_exits_zero(self) -> None:
        code, text = self.run_gate(
            "check", "--track", "fixture", "--repo-root", str(self.root),
            "--commit", self.head, "--json",
        )
        self.assertEqual(code, 0, text)
        self.assertIn('"exit": 0', text)

    def test_failing_tree_exits_one(self) -> None:
        write(self.root, "PaperLib/Fixture/Sites.lean", BAD_LEAN)
        code, text = self.run_gate(
            "check", "--track", "fixture", "--repo-root", str(self.root),
            "--commit", self.head,
        )
        self.assertEqual(code, 1)
        self.assertIn("FAIL: C1", text)

    def test_unknown_track_exits_two(self) -> None:
        code, text = self.run_gate(
            "check", "--track", "nope", "--repo-root", str(self.root)
        )
        self.assertEqual(code, 2)
        self.assertIn("unknown track", text)

    def test_list_prints_the_registered_track_names(self) -> None:
        code, text = self.run_gate("list", "--repo-root", str(self.root))
        self.assertEqual(code, 0)
        self.assertIn("fixture", text)

    def test_broken_shared_rule_exits_two(self) -> None:
        (self.root / gate.ESTIMATE_SH).write_text("#!/bin/sh\n", encoding="utf-8")
        code, _ = self.run_gate(
            "check", "--track", "fixture", "--repo-root", str(self.root)
        )
        self.assertEqual(code, 2)

    def test_text_report_names_every_criterion(self) -> None:
        criteria = gate.run_check(self.root, self.track, self.head)
        text = gate.render_text(self.track, self.head, criteria)
        for ident in ("C1", "C2", "C3", "C4", "C5", "C6", "C7"):
            self.assertIn(ident, text)

    def test_text_report_lists_the_delegated_criteria(self) -> None:
        criteria = gate.run_check(self.root, self.track, self.head)
        delegated = [c.ident for c in criteria if c.status == gate.DELEGATED]
        self.assertEqual(delegated, ["C2", "C4", "C5", "C7"])
        self.assertIn(
            "(C2, C4, C5, C7)", gate.render_text(self.track, self.head, criteria)
        )

    def test_missing_artifact_file_fails_the_run(self) -> None:
        (self.root / "LICENSE").unlink()
        code, text = self.run_gate(
            "check", "--track", "fixture", "--repo-root", str(self.root),
            "--commit", self.head,
        )
        self.assertEqual(code, 1)
        self.assertIn("FAIL: C7", text)


@unittest.skipUnless(shutil.which("git"), "git is required")
class NoTrackRegisteredTests(unittest.TestCase):
    """A freshly bootstrapped repository: the gate explains, it does not crash."""

    def run_gate(self, *argv: str) -> tuple[int, str, str]:
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = gate.main(list(argv))
        return code, out.getvalue(), err.getvalue()

    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory(prefix="completion-gate-empty-")
        self.addCleanup(self._tmp.cleanup)
        self.root = Path(self._tmp.name)
        write(self.root, "local/project.json", json.dumps({"schema": 1}))

    def test_check_exits_two_and_points_at_the_bootstrap_protocol(self) -> None:
        code, _, err = self.run_gate(
            "check", "--track", "main", "--repo-root", str(self.root)
        )
        self.assertEqual(code, 2)
        self.assertIn("no track is registered in local/project.json", err)
        self.assertIn("local/protocols/bootstrap.md", err)

    def test_list_prints_no_track_name_and_exits_zero(self) -> None:
        code, out, err = self.run_gate("list", "--repo-root", str(self.root))
        self.assertEqual(code, 0)
        self.assertEqual(out.strip(), "")
        self.assertIn("no track is registered", err)

    def test_a_broken_project_file_exits_two_with_a_message(self) -> None:
        write(self.root, "local/project.json", "{not json")
        code, _, err = self.run_gate(
            "check", "--track", "main", "--repo-root", str(self.root)
        )
        self.assertEqual(code, 2)
        self.assertIn("not valid JSON", err)


class RegisteredTrackTests(unittest.TestCase):
    """The registry is `local/project.json`; these tests hold for any project.

    A freshly bootstrapped repository registers no track, so most of them are
    vacuous there and gain teeth as soon as the first track is written.
    """

    def tracks(self) -> dict[str, gate.Track]:
        """The tracks of THIS repository whose mathematics has started.

        `scripts/bootstrap_project.py` registers the project's track on the first
        commit with `headline: []` and `blueprint_chapters: []` — the blueprint
        stage fills them, and the paths it will name (the gap register, the
        exemption table, the axiom audit) are written with it.  Holding a track
        to those rows before then would fail every freshly instantiated project
        on its own first commit, so an unstarted track is out of scope here; the
        completion gate still reports it as unfinished, which is what it is.
        """
        started = {}
        for name, track in gate.load_tracks(REPO_ROOT).items():
            if not track.headline:
                continue
            started[name] = track
        return started

    def test_a_registered_track_is_either_started_or_empty_by_construction(self) -> None:
        """An unstarted track carries no half-filled mathematics."""
        for name, track in gate.load_tracks(REPO_ROOT).items():
            if track.headline:
                continue
            self.assertEqual(
                track.blueprint_chapters, (),
                f"track {name} lists blueprint chapters but no headline theorem: "
                "the two are written together by the blueprint stage",
            )

    def test_every_registered_track_names_paths_that_exist_here(self) -> None:
        """Each criterion rests on its registered path, so none may be a ghost."""
        for name, track in self.tracks().items():
            for field_name in (
                "gap_register",
                "axiom_audit",
                "leanok_exemptions",
                "comparator_doc",
                "expected_challenge",
                "artifact_script",
            ):
                value = getattr(track, field_name)
                if not value:
                    continue
                self.assertTrue(
                    (REPO_ROOT / value).exists(),
                    f"track {name} registers {field_name} {value}, which is not "
                    "in this repository",
                )
            for rel in (*track.truthful_docs, *track.artifact_files, *track.blueprint_chapters):
                self.assertTrue(
                    (REPO_ROOT / rel).exists(),
                    f"track {name} registers {rel}, which is not in this repository",
                )

    def test_every_registered_track_names_its_headline_theorems(self) -> None:
        for name, track in self.tracks().items():
            self.assertTrue(track.headline, f"track {name} registers no headline theorem")
            for theorem, label in track.headline:
                self.assertIn(".", theorem, f"track {name}: {theorem} is not a full name")
                self.assertIn(":", label, f"track {name}: {label} is not a blueprint label")

    def test_a_repository_with_no_track_registers_none(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            self.assertEqual(gate.load_tracks(Path(td)), {})

    def test_a_track_written_into_the_project_file_is_registered(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            write(
                root,
                "local/project.json",
                json.dumps(
                    {
                        "schema": 1,
                        "project": {"name": "Widget", "lean_root": "Widget", "track": "core"},
                        "tracks": {
                            "core": {
                                "lean_root": "Widget/Core",
                                "headline": [["Widget.Core.main", "thm:main"]],
                                "gap_register": "docs/paper-gaps/core.md",
                                "axiom_audit": "Widget/Core/Test/AxiomAudit.lean",
                                "blueprint_chapters": ["blueprint/src/chapter/ch01.tex"],
                                "leanok_exemptions": "docs/completion/core.md",
                                "expected_challenge": "scripts/comparator/expected/C.expected",
                                "truthful_docs": ["README.md"],
                                "artifact_files": ["README.md"],
                            }
                        },
                    }
                ),
            )
            tracks = gate.load_tracks(root)
            self.assertEqual(sorted(tracks), ["core"])
            track = tracks["core"]
            self.assertEqual(track.name, "core")
            self.assertEqual(track.lean_root, "Widget/Core")
            self.assertEqual(track.headline, (("Widget.Core.main", "thm:main"),))
            self.assertEqual(track.blueprint_chapters, ("blueprint/src/chapter/ch01.tex",))
            # Unset fields fall back to the documented defaults rather than
            # failing the load half-way through a bootstrap.
            self.assertEqual(track.comparator_doc, "docs/comparator.md")
            self.assertEqual(track.artifact_script, "scripts/make_artifact.sh")

    def test_the_track_fields_are_the_ones_the_project_file_documents(self) -> None:
        import project_config

        self.assertEqual(
            {f.name for f in dataclasses.fields(gate.Track)},
            set(project_config.TRACK_FIELDS),
            "`Track` gained or lost a field: name it in "
            "scripts/project_config.py TRACK_FIELDS too",
        )

    def test_registry_and_protocol_agree_on_the_registered_paths(self) -> None:
        """Section 6 rows and the registry are one commit's work, so they match."""
        protocol = (REPO_ROOT / "local/protocols/completion.md").read_text(
            encoding="utf-8"
        )
        path_fields = (
            "lean_root",
            "gap_register",
            "axiom_audit",
            "blueprint_chapters",
            "leanok_exemptions",
            "comparator_doc",
            "expected_challenge",
            "truthful_docs",
            "artifact_files",
            "artifact_script",
        )
        # A field added to `Track` without a line here would silently escape
        # the rule stated at the end of section 6, which is the shape of defect
        # this gate exists to remove.
        self.assertEqual(
            {f.name for f in dataclasses.fields(gate.Track)},
            {"name", "headline", *path_fields},
            "`Track` gained or lost a field: name it here (and in section 6 of "
            "the protocol) so every path-valued field is still checked",
        )
        for name, track in self.tracks().items():
            registered: list[str] = []
            for fieldname in path_fields:
                value = getattr(track, fieldname)
                registered.extend(
                    value if isinstance(value, tuple) else (value,)
                )
            for rel in registered:
                if not rel:
                    continue
                self.assertIn(
                    f"`{rel}`",
                    protocol,
                    f"track {name} registers {rel}, which section 6 of "
                    "the protocol does not name",
                )

    def test_the_repository_still_carries_the_shared_rule(self) -> None:
        pattern = gate.load_sorry_site_rule(REPO_ROOT)
        self.assertTrue(gate.token_rule(pattern, "sorry").search("  := sorry"))


if __name__ == "__main__":
    unittest.main()
