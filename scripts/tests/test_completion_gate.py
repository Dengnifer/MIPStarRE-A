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
import io
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


def track_for(root: Path) -> gate.Track:
    return gate.Track(
        name="fixture",
        lean_root="MIPStarRE/Fixture",
        headline=(("Fixture.good", "thm:fixture"),),
        gap_register="docs/paper-gaps/fixture-register.md",
        axiom_audit="MIPStarRE/Fixture/AxiomAudit.lean",
        blueprint_chapters=("blueprint/src/chapter/ch99_fixture.tex",),
        leanok_exemptions="docs/completion/fixture-leanok-exemptions.md",
        comparator_doc="docs/comparator.md",
        truthful_docs=("README.md",),
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
        write(self.root, "MIPStarRE/Fixture/Good.lean", GOOD_LEAN)
        write(self.root, "MIPStarRE/Fixture/AxiomAudit.lean", GOOD_AUDIT)
        write(self.root, "docs/paper-gaps/fixture-register.md", GOOD_REGISTER)
        write(self.root, "blueprint/src/chapter/ch99_fixture.tex", GOOD_CHAPTER)
        write(self.root, "scripts/comparator/expected/fixture/Challenge.lean.expected", "-- x\n")
        write(self.root, "README.md", "Fixture track: 0 open sites.\n")

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
        lean = write(self.root, "MIPStarRE/Fixture/Sites.lean", BAD_LEAN)
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
        lean = write(self.root, "MIPStarRE/Fixture/Commented.lean", text)
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
        write(self.root, "MIPStarRE/Fixture/Sites.lean", BAD_LEAN)
        crit = gate.criterion_proof_integrity(self.root, self.track)
        self.assertEqual(crit.status, gate.FAIL)
        kinds = {line.split(": ")[1] for line in crit.evidence}
        self.assertEqual(kinds, {"sorry", "admit", "native", "axiom declaration"})
        for line in crit.evidence:
            path, number, _ = line.split(":", 2)
            self.assertEqual(path, "MIPStarRE/Fixture/Sites.lean")
            self.assertGreater(int(number), 0)

    def test_local_name_constant_on_a_continuation_line_is_not_a_declaration(self) -> None:
        write(
            self.root,
            "MIPStarRE/Fixture/Bounds.lean",
            "theorem bound (constant error : Nat) : 0 ≤ 8 * error +\n"
            "    constant * (error + error) := by\n"
            "  omega\n",
        )
        crit = gate.criterion_proof_integrity(self.root, self.track)
        self.assertEqual(crit.status, gate.PASS, crit.evidence)

    def test_empty_tree_fails_rather_than_passing_vacuously(self) -> None:
        shutil.rmtree(self.root / "MIPStarRE/Fixture")
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
        (self.root / "MIPStarRE/Fixture/AxiomAudit.lean").unlink()
        crit = gate.criterion_headline_axioms(self.root, self.track)
        self.assertEqual(crit.status, gate.FAIL)

    def test_uncovered_headline_theorem_fails(self) -> None:
        write(self.root, "MIPStarRE/Fixture/AxiomAudit.lean", "import Fixture\n")
        crit = gate.criterion_headline_axioms(self.root, self.track)
        self.assertEqual(crit.status, gate.FAIL)
        self.assertIn("Fixture.good", crit.evidence[0])

    def test_commented_assertion_does_not_count(self) -> None:
        write(
            self.root,
            "MIPStarRE/Fixture/AxiomAudit.lean",
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
        write(self.root, "MIPStarRE/Fixture/Sites.lean", BAD_LEAN)
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
        write(self.root, "MIPStarRE/Fixture/Sites.lean", BAD_LEAN)
        code, text = self.run_gate(
            "check", "--track", "fixture", "--repo-root", str(self.root),
            "--commit", self.head,
        )
        self.assertEqual(code, 1)
        self.assertIn("FAIL: C1", text)

    def test_unknown_track_exits_two(self) -> None:
        code, _ = self.run_gate(
            "check", "--track", "nope", "--repo-root", str(self.root)
        )
        self.assertEqual(code, 2)

    def test_broken_shared_rule_exits_two(self) -> None:
        (self.root / gate.ESTIMATE_SH).write_text("#!/bin/sh\n", encoding="utf-8")
        code, _ = self.run_gate(
            "check", "--track", "fixture", "--repo-root", str(self.root)
        )
        self.assertEqual(code, 2)

    def test_text_report_names_every_criterion(self) -> None:
        criteria = gate.run_check(self.root, self.track, self.head)
        text = gate.render_text(self.track, self.head, criteria)
        for ident in ("C1", "C2", "C3", "C4", "C5", "C6"):
            self.assertIn(ident, text)

    def test_text_report_lists_the_delegated_criteria(self) -> None:
        criteria = gate.run_check(self.root, self.track, self.head)
        delegated = [c.ident for c in criteria if c.status == gate.DELEGATED]
        self.assertEqual(delegated, ["C2", "C4", "C5"])
        self.assertIn("(C2, C4, C5)", gate.render_text(self.track, self.head, criteria))


class RegisteredTrackTests(unittest.TestCase):
    def test_qpbt_track_is_registered_with_its_headline_theorems(self) -> None:
        track = gate.TRACKS["qpbt"]
        names = [name for name, _ in track.headline]
        self.assertIn("MIPStarRE.QPBT.pauli_soundness", names)
        self.assertIn("MIPStarRE.QPBT.pauli_soundness_qubit", names)
        self.assertIn("MIPStarRE.QPBT.exists_spcc_value_one", names)
        self.assertIn("MIPStarRE.QPBT.exists_ld_soundness", names)

    def test_registered_truthful_docs_exist_in_this_repository(self) -> None:
        """C6 now fails on a missing doc, so the registry may not name a ghost."""
        for track in gate.TRACKS.values():
            for doc in track.truthful_docs:
                self.assertTrue(
                    (REPO_ROOT / doc).exists(),
                    f"track {track.name} registers a truthful doc that does "
                    f"not exist: {doc}",
                )

    def test_the_repository_still_carries_the_shared_rule(self) -> None:
        pattern = gate.load_sorry_site_rule(REPO_ROOT)
        self.assertTrue(gate.token_rule(pattern, "sorry").search("  := sorry"))


if __name__ == "__main__":
    unittest.main()
