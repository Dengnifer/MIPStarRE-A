#!/usr/bin/env python3
"""Regression tests for scripts/audit_paper_facing_proof_debt.py."""

from __future__ import annotations

import json
import re
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPT_DIR))

import audit_paper_facing_proof_debt as audit  # noqa: E402


def _write_register(root: Path, **registers) -> None:
    """Write the optional per-declaration register this repository may carry."""
    path = root / audit.REGISTER_PATH
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps({audit.REGISTER_SECTION: registers}, indent=2), encoding="utf-8"
    )


def _write_repo(root: Path, lean_source: str, tex_source: str) -> None:
    lean_file = root / "PaperLib" / "Foo.lean"
    lean_file.parent.mkdir(parents=True)
    lean_file.write_text(textwrap.dedent(lean_source).strip() + "\n", encoding="utf-8")

    tex_file = root / "blueprint" / "src" / "chapter" / "ch01_test.tex"
    tex_file.parent.mkdir(parents=True)
    tex_file.write_text(textwrap.dedent(tex_source).strip() + "\n", encoding="utf-8")


class PaperFacingProofDebtAuditTests(unittest.TestCase):
    def test_github_workflow_runs_audit_as_blocking_guard(self) -> None:
        workflow = SCRIPT_DIR.parent / ".github" / "workflows" / "pr-ci.yml"
        text = workflow.read_text(encoding="utf-8")
        self.assertIn("proof-debt:", text)
        self.assertIn("scripts/audit_paper_facing_proof_debt.py", text)
        self.assertIn("--ci", text)
        self.assertNotIn("--warn-only", text)
        propagates_pipeline_status = (
            re.search(r"(?m)^\s*set\s+-[^\n#]*\bpipefail\b", text) is not None
            or "${PIPESTATUS[0]}" in text
        )
        self.assertTrue(propagates_pipeline_status)

    def test_clean_paper_facing_theorem_has_no_findings(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_repo(
                root,
                """
                namespace PaperLib

                theorem paperTheorem (h : P) : Q := by
                  sorry

                end PaperLib
                """,
                r"""
                \begin{theorem}\label{thm:paper}
                  \lean{PaperLib.paperTheorem}
                \end{theorem}
                """,
            )
            result = audit.run_audit(root)
            self.assertEqual(result.scanned_refs, 1)
            self.assertEqual(result.findings, ())
            self.assertEqual(result.missing_refs, ())

    def test_bridge_hypothesis_in_paper_facing_header_is_reported(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_repo(
                root,
                """
                namespace PaperLib

                theorem paperTheorem
                    (hBridge : SomeBridgeHypotheses)
                    (h : P) : Q := by
                  sorry

                end PaperLib
                """,
                r"""
                \begin{theorem}\label{thm:paper}
                  \lean{PaperLib.paperTheorem}
                \end{theorem}
                """,
            )
            result = audit.run_audit(root)
            self.assertEqual(len(result.findings), 2)
            self.assertEqual(
                {finding.token for finding in result.findings},
                {"hBridge", "SomeBridgeHypotheses"},
            )
            self.assertTrue(all(finding.label == "thm:paper" for finding in result.findings))

    def test_non_theorem_like_blueprint_environment_is_not_scanned(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_repo(
                root,
                """
                namespace PaperLib

                def bridgeDefinition (hBridge : SomeBridgeHypotheses) : Q := q

                end PaperLib
                """,
                r"""
                \begin{definition}\label{def:bridge}
                  \lean{PaperLib.bridgeDefinition}
                \end{definition}
                """,
            )
            result = audit.run_audit(root)
            self.assertEqual(result.scanned_refs, 0)
            self.assertEqual(result.findings, ())

    def test_informational_blueprint_environment_can_be_scanned_on_request(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_repo(
                root,
                """
                namespace PaperLib

                def bridgeDefinition (hBridge : SomeBridgeHypotheses) : Q := q

                end PaperLib
                """,
                r"""
                \begin{definition}\label{def:bridge}
                  \lean{PaperLib.bridgeDefinition}
                \end{definition}
                """,
            )
            default_result = audit.run_audit(root)
            self.assertEqual(default_result.scanned_refs, 0)
            self.assertEqual(default_result.findings, ())

            result = audit.run_audit(root, include_informational_envs=True)
            self.assertEqual(result.scanned_refs, 1)
            self.assertEqual(len(result.findings), 2)
            self.assertEqual(
                {finding.token for finding in result.findings},
                {"hBridge", "SomeBridgeHypotheses"},
            )

    def test_comma_separated_lean_references_are_scanned(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_repo(
                root,
                """
                namespace PaperLib

                theorem cleanTheorem (h : P) : Q := by
                  sorry

                theorem repairedTheorem (repair : RepairInput) : Q := by
                  sorry

                end PaperLib
                """,
                r"""
                \begin{lemma}\label{lem:two}
                  \lean{PaperLib.cleanTheorem, PaperLib.repairedTheorem}
                \end{lemma}
                """,
            )
            result = audit.run_audit(root)
            self.assertEqual(result.scanned_refs, 2)
            self.assertEqual(len(result.findings), 2)
            self.assertEqual(
                {finding.token for finding in result.findings},
                {"repair", "RepairInput"},
            )

    def test_declaration_name_itself_is_not_a_finding(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_repo(
                root,
                """
                namespace PaperLib

                theorem mainFormal_ofRepairedBridge (h : P) : Q := by
                  sorry

                end PaperLib
                """,
                r"""
                \begin{lemma}\label{lem:helper}
                  \lean{PaperLib.mainFormal_ofRepairedBridge}
                \end{lemma}
                """,
            )
            result = audit.run_audit(root)
            self.assertEqual(result.scanned_refs, 1)
            self.assertEqual(result.findings, ())

    def test_conditional_declaration_name_in_paper_facing_entry_is_reported(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_repo(
                root,
                """
                namespace PaperLib

                theorem mainFormal_ofRepairedBridge (h : P) : Q := by
                  sorry

                end PaperLib
                """,
                r"""
                \begin{theorem}\label{thm:main-formal}
                  \lean{PaperLib.mainFormal_ofRepairedBridge}
                \end{theorem}
                """,
            )
            result = audit.run_audit(root)
            self.assertEqual(result.scanned_refs, 1)
            self.assertEqual(result.findings, ())
            self.assertEqual(len(result.conditional_decl_findings), 1)
            self.assertEqual(result.conditional_decl_findings[0].token, "_ofRepairedBridge")

    def test_known_informational_construction_name_is_classified_only_in_broad_mode(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_repo(
                root,
                """
                namespace PaperLib.Core

                theorem SelfConsistencyHandoff.ofCompleteStatements
                    (h : P) : Q := by
                  sorry

                end PaperLib.Core
                """,
                r"""
                \begin{remark}\label{rem:lean-only-helpers}
                  \lean{PaperLib.Core.SelfConsistencyHandoff.ofCompleteStatements}
                \end{remark}
                """,
            )
            _write_register(root, source_context_conditional_decl_names={
                "PaperLib.Core.SelfConsistencyHandoff.ofCompleteStatements":
                    "Lean-only construction displayed near the proof; see the "
                    "informational blueprint entry rem:lean-only-helpers"
            })
            theorem_like_result = audit.run_audit(root)
            self.assertEqual(theorem_like_result.scanned_refs, 0)

            broad_result = audit.run_audit(
                root,
                broad_vocabulary=True,
                include_informational_envs=True,
            )
            self.assertEqual(broad_result.findings, ())
            self.assertEqual(broad_result.conditional_decl_findings, ())
            self.assertEqual(len(broad_result.source_context_findings), 1)
            self.assertEqual(
                broad_result.source_context_findings[0].token,
                "ofCompleteStatements",
            )

    def test_known_construction_name_in_theorem_like_entry_is_still_reported(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_repo(
                root,
                """
                namespace PaperLib.Core

                theorem SelfConsistencyHandoff.ofCompleteStatements
                    (h : P) : Q := by
                  sorry

                end PaperLib.Core
                """,
                r"""
                \begin{theorem}\label{thm:main-formal}
                  \lean{PaperLib.Core.SelfConsistencyHandoff.ofCompleteStatements}
                \end{theorem}
                """,
            )
            result = audit.run_audit(root, broad_vocabulary=True)
            self.assertEqual(result.findings, ())
            self.assertEqual(len(result.conditional_decl_findings), 1)
            self.assertEqual(
                result.conditional_decl_findings[0].token,
                "ofCompleteStatements",
            )

    def test_internal_obligation_name_in_paper_facing_entry_is_reported(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_repo(
                root,
                """
                namespace PaperLib

                theorem mainFormal_ofInternalObligations (h : P) : Q := by
                  sorry

                end PaperLib
                """,
                r"""
                \begin{theorem}\label{thm:paper}
                  \lean{PaperLib.mainFormal_ofInternalObligations}
                \end{theorem}
                """,
            )
            result = audit.run_audit(root)
            self.assertEqual(result.scanned_refs, 1)
            self.assertEqual(result.findings, ())
            self.assertEqual(len(result.conditional_decl_findings), 1)
            self.assertEqual(result.conditional_decl_findings[0].token, "_ofInternalObligations")

    def test_residual_constructor_name_in_paper_facing_entry_is_reported(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_repo(
                root,
                """
                namespace PaperLib

                theorem paperTheorem_ofCompletionResidual (h : P) : Q := by
                  sorry

                end PaperLib
                """,
                r"""
                \begin{lemma}\label{lem:paper}
                  \lean{PaperLib.paperTheorem_ofCompletionResidual}
                \end{lemma}
                """,
            )
            result = audit.run_audit(root)
            self.assertEqual(result.scanned_refs, 1)
            self.assertEqual(result.findings, ())
            self.assertEqual(len(result.conditional_decl_findings), 1)
            self.assertEqual(result.conditional_decl_findings[0].token, "_ofCompletionResidual")

    def test_producer_constructor_name_in_paper_facing_entry_is_reported(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_repo(
                root,
                """
                namespace PaperLib

                theorem paperTheorem_ofProjectivizationProducer (h : P) : Q := by
                  sorry

                end PaperLib
                """,
                r"""
                \begin{theorem}\label{thm:paper}
                  \lean{PaperLib.paperTheorem_ofProjectivizationProducer}
                \end{theorem}
                """,
            )
            result = audit.run_audit(root)
            self.assertEqual(result.scanned_refs, 1)
            self.assertEqual(result.findings, ())
            self.assertEqual(len(result.conditional_decl_findings), 1)
            self.assertEqual(
                result.conditional_decl_findings[0].token,
                "_ofProjectivizationProducer",
            )

    def test_singular_hypothesis_name_in_paper_facing_entry_is_reported(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_repo(
                root,
                """
                namespace PaperLib

                theorem paperTheorem_ofBridgeHypothesis (h : P) : Q := by
                  sorry

                end PaperLib
                """,
                r"""
                \begin{lemma}\label{lem:paper}
                  \lean{PaperLib.paperTheorem_ofBridgeHypothesis}
                \end{lemma}
                """,
            )
            result = audit.run_audit(root)
            self.assertEqual(result.scanned_refs, 1)
            self.assertEqual(result.findings, ())
            self.assertEqual(len(result.conditional_decl_findings), 1)
            self.assertEqual(
                result.conditional_decl_findings[0].token,
                "_ofBridgeHypothesis",
            )

    def test_singular_assumption_name_in_paper_facing_entry_is_reported(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_repo(
                root,
                """
                namespace PaperLib

                theorem paperTheorem_ofExtraAssumption (h : P) : Q := by
                  sorry

                end PaperLib
                """,
                r"""
                \begin{corollary}\label{cor:paper}
                  \lean{PaperLib.paperTheorem_ofExtraAssumption}
                \end{corollary}
                """,
            )
            result = audit.run_audit(root)
            self.assertEqual(result.scanned_refs, 1)
            self.assertEqual(result.findings, ())
            self.assertEqual(len(result.conditional_decl_findings), 1)
            self.assertEqual(
                result.conditional_decl_findings[0].token,
                "_ofExtraAssumption",
            )

    def test_conditional_prefix_name_in_paper_facing_entry_is_reported(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_repo(
                root,
                """
                namespace PaperLib

                theorem conditionalPaperTheorem (h : P) : Q := by
                  sorry

                end PaperLib
                """,
                r"""
                \begin{corollary}\label{cor:paper}
                  \lean{PaperLib.conditionalPaperTheorem}
                \end{corollary}
                """,
            )
            result = audit.run_audit(root)
            self.assertEqual(result.scanned_refs, 1)
            self.assertEqual(result.findings, ())
            self.assertEqual(len(result.conditional_decl_findings), 1)
            self.assertEqual(result.conditional_decl_findings[0].token, "conditionalPaperTheorem")

    def test_plain_hypotheses_bundle_in_paper_facing_header_is_reported(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_repo(
                root,
                """
                namespace PaperLib

                theorem cascadeBound (h : ExtraHypotheses params k eps) : Q := by
                  sorry

                end PaperLib
                """,
                r"""
                \begin{theorem}\label{thm:cascade}
                  \lean{PaperLib.cascadeBound}
                \end{theorem}
                """,
            )
            result = audit.run_audit(root)
            self.assertEqual(result.scanned_refs, 1)
            self.assertEqual(
                {finding.token for finding in result.findings},
                {"ExtraHypotheses"},
            )

    def test_input_bundle_in_paper_facing_header_is_reported(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_repo(
                root,
                """
                namespace PaperLib

                theorem paperTheorem (hinput : OrthonormalizationInput params) : Q := by
                  sorry

                end PaperLib
                """,
                r"""
                \begin{theorem}\label{thm:paper}
                  \lean{PaperLib.paperTheorem}
                \end{theorem}
                """,
            )
            result = audit.run_audit(root)
            self.assertEqual(result.scanned_refs, 1)
            self.assertEqual(
                {finding.token for finding in result.findings},
                {"hinput", "OrthonormalizationInput"},
            )

    def test_slice_boundedness_input_is_classified_as_faithful_boundary(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_repo(
                root,
                """
                namespace PaperLib

                theorem paperTheorem (hbound : BoundednessInput strategy family zeta) :
                    Q := by
                  sorry

                end PaperLib
                """,
                r"""
                \begin{theorem}\label{thm:paper}
                  \lean{PaperLib.paperTheorem}
                \end{theorem}
                """,
            )
            _write_register(root, faithful_boundary_tokens={
                "BoundednessInput": "faithful encoding of the paper's boundedness "
                "hypothesis; see references/source-paper/commutativity.tex:29-36"
            })
            result = audit.run_audit(root)
            self.assertEqual(result.scanned_refs, 1)
            self.assertEqual(result.findings, ())
            self.assertEqual(len(result.faithful_boundary_findings), 1)
            self.assertEqual(result.faithful_boundary_findings[0].token, "BoundednessInput")

    def test_cascade_hypotheses_is_classified_as_faithful_boundary(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_repo(
                root,
                """
                namespace PaperLib

                theorem paperTheorem (h : CascadeHypotheses params k eps) :
                    Q := by
                  sorry

                end PaperLib
                """,
                r"""
                \begin{theorem}\label{thm:paper}
                  \lean{PaperLib.paperTheorem}
                \end{theorem}
                """,
            )
            _write_register(root, faithful_boundary_tokens={
                "CascadeHypotheses": "faithful encoding of the standing numeric "
                "regime; see references/source-paper/inductive_step.tex:187-234"
            })
            result = audit.run_audit(root)
            self.assertEqual(result.scanned_refs, 1)
            self.assertEqual(result.findings, ())
            self.assertEqual(len(result.faithful_boundary_findings), 1)
            self.assertEqual(result.faithful_boundary_findings[0].token, "CascadeHypotheses")

            # Without the register the same header is a finding: the register
            # is what classifies it, and it is empty in a fresh repository.
            (root / audit.REGISTER_PATH).unlink()
            plain = audit.run_audit(root)
            self.assertEqual(plain.faithful_boundary_findings, ())
            self.assertEqual(len(plain.findings), 1)

    def test_assumptions_bundle_in_paper_facing_header_is_reported(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_repo(
                root,
                """
                namespace PaperLib

                theorem paperTheorem
                    (hasExtraAssumptions : ExtraAssumptions params) : Q := by
                  sorry

                end PaperLib
                """,
                r"""
                \begin{theorem}\label{thm:paper}
                  \lean{PaperLib.paperTheorem}
                \end{theorem}
                """,
            )
            result = audit.run_audit(root)
            self.assertEqual(result.scanned_refs, 1)
            self.assertEqual(
                {finding.token for finding in result.findings},
                {"hasExtraAssumptions", "ExtraAssumptions"},
            )

    def test_singular_assumption_in_paper_facing_header_is_reported(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_repo(
                root,
                """
                namespace PaperLib

                theorem paperTheorem
                    (hasExtraAssumption : ExtraAssumption params) : Q := by
                  sorry

                end PaperLib
                """,
                r"""
                \begin{theorem}\label{thm:paper}
                  \lean{PaperLib.paperTheorem}
                \end{theorem}
                """,
            )
            result = audit.run_audit(root)
            self.assertEqual(
                {finding.token for finding in result.findings},
                {"hasExtraAssumption", "ExtraAssumption"},
            )

    def test_obligation_wrapper_in_paper_facing_header_is_reported(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_repo(
                root,
                """
                namespace PaperLib

                theorem paperTheorem
                    (h : InternalObligationWrapper params) : Q := by
                  sorry

                end PaperLib
                """,
                r"""
                \begin{theorem}\label{thm:paper}
                  \lean{PaperLib.paperTheorem}
                \end{theorem}
                """,
            )
            result = audit.run_audit(root)
            self.assertEqual(result.scanned_refs, 1)
            self.assertEqual(
                {finding.token for finding in result.findings},
                {"InternalObligationWrapper"},
            )

    def test_bundle_input_in_paper_facing_header_is_reported(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_repo(
                root,
                """
                namespace PaperLib

                theorem paperTheorem
                    (bundle : CompletionBundle params) : Q := by
                  sorry

                end PaperLib
                """,
                r"""
                \begin{theorem}\label{thm:paper}
                  \lean{PaperLib.paperTheorem}
                \end{theorem}
                """,
            )
            result = audit.run_audit(root)
            self.assertEqual(
                {finding.token for finding in result.findings},
                {"bundle", "CompletionBundle"},
            )

    def test_unfaithful_marker_input_in_paper_facing_header_is_reported(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_repo(
                root,
                """
                namespace PaperLib

                theorem paperTheorem
                    (h : UnfaithfulCompletion params) : Q := by
                  sorry

                end PaperLib
                """,
                r"""
                \begin{theorem}\label{thm:paper}
                  \lean{PaperLib.paperTheorem}
                \end{theorem}
                """,
            )
            result = audit.run_audit(root)
            self.assertEqual(
                {finding.token for finding in result.findings},
                {"UnfaithfulCompletion"},
            )

    def test_witness_input_in_paper_facing_header_is_reported_in_broad_mode(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_repo(
                root,
                """
                namespace PaperLib

                theorem paperTheorem
                    (hwitness : CompletionWitness params) : Q := by
                  sorry

                end PaperLib
                """,
                r"""
                \begin{theorem}\label{thm:paper}
                  \lean{PaperLib.paperTheorem}
                \end{theorem}
                """,
            )
            result = audit.run_audit(root, broad_vocabulary=True)
            self.assertEqual(
                {finding.token for finding in result.findings},
                {"hwitness", "CompletionWitness"},
            )

    def test_compatibility_data_in_paper_facing_header_is_reported_in_broad_mode(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_repo(
                root,
                """
                namespace PaperLib

                theorem paperTheorem
                    (hcompat : CompletionCompatibilityData params) : Q := by
                  sorry

                end PaperLib
                """,
                r"""
                \begin{theorem}\label{thm:paper}
                  \lean{PaperLib.paperTheorem}
                \end{theorem}
                """,
            )
            result = audit.run_audit(root, broad_vocabulary=True)
            self.assertEqual(
                {finding.token for finding in result.findings},
                {"CompletionCompatibilityData"},
            )

    def test_lowercase_data_binder_is_not_double_counted_in_broad_mode(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_repo(
                root,
                """
                namespace PaperLib

                theorem paperTheorem
                    (data : CompletionData params) : Q := by
                  sorry

                end PaperLib
                """,
                r"""
                \begin{theorem}\label{thm:paper}
                  \lean{PaperLib.paperTheorem}
                \end{theorem}
                """,
            )
            result = audit.run_audit(root, broad_vocabulary=True)
            self.assertEqual(
                {finding.token for finding in result.findings},
                {"CompletionData"},
            )

    def test_qxp_layer_data_is_classified_as_source_context(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_repo(
                root,
                """
                namespace PaperLib

                theorem paperTheorem
                    (data : QXPLayerData Outcome ι) : Q := by
                  sorry

                end PaperLib
                """,
                r"""
                \begin{theorem}\label{thm:paper}
                  \lean{PaperLib.paperTheorem}
                \end{theorem}
                """,
            )
            _write_register(root, source_context_tokens={
                "QXPLayerData": "layer data of the fixed construction context; "
                "see references/source-paper/self_improvement.tex:635-671"
            })
            result = audit.run_audit(root, broad_vocabulary=True)
            self.assertEqual(result.findings, ())
            self.assertEqual(len(result.source_context_findings), 1)
            self.assertEqual(result.source_context_findings[0].token, "QXPLayerData")

    def test_rank_reduction_witness_is_classified_as_source_context(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_repo(
                root,
                """
                namespace PaperLib

                theorem paperTheorem
                    (hRank : RankReductionWitness psi A zeta qLayer) : Q := by
                  sorry

                end PaperLib
                """,
                r"""
                \begin{lemma}\label{lem:paper}
                  \lean{PaperLib.paperTheorem}
                \end{lemma}
                """,
            )
            _write_register(root, source_context_tokens={
                "RankReductionWitness": "witness of the rank-reduction step; "
                "see references/source-paper/rank_reduction.tex:12-48"
            })
            result = audit.run_audit(root, broad_vocabulary=True)
            self.assertEqual(result.findings, ())
            self.assertEqual(len(result.source_context_findings), 1)
            self.assertEqual(result.source_context_findings[0].token, "RankReductionWitness")

    def test_external_statement_interface_is_classified_in_broad_mode(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_repo(
                root,
                """
                namespace PaperLib

                theorem classicalTestSoundness
                    (hPS : ExternalClassicalSoundnessStatement params a eps kappa) :
                    Q := by
                  sorry

                end PaperLib
                """,
                r"""
                \begin{theorem}\label{thm:classical-test-soundness}
                  \lean{PaperLib.classicalTestSoundness}
                \end{theorem}
                """,
            )
            _write_register(root, external_citation_tokens={
                "ExternalClassicalSoundnessStatement": "interface of the external "
                "theorem quoted in references/source-paper/introduction.tex:69-92"
            })
            result = audit.run_audit(root, broad_vocabulary=True)
            self.assertEqual(result.findings, ())
            self.assertEqual(len(result.external_citation_findings), 1)
            self.assertEqual(
                result.external_citation_findings[0].token,
                "ExternalClassicalSoundnessStatement",
            )

    def test_external_statement_interface_is_not_hidden_in_strict_mode(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_repo(
                root,
                """
                namespace PaperLib

                theorem classicalTestSoundness
                    (hPS : ExternalClassicalSoundnessStatement params a eps kappa) :
                    Q := by
                  sorry

                end PaperLib
                """,
                r"""
                \begin{theorem}\label{thm:classical-test-soundness}
                  \lean{PaperLib.classicalTestSoundness}
                \end{theorem}
                """,
            )
            result = audit.run_audit(root)
            self.assertEqual(result.findings, ())
            self.assertEqual(result.external_citation_findings, ())

    def test_bundle_constructor_name_in_paper_facing_entry_is_reported(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_repo(
                root,
                """
                namespace PaperLib

                theorem paperTheorem_ofCompletionBundle (h : P) : Q := by
                  sorry

                end PaperLib
                """,
                r"""
                \begin{lemma}\label{lem:paper}
                  \lean{PaperLib.paperTheorem_ofCompletionBundle}
                \end{lemma}
                """,
            )
            result = audit.run_audit(root)
            self.assertEqual(result.findings, ())
            self.assertEqual(len(result.conditional_decl_findings), 1)
            self.assertEqual(result.conditional_decl_findings[0].token, "_ofCompletionBundle")

    def test_debt_vocabulary_is_not_reported_inside_unrelated_identifiers(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_repo(
                root,
                """
                namespace PaperLib

                theorem paperTheorem (reproducer : P) (repackaged : Q) : R := by
                  sorry

                end PaperLib
                """,
                r"""
                \begin{theorem}\label{thm:paper}
                  \lean{PaperLib.paperTheorem}
                \end{theorem}
                """,
            )
            result = audit.run_audit(root)
            self.assertEqual(result.scanned_refs, 1)
            self.assertEqual(result.findings, ())

    def test_debt_vocabulary_still_reports_full_identifiers(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_repo(
                root,
                """
                namespace PaperLib

                theorem paperTheorem
                    (hbaseBridge : BaseBridgeHypotheses)
                    (residualDomination : P) : Q := by
                  sorry

                end PaperLib
                """,
                r"""
                \begin{theorem}\label{thm:paper}
                  \lean{PaperLib.paperTheorem}
                \end{theorem}
                """,
            )
            result = audit.run_audit(root)
            self.assertEqual(
                {finding.token for finding in result.findings},
                {"hbaseBridge", "BaseBridgeHypotheses", "residualDomination"},
            )

    def test_debt_vocabulary_in_result_type_is_not_an_input_finding(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_repo(
                root,
                """
                namespace PaperLib

                theorem collisionResidualBound (h : P) :
                    generalizeBCollisionResidual params strategy G g ≤ error := by
                  sorry

                end PaperLib
                """,
                r"""
                \begin{lemma}\label{lem:collision}
                  \lean{PaperLib.collisionResidualBound}
                \end{lemma}
                """,
            )
            result = audit.run_audit(root)
            self.assertEqual(result.scanned_refs, 1)
            self.assertEqual(result.findings, ())


if __name__ == "__main__":
    unittest.main()
