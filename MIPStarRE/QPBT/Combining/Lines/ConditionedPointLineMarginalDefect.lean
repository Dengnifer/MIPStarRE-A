import MIPStarRE.QPBT.Combining.Lines.CombinedPointLineMarginalDefect
import MIPStarRE.QPBT.Combining.Lines.ConditionedPastingDefect

/-!
# Conditioned point-to-line marginal defects

This module transfers both completed combined-point marginal comparisons to
the proof-only nondegenerate line-pasting question law.

## References

The two comparisons formalize the marginal inputs in `eq:pasting-q1`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:936-963`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-- The completed point marginals, ordered Z then X, satisfy both conditioned
line comparisons with the original point and line error terms divided by the
retained nondegenerate-line mass. -/
theorem exists_combinedPoints_conditioned_line_marginal_defect_le :
    ∃ constant : ℝ, 1 ≤ constant ∧
      ∀ (P : AdmissibleParams) (ε δQ : ℝ) (S : ProjectiveSetting P ε)
        (points : CombinedPointsWitness S δQ)
        (p1 p2 : Placement), p1.IsOpposite p2 →
        consistencyDefect (nondegenerateLinePastingDist P.toLdParams)
          (fun question answer => S.place p1
            ((((points.Q p1.side question.2.2 question.1.2.2).postprocess
              (fun pair => (some pair.2, some pair.1))).postprocess Prod.fst).effect answer))
          (fun question answer => S.place p2
            ((S.lineEvalMeasExp p2.side .Z question.1.1.2 question.1.2.2).effect answer))
          S.psiHat ≤ (8 * δQ + constant * (ε + deltaLine ε)) /
            nondegenerateLinePastingMass P.toLdParams ∧
        consistencyDefect (nondegenerateLinePastingDist P.toLdParams)
          (fun question answer => S.place p1
            ((((points.Q p1.side question.2.2 question.1.2.2).postprocess
              (fun pair => (some pair.2, some pair.1))).postprocess Prod.snd).effect answer))
          (fun question answer => S.place p2
            ((S.lineEvalMeasExp p2.side .X question.1.1.1 question.2.2).effect answer))
          S.psiHat ≤ (8 * δQ + constant * (ε + deltaLine ε)) /
            nondegenerateLinePastingMass P.toLdParams := by
  obtain ⟨constant, hconstant, hbound⟩ := exists_combinedPoints_line_marginal_defect_le
  refine ⟨constant, hconstant, ?_⟩
  intro P ε δQ S points p1 p2 hopp
  classical
  have hswap (side : PlayerSide) (pointX pointZ : Fin P.m → PauliScalar P)
      (answer : Option (PauliScalar P)) :
      (((points.Q side pointX pointZ).postprocess
        (fun pair => (some pair.2, some pair.1))).postprocess Prod.fst).effect answer =
        (((points.Q side pointX pointZ).postprocess
          (fun pair => (some pair.1, some pair.2))).postprocess Prod.snd).effect answer ∧
      (((points.Q side pointX pointZ).postprocess
        (fun pair => (some pair.2, some pair.1))).postprocess Prod.snd).effect answer =
        (((points.Q side pointX pointZ).postprocess
          (fun pair => (some pair.1, some pair.2))).postprocess Prod.fst).effect answer := by
    simp only [MIPStarRE.Quantum.Measurement.postprocess_comp, and_self]
  simp_rw [(hswap _ _ _ _).1, (hswap _ _ _ _).2]
  have hmass := (prod_linePointDist_nondegenerate_mass_pos P.toLdParams).le
  constructor
  · have h := (consistencyDefect_nondegenerateLinePastingDist_le S p1 p2 hopp
      (fun sample => ((points.Q p1.side sample.1.2 sample.2.2).postprocess
        (fun pair => (some pair.1, some pair.2))).postprocess Prod.snd)
      (fun sample => S.lineEvalMeasExp p2.side .Z sample.2.1 sample.2.2)).trans
      (div_le_div_of_nonneg_right (hbound P ε δQ S points p1 p2 hopp).2 hmass)
    unfold consistencyDefect nondegenerateLinePastingDist at h ⊢
    simp only [Distribution.avgOver_map] at h ⊢
    exact h
  · have h := (consistencyDefect_nondegenerateLinePastingDist_le S p1 p2 hopp
      (fun sample => ((points.Q p1.side sample.1.2 sample.2.2).postprocess
        (fun pair => (some pair.1, some pair.2))).postprocess Prod.fst)
      (fun sample => S.lineEvalMeasExp p2.side .X sample.1.1 sample.1.2)).trans
      (div_le_div_of_nonneg_right (hbound P ε δQ S points p1 p2 hopp).1 hmass)
    unfold consistencyDefect nondegenerateLinePastingDist at h ⊢
    simp only [Distribution.avgOver_map] at h ⊢
    exact h

end

end MIPStarRE.QPBT
