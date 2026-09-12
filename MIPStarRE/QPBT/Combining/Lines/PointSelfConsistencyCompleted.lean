import MIPStarRE.QPBT.Combining.Lines.ConditionedPastingDefect
import MIPStarRE.QPBT.Combining.Lines.PointSelfConsistency

/-!
# Completed point self-consistency

This module completes both answers of the joint point measurement with `some`
and transports its self-consistency estimate to the proof-only nondegenerate
pasting question law.

## References

The completed self-consistency estimate supplies `eq:pasting-2` in
`lem:pasting`, as used in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-963`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-- Completing both coordinates of two pair-valued measurements with `some`
preserves their consistency defect exactly. -/
theorem ProjectiveSetting.consistencyDefect_postprocess_some_pair
    {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε)
    {Sample : Type*} [Fintype Sample] [DecidableEq Sample]
    (law : Distribution Sample) (p1 p2 : Placement)
    (first : Sample → MIPStarRE.Quantum.Measurement
      (PauliScalar P × PauliScalar P) (S.ExpandedLocalSpace p1.side))
    (second : Sample → MIPStarRE.Quantum.Measurement
      (PauliScalar P × PauliScalar P) (S.ExpandedLocalSpace p2.side)) :
    consistencyDefect law
      (fun sample answer => S.place p1
        (((first sample).postprocess (fun pair => (some pair.1, some pair.2))).effect answer))
      (fun sample answer => S.place p2
        (((second sample).postprocess (fun pair => (some pair.1, some pair.2))).effect answer))
      S.psiHat =
    consistencyDefect law (fun sample answer => S.place p1 ((first sample).effect answer))
      (fun sample answer => S.place p2 ((second sample).effect answer)) S.psiHat := by
  classical
  unfold consistencyDefect
  congr 1
  funext sample
  simp [Fintype.sum_prod_type, Fintype.sum_option,
    MIPStarRE.Quantum.Measurement.postprocess,
    MIPStarRE.Quantum.Submeasurement.postprocess, Finset.sum_filter,
    Prod.ext_iff, ite_and, S.place_zero]

/-- Completing both joint-point answers preserves the product line-point
self-consistency bound `δQ` on every directed opposite placement. -/
theorem CombinedPointsWitness.self_consistency_completed_linePoint_defect_le
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
    consistencyDefect (Distribution.prod (linePointDist P.toLdParams)
      (linePointDist P.toLdParams))
      (fun sample answer => S.place p1
        (((points.Q p1.side sample.1.2 sample.2.2).postprocess
          (fun pair => (some pair.1, some pair.2))).effect answer))
      (fun sample answer => S.place p2
        (((points.Q p2.side sample.1.2 sample.2.2).postprocess
          (fun pair => (some pair.1, some pair.2))).effect answer)) S.psiHat ≤ δQ := by
  erw [S.consistencyDefect_postprocess_some_pair]
  exact points.self_consistency_linePoint_defect_le p1 p2 hopp

/-- The completed joint-point measurements remain self-consistent under the
nondegenerate pasting law with defect at most `δQ` divided by the retained
mass, on every directed opposite placement. -/
theorem CombinedPointsWitness.self_consistency_conditioned_completed_defect_le
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
    consistencyDefect (nondegenerateLinePastingDist P.toLdParams)
      (fun question answer => S.place p1
        (((points.Q p1.side question.2.2 question.1.2.2).postprocess
          (fun pair => (some pair.1, some pair.2))).effect answer))
      (fun question answer => S.place p2
        (((points.Q p2.side question.2.2 question.1.2.2).postprocess
          (fun pair => (some pair.1, some pair.2))).effect answer)) S.psiHat ≤
      δQ / nondegenerateLinePastingMass P.toLdParams := by
  exact (consistencyDefect_nondegenerateLinePastingDist_le S p1 p2 hopp
    (fun sample => (points.Q p1.side sample.1.2 sample.2.2).postprocess
      (fun pair => (some pair.1, some pair.2)))
    (fun sample => (points.Q p2.side sample.1.2 sample.2.2).postprocess
      (fun pair => (some pair.1, some pair.2)))).trans
    (div_le_div_of_nonneg_right
      (points.self_consistency_completed_linePoint_defect_le p1 p2 hopp)
      (prod_linePointDist_nondegenerate_mass_pos P.toLdParams).le)

end

end MIPStarRE.QPBT
