import MIPStarRE.QPBT.Combining.Lines.ConditionedPastingDefect
import MIPStarRE.QPBT.Combining.Lines.PointSelfConsistency

/-!
# Completed point self-consistency

The joint point measurement of `lem:qld-4-10` answers with a pair of field
elements. This module extends both of its answers along the coordinatewise
inclusion into the completed answer alphabet, in which each coordinate may
also be absent, and transports the resulting self-consistency estimate first
to the product of two independent line-point distributions and then to that
product conditioned on a nonzero direction of the first line.

Both orderings of the completed pair are recorded. The pasting argument is
applied to the X-Z-X sandwich, whose inner family is the Z-line family and
whose outer family is the X-line family, so its outcome pair is ordered Z
then X; that ordering, rather than the X-then-Z ordering of the point
measurement itself, is the one carried by the conditioned marginal
comparisons of `ConditionedPointLineMarginalDefect`.

## References

The point estimate is `eq:qld-q-self-cons` in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:693-697`; it
enters the pasting argument as `eq:pasting-2` at lines 950--963. The
statements below are formalization-only consequences of that estimate: they
carry the completed answer alphabet, the product line-point question law
rather than the uniform law on point pairs, and, in the conditioned form, the
restricted question law with the error inflated by the inverse retained mass.
Their blueprint entries are `lem:qld-completed-point-answers`,
`lem:qld-completed-point-self-consistency`, and
`lem:qld-conditioned-completed-point-self-consistency`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-- Extending both coordinates of two pair-valued measurements along the
coordinatewise inclusion into the completed answer alphabet preserves their
consistency defect exactly. -/
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

/-- Exchanging the two completed coordinates of the joint point measurement
relabels its answers by the coordinate exchange: the effect at a completed
pair equals the effect of the unexchanged completion at the transposed pair.
-/
theorem CombinedPointsWitness.completed_orderedZX_effect
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ) (side : PlayerSide)
    (pointX pointZ : Fin P.m → PauliScalar P)
    (answer : Option (PauliScalar P) × Option (PauliScalar P)) :
    ((points.Q side pointX pointZ).postprocess
        (fun pair => (some pair.2, some pair.1))).effect answer =
      ((points.Q side pointX pointZ).postprocess
        (fun pair => (some pair.1, some pair.2))).effect answer.swap := by
  classical
  simp only [MIPStarRE.Quantum.Measurement.postprocess_effect]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext pair
  simp [Prod.ext_iff, and_comm]

/-- The completed joint-point measurements retain the self-consistency bound
`δQ` under the product of two independent line-point distributions, on every
directed opposite placement. -/
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

/-- The same bound holds after exchanging the two completed coordinates, that
is for the answer pair ordered Z then X. This is the ordering carried by the
X-Z-X pasting application, whose inner family is the Z-line family and whose
outer family is the X-line family. -/
theorem CombinedPointsWitness.self_consistency_completed_orderedZX_linePoint_defect_le
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
    consistencyDefect (Distribution.prod (linePointDist P.toLdParams)
      (linePointDist P.toLdParams))
      (fun sample answer => S.place p1
        (((points.Q p1.side sample.1.2 sample.2.2).postprocess
          (fun pair => (some pair.2, some pair.1))).effect answer))
      (fun sample answer => S.place p2
        (((points.Q p2.side sample.1.2 sample.2.2).postprocess
          (fun pair => (some pair.2, some pair.1))).effect answer)) S.psiHat ≤ δQ := by
  classical
  have hrelabel := consistencyDefect_outcome_equiv
    (Distribution.prod (linePointDist P.toLdParams) (linePointDist P.toLdParams))
    (Equiv.prodComm (Option (PauliScalar P)) (Option (PauliScalar P)))
    (fun sample answer => S.place p1
      (((points.Q p1.side sample.1.2 sample.2.2).postprocess
        (fun pair => (some pair.1, some pair.2))).effect answer))
    (fun sample answer => S.place p2
      (((points.Q p2.side sample.1.2 sample.2.2).postprocess
        (fun pair => (some pair.1, some pair.2))).effect answer)) S.psiHat
  simp only [Equiv.prodComm_apply] at hrelabel
  simp only [points.completed_orderedZX_effect]
  rw [hrelabel]
  exact points.self_consistency_completed_linePoint_defect_le p1 p2 hopp

/-- Under the product line-point distribution conditioned on a nonzero
direction of the first line, the completed joint-point measurements remain
self-consistent with defect at most `δQ` divided by the retained mass of that
event, on every directed opposite placement. -/
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

/-- The conditioned estimate for the answer pair ordered Z then X, matching
the ordering of the conditioned point-to-line marginal comparisons. -/
theorem CombinedPointsWitness.self_consistency_conditioned_completed_orderedZX_defect_le
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
    consistencyDefect (nondegenerateLinePastingDist P.toLdParams)
      (fun question answer => S.place p1
        (((points.Q p1.side question.2.2 question.1.2.2).postprocess
          (fun pair => (some pair.2, some pair.1))).effect answer))
      (fun question answer => S.place p2
        (((points.Q p2.side question.2.2 question.1.2.2).postprocess
          (fun pair => (some pair.2, some pair.1))).effect answer)) S.psiHat ≤
      δQ / nondegenerateLinePastingMass P.toLdParams := by
  exact (consistencyDefect_nondegenerateLinePastingDist_le S p1 p2 hopp
    (fun sample => (points.Q p1.side sample.1.2 sample.2.2).postprocess
      (fun pair => (some pair.2, some pair.1)))
    (fun sample => (points.Q p2.side sample.1.2 sample.2.2).postprocess
      (fun pair => (some pair.2, some pair.1)))).trans
    (div_le_div_of_nonneg_right
      (points.self_consistency_completed_orderedZX_linePoint_defect_le p1 p2 hopp)
      (prod_linePointDist_nondegenerate_mass_pos P.toLdParams).le)

end

end MIPStarRE.QPBT
