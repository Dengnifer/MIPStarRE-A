import MIPStarRE.QPBT.Combining.Points.MarginalContraction

/-!
# Marginal distances for combined point witnesses

This module applies the generic marginal contraction estimate to the joint
point measurements of a `CombinedPointsWitness`.  The X marginal uses the
ordered Z-then-X consistency field, while the Z marginal uses the ordered
X-then-Z field; no commutation of point effects on one player is assumed.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:917-935`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

set_option maxHeartbeats 800000 in
-- Expanding the nested finite sums and projector products exceeds the default limit.
/-- The X marginal of any joint point witness is within squared distance
`4 * δQ` of the opposite X point measurement. This is
`eq:qld-qxz-close-to-point`, paper lines 917--932, with the supplied witness
error retained; the source later specializes to its constructed points. -/
theorem CombinedPointsWitness.marginal_X_distance_le
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
    opFamilyDistSq
      (uniformDistribution
        ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
      (fun xz a => ∑ b, S.place p1 ((points.Q p1.side xz.1 xz.2).effect (a, b)))
      (fun xz a => S.place p2 ((S.pointMeasExp p2.side .X xz.1).effect a))
      S.psiHat ≤ 4 * δQ := by
  classical
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (points.consistent_ZX p1 p2 hopp)
    (by norm_num : (0 : ℝ) ≤ 4))
  unfold opFamilyDistSq
  rw [← avgOver_const_mul]
  apply avgOver_mono
  intro xz
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  simpa only [ProjectiveSetting.placedMeasurement_effect, ProjectiveSetting.place_mul] using
    norm_marginal_sub_sq_le
    (fun b => S.place p1 ((points.Q p1.side xz.1 xz.2).effect (a, b)))
    (fun b => S.placedMeasurement_isProjective p1 _ (points.projective _ _ _) (a, b))
    (fun hbc => DistanceCalculus.projective_effect_mul_effect_eq_zero
      (S.placedMeasurement p1 (points.Q p1.side xz.1 xz.2))
      (S.placedMeasurement_isProjective p1 _ (points.projective _ _ _))
      (fun hpair => hbc (congrArg Prod.snd hpair)))
    (S.placedMeasurement p2 (S.pointMeasExp p2.side .Z xz.2))
    (S.placedMeasurement_isProjective p2 _ (S.pointMeasExp_isProjective _ _ _))
    (fun b => S.place_comm p1 p2 hopp _ _)
    (S.place p2 ((S.pointMeasExp p2.side .X xz.1).effect a)) S.psiHat

set_option maxHeartbeats 800000 in
-- Expanding the nested finite sums and projector products exceeds the default limit.
/-- The Z marginal of any joint point witness is within squared distance
`4 * δQ` of the opposite Z point measurement. This is the symmetric
calculation `eq:qld-qxz-close-to-point-2`, paper lines 933--935. -/
theorem CombinedPointsWitness.marginal_Z_distance_le
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
    opFamilyDistSq
      (uniformDistribution
        ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
      (fun xz b => ∑ a, S.place p1 ((points.Q p1.side xz.1 xz.2).effect (a, b)))
      (fun xz b => S.place p2 ((S.pointMeasExp p2.side .Z xz.2).effect b))
      S.psiHat ≤ 4 * δQ := by
  classical
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (points.consistent_XZ p1 p2 hopp)
    (by norm_num : (0 : ℝ) ≤ 4))
  unfold opFamilyDistSq
  rw [← avgOver_const_mul]
  apply avgOver_mono
  intro xz
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b _
  simpa only [ProjectiveSetting.placedMeasurement_effect, ProjectiveSetting.place_mul] using
    norm_marginal_sub_sq_le
    (fun a => S.place p1 ((points.Q p1.side xz.1 xz.2).effect (a, b)))
    (fun a => S.placedMeasurement_isProjective p1 _ (points.projective _ _ _) (a, b))
    (fun hac => DistanceCalculus.projective_effect_mul_effect_eq_zero
      (S.placedMeasurement p1 (points.Q p1.side xz.1 xz.2))
      (S.placedMeasurement_isProjective p1 _ (points.projective _ _ _))
      (fun hpair => hac (congrArg Prod.fst hpair)))
    (S.placedMeasurement p2 (S.pointMeasExp p2.side .X xz.1))
    (S.placedMeasurement_isProjective p2 _ (S.pointMeasExp_isProjective _ _ _))
    (fun a => S.place_comm p1 p2 hopp _ _)
    (S.place p2 ((S.pointMeasExp p2.side .Z xz.2).effect b)) S.psiHat

end

end MIPStarRE.QPBT
