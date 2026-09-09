import MIPStarRE.QPBT.Combining.Points.Closeness
import MIPStarRE.QPBT.Combining.Witnesses

/-!
# Absorption estimates for combined point measurements

This module proves the first projection step used to compare a joint point
measurement with the corresponding marginal point measurement.  Projectivity
makes the complementary projection contractive, and the two ordered
consistency fields of `CombinedPointsWitness` supply the resulting averaged
bounds.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:902-915`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-- Removing the component outside a projective effect is a contraction.
This is the projection step preceding `eq:qqm`, paper
`14_analysis_of_the_pauli_basis_test.tex:902-915`. No commutation of the
two operators being compared is required. -/
theorem norm_sub_projective_mul_sq_le {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι] (M : Quantum.Measurement α ι)
    (hM : Measurement.IsProjective M) (a : α) (A D : Op ι)
    (ψ : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState (A - M.effect a * A) ψ‖ ^ 2 ≤
      ‖applyOperatorToState (A - M.effect a * D) ψ‖ ^ 2 := by
  have hidem := (hM a).isIdempotentElem.eq
  have hgram : (1 - M.effect a)ᴴ * (1 - M.effect a) ≤ 1 := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      (hM a).isSelfAdjoint.isHermitian.eq]
    calc
      (1 - M.effect a) * (1 - M.effect a) = 1 - M.effect a := by
        simp only [sub_mul, mul_sub, one_mul, mul_one, hidem]
        abel
      _ ≤ 1 := sub_le_self _ (M.pos a)
  have heq : A - M.effect a * A =
      (1 - M.effect a) * (A - M.effect a * D) := by
    simp only [sub_mul, mul_sub, one_mul, ← mul_assoc, hidem]
    abel
  rw [heq, DistanceCalculus.applyOperatorToState_mul]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (MagicSquareRigidity.norm_applyOperatorToState_le hgram _) 2

/-- The joint point witness absorbs the opposite X point projector with
error at most its actual parameter. This is the X counterpart of the first
projection step of `lem:qld-xz-lines`, paper lines 902--915, obtained from
`consistent_XZ` rather than from an assumed marginal identity. -/
theorem CombinedPointsWitness.absorb_X_le {P : AdmissibleParams} {ε δQ : ℝ}
    {S : ProjectiveSetting P ε} (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
    opFamilyDistSq
      (uniformDistribution
        ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
      (fun xz ab => S.place p1 ((points.Q p1.side xz.1 xz.2).effect ab))
      (fun xz ab => S.place p2 ((S.pointMeasExp p2.side .X xz.1).effect ab.1) *
        S.place p1 ((points.Q p1.side xz.1 xz.2).effect ab)) S.psiHat ≤ δQ := by
  refine le_trans ?_ (points.consistent_XZ p1 p2 hopp)
  unfold opFamilyDistSq
  apply avgOver_mono
  intro xz
  apply Finset.sum_le_sum
  intro ab _
  simpa only [ProjectiveSetting.placedMeasurement_effect, ProjectiveSetting.place_mul]
    using norm_sub_projective_mul_sq_le
      (S.placedMeasurement p2 (S.pointMeasExp p2.side .X xz.1))
      (S.placedMeasurement_isProjective p2 _ (S.pointMeasExp_isProjective _ _ _))
      ab.1 (S.place p1 ((points.Q p1.side xz.1 xz.2).effect ab))
      (S.place p2 ((S.pointMeasExp p2.side .Z xz.2).effect ab.2)) S.psiHat

/-- The joint point witness absorbs the opposite Z point projector with
error at most its actual parameter. This is the first projection step in
`lem:qld-xz-lines`, paper lines 902--915, derived from `consistent_ZX`. -/
theorem CombinedPointsWitness.absorb_Z_le {P : AdmissibleParams} {ε δQ : ℝ}
    {S : ProjectiveSetting P ε} (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
    opFamilyDistSq
      (uniformDistribution
        ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
      (fun xz ab => S.place p1 ((points.Q p1.side xz.1 xz.2).effect ab))
      (fun xz ab => S.place p2 ((S.pointMeasExp p2.side .Z xz.2).effect ab.2) *
        S.place p1 ((points.Q p1.side xz.1 xz.2).effect ab)) S.psiHat ≤ δQ := by
  refine le_trans ?_ (points.consistent_ZX p1 p2 hopp)
  unfold opFamilyDistSq
  apply avgOver_mono
  intro xz
  apply Finset.sum_le_sum
  intro ab _
  simpa only [ProjectiveSetting.placedMeasurement_effect, ProjectiveSetting.place_mul]
    using norm_sub_projective_mul_sq_le
      (S.placedMeasurement p2 (S.pointMeasExp p2.side .Z xz.2))
      (S.placedMeasurement_isProjective p2 _ (S.pointMeasExp_isProjective _ _ _))
      ab.2 (S.place p1 ((points.Q p1.side xz.1 xz.2).effect ab))
      (S.place p2 ((S.pointMeasExp p2.side .X xz.1).effect ab.1)) S.psiHat

end

end MIPStarRE.QPBT
