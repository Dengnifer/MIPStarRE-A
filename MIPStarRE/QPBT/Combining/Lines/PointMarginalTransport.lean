import MIPStarRE.QPBT.Combining.Lines.PointSelfConsistency
import MIPStarRE.QPBT.Combining.Points.WitnessMarginals

/-!
# Point marginals on line-point samples

This module transports the two coordinate-marginal squared-distance bounds for
a joint point witness from uniform point pairs to the point coordinates of two
independent line-point samples.

## References

The transport is the first step of `eq:pasting-q1` in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:936-941`.
-/

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-- The X marginal distance on the product line-point law, retaining the
supplied point-witness error. This is the first transport step of
`eq:pasting-q1`, paper lines 936--941; no line comparison is assumed. -/
theorem CombinedPointsWitness.marginal_X_linePoint_distance_le
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
    opFamilyDistSq (Distribution.prod (linePointDist P.toLdParams)
      (linePointDist P.toLdParams))
      (fun sample a => S.place p1
        (((points.Q p1.side sample.1.2 sample.2.2).postprocess Prod.fst).effect a))
      (fun sample a => S.place p2 ((S.pointMeasExp p2.side .X sample.1.2).effect a))
      S.psiHat ≤ 4 * δQ := by
  classical
  simp_rw [points.postprocess_fst_effect, place_sum]
  unfold opFamilyDistSq
  rw [avgOver_prod_linePointDist_points P.toLdParams (fun xz =>
    ∑ a, ‖applyOperatorToState
      ((∑ b, S.place p1 ((points.Q p1.side xz.1 xz.2).effect (a, b))) -
        S.place p2 ((S.pointMeasExp p2.side .X xz.1).effect a)) S.psiHat‖ ^ 2)]
  exact points.marginal_X_distance_le p1 p2 hopp

/-- The Z marginal distance on the product line-point law, with the same error
as the uniform-point estimate. This is the second transport step of
`eq:pasting-q1`, paper lines 936--941. -/
theorem CombinedPointsWitness.marginal_Z_linePoint_distance_le
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
    opFamilyDistSq (Distribution.prod (linePointDist P.toLdParams)
      (linePointDist P.toLdParams))
      (fun sample b => S.place p1
        (((points.Q p1.side sample.1.2 sample.2.2).postprocess Prod.snd).effect b))
      (fun sample b => S.place p2 ((S.pointMeasExp p2.side .Z sample.2.2).effect b))
      S.psiHat ≤ 4 * δQ := by
  classical
  simp_rw [points.postprocess_snd_effect, place_sum]
  unfold opFamilyDistSq
  rw [avgOver_prod_linePointDist_points P.toLdParams (fun xz =>
    ∑ b, ‖applyOperatorToState
      ((∑ a, S.place p1 ((points.Q p1.side xz.1 xz.2).effect (a, b))) -
        S.place p2 ((S.pointMeasExp p2.side .Z xz.2).effect b)) S.psiHat‖ ^ 2)]
  exact points.marginal_Z_distance_le p1 p2 hopp

end

end MIPStarRE.QPBT
