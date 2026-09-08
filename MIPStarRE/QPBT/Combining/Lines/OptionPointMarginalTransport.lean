import MIPStarRE.QPBT.Combining.Lines.OptionPostprocessDistance
import MIPStarRE.QPBT.Combining.Lines.PointMarginalTransport

/-!
# Completed point marginals on line-point samples

This module transports the coordinate-marginal bounds for a joint point
witness to the option-valued convention used by completed point measurements.

## References

The transport is the completion step of `eq:pasting-q1` in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:936-941`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-- Completing the X marginal and point measurement with a zero outcome
preserves the line-point distance bound from `eq:pasting-q1`. -/
theorem CombinedPointsWitness.marginal_X_option_linePoint_distance_le
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
    opFamilyDistSq (Distribution.prod (linePointDist P.toLdParams)
      (linePointDist P.toLdParams))
      (fun sample answer => S.place p1
        ((((points.Q p1.side sample.1.2 sample.2.2).postprocess Prod.fst).postprocess
          some).effect answer))
      (fun sample answer => S.place p2
        ((S.pointMeasExpOption p2.side .X sample.1.2).effect answer))
      S.psiHat ≤ 4 * δQ := by
  unfold ProjectiveSetting.pointMeasExpOption
  rw [S.opFamilyDistSq_postprocess_some]
  exact points.marginal_X_linePoint_distance_le p1 p2 hopp

/-- Completing the Z marginal and point measurement with a zero outcome
preserves the line-point distance bound from `eq:pasting-q1`. -/
theorem CombinedPointsWitness.marginal_Z_option_linePoint_distance_le
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
    opFamilyDistSq (Distribution.prod (linePointDist P.toLdParams)
      (linePointDist P.toLdParams))
      (fun sample answer => S.place p1
        ((((points.Q p1.side sample.1.2 sample.2.2).postprocess Prod.snd).postprocess
          some).effect answer))
      (fun sample answer => S.place p2
        ((S.pointMeasExpOption p2.side .Z sample.2.2).effect answer))
      S.psiHat ≤ 4 * δQ := by
  unfold ProjectiveSetting.pointMeasExpOption
  rw [S.opFamilyDistSq_postprocess_some]
  exact points.marginal_Z_linePoint_distance_le p1 p2 hopp

end

end MIPStarRE.QPBT
