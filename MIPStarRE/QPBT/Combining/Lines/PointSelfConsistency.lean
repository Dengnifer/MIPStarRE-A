import MIPStarRE.QPBT.Combining.Lines.PointComparison

/-!
# Point self-consistency on line-point samples

This module converts the joint point witness's squared-distance estimate to a
consistency defect and transports it to independent line-point samples.

## References

The source point estimate is `eq:qld-q-self-cons` in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:693-697`.
Its use in pasting occurs at lines 955--963; uniform point marginals are used
at lines 936--941. These are formalization-only supplied-witness estimates.
-/

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-- Convert the joint point witness's projective squared-distance estimate to
the consistency-defect convention used in the pasting argument. This is a
formalization-only consequence of `eq:qld-q-self-cons`, paper lines 955--963. -/
theorem CombinedPointsWitness.self_consistency_defect_le
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
    consistencyDefect
      (uniformDistribution
        ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
      (fun xz ab => S.place p1 ((points.Q p1.side xz.1 xz.2).effect ab))
      (fun xz ab => S.place p2 ((points.Q p2.side xz.1 xz.2).effect ab))
      S.psiHat ≤ δQ := by
  exact le_trans (consistencyDefect_le_opFamilyDistSq_of_projective _
    (fun xz : (Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P) =>
      S.placedMeasurement p1 (points.Q p1.side xz.1 xz.2))
    (fun xz : (Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P) =>
      S.placedMeasurement p2 (points.Q p2.side xz.1 xz.2)) S.psiHat
    (fun xz => S.placedMeasurement_isProjective p1 _
      (points.projective _ xz.1 xz.2))
    (fun xz => S.placedMeasurement_isProjective p2 _
      (points.projective _ xz.1 xz.2)))
    (points.self_consistent p1 p2 hopp)

/-- Transport joint point self-consistency to the point coordinates of two
independent line-point samples. This formalization-only sampling step uses the
uniform point marginals of paper lines 936--941 in the second pasting
hypothesis at lines 955--963. -/
theorem CombinedPointsWitness.self_consistency_linePoint_defect_le
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
    consistencyDefect (Distribution.prod (linePointDist P.toLdParams)
      (linePointDist P.toLdParams))
      (fun sample ab =>
        S.place p1 ((points.Q p1.side sample.1.2 sample.2.2).effect ab))
      (fun sample ab =>
        S.place p2 ((points.Q p2.side sample.1.2 sample.2.2).effect ab))
      S.psiHat ≤ δQ := by
  classical
  have htransport := avgOver_prod_linePointDist_points P.toLdParams (fun xz =>
    ∑ ab, ∑ cd, if ab = cd then 0 else
      (inner ℂ S.psiHat ((EuclideanSpace.equiv _ ℂ).symm
        ((S.place p1 ((points.Q p1.side xz.1 xz.2).effect ab) *
          S.place p2 ((points.Q p2.side xz.1 xz.2).effect cd)) *ᵥ S.psiHat.ofLp))).re)
  unfold consistencyDefect
  rw [htransport]
  exact points.self_consistency_defect_le p1 p2 hopp

end

end MIPStarRE.QPBT
