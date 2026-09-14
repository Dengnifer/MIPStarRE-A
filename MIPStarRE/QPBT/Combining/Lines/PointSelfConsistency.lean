import MIPStarRE.QPBT.Combining.Points
import MIPStarRE.QPBT.Combining.Points.Placement
import MIPStarRE.QPBT.Games.Sandwich.Support
import MIPStarRE.QPBT.Test.LowDegreeGameTheorems

/-!
# Point self-consistency on line-point samples

This module converts the joint point measurement's squared-distance estimate
to the consistency-defect convention and transports it from uniform point
pairs to the point marginals of two independent line-point samples.

## References

The point estimate is `eq:qld-q-self-cons` in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:693-697`.
Its use as the second pasting hypothesis occurs at lines 955--963, while the
uniform point marginals used for the sampling transport are discussed at
lines 936--941.
-/

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

private theorem avgOver_mix_noFinite {α : Type*} [DecidableEq α]
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (μ ν : Distribution α) (f : α → ℝ) :
    avgOver (Distribution.mix t ht0 ht1 μ ν) f =
      t * avgOver μ f + (1 - t) * avgOver ν f := by
  classical
  unfold avgOver
  have hsplit : (∑ a ∈ μ.support ∪ ν.support,
        (t * μ.weight a + (1 - t) * ν.weight a) * f a) =
      t * (∑ a ∈ μ.support ∪ ν.support, μ.weight a * f a) +
        (1 - t) * (∑ a ∈ μ.support ∪ ν.support, ν.weight a * f a) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  have hμ : (∑ a ∈ μ.support ∪ ν.support, μ.weight a * f a) =
      ∑ a ∈ μ.support, μ.weight a * f a := by
    refine (Finset.sum_subset Finset.subset_union_left ?_).symm
    intro a _ ha
    rw [μ.outsideSupport a ha, zero_mul]
  have hν : (∑ a ∈ μ.support ∪ ν.support, ν.weight a * f a) =
      ∑ a ∈ ν.support, ν.weight a * f a := by
    refine (Finset.sum_subset Finset.subset_union_right ?_).symm
    intro a _ ha
    rw [ν.outsideSupport a ha, zero_mul]
  change (∑ a ∈ μ.support ∪ ν.support,
    (t * μ.weight a + (1 - t) * ν.weight a) * f a) = _
  rw [hsplit, hμ, hν]

/-- Convert the joint point witness's projective squared-distance estimate to
the consistency-defect convention required by the pasting argument. This is a
formalization-only consequence of `eq:qld-q-self-cons`, used at paper lines
955--963. -/
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

/-- The point marginal of the line-point law is uniform. This is the
formalization-only averaging step used at paper lines 936--941, based on
`lem:alnf` and `lem:dlnf`. -/
theorem avgOver_linePointDist_point (L : LdParams)
    (value : (Fin L.m → ScalarQ L) → ℝ) :
    avgOver (linePointDist L) (fun sample => value sample.2) =
      avgOver (uniformDistribution (Fin L.m → ScalarQ L)) value := by
  rw [linePointDist, avgOver_mix_noFinite]
  rw [← Distribution.avgOver_map (aLinePointDist L) Prod.snd value,
    ← Distribution.avgOver_map (dLinePointDist L) Prod.snd value,
    (aLinePointDist_point_marginal_uniform L).1,
    (dLinePointDist_point_marginal_uniform L).1]
  ring

/-- Independent line-point samples have independent uniform point marginals.
This formalization-only identity supplies the product sampling transport used
in the pasting argument at paper lines 936--941. -/
theorem avgOver_prod_linePointDist_points (L : LdParams)
    (value : (Fin L.m → ScalarQ L) × (Fin L.m → ScalarQ L) → ℝ) :
    avgOver (Distribution.prod (linePointDist L) (linePointDist L))
      (fun sample => value (sample.1.2, sample.2.2)) =
      avgOver (uniformDistribution
        ((Fin L.m → ScalarQ L) × (Fin L.m → ScalarQ L))) value := by
  calc
    avgOver (Distribution.prod (linePointDist L) (linePointDist L))
        (fun sample => value (sample.1.2, sample.2.2)) =
      avgOver (linePointDist L) (fun first =>
        avgOver (linePointDist L) (fun second => value (first.2, second.2))) :=
      SandwichProduct.avgOver_distribution_prod _ _ _
    _ = avgOver (uniformDistribution (Fin L.m → ScalarQ L)) (fun point =>
        avgOver (uniformDistribution (Fin L.m → ScalarQ L))
          (fun other => value (point, other))) := by
      conv_lhs =>
        arg 2
        ext sample
        rw [avgOver_linePointDist_point L (fun point => value (sample.2, point))]
      exact avgOver_linePointDist_point L
        (fun point => avgOver (uniformDistribution _) (fun other => value (point, other)))
    _ = avgOver (uniformDistribution
        ((Fin L.m → ScalarQ L) × (Fin L.m → ScalarQ L))) value := by
      exact (avgOver_uniform_prod (fun point other => value (point, other))).symm

/-- Transport joint point self-consistency to the point coordinates of two
independent line-point samples. This is the formalization-only sampling step
for the second pasting hypothesis at paper lines 955--963. -/
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
