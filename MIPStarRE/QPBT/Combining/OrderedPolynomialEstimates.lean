import MIPStarRE.QPBT.Combining.Points

/-!
# Ordered products selected by a global projective measurement

The point comparison of a projective measurement can be refined to its original
outcomes and composed with the two combined-point ordered-product estimates.
All bounds are on the actual expanded state and retain the complete outcome sum.

## References

`eq:qld-g-42` and `eq:qld-g-43`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1283-1300`.
These are auxiliary estimates for issue #513, not the global-pair constructor.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

/-- Projective refinement followed by two operator comparisons. If the evaluated
measurement has consistency defect at most `eta` with `B`, and `B` is within
`deltaSelf` of `A`, which is within `deltaOrder` of `T`, the full outcome sum
for `R - R T` is at most `4 eta + 4 deltaSelf + 4 deltaOrder`.
This is the quantitative insertion calculation in `eq:qld-g-42/43`; `T` need
not be a measurement, so it applies to either ordered product. -/
theorem projective_refinement_ordered_dist_le {X Γ α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype Γ] [DecidableEq Γ]
    [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (R : Measurement Γ ι) (hR : Measurement.IsProjective R)
    (ev : X → Γ → α) (A B : X → Measurement α ι) (T : X → α → Op ι)
    (ψ : EuclideanSpace ℂ ι) (eta deltaSelf deltaOrder : ℝ)
    (hpoint : consistencyDefect μ
      (fun x a => (R.postprocess (ev x)).effect a) (fun x a => (B x).effect a) ψ ≤ eta)
    (hself : opFamilyDistSq μ (fun x a => (B x).effect a)
      (fun x a => (A x).effect a) ψ ≤ deltaSelf)
    (horder : opFamilyDistSq μ (fun x a => (A x).effect a) T ψ ≤ deltaOrder) :
    opFamilyDistSq μ (fun _ g => R.effect g)
      (fun x g => R.effect g * T x (ev x g)) ψ ≤
        4 * eta + 4 * deltaSelf + 4 * deltaOrder := by
  have hlift (U V : X → α → Op ι) :
      opFamilyDistSq μ (fun x g => R.effect g * U x (ev x g))
        (fun x g => R.effect g * V x (ev x g)) ψ ≤ opFamilyDistSq μ U V ψ := by
    unfold opFamilyDistSq
    apply avgOver_mono
    intro x
    simpa only [mul_sub] using sum_norm_mul_funIndexed_apply_le (ev x) R.effect
      (fun a => U x a - V x a) ψ (measurement_sum_adjoint_mul_le_one R)
  have hinsert : opFamilyDistSq μ (fun _ g => R.effect g)
      (fun x g => R.effect g * (B x).effect (ev x g)) ψ ≤ 2 * eta := by
    have h := hlift (fun x a => (R.postprocess (ev x)).effect a)
      (fun x a => (B x).effect a)
    simp only [effect_mul_postprocess_effect_self R hR] at h
    exact h.trans ((opFamilyDistSq_le_two_mul_consistencyDefect μ
      (fun x => R.postprocess (ev x)) B ψ).trans (mul_le_mul_of_nonneg_left hpoint
        (by norm_num)))
  have htail := (hlift (fun x a => (B x).effect a) T).trans
    (opFamilyDistSq_le_of_le_of_le μ (fun x a => (B x).effect a)
      (fun x a => (A x).effect a) T ψ deltaSelf deltaOrder hself horder)
  have h := opFamilyDistSq_le_of_le_of_le μ (fun _ g => R.effect g)
    (fun x g => R.effect g * (B x).effect (ev x g))
    (fun x g => R.effect g * T x (ev x g)) ψ (2 * eta)
    (2 * deltaSelf + 2 * deltaOrder) hinsert htail
  convert h using 1
  ring

namespace CombinedPointsWitness

/-- Both ordered estimates `eq:qld-g-42/43` for a projective global measurement
on any expanded block, compared to point operators on its opposite block.
The readout `ev` may in particular be evaluation of an extended polynomial.
The input `eta` is the actual rounded point-comparison error, not the unrounded
low-degree error. The two losses of `deltaQ` come respectively from point
self-consistency and the existing ordered-product approximation. No global-pair
witness or concentration estimate is assumed. -/
theorem ordered_dist_le {P : AdmissibleParams} {ε δQ : ℝ}
    {S : ProjectiveSetting P ε} (points : CombinedPointsWitness S δQ)
    {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (p1 p2 : Placement) (hopposite : p1.IsOpposite p2)
    (R : Measurement Γ (S.ExpandedLocalSpace p1.side))
    (hR : Measurement.IsProjective R) (ev : ExtendedPointQuestion P → Γ → PauliScalar P)
    (eta : ℝ)
    (hpoint : consistencyDefect (uniformDistribution (ExtendedPointQuestion P))
      (fun x a => S.place p1 ((R.postprocess (ev x)).effect a))
      (fun x a => S.place p2
        ((points.extendedQ p2.side x.1.1 x.1.2 x.2.1 x.2.2).effect a)) S.psiHat ≤ eta) :
    (opFamilyDistSq (uniformDistribution (ExtendedPointQuestion P))
      (fun _ g => S.place p1 (R.effect g))
      (fun x g => S.place p1 (R.effect g) * S.place p2
        (∑ ab ∈ Finset.univ.filter (fun ab : PauliScalar P × PauliScalar P =>
            x.2.1 * ab.1 + x.2.2 * ab.2 = ev x g),
          (S.pointMeasExp p2.side .X x.1.1).effect ab.1 *
            (S.pointMeasExp p2.side .Z x.1.2).effect ab.2)) S.psiHat ≤
        4 * eta + 8 * δQ) ∧
    (opFamilyDistSq (uniformDistribution (ExtendedPointQuestion P))
      (fun _ g => S.place p1 (R.effect g))
      (fun x g => S.place p1 (R.effect g) * S.place p2
        (∑ ab ∈ Finset.univ.filter (fun ab : PauliScalar P × PauliScalar P =>
            x.2.1 * ab.1 + x.2.2 * ab.2 = ev x g),
          (S.pointMeasExp p2.side .Z x.1.2).effect ab.2 *
            (S.pointMeasExp p2.side .X x.1.1).effect ab.1)) S.psiHat ≤
        4 * eta + 8 * δQ) := by
  classical
  let A (x : ExtendedPointQuestion P) := S.placedMeasurement p1
    (points.extendedQ p1.side x.1.1 x.1.2 x.2.1 x.2.2)
  let B (x : ExtendedPointQuestion P) := S.placedMeasurement p2
    (points.extendedQ p2.side x.1.1 x.1.2 x.2.1 x.2.2)
  have hpoint' : consistencyDefect (uniformDistribution (ExtendedPointQuestion P))
      (fun x a => ((S.placedMeasurement p1 R).postprocess (ev x)).effect a)
      (fun x a => (B x).effect a) S.psiHat ≤ eta := by
    simpa only [Measurement.postprocess_effect, ProjectiveSetting.placedMeasurement_effect,
      ProjectiveSetting.place_finsetSum, B] using hpoint
  have hself : opFamilyDistSq (uniformDistribution (ExtendedPointQuestion P))
      (fun x a => (B x).effect a) (fun x a => (A x).effect a) S.psiHat ≤ δQ := by
    rw [opFamilyDistSq_symm]
    exact (extendedQ_spec points).2.1 p1 p2 hopposite
  have hbound := projective_refinement_ordered_dist_le
    (uniformDistribution (ExtendedPointQuestion P)) (S.placedMeasurement p1 R)
    (S.placedMeasurement_isProjective p1 R hR) ev A B
  constructor
  · have h := hbound _ S.psiHat eta δQ δQ hpoint' hself
      ((extendedQ_spec points).2.2.1 p1 p2 hopposite)
    simpa only [ProjectiveSetting.placedMeasurement_effect,
      show 4 * eta + 4 * δQ + 4 * δQ = 4 * eta + 8 * δQ by ring] using h
  · have h := hbound _ S.psiHat eta δQ δQ hpoint' hself
      ((extendedQ_spec points).2.2.2 p1 p2 hopposite)
    simpa only [ProjectiveSetting.placedMeasurement_effect,
      show 4 * eta + 4 * δQ + 4 * δQ = 4 * eta + 8 * δQ by ring] using h

end CombinedPointsWitness

end

end MIPStarRE.QPBT
