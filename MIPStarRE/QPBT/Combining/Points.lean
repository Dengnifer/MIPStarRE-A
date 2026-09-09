import MIPStarRE.QPBT.Combining.Points.Closeness
import MIPStarRE.QPBT.Combining.Points.WitnessMarginals
import MIPStarRE.QPBT.Combining.PointsDataProcessing

/-!
# Combining the point measurements

This module states the construction obligation for the joint X/Z point
measurements and defines their scalar linear coarse-graining.  The latter is
the genuine postprocessing of a complete measurement on each heterogeneous
player space.

## References

The construction is `lem:qld-4-10` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`, with paper source
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:689-709`.
The coarse-graining is `lem:qld-4-12` in the same blueprint, with paper source
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:993-1011`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-- A pair of source points and the two scalar coefficients used by the
extended point measurement. -/
abbrev ExtendedPointQuestion (P : AdmissibleParams) :=
  ((Fin P.m -> PauliScalar P) × (Fin P.m -> PauliScalar P)) ×
    (PauliScalar P × PauliScalar P)

namespace CombinedPointsWitness

/-- Coarse-grain a joint point measurement by `(a,b) |-> alpha*a + beta*b`
on the selected player side.  This is the concrete measurement of
`lem:qld-4-12`, paper lines 993--1011. -/
noncomputable def extendedQ {P : AdmissibleParams} {ε δ : ℝ}
    {S : ProjectiveSetting P ε} (points : CombinedPointsWitness S δ)
    (side : PlayerSide) (x z : Fin P.m -> PauliScalar P)
    (alpha beta : PauliScalar P) :
    Measurement (PauliScalar P) (S.ExpandedLocalSpace side) :=
  (points.Q side x z).postprocess fun ab => alpha * ab.1 + beta * ab.2

end CombinedPointsWitness

/-- Construction of the projective joint point measurements of
`lem:qld-4-10`, paper lines 689--709.  The witness retains both ordered
products and all four directed heterogeneous placement comparisons.

The construction works on the original expanded local spaces: the sandwich
POVM `M^Z_b M^X_a M^Z_b`, formed directly with outcomes in `F_q × F_q`, is
close to the ordered product by the field-valued commutation estimate
(`expPoint_comm`), self-consistent between opposite placements
(`sandwich_offDiagonal_le_sandwichDefectBound`), and is made projective for
each point pair by the orthonormalization lemma
(`exists_projective_close_sandwich`); the three consistency conclusions follow
by the triangle inequality (`chain_bounds`).  This replacement for the source's
binary-refinement and quantum-linearity argument is explained in
`docs/paper-gaps/qpbt_combined-points-field-valued.tex`.  It uses no additional
ancillary space and does not require the common-extension construction of
`rem:linearity-import`.  The error is
`K ε^{1/8}` for a universal constant `K`. -/
theorem exists_combinedPointsWitness :
    ∃ deltaQ : ℝ -> ℝ, IsPolyErr deltaQ ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
        Nonempty (CombinedPointsWitness S (deltaQ ε)) := by
  obtain ⟨C₀, hC₀, h₀⟩ := ProjectiveSetting.avg_sandwichDefectBound_le
  obtain ⟨C₁, hC₁, h₁⟩ := ProjectiveSetting.sandwichPoint_ordered_dist_le
  obtain ⟨C₂, hC₂, h₂⟩ := ProjectiveSetting.expPoint_comm
  obtain ⟨C₃, hC₃, h₃⟩ := ProjectiveSetting.ordered_cross_dist_le
  -- the universal constant of the final error `K ε^{1/8}`
  set K : ℝ := 12 * (440 * (2 * C₀)) + 20 * C₁ + 16 * C₃ + 4 * C₂ with hK
  have hK4 : (4 : ℝ) ≤ K := by rw [hK]; nlinarith
  refine ⟨fun ε => K * Real.rpow ε (1 / 8 : ℝ),
    ⟨K, 1 / 8, by linarith, by norm_num, fun x hx =>
      ⟨mul_nonneg (by linarith) (Real.rpow_nonneg hx _), le_rfl⟩⟩, ?_⟩
  intro P ε S
  have hε : (0 : ℝ) ≤ ε := by
    have hv := WinImplications.strategy_value_le_one S.toStrategy
    have hw := S.win
    linarith
  obtain ⟨Qa, hQa, hQaR⟩ := S.exists_projective_close_sandwich_alice
  obtain ⟨Qb, hQb, hQbR⟩ := S.exists_projective_close_sandwich_bob
  -- the joint measurements on the two sides
  let Q : (side : PlayerSide) → PointPair P →
      Measurement (PauliScalar P × PauliScalar P) (S.ExpandedLocalSpace side) :=
    fun side => match side with
      | .alice => Qa
      | .bob => Qb
  have hQproj : ∀ side xz, MIPStarRE.QPBT.Measurement.IsProjective (Q side xz) := by
    intro side xz
    cases side
    · exact hQa xz
    · exact hQb xz
  -- the closeness of `Q` to the sandwich on every placement
  set η : ℝ := 440 * Real.rpow (C₀ * (ε + Real.sqrt ε)) (1 / 4 : ℝ) with hη
  have hbound : ∀ p₁ p₂ : Placement, p₁.IsOpposite p₂ →
      220 * Real.rpow (avgOver (uniformDistribution (PointPair P))
        (S.sandwichDefectBound p₁ p₂)) (1 / 4 : ℝ) ≤ η := by
    intro p₁ p₂ hopp
    have hnn : 0 ≤ avgOver (uniformDistribution (PointPair P))
        (S.sandwichDefectBound p₁ p₂) :=
      avgOver_nonneg _ _ (S.sandwichDefectBound_nonneg p₁ p₂)
    have hr : Real.rpow (avgOver (uniformDistribution (PointPair P))
        (S.sandwichDefectBound p₁ p₂)) (1 / 4 : ℝ) ≤
        Real.rpow (C₀ * (ε + Real.sqrt ε)) (1 / 4 : ℝ) :=
      Real.rpow_le_rpow hnn (h₀ P ε S p₁ p₂ hopp) (by norm_num)
    have hr0 : 0 ≤ Real.rpow (C₀ * (ε + Real.sqrt ε)) (1 / 4 : ℝ) :=
      Real.rpow_nonneg (by positivity) _
    rw [hη]
    nlinarith
  have hQR : ∀ p : Placement, opFamilyDistSq (uniformDistribution (PointPair P))
      (fun xz (ab : PauliScalar P × PauliScalar P) =>
        S.place p ((Q p.side xz).effect ab))
      (fun xz ab => S.place p ((S.sandwichPoint p.side xz.1 xz.2).effect ab))
      S.psiHat ≤ η := by
    intro p
    cases p
    · exact le_trans hQaR (hbound .AA' .BA'' trivial)
    · exact le_trans hQbR (hbound .BA'' .AA' trivial)
    · rw [ProjectiveSetting.opFamilyDistSq_place_BB'_eq_BA'']
      exact le_trans hQbR (hbound .BA'' .AA' trivial)
    · rw [ProjectiveSetting.opFamilyDistSq_place_AB''_eq_AA']
      exact le_trans hQaR (hbound .AA' .BA'' trivial)
  have hchain := fun (p₁ p₂ : Placement) (hopp : p₁.IsOpposite p₂) =>
    S.chain_bounds Q η C₁ C₂ C₃ hQR (h₁ P ε S) (h₂ P ε S) (h₃ P ε S) p₁ p₂ hopp
  -- the numeric bound on the longest chain, in the two regimes of `ε`
  have hηnn : 0 ≤ η := by
    rw [hη]
    exact mul_nonneg (by norm_num)
      (Real.rpow_nonneg (mul_nonneg (by linarith) (add_nonneg hε (Real.sqrt_nonneg ε))) _)
  have hs : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  have htotal : 12 * η + 20 * (C₁ * Real.sqrt ε) + 16 * (C₃ * ε) +
      4 * (C₂ * Real.sqrt ε) ≤ K * Real.rpow ε (1 / 8 : ℝ) ∨ 1 < ε := by
    by_cases hε1 : ε ≤ 1
    · left
      obtain ⟨hε8, hs8, hq8⟩ := error_terms_le_rpow_eighth hε hε1 hC₀
      rw [hη, hK]
      nlinarith [mul_le_mul_of_nonneg_left hq8 (by norm_num : (0 : ℝ) ≤ 440),
        mul_le_mul_of_nonneg_left hs8 (by linarith : (0 : ℝ) ≤ C₁),
        mul_le_mul_of_nonneg_left hs8 (by linarith : (0 : ℝ) ≤ C₂),
        mul_le_mul_of_nonneg_left hε8 (by linarith : (0 : ℝ) ≤ C₃)]
    · right
      exact lt_of_not_ge hε1
  have hK8 : 1 < ε → (4 : ℝ) ≤ K * Real.rpow ε (1 / 8 : ℝ) := by
    intro hε1
    have h1 : (1 : ℝ) ≤ Real.rpow ε (1 / 8 : ℝ) :=
      Real.one_le_rpow (le_of_lt hε1) (by norm_num)
    nlinarith
  have hsub1 : 2 * η + 4 * (C₁ * Real.sqrt ε) + 4 * (C₃ * ε) ≤
      12 * η + 20 * (C₁ * Real.sqrt ε) + 16 * (C₃ * ε) + 4 * (C₂ * Real.sqrt ε) := by
    nlinarith
  have hsub2 : 4 * η + 8 * (C₁ * Real.sqrt ε) + 8 * (C₃ * ε) +
      2 * (C₂ * Real.sqrt ε) ≤
      12 * η + 20 * (C₁ * Real.sqrt ε) + 16 * (C₃ * ε) + 4 * (C₂ * Real.sqrt ε) := by
    nlinarith
  -- square-summability of the families, for the trivial bound
  have hsqQ : ∀ (p : Placement) (xz : PointPair P),
      (∑ ab : PauliScalar P × PauliScalar P,
        (S.place p ((Q p.side xz).effect ab))ᴴ *
          S.place p ((Q p.side xz).effect ab)) ≤ 1 :=
    fun p xz => S.sum_place_effect_conjTranspose_mul_self_le_one p _ (hQproj p.side xz)
  have hsqXZ : ∀ (p : Placement) (xz : PointPair P),
      (∑ ab : PauliScalar P × PauliScalar P,
        (S.place p ((S.pointMeasExp p.side .X xz.1).effect ab.1 *
          (S.pointMeasExp p.side .Z xz.2).effect ab.2))ᴴ *
        S.place p ((S.pointMeasExp p.side .X xz.1).effect ab.1 *
          (S.pointMeasExp p.side .Z xz.2).effect ab.2)) ≤ 1 := by
    intro p xz
    refine le_of_eq ?_
    simp only [ProjectiveSetting.place_mul]
    exact sum_mul_conjTranspose_mul_self_eq_one
      (S.placedMeasurement p (S.pointMeasExp p.side .X xz.1))
      (S.placedMeasurement p (S.pointMeasExp p.side .Z xz.2))
      (S.placedMeasurement_isProjective p _ (S.pointMeasExp_isProjective _ _ _))
      (S.placedMeasurement_isProjective p _ (S.pointMeasExp_isProjective _ _ _))
  have hsqZX : ∀ (p : Placement) (xz : PointPair P),
      (∑ ab : PauliScalar P × PauliScalar P,
        (S.place p ((S.pointMeasExp p.side .Z xz.2).effect ab.2 *
          (S.pointMeasExp p.side .X xz.1).effect ab.1))ᴴ *
        S.place p ((S.pointMeasExp p.side .Z xz.2).effect ab.2 *
          (S.pointMeasExp p.side .X xz.1).effect ab.1)) ≤ 1 := by
    intro p xz
    refine le_of_eq ?_
    simp only [ProjectiveSetting.place_mul]
    exact sum_mul_conjTranspose_mul_self_eq_one'
      (S.placedMeasurement p (S.pointMeasExp p.side .X xz.1))
      (S.placedMeasurement p (S.pointMeasExp p.side .Z xz.2))
      (S.placedMeasurement_isProjective p _ (S.pointMeasExp_isProjective _ _ _))
      (S.placedMeasurement_isProjective p _ (S.pointMeasExp_isProjective _ _ _))
  refine ⟨CombinedPointsWitness.mk (fun side x z => Q side (x, z)) ?_ ?_ ?_ ?_⟩
  · intro side x z
    exact hQproj side (x, z)
  · intro p₁ p₂ hopp
    rcases htotal with htot | hε1
    · exact le_trans (hchain p₁ p₂ hopp).2.2 htot
    · exact le_trans (opFamilyDistSq_uniform_le_four _ _ S.psiHat S.psiHat_norm
        (fun xz => hsqQ p₁ xz) (fun xz => hsqQ p₂ xz)) (hK8 hε1)
  · intro p₁ p₂ hopp
    rcases htotal with htot | hε1
    · exact le_trans (hchain p₁ p₂ hopp).1 (le_trans hsub1 htot)
    · exact le_trans (opFamilyDistSq_uniform_le_four _ _ S.psiHat S.psiHat_norm
        (fun xz => hsqQ p₁ xz) (fun xz => hsqXZ p₂ xz)) (hK8 hε1)
  · intro p₁ p₂ hopp
    rcases htotal with htot | hε1
    · exact le_trans (hchain p₁ p₂ hopp).2.1 (le_trans hsub2 htot)
    · exact le_trans (opFamilyDistSq_uniform_le_four _ _ S.psiHat S.psiHat_norm
        (fun xz => hsqQ p₁ xz) (fun xz => hsqZX p₂ xz)) (hK8 hε1)

/-- Register placement distributes over a filtered outcome sum. -/
private theorem place_finset_sum {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (p : Placement) {α : Type*}
    (s : Finset α) (A : α → Op (S.ExpandedLocalSpace p.side)) :
    S.place p (∑ a ∈ s, A a) = ∑ a ∈ s, S.place p (A a) := by
  classical
  ext i j
  cases p <;> simp [ProjectiveSetting.place, Matrix.sum_apply,
    Finset.sum_mul, Finset.mul_sum]

set_option maxHeartbeats 1600000 in
/-- Projectivity and the three data-processed consistency guarantees for
`CombinedPointsWitness.extendedQ`.  This is `lem:qld-4-12`, paper lines
993--1011; the `XZ` and `ZX` source products remain separate. -/
theorem extendedQ_spec {P : AdmissibleParams} {ε δ : ℝ}
    {S : ProjectiveSetting P ε} (points : CombinedPointsWitness S δ) :
    (∀ side x z alpha beta,
      Measurement.IsProjective (points.extendedQ side x z alpha beta)) ∧
    (∀ p1 p2 : Placement, p1.IsOpposite p2 ->
      opFamilyDistSq (uniformDistribution (ExtendedPointQuestion P))
        (fun question c => S.place p1
          ((points.extendedQ p1.side question.1.1 question.1.2
            question.2.1 question.2.2).effect c))
        (fun question c => S.place p2
          ((points.extendedQ p2.side question.1.1 question.1.2
            question.2.1 question.2.2).effect c))
        S.psiHat <= δ) ∧
    (∀ p1 p2 : Placement, p1.IsOpposite p2 ->
      opFamilyDistSq (uniformDistribution (ExtendedPointQuestion P))
        (fun question c => S.place p1
          ((points.extendedQ p1.side question.1.1 question.1.2
            question.2.1 question.2.2).effect c))
        (fun question c => S.place p2
          (∑ ab ∈ Finset.univ.filter (fun ab : PauliScalar P × PauliScalar P =>
              question.2.1 * ab.1 + question.2.2 * ab.2 = c),
            (S.pointMeasExp p2.side .X question.1.1).effect ab.1 *
              (S.pointMeasExp p2.side .Z question.1.2).effect ab.2))
        S.psiHat <= δ) ∧
    ∀ p1 p2 : Placement, p1.IsOpposite p2 ->
      opFamilyDistSq (uniformDistribution (ExtendedPointQuestion P))
        (fun question c => S.place p1
          ((points.extendedQ p1.side question.1.1 question.1.2
            question.2.1 question.2.2).effect c))
        (fun question c => S.place p2
          (∑ ab ∈ Finset.univ.filter (fun ab : PauliScalar P × PauliScalar P =>
              question.2.1 * ab.1 + question.2.2 * ab.2 = c),
            (S.pointMeasExp p2.side .Z question.1.2).effect ab.2 *
              (S.pointMeasExp p2.side .X question.1.1).effect ab.1))
        S.psiHat <= δ := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro side x z alpha beta
    exact SandwichProduct.postprocess_isProjective _ (points.projective side x z) _
  · intro p1 p2 hopposite
    let A : ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)) →
        (PauliScalar P × PauliScalar P) → Op (SixReg P S.toStrategy.ιA S.toStrategy.ιB) :=
      fun xz ab => S.place p1 ((points.Q p1.side xz.1 xz.2).effect ab)
    let B : ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)) →
        (PauliScalar P × PauliScalar P) → Op (SixReg P S.toStrategy.ιA S.toStrategy.ιB) :=
      fun xz ab => S.place p2 ((points.Q p2.side xz.1 xz.2).effect ab)
    refine le_trans ?_ (points.self_consistent p1 p2 hopposite)
    have h := opFamilyDistSq_uniform_affine_postprocess_le A B S.psiHat (fun xz => ?_)
    · simpa only [A, B, CombinedPointsWitness.extendedQ,
        Measurement.postprocess_effect, place_finset_sum] using h
    · rw [sum_placed_measurement_eq_one, sum_placed_measurement_eq_one]
  · intro p1 p2 hopposite
    let A : ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)) →
        (PauliScalar P × PauliScalar P) → Op (SixReg P S.toStrategy.ιA S.toStrategy.ιB) :=
      fun xz ab => S.place p1 ((points.Q p1.side xz.1 xz.2).effect ab)
    let B : ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)) →
        (PauliScalar P × PauliScalar P) → Op (SixReg P S.toStrategy.ιA S.toStrategy.ιB) :=
      fun xz ab => S.place p2
        ((S.pointMeasExp p2.side .X xz.1).effect ab.1 *
          (S.pointMeasExp p2.side .Z xz.2).effect ab.2)
    refine le_trans ?_ (points.consistent_XZ p1 p2 hopposite)
    have h := opFamilyDistSq_uniform_affine_postprocess_le A B S.psiHat (fun xz => ?_)
    · simpa only [A, B, CombinedPointsWitness.extendedQ,
        Measurement.postprocess_effect, place_finset_sum] using h
    · rw [sum_placed_measurement_eq_one, sum_placed_measurement_products_eq_one]
  · intro p1 p2 hopposite
    let A : ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)) →
        (PauliScalar P × PauliScalar P) → Op (SixReg P S.toStrategy.ιA S.toStrategy.ιB) :=
      fun xz ab => S.place p1 ((points.Q p1.side xz.1 xz.2).effect ab)
    let B : ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)) →
        (PauliScalar P × PauliScalar P) → Op (SixReg P S.toStrategy.ιA S.toStrategy.ιB) :=
      fun xz ab => S.place p2
        ((S.pointMeasExp p2.side .Z xz.2).effect ab.2 *
          (S.pointMeasExp p2.side .X xz.1).effect ab.1)
    refine le_trans ?_ (points.consistent_ZX p1 p2 hopposite)
    have h := opFamilyDistSq_uniform_affine_postprocess_le A B S.psiHat (fun xz => ?_)
    · simpa only [A, B, CombinedPointsWitness.extendedQ,
        Measurement.postprocess_effect, place_finset_sum] using h
    · rw [sum_placed_measurement_eq_one]
      have htotal := sum_placed_measurement_products_eq_one S p2
        (S.pointMeasExp p2.side .Z xz.2) (S.pointMeasExp p2.side .X xz.1)
      rw [Fintype.sum_prod_type, Finset.sum_comm] at htotal
      simpa only [B, Fintype.sum_prod_type] using htotal.symm

end


end MIPStarRE.QPBT
