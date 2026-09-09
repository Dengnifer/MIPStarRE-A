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

open scoped BigOperators

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
products and all four directed heterogeneous placement comparisons. -/
theorem exists_combinedPointsWitness :
    ∃ deltaQ : ℝ -> ℝ, IsPolyErr deltaQ ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
        Nonempty (CombinedPointsWitness S (deltaQ ε)) := by
  sorry

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
