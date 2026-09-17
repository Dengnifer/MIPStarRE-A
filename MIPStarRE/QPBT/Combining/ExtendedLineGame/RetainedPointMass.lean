import MIPStarRE.QPBT.Combining.ExtendedLineGame.PairMeasurement
import MIPStarRE.QPBT.Combining.RetainedPointBounds

/-!
# Retained point mismatch on the faithful combining image

The outcome sum ranges over the actual bounded polynomial-pair embedding.
The projected vectors and both heterogeneous placements are preserved.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1360-1404`,
`eq:qld-s-good-and-bad` through `eq:qld-sgg-mhat-sandwich`;
blueprint `lem:qld-4-7`.
-/

open scoped BigOperators MatrixOrder

namespace MIPStarRE.QPBT.ExtendedLineGame

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus PolynomialImageBounds

noncomputable section

/-- The retained point mismatch is the squared norm of the incorrect point
projection on the actual vector `R_g psiHat`, averaged over the point. -/
def retainedPointMismatch {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (p1 p2 : Placement)
    (R : DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace p1.side))
    (W : PauliKind) : ℝ :=
  avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun x =>
    ∑ pair : PolyPair P, ‖applyOperatorToState
      (1 - S.place p2 ((S.pointMeasExp p2.side W x).effect (evalAt W x pair)))
      (applyOperatorToState (S.place p1 (R.effect (directCombinedEmbedding P pair)))
        S.psiHat)‖ ^ 2)

/-- Both retained point mismatches are bounded by their appropriate full
ordered error. The wrong point projection is the outer factor: `XZ` for X,
`ZX` for Z. Normalization is used only after summing the actual vector masses,
so there is no outcome-cardinality factor. -/
theorem retainedPointMismatch_le_ordered_error {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (p1 p2 : Placement) (hopposite : p1.IsOpposite p2)
    (R : DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace p1.side))
    (hR : Measurement.IsProjective R) (reverse : Bool) :
    retainedPointMismatch S p1 p2 R (if reverse then .Z else .X) ≤
      2 * extendedPolynomialOrderedError S p1 p2 R reverse + 4 / P.q := by
  classical
  let ψ := fun g => applyOperatorToState (S.place p1 (R.effect g)) S.psiHat
  let X := fun x : Fin P.m → PauliScalar P => S.placedMeasurement p2
    (S.pointMeasExp p2.side (if reverse then .Z else .X) x)
  let Z := fun z : Fin P.m → PauliScalar P => S.placedMeasurement p2
    (S.pointMeasExp p2.side (if reverse then .X else .Z) z)
  let A := fun (z x : Fin P.m → PauliScalar P) (v : Fin 2 → PauliScalar P) g =>
    applyOperatorToState (orderedIndicator (X x) (Z z) (v 0) (v 1)
      (extendedPolynomialRead P (fiberQuestionEquiv P reverse ((z, x), v)) g)) (ψ g)
  have hmass : ∑ g, ‖ψ g‖ ^ 2 = 1 := by
    simpa only [ψ, ProjectiveSetting.placedMeasurement_effect, S.psiHat_norm, one_pow] using
      sum_projective_state_norm_sq (S.placedMeasurement p1 R)
        (S.placedMeasurement_isProjective p1 R hR) S.psiHat
  have hretained : ∑ pair, ‖ψ (directCombinedEmbedding P pair)‖ ^ 2 ≤ 1 := by
    rw [← hmass, ← Finset.sum_image (f := fun g => ‖ψ g‖ ^ 2) (fun a _ b _ h =>
      (directCombinedEmbedding P).injective h)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
      intros; exact sq_nonneg _)
  have hread (z x : Fin P.m → PauliScalar P) (v : Fin 2 → PauliScalar P)
      (pair : PolyPair P) :
      extendedPolynomialRead P (fiberQuestionEquiv P reverse ((z, x), v))
        (directCombinedEmbedding P pair) =
      v 0 * evalAt (if reverse then .Z else .X) x pair +
        v 1 * evalAt (if reverse then .X else .Z) z pair := by
    rw [directCombinedEmbedding_read]
    cases reverse <;> simp [fiberQuestionEquiv, finTwoArrowEquiv, add_comm]
  have hpoint (z x : Fin P.m → PauliScalar P) :
      (∑ pair : PolyPair P, ‖applyOperatorToState
        (1 - (X x).effect (evalAt (if reverse then .Z else .X) x pair))
          (ψ (directCombinedEmbedding P pair))‖ ^ 2) ≤
      2 * avgOver (uniformDistribution (Fin 2 → PauliScalar P)) (fun v =>
        ∑ g, ‖ψ g - A z x v g‖ ^ 2) + 4 / P.q := by
    have h (pair : PolyPair P) := point_mismatch_le_ordered_error (X x) (Z z)
      (S.placedMeasurement_isProjective p2 _ (S.pointMeasExp_isProjective _ _ _))
      (S.placedMeasurement_isProjective p2 _ (S.pointMeasExp_isProjective _ _ _))
      (evalAt (if reverse then .Z else .X) x pair)
      (evalAt (if reverse then .X else .Z) z pair) (ψ (directCombinedEmbedding P pair))
    simp_rw [← hread z x] at h
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun pair _ => h pair)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← avgOver_sum] at hs
    have herr : avgOver (uniformDistribution (Fin 2 → PauliScalar P)) (fun v =>
        ∑ pair, ‖ψ (directCombinedEmbedding P pair) -
          A z x v (directCombinedEmbedding P pair)‖ ^ 2) ≤
      avgOver (uniformDistribution (Fin 2 → PauliScalar P)) (fun v =>
        ∑ g, ‖ψ g - A z x v g‖ ^ 2) := by
      apply avgOver_mono
      intro v
      rw [← Finset.sum_image (f := fun g => ‖ψ g - A z x v g‖ ^ 2)
        (fun a _ b _ h => (directCombinedEmbedding P).injective h)]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
        intros; exact sq_nonneg _)
    have hcard : Fintype.card (PauliScalar P) = P.q :=
      @FieldModel.card P.q P.model.toFieldModel
    have hc := mul_le_mul_of_nonneg_left hretained
      (show 0 ≤ 4 * (Fintype.card (PauliScalar P) : ℝ)⁻¹ by positivity)
    rw [hcard, mul_one] at hc
    change _ ≤ 2 * _ + 4 * (Fintype.card (PauliScalar P) : ℝ)⁻¹ * _ at hs
    rw [hcard] at hs
    change _ ≤ 2 * avgOver _ (fun v => ∑ pair,
      ‖ψ (directCombinedEmbedding P pair) - A z x v (directCombinedEmbedding P pair)‖ ^ 2) +
      4 * (P.q : ℝ)⁻¹ * _ at hs
    rw [div_eq_mul_inv]
    linarith
  have hfull :
      avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun z =>
        avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun x =>
          avgOver (uniformDistribution (Fin 2 → PauliScalar P)) (fun v =>
            ∑ g, ‖ψ g - A z x v g‖ ^ 2))) =
        extendedPolynomialOrderedError S p1 p2 R reverse := by
    rw [← avgOver_uniform_prod (fun z x =>
      avgOver (uniformDistribution (Fin 2 → PauliScalar P)) (fun v =>
        ∑ g, ‖ψ g - A z x v g‖ ^ 2))]
    rw [← avgOver_uniform_prod
      (fun zx : (Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P) =>
        fun v => ∑ g, ‖ψ g - A zx.1 zx.2 v g‖ ^ 2)]
    unfold extendedPolynomialOrderedError
    rw [avgOver_uniform_equiv (fiberQuestionEquiv P reverse).symm]
    apply avgOver_congr
    rintro ⟨⟨z, x⟩, v⟩
    apply Finset.sum_congr rfl
    intro g _
    dsimp only [A, X, Z]
    rw [placed_fiber_orderedIndicator]
    dsimp only [ψ]
    rw [placed_residual S p1 p2 hopposite]
    rfl
  have h := avgOver_mono (uniformDistribution (Fin P.m → PauliScalar P)) _ _ fun z =>
    avgOver_mono (uniformDistribution (Fin P.m → PauliScalar P)) _ _ (hpoint z)
  simp only [avgOver_uniform_const, avgOver_add, avgOver_const_mul, hfull] at h
  exact h

end

end MIPStarRE.QPBT.ExtendedLineGame
