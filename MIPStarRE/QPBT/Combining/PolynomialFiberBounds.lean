import MIPStarRE.QPBT.Combining.PolynomialImageBounds
import MIPStarRE.QPBT.Combining.PointsDataProcessing

/-!
# Common exceptional fibers for polynomial coefficients

A nonconstant polynomial in one block, with polynomial coefficients in a
second block, has one nonzero nonconstant coefficient. Its zero set controls
all exceptional specializations simultaneously, independently of the outcome
of a measurement. The weights may depend on the fixed block but not on the
block being averaged.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1341-1358`,
especially `eq:qld-g-2`; support for blueprint `lem:qld-4-7`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.PolynomialImageBounds

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private theorem exists_nonconstant_coeff {R : Type*} [CommSemiring R] {n : ℕ}
    (p : MvPolynomial (Fin n) R) (hp : ¬ ∃ r, p = MvPolynomial.C r) :
    ∃ e : Fin n →₀ ℕ, e ≠ 0 ∧ p.coeff e ≠ 0 := by
  classical
  by_contra! h
  apply hp
  refine ⟨p.coeff 0, ?_⟩
  ext e
  by_cases he : e = 0
  · simp [he]
  · simp [MvPolynomial.coeff_C, Ne.symm he, h e he]

/-- A single coefficient defines the exceptional slices for every field
outcome. Outside its zero set, every fiber has probability at most `D/q`;
the exceptional set itself has probability at most `C/q`. Both degree
conditions concern the displayed polynomial, not an assumed collision law.
This is the common-set argument following `eq:qld-g-2`, supporting
blueprint `lem:qld-4-7`. -/
theorem exists_common_exceptional_coefficient {n k C D : ℕ}
    (p : MvPolynomial (Fin n) (MvPolynomial (Fin k) F))
    (hp : ¬ ∃ r, p = MvPolynomial.C r)
    (hcoeff : ∀ e, (p.coeff e).totalDegree ≤ C) (hdegree : p.totalDegree ≤ D) :
    ∃ e : Fin n →₀ ℕ, e ≠ 0 ∧ p.coeff e ≠ 0 ∧
      avgOver (uniformDistribution (Fin k → F))
        (fun z => if MvPolynomial.eval z (p.coeff e) = 0 then 1 else 0) ≤
          (C : ℝ) / Fintype.card F ∧
      ∀ z : Fin k → F, MvPolynomial.eval z (p.coeff e) ≠ 0 → ∀ b : F,
        avgOver (uniformDistribution (Fin n → F))
          (fun x => if MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval z) p) = b
            then 1 else 0) ≤ (D : ℝ) / Fintype.card F := by
  obtain ⟨e, he, hc⟩ := exists_nonconstant_coeff p hp
  refine ⟨e, he, hc, ?_, ?_⟩
  · simpa using avg_eval_eq_le (p.coeff e) 0 hc (hcoeff e) (by simp)
  · intro z hz b
    have hne : MvPolynomial.map (MvPolynomial.eval z) p ≠ MvPolynomial.C b := by
      intro h
      apply hz
      have h' := congrArg (MvPolynomial.coeff e) h
      simpa [MvPolynomial.coeff_map, MvPolynomial.coeff_C, Ne.symm he] using h'
    have hd : (MvPolynomial.map (MvPolynomial.eval z) p).totalDegree ≤ D :=
      (Finset.sup_mono (MvPolynomial.support_map_subset _ _)).trans hdegree
    simpa using avg_eval_eq_le _ (MvPolynomial.C b) hne hd (by simp)

/-- Summing all nonnegative outcome weights before averaging exceptional
slices avoids an outcome-cardinality factor. The weights may depend on `z`
and their sum is the same mass `M` at every `z`. This is the weighted fiber
calculation in `eq:qld-g-2`, supporting blueprint `lem:qld-4-7`. -/
theorem avg_weighted_fiber_le {n k C D : ℕ}
    (p : MvPolynomial (Fin n) (MvPolynomial (Fin k) F))
    (hp : ¬ ∃ r, p = MvPolynomial.C r)
    (hcoeff : ∀ e, (p.coeff e).totalDegree ≤ C) (hdegree : p.totalDegree ≤ D)
    (w : (Fin k → F) → F → ℝ) (M : ℝ)
    (hw : ∀ z b, 0 ≤ w z b) (hsum : ∀ z, ∑ b, w z b = M) :
    avgOver (uniformDistribution (Fin k → F)) (fun z => ∑ b : F,
      avgOver (uniformDistribution (Fin n → F))
        (fun x => if MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval z) p) = b
          then 1 else 0) * w z b) ≤ ((C + D : ℕ) : ℝ) / Fintype.card F * M := by
  classical
  obtain ⟨e, _, _, hbad, hgood⟩ :=
    exists_common_exceptional_coefficient p hp hcoeff hdegree
  have hM : 0 ≤ M := by
    rw [← hsum (fun _ => 0)]
    exact Finset.sum_nonneg fun b _ => hw _ b
  have hpoint (z : Fin k → F) :
      (∑ b : F, avgOver (uniformDistribution (Fin n → F))
        (fun x => if MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval z) p) = b
          then 1 else 0) * w z b) ≤
      (if MvPolynomial.eval z (p.coeff e) = 0 then 1 else 0) * M +
        (D : ℝ) / Fintype.card F * M := by
    by_cases hz : MvPolynomial.eval z (p.coeff e) = 0
    · simp only [hz, if_true, one_mul]
      apply le_trans (b := M)
      · rw [← hsum z]
        apply Finset.sum_le_sum
        intro b _
        apply le_trans (b := 1 * w z b)
        · apply mul_le_mul_of_nonneg_right _ (hw z b)
          apply avgOver_uniform_le_const
          intro x
          split_ifs <;> norm_num
        · rw [one_mul]
      · exact le_add_of_nonneg_right (mul_nonneg (by positivity) hM)
    · simp only [hz, if_false, zero_mul, zero_add]
      rw [← hsum z, Finset.mul_sum]
      exact Finset.sum_le_sum fun b _ =>
        mul_le_mul_of_nonneg_right (hgood z hz b) (hw z b)
  calc
    _ ≤ avgOver (uniformDistribution (Fin k → F)) (fun z =>
        (if MvPolynomial.eval z (p.coeff e) = 0 then 1 else 0) * M +
          (D : ℝ) / Fintype.card F * M) := avgOver_mono _ _ _ hpoint
    _ ≤ (C : ℝ) / Fintype.card F * M + (D : ℝ) / Fintype.card F * M := by
      rw [avgOver_add, avgOver_mul_const, avgOver_uniform_const]
      exact add_le_add (mul_le_mul_of_nonneg_right hbad hM) le_rfl
    _ = _ := by push_cast; ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem avg_diagonalIndicator_linear_le
    (X Z : Quantum.Measurement F ι) (hZ : Measurement.IsProjective Z)
    (r t : F) (ψ : EuclideanSpace ℂ ι) :
    avgOver (uniformDistribution (Fin 2 → F)) (fun v =>
      stateQForm ψ (diagonalIndicator X Z (v 0) (v 1) (v 0 * r + v 1 * t))) ≤
      (Fintype.card F : ℝ)⁻¹ * ‖ψ‖ ^ 2 +
        stateQForm ψ (Z.effect t * X.effect r * Z.effect t) := by
  classical
  let w (bc : F × F) : ℝ := stateQForm ψ
    (Z.effect bc.2 * X.effect bc.1 * Z.effect bc.2)
  have hw (bc : F × F) : 0 ≤ w bc :=
    stateQForm_nonneg ψ ((pastedMeasurement_isMeasurement X Z hZ).1 bc)
  have hsum : ∑ bc, w bc = ‖ψ‖ ^ 2 := by
    rw [← stateQForm_one ψ, ← (pastedMeasurement_isMeasurement X Z hZ).2,
      stateQForm_finset_sum]
    rfl
  have hexpand (v : Fin 2 → F) :
      stateQForm ψ (diagonalIndicator X Z (v 0) (v 1) (v 0 * r + v 1 * t)) =
      ∑ bc : F × F, (if v 0 * bc.1 + v 1 * bc.2 = v 0 * r + v 1 * t
        then 1 else 0) * w bc := by
    rw [diagonalIndicator, stateQForm_finset_sum]
    apply Finset.sum_congr rfl
    intro bc _
    split_ifs <;> simp [w, stateQForm, applyOperatorToState]
  have hcollision (bc : F × F) :
      avgOver (uniformDistribution (Fin 2 → F)) (fun v =>
        if v 0 * bc.1 + v 1 * bc.2 = v 0 * r + v 1 * t then (1 : ℝ) else 0) =
        if bc = (r, t) then 1 else (Fintype.card F : ℝ)⁻¹ := by
    rw [avgOver_uniform_equiv (finTwoArrowEquiv F)]
    exact affine_collision_average bc (r, t)
  simp_rw [hexpand, avgOver_sum, avgOver_mul_const, hcollision]
  calc
    _ ≤ ∑ bc : F × F, ((Fintype.card F : ℝ)⁻¹ +
        if bc = (r, t) then 1 else 0) * w bc := by
      apply Finset.sum_le_sum
      intro bc _
      apply mul_le_mul_of_nonneg_right _ (hw bc)
      split_ifs <;> simp
    _ = _ := by
      simp_rw [add_mul, Finset.sum_add_distrib]
      rw [← Finset.mul_sum, hsum]
      simp [w]

private theorem avg_orderedIndicator_linear_le
    (X Z : Quantum.Measurement F ι) (hX : Measurement.IsProjective X)
    (hZ : Measurement.IsProjective Z) (r t : F) (ψ : EuclideanSpace ℂ ι) :
    avgOver (uniformDistribution (Fin 2 → F)) (fun v =>
      ‖applyOperatorToState (orderedIndicator X Z (v 0) (v 1)
        (v 0 * r + v 1 * t)) ψ‖ ^ 2) ≤
      2 * (Fintype.card F : ℝ)⁻¹ * ‖ψ‖ ^ 2 + stateQForm ψ (Z.effect t) := by
  have hexc : avgOver (uniformDistribution (Fin 2 → F))
      (fun v => if v 1 = 0 then ‖ψ‖ ^ 2 else 0) =
        (Fintype.card F : ℝ)⁻¹ * ‖ψ‖ ^ 2 := by
    change avgOver (uniformDistribution (Fin 2 → F))
      (fun v => if ((finTwoArrowEquiv F) v).2 = 0 then ‖ψ‖ ^ 2 else 0) = _
    rw [avgOver_uniform_equiv (finTwoArrowEquiv F)]
    simp only [Equiv.apply_symm_apply]
    rw [avgOver_uniform_snd (fun β : F => if β = 0 then ‖ψ‖ ^ 2 else 0)]
    simp [avgOver_uniform_eq_inv_card_mul_sum]
  have hdrop : stateQForm ψ (Z.effect t * X.effect r * Z.effect t) ≤
      stateQForm ψ (Z.effect t) := by
    apply quadratic_form_mono
    simpa only [Matrix.star_eq_conjTranspose, measurement_effect_hermitian, mul_one,
      (hZ t).isIdempotentElem.eq] using
      star_left_conjugate_le_conjugate (measurement_effect_le_one X r) (Z.effect t)
  have havg := avgOver_mono (uniformDistribution (Fin 2 → F)) _ _ (fun v =>
    le_trans (le_abs_self _) (abs_orderedIndicator_norm_sq_sub_diagonal_le
      X Z hX hZ (v 0) (v 1) (v 0 * r + v 1 * t) ψ))
  rw [avgOver_sub, hexc] at havg
  have hdiag := avg_diagonalIndicator_linear_le X Z hZ r t ψ
  linarith

/-- The wrong-variable coefficient is concentrated only after the middle
contraction has been removed. The outer measurement depends solely on the
fixed block `z`; `X` depends solely on the varying block `x`. For the other
class interchange `X,Z` and the two blocks. The vector is arbitrary and
need not be normalized. This proves the local norm bound behind
`eq:qld-g-prime-xpt-bound` and its reversed-order counterpart, supporting
blueprint `lem:qld-4-7`. -/
theorem avg_orderedIndicator_norm_sq_le_of_nonconstant {n k C D : ℕ}
    (p : MvPolynomial (Fin n) (MvPolynomial (Fin k) F))
    (hp : ¬ ∃ r, p = MvPolynomial.C r)
    (hcoeff : ∀ e, (p.coeff e).totalDegree ≤ C) (hdegree : p.totalDegree ≤ D)
    (r : (Fin n → F) → (Fin k → F) → F)
    (X : (Fin n → F) → Quantum.Measurement F ι)
    (Z : (Fin k → F) → Quantum.Measurement F ι)
    (hX : ∀ x, Measurement.IsProjective (X x))
    (hZ : ∀ z, Measurement.IsProjective (Z z)) (ψ : EuclideanSpace ℂ ι) :
    avgOver (uniformDistribution (Fin k → F)) (fun z =>
      avgOver (uniformDistribution (Fin n → F)) (fun x =>
        avgOver (uniformDistribution (Fin 2 → F)) (fun v =>
          ‖applyOperatorToState (orderedIndicator (X x) (Z z) (v 0) (v 1)
            (v 0 * r x z + v 1 *
              MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval z) p))) ψ‖ ^ 2))) ≤
      ((C + D + 2 : ℕ) : ℝ) / Fintype.card F * ‖ψ‖ ^ 2 := by
  classical
  let w (z : Fin k → F) (b : F) := stateQForm ψ ((Z z).effect b)
  have hsum (z : Fin k → F) : ∑ b, w z b = ‖ψ‖ ^ 2 := by
    rw [← stateQForm_finset_sum, (Z z).sum_eq_one, stateQForm_one]
  have hfiber := avg_weighted_fiber_le p hp hcoeff hdegree w (‖ψ‖ ^ 2)
    (fun z b => stateQForm_nonneg ψ ((Z z).pos b)) hsum
  have heval (z : Fin k → F) (x : Fin n → F) :
      stateQForm ψ ((Z z).effect
        (MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval z) p))) =
      ∑ b : F, (if MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval z) p) = b
        then 1 else 0) * w z b := by
    simp [w]
  calc
    _ ≤ avgOver (uniformDistribution (Fin k → F)) (fun z =>
        avgOver (uniformDistribution (Fin n → F)) (fun x =>
          2 * (Fintype.card F : ℝ)⁻¹ * ‖ψ‖ ^ 2 +
          stateQForm ψ ((Z z).effect
            (MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval z) p))))) := by
      apply avgOver_mono
      intro z
      apply avgOver_mono
      intro x
      exact avg_orderedIndicator_linear_le (X x) (Z z) (hX x) (hZ z) _ _ ψ
    _ = 2 * (Fintype.card F : ℝ)⁻¹ * ‖ψ‖ ^ 2 +
        avgOver (uniformDistribution (Fin k → F)) (fun z => ∑ b : F,
          avgOver (uniformDistribution (Fin n → F))
            (fun x => if MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval z) p) = b
              then 1 else 0) * w z b) := by
      simp_rw [heval, avgOver_add, avgOver_uniform_const, avgOver_sum, avgOver_mul_const]
    _ ≤ 2 * (Fintype.card F : ℝ)⁻¹ * ‖ψ‖ ^ 2 +
        ((C + D : ℕ) : ℝ) / Fintype.card F * ‖ψ‖ ^ 2 := add_le_add le_rfl hfiber
    _ = _ := by push_cast; ring

end

end MIPStarRE.QPBT.PolynomialImageBounds
