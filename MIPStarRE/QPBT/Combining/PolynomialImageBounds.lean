import MIPStarRE.LDT.Preliminaries.Polynomials
import MIPStarRE.QPBT.Games.Sandwich
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.GroundSlice

/-!
# Indicator-weighted ordered projectors

This module proves the local norm calculation in `eq:qld-g-prime`. The state
vector is not assumed normalized: its squared norm controls the exceptional
coefficient, so the estimate can be summed over all polynomial outcomes.
The measurements act on an arbitrary finite space, which includes either
player's placed expanded measurements.

The coefficient-polynomial argument also bounds mass outside the scalar-linear
image, with its actual ordered-correlation error displayed in the conclusion.
These are auxiliary estimates, not the global polynomial-pair construction.
The remaining block-separation and construction obligations are recorded in
`docs/paper-gaps/qpbt_combined-lines-error-term.tex` and issue #118.

## References

* Blueprint `lem:aux-ordered-nonlinear-mass`, a formalization-only auxiliary.
* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1289-1320`,
  especially `eq:qld-g-42`, `eq:qld-g-43`, and `eq:qld-g-prime`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

namespace PolynomialImageBounds

variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι]

/-- The ordered product selected by the linear field-answer check in
`eq:qld-g-42`. This is an operator, not an asserted measurement effect. -/
def orderedIndicator (X Z : Quantum.Measurement F ι) (α β a : F) : Op ι :=
  ∑ bc : F × F, if α * bc.1 + β * bc.2 = a then X.effect bc.1 * Z.effect bc.2 else 0

/-- The diagonal sandwich sum in `eq:qld-g-prime`. -/
def diagonalIndicator (X Z : Quantum.Measurement F ι) (α β a : F) : Op ι :=
  ∑ bc : F × F,
    if α * bc.1 + β * bc.2 = a then
      Z.effect bc.2 * X.effect bc.1 * Z.effect bc.2 else 0

/-- For a nonzero second coefficient, X orthogonality and cancellation in
the field eliminate every off-diagonal term of the ordered Gram operator.
This is the exact local algebra behind `eq:qld-g-prime`; no commutation of
the X and Z measurements is assumed. -/
theorem orderedIndicator_gram_of_ne_zero (X Z : Quantum.Measurement F ι)
    (hX : Measurement.IsProjective X) (α β a : F) (hβ : β ≠ 0) :
    (orderedIndicator X Z α β a)ᴴ * orderedIndicator X Z α β a =
      diagonalIndicator X Z α β a := by
  classical
  unfold orderedIndicator diagonalIndicator
  rw [Matrix.conjTranspose_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun bc _ => ?_
  rw [Finset.mul_sum, Finset.sum_eq_single bc]
  · by_cases h : α * bc.1 + β * bc.2 = a
    · simp only [if_pos h, Matrix.conjTranspose_mul, measurement_effect_hermitian]
      rw [mul_assoc (Z.effect bc.2), ← mul_assoc (X.effect bc.1),
        (hX bc.1).isIdempotentElem.eq, ← mul_assoc]
    · simp [h]
  · intro bc' _ hne
    by_cases h : α * bc.1 + β * bc.2 = a
    · by_cases h' : α * bc'.1 + β * bc'.2 = a
      · have hb : bc.1 ≠ bc'.1 := by
          intro hb
          have hc : bc.2 = bc'.2 := mul_left_cancel₀ hβ (by
            apply add_left_cancel (a := α * bc.1)
            simpa only [hb] using h.trans h'.symm)
          exact hne (Prod.ext hb hc).symm
        simp only [if_pos h, if_pos h', Matrix.conjTranspose_mul,
          measurement_effect_hermitian]
        calc
          Z.effect bc.2 * X.effect bc.1 * (X.effect bc'.1 * Z.effect bc'.2) =
              Z.effect bc.2 * (X.effect bc.1 * X.effect bc'.1) * Z.effect bc'.2 := by
            simp only [mul_assoc]
          _ = 0 := by rw [projective_effect_mul_effect_eq_zero X hX hb]; simp
      · simp [h']
    · simp [h]
  · simp

/-- The squared state norm of the ordered indicator equals its diagonal
sandwich quadratic form when the second coefficient is nonzero. -/
theorem orderedIndicator_norm_sq_of_ne_zero (X Z : Quantum.Measurement F ι)
    (hX : Measurement.IsProjective X) (α β a : F) (hβ : β ≠ 0)
    (ψ : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState (orderedIndicator X Z α β a) ψ‖ ^ 2 =
      stateQForm ψ (diagonalIndicator X Z α β a) := by
  rw [MagicSquareRigidity.norm_applyOperatorToState_sq,
    orderedIndicator_gram_of_ne_zero X Z hX α β a hβ]
  rfl

/-- The diagonal indicator is a positive contraction, since it selects
effects from the complete sandwich POVM. -/
theorem diagonalIndicator_bounds (X Z : Quantum.Measurement F ι)
    (hZ : Measurement.IsProjective Z) (α β a : F) :
    0 ≤ diagonalIndicator X Z α β a ∧ diagonalIndicator X Z α β a ≤ 1 := by
  obtain ⟨hpos, hsum⟩ := pastedMeasurement_isMeasurement X Z hZ
  change (∀ bc : F × F, 0 ≤ Z.effect bc.2 * X.effect bc.1 * Z.effect bc.2) at hpos
  change (∑ bc : F × F, Z.effect bc.2 * X.effect bc.1 * Z.effect bc.2) = 1 at hsum
  constructor
  · exact Finset.sum_nonneg fun bc _ => by
      split_ifs
      · exact hpos bc
      · exact le_refl 0
  · calc
      diagonalIndicator X Z α β a ≤
          ∑ bc : F × F, Z.effect bc.2 * X.effect bc.1 * Z.effect bc.2 := by
        refine Finset.sum_le_sum fun bc _ => ?_
        split_ifs
        · exact le_refl _
        · exact hpos bc
      _ = 1 := hsum

/-- At the exceptional coefficient zero, completeness of Z leaves a
coarse-grained X projection. This includes zero first coefficient. -/
theorem orderedIndicator_zero (X Z : Quantum.Measurement F ι) (α a : F) :
    orderedIndicator X Z α 0 a = (X.postprocess (fun b => α * b)).effect a := by
  unfold orderedIndicator
  rw [Fintype.sum_prod_type, Quantum.Measurement.postprocess_effect, Finset.sum_filter]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h : α * b = a
  · simp only [zero_mul, add_zero, h, if_true]
    rw [← Finset.mul_sum, Z.sum_eq_one, mul_one]
  · simp [h]

/-- Every linear-answer ordered indicator is a contraction. For nonzero
second coefficient this follows from the diagonal identity; at zero it
follows from completeness and projective postprocessing. -/
theorem orderedIndicator_gram_le_one (X Z : Quantum.Measurement F ι)
    (hX : Measurement.IsProjective X) (hZ : Measurement.IsProjective Z) (α β a : F) :
    (orderedIndicator X Z α β a)ᴴ * orderedIndicator X Z α β a ≤ 1 := by
  by_cases hβ : β = 0
  · subst β
    rw [orderedIndicator_zero, measurement_effect_hermitian,
      (SandwichProduct.postprocess_isProjective X hX (fun b => α * b) a).isIdempotentElem.eq]
    exact measurement_effect_le_one _ _
  · rw [orderedIndicator_gram_of_ne_zero X Z hX α β a hβ]
    exact (diagonalIndicator_bounds X Z hZ α β a).2

/-- The pointwise error in `eq:qld-g-prime` is supported on the zero second
coefficient and bounded by the squared norm of the actual state vector. -/
theorem abs_orderedIndicator_norm_sq_sub_diagonal_le (X Z : Quantum.Measurement F ι)
    (hX : Measurement.IsProjective X) (hZ : Measurement.IsProjective Z)
    (α β a : F) (ψ : EuclideanSpace ℂ ι) :
    |‖applyOperatorToState (orderedIndicator X Z α β a) ψ‖ ^ 2 -
        stateQForm ψ (diagonalIndicator X Z α β a)| ≤
      if β = 0 then ‖ψ‖ ^ 2 else 0 := by
  by_cases hβ : β = 0
  · rw [if_pos hβ]
    have hA0 := sq_nonneg ‖applyOperatorToState (orderedIndicator X Z α β a) ψ‖
    have hA1 : ‖applyOperatorToState (orderedIndicator X Z α β a) ψ‖ ^ 2 ≤ ‖ψ‖ ^ 2 := by
      rw [MagicSquareRigidity.norm_applyOperatorToState_sq, ← stateQForm_one ψ]
      exact quadratic_form_mono (orderedIndicator_gram_le_one X Z hX hZ α β a) ψ
    have hD := diagonalIndicator_bounds X Z hZ α β a
    have hD0 := stateQForm_nonneg ψ hD.1
    have hD1 : stateQForm ψ (diagonalIndicator X Z α β a) ≤ ‖ψ‖ ^ 2 := by
      rw [← stateQForm_one ψ]
      exact quadratic_form_mono hD.2 ψ
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · rw [if_neg hβ, orderedIndicator_norm_sq_of_ne_zero X Z hX α β a hβ ψ]
    simp

/-- The genuine uniform field average of the exceptional error is at most
`q⁻¹ * ‖ψ‖²`, even when the tested answer depends arbitrarily on the coefficient. -/
theorem avg_abs_orderedIndicator_norm_sq_sub_diagonal_le (X Z : Quantum.Measurement F ι)
    (hX : Measurement.IsProjective X) (hZ : Measurement.IsProjective Z)
    (α : F) (a : F → F) (ψ : EuclideanSpace ℂ ι) :
    avgOver (uniformDistribution F) (fun β =>
      |‖applyOperatorToState (orderedIndicator X Z α β (a β)) ψ‖ ^ 2 -
        stateQForm ψ (diagonalIndicator X Z α β (a β))|) ≤
      (Fintype.card F : ℝ)⁻¹ * ‖ψ‖ ^ 2 := by
  calc
    _ ≤ avgOver (uniformDistribution F) (fun β : F => if β = 0 then ‖ψ‖ ^ 2 else 0) :=
      avgOver_mono _ _ _ fun β =>
        abs_orderedIndicator_norm_sq_sub_diagonal_le X Z hX hZ α β (a β) ψ
    _ = _ := by simp [avgOver_uniform_eq_inv_card_mul_sum]

/-- The exceptional error can be summed over any finite collection of state
vectors. Its bound is the total squared mass, with no outcome-cardinality factor. -/
theorem avg_sum_abs_orderedIndicator_norm_sq_sub_diagonal_le {Γ : Type*} [Fintype Γ]
    (X Z : Quantum.Measurement F ι)
    (hX : Measurement.IsProjective X) (hZ : Measurement.IsProjective Z)
    (α : F) (a : Γ → F → F) (ψ : Γ → EuclideanSpace ℂ ι) :
    avgOver (uniformDistribution F) (fun β => ∑ g : Γ,
      |‖applyOperatorToState (orderedIndicator X Z α β (a g β)) (ψ g)‖ ^ 2 -
        stateQForm (ψ g) (diagonalIndicator X Z α β (a g β))|) ≤
      (Fintype.card F : ℝ)⁻¹ * ∑ g : Γ, ‖ψ g‖ ^ 2 := by
  rw [avgOver_sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun g _ =>
    avg_abs_orderedIndicator_norm_sq_sub_diagonal_le X Z hX hZ α (a g) (ψ g)

/-- Completeness and projectivity preserve total squared state mass. This is
the normalization used after summing `eq:qld-g-prime` over polynomial labels. -/
theorem sum_projective_state_norm_sq {Γ : Type*} [Fintype Γ]
    (S : Quantum.Measurement Γ ι) (hS : Measurement.IsProjective S)
    (ψ : EuclideanSpace ℂ ι) :
    ∑ g : Γ, ‖applyOperatorToState (S.effect g) ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
  simp_rw [MagicSquareRigidity.norm_applyOperatorToState_sq, measurement_effect_hermitian,
    fun g => (hS g).isIdempotentElem.eq]
  change (∑ g : Γ, stateQForm ψ (S.effect g)) = ‖ψ‖ ^ 2
  rw [← stateQForm_finset_sum, S.sum_eq_one, stateQForm_one]

/-- Summing the exceptional estimate over all outcomes of a complete projective
measurement costs `q⁻¹ * ‖ψ‖²`. There is no commutation assumption on S, X, or Z. -/
theorem avg_sum_abs_projective_orderedIndicator_le {Γ : Type*} [Fintype Γ]
    (S : Quantum.Measurement Γ ι) (X Z : Quantum.Measurement F ι)
    (hS : Measurement.IsProjective S)
    (hX : Measurement.IsProjective X) (hZ : Measurement.IsProjective Z)
    (α : F) (a : Γ → F → F) (ψ : EuclideanSpace ℂ ι) :
    avgOver (uniformDistribution F) (fun β => ∑ g : Γ,
      |‖applyOperatorToState (orderedIndicator X Z α β (a g β))
          (applyOperatorToState (S.effect g) ψ)‖ ^ 2 -
        stateQForm (applyOperatorToState (S.effect g) ψ)
          (diagonalIndicator X Z α β (a g β))|) ≤
      (Fintype.card F : ℝ)⁻¹ * ‖ψ‖ ^ 2 := by
  simpa only [sum_projective_state_norm_sq S hS ψ] using
    avg_sum_abs_orderedIndicator_norm_sq_sub_diagonal_le X Z hX hZ α a
      (fun g => applyOperatorToState (S.effect g) ψ)

/-- The full uniform law on base points and both scalar coefficients preserves
the `q⁻¹` exceptional bound after summing all polynomial labels. The base type
may be the pair of X and Z point spaces. -/
theorem avg_uniform_sum_abs_projective_orderedIndicator_le
    {T Γ : Type*} [Fintype T] [DecidableEq T] [Nonempty T] [Fintype Γ]
    (S : Quantum.Measurement Γ ι) (X Z : T → Quantum.Measurement F ι)
    (hS : Measurement.IsProjective S)
    (hX : ∀ t, Measurement.IsProjective (X t))
    (hZ : ∀ t, Measurement.IsProjective (Z t))
    (a : Γ → T → F → F → F) (ψ : EuclideanSpace ℂ ι) :
    avgOver (uniformDistribution (T × (F × F))) (fun tαβ => ∑ g : Γ,
      |‖applyOperatorToState
          (orderedIndicator (X tαβ.1) (Z tαβ.1) tαβ.2.1 tαβ.2.2
            (a g tαβ.1 tαβ.2.1 tαβ.2.2)) (applyOperatorToState (S.effect g) ψ)‖ ^ 2 -
        stateQForm (applyOperatorToState (S.effect g) ψ)
          (diagonalIndicator (X tαβ.1) (Z tαβ.1) tαβ.2.1 tαβ.2.2
            (a g tαβ.1 tαβ.2.1 tαβ.2.2))|) ≤
      (Fintype.card F : ℝ)⁻¹ * ‖ψ‖ ^ 2 := by
  rw [avgOver_uniform_prod (fun (t : T) (αβ : F × F) => ∑ g : Γ,
    |‖applyOperatorToState (orderedIndicator (X t) (Z t) αβ.1 αβ.2 (a g t αβ.1 αβ.2))
        (applyOperatorToState (S.effect g) ψ)‖ ^ 2 -
      stateQForm (applyOperatorToState (S.effect g) ψ)
        (diagonalIndicator (X t) (Z t) αβ.1 αβ.2 (a g t αβ.1 αβ.2))|)]
  apply avgOver_uniform_le_const
  intro t
  rw [avgOver_uniform_prod (fun (α β : F) => ∑ g : Γ,
    |‖applyOperatorToState (orderedIndicator (X t) (Z t) α β (a g t α β))
        (applyOperatorToState (S.effect g) ψ)‖ ^ 2 -
      stateQForm (applyOperatorToState (S.effect g) ψ)
        (diagonalIndicator (X t) (Z t) α β (a g t α β))|)]
  apply avgOver_uniform_le_const
  intro α
  exact avg_sum_abs_projective_orderedIndicator_le S (X t) (Z t) hS (hX t) (hZ t)
    α (fun g β => a g t α β) ψ

/-- Reversing the product amounts to exchanging the measurements and the
coefficients. Thus the same norm and average estimates also apply to
`eq:qld-g-43`, with the exceptional coefficient alpha instead of beta. -/
theorem orderedIndicator_reverse (X Z : Quantum.Measurement F ι) (α β a : F) :
    (∑ bc : F × F,
      if α * bc.1 + β * bc.2 = a then Z.effect bc.2 * X.effect bc.1 else 0) =
      orderedIndicator Z X β α a := by
  unfold orderedIndicator
  exact Fintype.sum_equiv (Equiv.prodComm F F) _ _ fun bc => by simp [add_comm]

/-- A polynomial not of the form `alpha * u + beta * v` has a nonzero
coefficient outside those two monomials. Applied over the ring of base-point
polynomials, this chooses one coefficient independently of both measurement
outcomes in the argument following `eq:qld-g-prime`. -/
theorem exists_nonzero_nonlinear_coeff {R : Type*} [CommRing R]
    (p : MvPolynomial (Fin 2) R)
    (hp : ¬ ∃ u v : R, p = MvPolynomial.C u * MvPolynomial.X 0 +
      MvPolynomial.C v * MvPolynomial.X 1) :
    ∃ e : Fin 2 →₀ ℕ, e ≠ Finsupp.single 0 1 ∧ e ≠ Finsupp.single 1 1 ∧
      p.coeff e ≠ 0 := by
  classical
  have h01 : (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := by
    intro h
    simpa using congrArg (fun e : Fin 2 →₀ ℕ => e 0) h
  by_contra! h
  apply hp
  refine ⟨p.coeff (Finsupp.single 0 1), p.coeff (Finsupp.single 1 1), ?_⟩
  ext e
  by_cases h0 : e = Finsupp.single 0 1
  · subst e
    simp [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, Ne.symm h01]
  · by_cases h1 : e = Finsupp.single 1 1
    · subst e
      simp [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, h01]
    · simp [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, Ne.symm h0, Ne.symm h1,
        h e h0 h1]

omit [Fintype F] [DecidableEq F] in
/-- A nonzero specialized coefficient outside the scalar-linear monomials
certifies nonzero difference from every `alpha * b + beta * c` simultaneously.
This is the common good-base-point criterion needed before sandwich weighting. -/
theorem specialization_ne_linear_of_coeff {n : ℕ}
    (p : MvPolynomial (Fin 2) (MvPolynomial (Fin n) F)) (e : Fin 2 →₀ ℕ)
    (he0 : e ≠ Finsupp.single 0 1) (he1 : e ≠ Finsupp.single 1 1)
    (u : Fin n → F) (hu : MvPolynomial.eval u (p.coeff e) ≠ 0) (b c : F) :
    MvPolynomial.map (MvPolynomial.eval u) p ≠
      MvPolynomial.C b * MvPolynomial.X 0 + MvPolynomial.C c * MvPolynomial.X 1 := by
  intro h
  apply hu
  have hc := congrArg (MvPolynomial.coeff e) h
  simpa [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X,
    Ne.symm he0, Ne.symm he1] using hc

private theorem avg_eval_eq_le {n D : ℕ} (p r : MvPolynomial (Fin n) F)
    (hne : p ≠ r) (hp : p.totalDegree ≤ D) (hr : r.totalDegree ≤ D) :
    avgOver (uniformDistribution (Fin n → F))
      (fun u => if MvPolynomial.eval u p = MvPolynomial.eval u r then 1 else 0) ≤
      (D : ℝ) / Fintype.card F := by
  have hsz := Preliminaries.schwartzZippel_totalDegree hne hp hr
  calc
    _ = (Preliminaries.polynomialAgreementProbability n F p r : ℝ) := by
      simp [avgOver_uniform_eq_inv_card_mul_sum,
        Preliminaries.polynomialAgreementProbability, div_eq_mul_inv, mul_comm]
    _ ≤ (((D : ℚ≥0) / Fintype.card F : ℚ≥0) : ℝ) := by exact_mod_cast hsz
    _ = _ := by simp

/-- On every base point where the selected coefficient remains nonzero,
Schwartz--Zippel bounds agreement with each linear answer polynomial. The
bound is derived from coefficient polynomials, not assumed as a collision law. -/
theorem avg_specialization_eq_linear_le_of_coeff {n : ℕ}
    (p : MvPolynomial (Fin 2) (MvPolynomial (Fin n) F)) (e : Fin 2 →₀ ℕ)
    (he0 : e ≠ Finsupp.single 0 1) (he1 : e ≠ Finsupp.single 1 1)
    (u : Fin n → F) (hu : MvPolynomial.eval u (p.coeff e) ≠ 0) (b c : F) :
    avgOver (uniformDistribution (Fin 2 → F)) (fun v =>
      if MvPolynomial.eval v (MvPolynomial.map (MvPolynomial.eval u) p) =
        v 0 * b + v 1 * c then 1 else 0) ≤
      (max 1 p.totalDegree : ℕ) / (Fintype.card F : ℝ) := by
  have hdeg : (MvPolynomial.map (MvPolynomial.eval u) p).totalDegree ≤ p.totalDegree :=
    Finset.sup_mono (MvPolynomial.support_map_subset _ _)
  have hlin : (MvPolynomial.C b * MvPolynomial.X (0 : Fin 2) +
      MvPolynomial.C c * MvPolynomial.X (1 : Fin 2)).totalDegree ≤ 1 := by
    apply (MvPolynomial.totalDegree_add _ _).trans
    apply max_le
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
  simpa [mul_comm] using
    avg_eval_eq_le _ _ (specialization_ne_linear_of_coeff p e he0 he1 u hu b c)
      (hdeg.trans (le_max_right 1 _)) (hlin.trans (le_max_left 1 _))

/-- The first polynomial-image estimate for the diagonal sandwich, with
explicit degrees of the scalar polynomial and its base-point coefficients.
A single nonzero nonlinear coefficient supplies a common exceptional set for
all outcomes. Neither a uniform-collision premise nor an outcome-count loss
occurs. The nested polynomial ring is the coefficient expansion used at paper
lines 1311--1316; this theorem does not assert the later block-separation step. -/
theorem avg_diagonalIndicator_le_of_not_linear {n : ℕ}
    (p : MvPolynomial (Fin 2) (MvPolynomial (Fin n) F))
    (hp : ¬ ∃ r s : MvPolynomial (Fin n) F,
      p = MvPolynomial.C r * MvPolynomial.X 0 + MvPolynomial.C s * MvPolynomial.X 1)
    (X Z : (Fin n → F) → Quantum.Measurement F ι)
    (hZ : ∀ u, Measurement.IsProjective (Z u)) (ψ : EuclideanSpace ℂ ι) :
    avgOver (uniformDistribution (Fin n → F)) (fun u =>
      avgOver (uniformDistribution (Fin 2 → F)) (fun v =>
        stateQForm ψ (diagonalIndicator (X u) (Z u) (v 0) (v 1)
          (MvPolynomial.eval v (MvPolynomial.map (MvPolynomial.eval u) p))))) ≤
      ((p.support.sup fun e => (p.coeff e).totalDegree) + max 1 p.totalDegree : ℕ) /
        (Fintype.card F : ℝ) * ‖ψ‖ ^ 2 := by
  classical
  obtain ⟨e, he0, he1, he⟩ := exists_nonzero_nonlinear_coeff p hp
  let D : ℕ := p.support.sup fun e => (p.coeff e).totalDegree
  let E : ℝ := (max 1 p.totalDegree : ℕ) / (Fintype.card F : ℝ)
  let w (u : Fin n → F) (bc : F × F) : ℝ :=
    stateQForm ψ ((Z u).effect bc.2 * (X u).effect bc.1 * (Z u).effect bc.2)
  let f (u : Fin n → F) (v : Fin 2 → F) : F :=
    MvPolynomial.eval v (MvPolynomial.map (MvPolynomial.eval u) p)
  have hw (u : Fin n → F) (bc : F × F) : 0 ≤ w u bc :=
    stateQForm_nonneg ψ ((pastedMeasurement_isMeasurement (X u) (Z u) (hZ u)).1 bc)
  have hsum (u : Fin n → F) : ∑ bc : F × F, w u bc = ‖ψ‖ ^ 2 := by
    rw [← stateQForm_one ψ,
      ← (pastedMeasurement_isMeasurement (X u) (Z u) (hZ u)).2, stateQForm_finset_sum]
    rfl
  have hexpand (u : Fin n → F) (v : Fin 2 → F) :
      stateQForm ψ (diagonalIndicator (X u) (Z u) (v 0) (v 1) (f u v)) =
        ∑ bc : F × F, (if f u v = v 0 * bc.1 + v 1 * bc.2 then 1 else 0) * w u bc := by
    rw [diagonalIndicator, stateQForm_finset_sum]
    refine Finset.sum_congr rfl fun bc _ => ?_
    by_cases h : f u v = v 0 * bc.1 + v 1 * bc.2
    · simp [h, w]
    · simp [Ne.symm h, h, stateQForm, applyOperatorToState]
  have hgood (u : Fin n → F) (hu : MvPolynomial.eval u (p.coeff e) ≠ 0) :
      avgOver (uniformDistribution (Fin 2 → F)) (fun v =>
        stateQForm ψ (diagonalIndicator (X u) (Z u) (v 0) (v 1) (f u v))) ≤
        E * ‖ψ‖ ^ 2 := by
    simp_rw [hexpand, avgOver_sum, avgOver_mul_const]
    rw [← hsum u, Finset.mul_sum]
    exact Finset.sum_le_sum fun bc _ => mul_le_mul_of_nonneg_right
      (avg_specialization_eq_linear_le_of_coeff p e he0 he1 u hu bc.1 bc.2) (hw u bc)
  have hpoint (u : Fin n → F) :
      avgOver (uniformDistribution (Fin 2 → F)) (fun v =>
        stateQForm ψ (diagonalIndicator (X u) (Z u) (v 0) (v 1) (f u v))) ≤
        (if MvPolynomial.eval u (p.coeff e) = 0 then 1 else 0) * ‖ψ‖ ^ 2 + E * ‖ψ‖ ^ 2 := by
    by_cases hu : MvPolynomial.eval u (p.coeff e) = 0
    · simp only [hu, if_true, one_mul]
      apply le_trans (b := ‖ψ‖ ^ 2)
      · apply avgOver_uniform_le_const
        intro v
        rw [← stateQForm_one ψ]
        exact quadratic_form_mono (diagonalIndicator_bounds (X u) (Z u) (hZ u) _ _ _).2 ψ
      · exact le_add_of_nonneg_right (mul_nonneg (by positivity) (sq_nonneg _))
    · simpa only [hu, if_false, zero_mul, zero_add] using hgood u hu
  have hbad : avgOver (uniformDistribution (Fin n → F))
      (fun u => if MvPolynomial.eval u (p.coeff e) = 0 then 1 else 0) ≤
        (D : ℝ) / Fintype.card F := by
    simpa using avg_eval_eq_le (p.coeff e) 0 he
      (Finset.le_sup (f := fun j => (p.coeff j).totalDegree)
        (MvPolynomial.mem_support_iff.mpr he)) (by simp)
  calc
    _ ≤ avgOver (uniformDistribution (Fin n → F)) (fun u =>
        (if MvPolynomial.eval u (p.coeff e) = 0 then 1 else 0) * ‖ψ‖ ^ 2 + E * ‖ψ‖ ^ 2) :=
      avgOver_mono _ _ _ hpoint
    _ ≤ (D : ℝ) / Fintype.card F * ‖ψ‖ ^ 2 + E * ‖ψ‖ ^ 2 := by
      rw [avgOver_add, avgOver_mul_const, avgOver_uniform_const]
      exact add_le_add (mul_le_mul_of_nonneg_right hbad (sq_nonneg _)) le_rfl
    _ = _ := by dsimp [D, E]; push_cast; ring

/-- Adding the genuinely uniform zero-coefficient contribution gives the
ordered-projector estimate for a polynomial outside the scalar-linear image.
The right side retains the squared norm of the unnormalized state. -/
theorem avg_orderedIndicator_norm_sq_le_of_not_linear {n : ℕ}
    (p : MvPolynomial (Fin 2) (MvPolynomial (Fin n) F))
    (hp : ¬ ∃ r s : MvPolynomial (Fin n) F,
      p = MvPolynomial.C r * MvPolynomial.X 0 + MvPolynomial.C s * MvPolynomial.X 1)
    (X Z : (Fin n → F) → Quantum.Measurement F ι)
    (hX : ∀ u, Measurement.IsProjective (X u))
    (hZ : ∀ u, Measurement.IsProjective (Z u)) (ψ : EuclideanSpace ℂ ι) :
    avgOver (uniformDistribution (Fin n → F)) (fun u =>
      avgOver (uniformDistribution (Fin 2 → F)) (fun v =>
        ‖applyOperatorToState (orderedIndicator (X u) (Z u) (v 0) (v 1)
          (MvPolynomial.eval v (MvPolynomial.map (MvPolynomial.eval u) p))) ψ‖ ^ 2)) ≤
      ((p.support.sup fun e => (p.coeff e).totalDegree) + max 1 p.totalDegree + 1 : ℕ) /
        (Fintype.card F : ℝ) * ‖ψ‖ ^ 2 := by
  let f (u : Fin n → F) (v : Fin 2 → F) : F :=
    MvPolynomial.eval v (MvPolynomial.map (MvPolynomial.eval u) p)
  have hexc : avgOver (uniformDistribution (Fin 2 → F))
      (fun v => if v 1 = 0 then ‖ψ‖ ^ 2 else 0) =
        (Fintype.card F : ℝ)⁻¹ * ‖ψ‖ ^ 2 := by
    change avgOver (uniformDistribution (Fin 2 → F))
      (fun v => if ((finTwoArrowEquiv F) v).2 = 0 then ‖ψ‖ ^ 2 else 0) = _
    rw [avgOver_uniform_equiv (finTwoArrowEquiv F)]
    simp only [Equiv.apply_symm_apply]
    rw [avgOver_uniform_snd (fun β : F => if β = 0 then ‖ψ‖ ^ 2 else 0)]
    simp [avgOver_uniform_eq_inv_card_mul_sum]
  calc
    _ ≤ avgOver (uniformDistribution (Fin n → F)) (fun u =>
        avgOver (uniformDistribution (Fin 2 → F)) (fun v =>
          stateQForm ψ (diagonalIndicator (X u) (Z u) (v 0) (v 1) (f u v)) +
            (if v 1 = 0 then ‖ψ‖ ^ 2 else 0))) := by
      apply avgOver_mono
      intro u
      apply avgOver_mono
      intro v
      have habs := abs_orderedIndicator_norm_sq_sub_diagonal_le
        (X u) (Z u) (hX u) (hZ u) (v 0) (v 1) (f u v) ψ
      have hle := le_trans (le_abs_self _) habs
      linarith
    _ = avgOver (uniformDistribution (Fin n → F)) (fun u =>
        avgOver (uniformDistribution (Fin 2 → F)) (fun v =>
          stateQForm ψ (diagonalIndicator (X u) (Z u) (v 0) (v 1) (f u v)))) +
            (Fintype.card F : ℝ)⁻¹ * ‖ψ‖ ^ 2 := by
      simp_rw [avgOver_add, hexc, avgOver_uniform_const]
    _ ≤ ((p.support.sup fun e => (p.coeff e).totalDegree) + max 1 p.totalDegree : ℕ) /
        (Fintype.card F : ℝ) * ‖ψ‖ ^ 2 + (Fintype.card F : ℝ)⁻¹ * ‖ψ‖ ^ 2 :=
      add_le_add (avg_diagonalIndicator_le_of_not_linear p hp X Z hZ ψ) le_rfl
    _ = _ := by push_cast; ring

/-- The ordered polynomial estimate sums over any specified set of polynomial
labels outside the scalar-linear image. Each label is weighted by its actual
state mass; the estimate never replaces a sum by the number of labels. -/
theorem avg_sum_orderedIndicator_norm_sq_le_of_not_linear {n : ℕ} {Γ : Type*}
    (s : Finset Γ) (p : Γ → MvPolynomial (Fin 2) (MvPolynomial (Fin n) F))
    (hp : ∀ g ∈ s, ¬ ∃ r t : MvPolynomial (Fin n) F,
      p g = MvPolynomial.C r * MvPolynomial.X 0 + MvPolynomial.C t * MvPolynomial.X 1)
    (X Z : (Fin n → F) → Quantum.Measurement F ι)
    (hX : ∀ u, Measurement.IsProjective (X u))
    (hZ : ∀ u, Measurement.IsProjective (Z u)) (ψ : Γ → EuclideanSpace ℂ ι) :
    avgOver (uniformDistribution (Fin n → F)) (fun u =>
      avgOver (uniformDistribution (Fin 2 → F)) (fun v => ∑ g ∈ s,
        ‖applyOperatorToState (orderedIndicator (X u) (Z u) (v 0) (v 1)
          (MvPolynomial.eval v (MvPolynomial.map (MvPolynomial.eval u) (p g)))) (ψ g)‖ ^ 2)) ≤
      ∑ g ∈ s,
        (((p g).support.sup fun e => ((p g).coeff e).totalDegree) +
          max 1 (p g).totalDegree + 1 : ℕ) / (Fintype.card F : ℝ) * ‖ψ g‖ ^ 2 := by
  simp_rw [avgOver_finset_sum]
  exact Finset.sum_le_sum fun g hg =>
    avg_orderedIndicator_norm_sq_le_of_not_linear (p g) (hp g hg) X Z hX hZ (ψ g)

/-- Scalar-linearity concentration with the actual ordered-correlation error
displayed in the conclusion. Combining this inequality with `eq:qld-g-42`
requires deriving that correlation from the source measurements; no such
estimate is an input to this auxiliary theorem. -/
theorem nonlinear_mass_le_ordered_error {n : ℕ} {Γ : Type*}
    (s : Finset Γ) (p : Γ → MvPolynomial (Fin 2) (MvPolynomial (Fin n) F))
    (hp : ∀ g ∈ s, ¬ ∃ r t : MvPolynomial (Fin n) F,
      p g = MvPolynomial.C r * MvPolynomial.X 0 + MvPolynomial.C t * MvPolynomial.X 1)
    (X Z : (Fin n → F) → Quantum.Measurement F ι)
    (hX : ∀ u, Measurement.IsProjective (X u))
    (hZ : ∀ u, Measurement.IsProjective (Z u)) (ψ : Γ → EuclideanSpace ℂ ι) :
    ∑ g ∈ s, ‖ψ g‖ ^ 2 ≤
      2 * avgOver (uniformDistribution (Fin n → F)) (fun u =>
        avgOver (uniformDistribution (Fin 2 → F)) (fun v => ∑ g ∈ s,
          ‖ψ g - applyOperatorToState (orderedIndicator (X u) (Z u) (v 0) (v 1)
            (MvPolynomial.eval v (MvPolynomial.map (MvPolynomial.eval u) (p g)))) (ψ g)‖ ^ 2)) +
      2 * ∑ g ∈ s,
        (((p g).support.sup fun e => ((p g).coeff e).totalDegree) +
          max 1 (p g).totalDegree + 1 : ℕ) / (Fintype.card F : ℝ) * ‖ψ g‖ ^ 2 := by
  let A (u : Fin n → F) (v : Fin 2 → F) (g : Γ) : EuclideanSpace ℂ ι :=
    applyOperatorToState (orderedIndicator (X u) (Z u) (v 0) (v 1)
      (MvPolynomial.eval v (MvPolynomial.map (MvPolynomial.eval u) (p g)))) (ψ g)
  have hpoint (u : Fin n → F) (v : Fin 2 → F) :
      ∑ g ∈ s, ‖ψ g‖ ^ 2 ≤
        2 * ∑ g ∈ s, ‖ψ g - A u v g‖ ^ 2 + 2 * ∑ g ∈ s, ‖A u v g‖ ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun g _ => ?_
    have htriangle := norm_add_le (ψ g - A u v g) (A u v g)
    rw [sub_add_cancel] at htriangle
    have hsquare := pow_le_pow_left₀ (norm_nonneg _) htriangle 2
    nlinarith [sq_nonneg (‖ψ g - A u v g‖ - ‖A u v g‖)]
  have havg := avgOver_mono (uniformDistribution (Fin n → F)) _ _ fun u =>
    avgOver_mono (uniformDistribution (Fin 2 → F)) _ _ (hpoint u)
  simp only [avgOver_uniform_const, avgOver_add, avgOver_const_mul] at havg
  have hnorm := avg_sum_orderedIndicator_norm_sq_le_of_not_linear s p hp X Z hX hZ ψ
  change ∑ g ∈ s, ‖ψ g‖ ^ 2 ≤ 2 * avgOver (uniformDistribution (Fin n → F))
    (fun u => avgOver (uniformDistribution (Fin 2 → F))
      (fun v => ∑ g ∈ s, ‖ψ g - A u v g‖ ^ 2)) + _
  change avgOver (uniformDistribution (Fin n → F))
    (fun u => avgOver (uniformDistribution (Fin 2 → F))
      (fun v => ∑ g ∈ s, ‖A u v g‖ ^ 2)) ≤ _ at hnorm
  linarith

end PolynomialImageBounds

end

end MIPStarRE.QPBT
