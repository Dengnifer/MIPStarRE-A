import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.Assembly

/-!
# Transporting the first logical pair through the two-qubit controlled swap

The bit-measurement conclusions of `thm:ms-rigidity` compare each player's
variable-0 and variable-4 measurements, conjugated by the two-qubit
controlled-swap embedding, with the marginals of the two-qubit Pauli basis over
the first register coordinate.  `Rigidity/TwoQubitIntertwine.lean` identifies
those marginals with the spectral effects of the two-qubit Pauli observables.
This file carries the one-qubit intertwining relations of `Rigidity/Swap.lean`
through the *second* controlled swap, which is the remaining step.

The transport is expressed at the level of the matrix of the embedding.  The
phase observable is transported exactly, because the residual factors of the
first swap absorb their controlling observable with the sign of the register
label and the residual factors of the second swap are untouched.  For the shift
observable the transport defect `D` satisfies the exact identity
`Dᴴ D = (1/2) · GᴴG`, where `G` is the anticommutator of the first pair: the
residual factors of the second swap form a complete family and therefore drop
out of `Dᴴ D`, leaving the one-qubit computation of `Rigidity/Swap.lean`.  The
spectral effects of the two observables inherit these estimates with a further
factor `1/4`, and tensoring with the other player's embedding preserves them
because that embedding is an isometry.

## References

`thm:ms-rigidity`, blueprint `blueprint/src/chapter/ch13_qpbt_test.tex:224-253`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`;
the cited robust self-test is Coladangelo--Stark, arXiv:1709.09267v2,
Theorem 6.9, `references/cs-paper/self-testing.tex:660-730`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-! ## Matrix products with a register operator placed on the left -/

/-- Formalization-only: the entries of a product whose left factor acts on the
register coordinate only. -/
theorem heteroKron_left_mul_apply {κ ι ι' : Type} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] (M : Op κ) (W : Matrix (κ × ι) ι' ℂ)
    (e : κ) (i : ι) (i' : ι') :
    (heteroKron M (1 : Op ι) * W) (e, i) i' = ∑ e' : κ, M e e' * W (e', i) i' := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun e' _ => ?_
  have hentry : ∀ i'' : ι,
      heteroKron M (1 : Op ι) (e, i) (e', i'') * W (e', i'') i' =
        if i = i'' then M e e' * W (e', i'') i' else 0 := by
    intro i''
    by_cases h : i = i''
    · subst h
      simp [heteroKron, Matrix.kronecker]
    · simp [heteroKron, Matrix.kronecker, h]
  rw [Finset.sum_congr rfl fun i'' _ => hentry i'', Finset.sum_ite_eq]
  simp

/-- Formalization-only: the two-qubit phase observable acts on the register
coordinate by the sign of its first entry. -/
theorem twoQubitPauliObs_Z_mul_apply {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    (W : Matrix ((Fin 2 → ZMod 2) × ι) ι' ℂ) (e : Fin 2 → ZMod 2) (i : ι) (i' : ι') :
    (heteroKron (twoQubitPauliObs .Z) (1 : Op ι) * W) (e, i) i' =
      phaseSign (e 0) * W (e, i) i' := by
  rw [heteroKron_left_mul_apply]
  have hterm : ∀ e' : Fin 2 → ZMod 2,
      twoQubitPauliObs .Z e e' * W (e', i) i' =
        if e = e' then phaseSign (e' 0) * W (e', i) i' else 0 := by
    intro e'
    rw [twoQubitPauliObs_Z_apply]
    by_cases h : e = e' <;> simp [h]
  rw [Finset.sum_congr rfl fun e' _ => hterm e', Finset.sum_ite_eq]
  simp

/-- Formalization-only: adding the first basis label twice is the identity. -/
theorem add_single_zero_add_single_zero (e : Fin 2 → ZMod 2) :
    e + Pi.single (0 : Fin 2) (1 : ZMod 2) + Pi.single (0 : Fin 2) (1 : ZMod 2) = e := by
  have htwo : ∀ y : ZMod 2, y + y = 0 := by decide
  funext x
  simp only [Pi.add_apply, add_assoc, htwo, add_zero]

/-- Formalization-only: the two-qubit shift observable shifts the first entry of
the register coordinate. -/
theorem twoQubitPauliObs_X_mul_apply {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    (W : Matrix ((Fin 2 → ZMod 2) × ι) ι' ℂ) (e : Fin 2 → ZMod 2) (i : ι) (i' : ι') :
    (heteroKron (twoQubitPauliObs .X) (1 : Op ι) * W) (e, i) i' =
      W (e + Pi.single (0 : Fin 2) (1 : ZMod 2), i) i' := by
  rw [heteroKron_left_mul_apply]
  have hterm : ∀ e' : Fin 2 → ZMod 2,
      twoQubitPauliObs .X e e' * W (e', i) i' =
        if e + Pi.single (0 : Fin 2) (1 : ZMod 2) = e' then W (e', i) i' else 0 := by
    intro e'
    rw [twoQubitPauliObs_X_apply]
    by_cases h : e + Pi.single (0 : Fin 2) (1 : ZMod 2) = e'
    · have h' : e = e' + Pi.single (0 : Fin 2) (1 : ZMod 2) := by
        rw [← h, add_single_zero_add_single_zero]
      rw [if_pos h', if_pos h, one_mul]
    · have h' : ¬ e = e' + Pi.single (0 : Fin 2) (1 : ZMod 2) := by
        intro hc
        exact h (by rw [hc, add_single_zero_add_single_zero])
      rw [if_neg h', if_neg h, zero_mul]
  rw [Finset.sum_congr rfl fun e' _ => hterm e', Finset.sum_ite_eq]
  simp

/-! ## Block decomposition of a Gram matrix -/

/-- Formalization-only: the Gram matrix of a matrix indexed by a register label
is the sum of the Gram matrices of its blocks. -/
theorem conjTranspose_mul_of_blocks {κ ι ι' : Type} [Fintype κ] [Fintype ι] [Fintype ι']
    (E : Matrix (κ × ι) ι' ℂ) (F : κ → Matrix ι ι' ℂ)
    (hE : ∀ (k : κ) (i : ι) (i' : ι'), E (k, i) i' = F k i i') :
    Eᴴ * E = ∑ k : κ, (F k)ᴴ * F k := by
  ext a b
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact Finset.sum_congr rfl fun i _ => by rw [hE, hE]

/-! ## The matrix of the two-qubit controlled swap -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Formalization-only abbreviation: the matrix of the two-qubit controlled-swap
embedding attached to two pairs of binary observables. -/
noncomputable def twoSwapMatrix (X₁ Z₁ X₂ Z₂ : Op ι)
    (hX₁ : IsBinaryObservable X₁) (hZ₁ : IsBinaryObservable Z₁)
    (hX₂ : IsBinaryObservable X₂) (hZ₂ : IsBinaryObservable Z₂) :
    Matrix ((Fin 2 → ZMod 2) × ι) ι ℂ :=
  isometryMatrix (twoBinarySwapIsometry X₁ Z₁ X₂ Z₂ hX₁ hZ₁ hX₂ hZ₂)

/-- Formalization-only: the entries of the matrix of the two-qubit controlled
swap are those of the composed residual factors. -/
theorem twoSwapMatrix_apply (X₁ Z₁ X₂ Z₂ : Op ι)
    (hX₁ : IsBinaryObservable X₁) (hZ₁ : IsBinaryObservable Z₁)
    (hX₂ : IsBinaryObservable X₂) (hZ₂ : IsBinaryObservable Z₂)
    (e : Fin 2 → ZMod 2) (i i' : ι) :
    twoSwapMatrix X₁ Z₁ X₂ Z₂ hX₁ hZ₁ hX₂ hZ₂ (e, i) i' =
      (swapFactor X₂ Z₂ (e 1) * swapFactor X₁ Z₁ (e 0)) i i' :=
  isometryMatrix_of_family (twoBinarySwapIsometry X₁ Z₁ X₂ Z₂ hX₁ hZ₁ hX₂ hZ₂)
    (fun e => swapFactor X₂ Z₂ (e 1) * swapFactor X₁ Z₁ (e 0)) (fun _ _ _ => rfl) e i i'

/-- The two-qubit controlled swap transports the phase observable of the first
logical pair exactly to the two-qubit phase observable. -/
theorem twoSwap_matrix_intertwines_Z (X₁ Z₁ X₂ Z₂ : Op ι)
    (hX₁ : IsBinaryObservable X₁) (hZ₁ : IsBinaryObservable Z₁)
    (hX₂ : IsBinaryObservable X₂) (hZ₂ : IsBinaryObservable Z₂) :
    heteroKron (twoQubitPauliObs .Z) (1 : Op ι) *
        twoSwapMatrix X₁ Z₁ X₂ Z₂ hX₁ hZ₁ hX₂ hZ₂ -
      twoSwapMatrix X₁ Z₁ X₂ Z₂ hX₁ hZ₁ hX₂ hZ₂ * Z₁ = 0 := by
  ext p i'
  obtain ⟨e, i⟩ := p
  rw [Matrix.sub_apply, Matrix.zero_apply, sub_eq_zero, twoQubitPauliObs_Z_mul_apply,
    twoSwapMatrix_apply]
  have hR : (twoSwapMatrix X₁ Z₁ X₂ Z₂ hX₁ hZ₁ hX₂ hZ₂ * Z₁)
      (e, i) i' = (swapFactor X₂ Z₂ (e 1) * swapFactor X₁ Z₁ (e 0) * Z₁) i i' := by
    rw [Matrix.mul_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun j _ => by
      rw [twoSwapMatrix_apply]
  have hAZ : swapFactor X₂ Z₂ (e 1) * swapFactor X₁ Z₁ (e 0) * Z₁ =
      phaseSign (e 0) • (swapFactor X₂ Z₂ (e 1) * swapFactor X₁ Z₁ (e 0)) := by
    rw [Matrix.mul_assoc, swapFactor_mul_obs hZ₁, Matrix.mul_smul]
  rw [hR, hAZ]
  simp [Matrix.smul_apply]

/-! ## The shift transport defect -/

/-- Formalization-only: the entries of the shift transport defect factor through
the residual factors of the second swap. -/
theorem twoSwap_shift_defect_apply (X₁ Z₁ X₂ Z₂ : Op ι)
    (hX₁ : IsBinaryObservable X₁) (hZ₁ : IsBinaryObservable Z₁)
    (hX₂ : IsBinaryObservable X₂) (hZ₂ : IsBinaryObservable Z₂)
    (e : Fin 2 → ZMod 2) (i i' : ι) :
    (heteroKron (twoQubitPauliObs .X) (1 : Op ι) *
        twoSwapMatrix X₁ Z₁ X₂ Z₂ hX₁ hZ₁ hX₂ hZ₂ -
      twoSwapMatrix X₁ Z₁ X₂ Z₂ hX₁ hZ₁ hX₂ hZ₂ * X₁) (e, i) i' =
      (swapFactor X₂ Z₂ (e 1) *
        (swapFactor X₁ Z₁ (e 0 + 1) - swapFactor X₁ Z₁ (e 0) * X₁)) i i' := by
  have hshift0 :
      (e + Pi.single (0 : Fin 2) (1 : ZMod 2) : Fin 2 → ZMod 2) 0 = e 0 + 1 := by simp
  have hshift1 :
      (e + Pi.single (0 : Fin 2) (1 : ZMod 2) : Fin 2 → ZMod 2) 1 = e 1 := by simp
  rw [Matrix.sub_apply, twoQubitPauliObs_X_mul_apply, twoSwapMatrix_apply,
    hshift0, hshift1]
  have hR : (twoSwapMatrix X₁ Z₁ X₂ Z₂ hX₁ hZ₁ hX₂ hZ₂ * X₁)
      (e, i) i' = (swapFactor X₂ Z₂ (e 1) * swapFactor X₁ Z₁ (e 0) * X₁) i i' := by
    rw [Matrix.mul_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun j _ => by
      rw [twoSwapMatrix_apply]
  rw [hR]
  have hop : swapFactor X₂ Z₂ (e 1) *
      (swapFactor X₁ Z₁ (e 0 + 1) - swapFactor X₁ Z₁ (e 0) * X₁) =
      swapFactor X₂ Z₂ (e 1) * swapFactor X₁ Z₁ (e 0 + 1) -
        swapFactor X₂ Z₂ (e 1) * swapFactor X₁ Z₁ (e 0) * X₁ := by
    noncomm_ring
  rw [hop, Matrix.sub_apply]

/-- The one-qubit shift transport defect at the zero register label. -/
theorem swapFactor_shift_defect_zero (X Z : Op ι) :
    swapFactor X Z (0 + 1) - swapFactor X Z 0 * X =
      -((2 : ℂ)⁻¹ • (X * Z + Z * X)) := by
  have hid : reflectionEffect Z 0 * X - X * reflectionEffect Z 1 =
      (2 : ℂ)⁻¹ • (X * Z + Z * X) := by
    rw [reflectionEffect_zero_mul_X_sub_X_mul_one X Z]
  rw [zero_add, swapFactor_one, swapFactor_zero, ← hid]
  abel

/-- The one-qubit shift transport defect at the unit register label. -/
theorem swapFactor_shift_defect_one (X Z : Op ι) (hX : IsBinaryObservable X) :
    swapFactor X Z (1 + 1) - swapFactor X Z 1 * X =
      (2 : ℂ)⁻¹ • (X * (X * Z + Z * X)) := by
  have hid : X * reflectionEffect Z 1 * X - reflectionEffect Z 0 =
      -((2 : ℂ)⁻¹ • (X * (X * Z + Z * X))) := by
    rw [X_mul_reflectionEffect_one_mul_X_sub_zero X Z hX, neg_smul]
  have hz : swapFactor X Z (1 + 1) = reflectionEffect Z 0 := by
    rw [show (1 : ZMod 2) + 1 = 0 from by decide, swapFactor_zero]
  have hs : swapFactor X Z 1 * X = X * reflectionEffect Z 1 * X := by rw [swapFactor_one]
  rw [hz, hs, show reflectionEffect Z 0 - X * reflectionEffect Z 1 * X =
    -(X * reflectionEffect Z 1 * X - reflectionEffect Z 0) from by abel, hid, neg_neg]

/-- Formalization-only: the residual factors of the second swap drop out of a
Gram matrix built from the two-qubit residual factors. -/
theorem sum_twoSwapFactor_gram (X₂ Z₂ : Op ι) (hX₂ : IsBinaryObservable X₂)
    (hZ₂ : IsBinaryObservable Z₂) (D : ZMod 2 → Op ι) :
    (∑ e : Fin 2 → ZMod 2, (swapFactor X₂ Z₂ (e 1) * D (e 0))ᴴ *
        (swapFactor X₂ Z₂ (e 1) * D (e 0))) = ∑ b : ZMod 2, (D b)ᴴ * D b := by
  rw [sum_pi_fin_two
    (fun b c => (swapFactor X₂ Z₂ c * D b)ᴴ * (swapFactor X₂ Z₂ c * D b))]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hstep : ∀ c : ZMod 2, (swapFactor X₂ Z₂ c * D b)ᴴ * (swapFactor X₂ Z₂ c * D b) =
      (D b)ᴴ * ((swapFactor X₂ Z₂ c)ᴴ * swapFactor X₂ Z₂ c) * D b := by
    intro c
    rw [Matrix.conjTranspose_mul]
    noncomm_ring
  rw [Finset.sum_congr rfl fun c _ => hstep c, ← Finset.sum_mul, ← Finset.mul_sum,
    sum_swapFactor_conjTranspose_mul hX₂ hZ₂, Matrix.mul_one]

/-- The Gram matrix of the shift transport defect of the two-qubit controlled
swap is half the Gram matrix of the anticommutator of the first logical pair:
the residual factors of the second swap form a complete family and drop out. -/
theorem twoSwap_shift_defect_conjTranspose_mul (X₁ Z₁ X₂ Z₂ : Op ι)
    (hX₁ : IsBinaryObservable X₁) (hZ₁ : IsBinaryObservable Z₁)
    (hX₂ : IsBinaryObservable X₂) (hZ₂ : IsBinaryObservable Z₂) :
    (heteroKron (twoQubitPauliObs .X) (1 : Op ι) *
        twoSwapMatrix X₁ Z₁ X₂ Z₂ hX₁ hZ₁ hX₂ hZ₂ -
      twoSwapMatrix X₁ Z₁ X₂ Z₂ hX₁ hZ₁ hX₂ hZ₂ * X₁)ᴴ *
      (heteroKron (twoQubitPauliObs .X) (1 : Op ι) *
        twoSwapMatrix X₁ Z₁ X₂ Z₂ hX₁ hZ₁ hX₂ hZ₂ -
      twoSwapMatrix X₁ Z₁ X₂ Z₂ hX₁ hZ₁ hX₂ hZ₂ * X₁) =
      ((2 : ℂ)⁻¹) • ((X₁ * Z₁ + Z₁ * X₁)ᴴ * (X₁ * Z₁ + Z₁ * X₁)) := by
  have hblocks := conjTranspose_mul_of_blocks
    (heteroKron (twoQubitPauliObs .X) (1 : Op ι) *
        twoSwapMatrix X₁ Z₁ X₂ Z₂ hX₁ hZ₁ hX₂ hZ₂ -
      twoSwapMatrix X₁ Z₁ X₂ Z₂ hX₁ hZ₁ hX₂ hZ₂ * X₁)
    (fun e => swapFactor X₂ Z₂ (e 1) *
      (swapFactor X₁ Z₁ (e 0 + 1) - swapFactor X₁ Z₁ (e 0) * X₁))
    (fun e i i' => twoSwap_shift_defect_apply X₁ Z₁ X₂ Z₂ hX₁ hZ₁ hX₂ hZ₂ e i i')
  rw [hblocks, sum_twoSwapFactor_gram X₂ Z₂ hX₂ hZ₂
      (fun b => swapFactor X₁ Z₁ (b + 1) - swapFactor X₁ Z₁ b * X₁),
    sum_zmod_two]
  have hGH : (X₁ * Z₁ + Z₁ * X₁)ᴴ = X₁ * Z₁ + Z₁ * X₁ := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      hX₁.conjTranspose_eq, hZ₁.conjTranspose_eq]
    abel
  have h0 : (swapFactor X₁ Z₁ (0 + 1) - swapFactor X₁ Z₁ 0 * X₁)ᴴ *
      (swapFactor X₁ Z₁ (0 + 1) - swapFactor X₁ Z₁ 0 * X₁) =
      ((4 : ℂ)⁻¹) • ((X₁ * Z₁ + Z₁ * X₁)ᴴ * (X₁ * Z₁ + Z₁ * X₁)) := by
    rw [swapFactor_shift_defect_zero X₁ Z₁, Matrix.conjTranspose_neg,
      Matrix.conjTranspose_smul, neg_mul, mul_neg, neg_neg, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul]
    congr 1
    norm_num
  have h1 : (swapFactor X₁ Z₁ (1 + 1) - swapFactor X₁ Z₁ 1 * X₁)ᴴ *
      (swapFactor X₁ Z₁ (1 + 1) - swapFactor X₁ Z₁ 1 * X₁) =
      ((4 : ℂ)⁻¹) • ((X₁ * Z₁ + Z₁ * X₁)ᴴ * (X₁ * Z₁ + Z₁ * X₁)) := by
    rw [swapFactor_shift_defect_one X₁ Z₁ hX₁, Matrix.conjTranspose_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, Matrix.conjTranspose_mul, hX₁.conjTranspose_eq]
    have hcancel : (X₁ * Z₁ + Z₁ * X₁)ᴴ * X₁ * (X₁ * (X₁ * Z₁ + Z₁ * X₁)) =
        (X₁ * Z₁ + Z₁ * X₁)ᴴ * (X₁ * Z₁ + Z₁ * X₁) := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc X₁ X₁ (X₁ * Z₁ + Z₁ * X₁),
        hX₁.mul_self_eq_one, Matrix.one_mul]
    rw [hcancel]
    congr 1
    norm_num
  rw [h0, h1]
  module

/-! ## The spectral effects of the transported observables -/

/-- The spectral effects inherit the transport defect of their observable up to
the factor `1/2`. -/
theorem reflectionEffect_defect_eq {κ : Type} [Fintype κ] [DecidableEq κ]
    (τ : Op κ) (V : Matrix κ ι ℂ) (Z : Op ι) (b : ZMod 2) :
    reflectionEffect τ b * V - V * reflectionEffect Z b =
      (phaseSign b * (2 : ℂ)⁻¹) • (τ * V - V * Z) := by
  rcases zmod_two_eq_zero_or_one b with rfl | rfl
  · simp only [reflectionEffect, if_pos, phaseSign, one_mul]
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
      Matrix.mul_one]
    module
  · simp only [reflectionEffect, phaseSign, if_neg one_ne_zero]
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one]
    module

/-- The Gram matrix of the spectral transport defect is a quarter of the Gram
matrix of the observable transport defect. -/
theorem reflectionEffect_defect_conjTranspose_mul {κ : Type} [Fintype κ] [DecidableEq κ]
    (τ : Op κ) (V : Matrix κ ι ℂ) (Z : Op ι) (b : ZMod 2) (N : Op ι) (c : ℂ)
    (hF : (τ * V - V * Z)ᴴ * (τ * V - V * Z) = c • N) :
    (reflectionEffect τ b * V - V * reflectionEffect Z b)ᴴ *
        (reflectionEffect τ b * V - V * reflectionEffect Z b) =
      ((4 : ℂ)⁻¹ * c) • N := by
  have hp : phaseSign b * phaseSign b = 1 := by
    rcases zmod_two_eq_zero_or_one b with rfl | rfl <;> simp [phaseSign]
  have hc : star (phaseSign b) = phaseSign b := by
    rcases zmod_two_eq_zero_or_one b with rfl | rfl <;> simp [phaseSign]
  have hs :
      star (phaseSign b * (2 : ℂ)⁻¹) * (phaseSign b * (2 : ℂ)⁻¹) = (4 : ℂ)⁻¹ := by
    rw [star_mul, show star ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ from by simp,
      show star (phaseSign b) = phaseSign b from hc]
    calc (2 : ℂ)⁻¹ * phaseSign b * (phaseSign b * (2 : ℂ)⁻¹)
        = phaseSign b * phaseSign b * ((2 : ℂ)⁻¹ * (2 : ℂ)⁻¹) := by ring
      _ = (4 : ℂ)⁻¹ := by rw [hp]; norm_num
  rw [reflectionEffect_defect_eq, Matrix.conjTranspose_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, hs, hF, smul_smul]

/-! ## Transport on the joint state -/

variable {ιA ιB κA κB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
  [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]

/-- The defect of a left-placed register operator against a local operator on
the doubly transported state, in matrix form. -/
theorem leftTensor_isometryTensor_defect_eq
    (φA : EuclideanSpace ℂ ιA →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (φB : EuclideanSpace ℂ ιB →ₗᵢ[ℂ] EuclideanSpace ℂ κB)
    (M : Op κA) (N : Op ιA) (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    applyOperatorToState (heteroKron M (1 : Op κB)) (isometryTensor φA φB ψ) -
        isometryTensor φA φB (applyOperatorToState (heteroKron N (1 : Op ιB)) ψ) =
      Matrix.toEuclideanLin
        (Matrix.kronecker (M * isometryMatrix φA - isometryMatrix φA * N)
          (isometryMatrix φB)) ψ := by
  rw [isometryTensor_eq_toEuclideanLin, isometryTensor_eq_toEuclideanLin]
  unfold applyOperatorToState
  rw [← toEuclideanLin_mul_apply, ← toEuclideanLin_mul_apply, ← LinearMap.sub_apply,
    ← map_sub]
  congr 1
  unfold heteroKron Matrix.kronecker
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    Matrix.mul_one, kroneckerMap_sub_left]

/-- The defect of a right-placed register operator against a local operator on
the doubly transported state, in matrix form. -/
theorem rightTensor_isometryTensor_defect_eq
    (φA : EuclideanSpace ℂ ιA →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (φB : EuclideanSpace ℂ ιB →ₗᵢ[ℂ] EuclideanSpace ℂ κB)
    (M : Op κB) (N : Op ιB) (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    applyOperatorToState (heteroKron (1 : Op κA) M) (isometryTensor φA φB ψ) -
        isometryTensor φA φB (applyOperatorToState (heteroKron (1 : Op ιA) N) ψ) =
      Matrix.toEuclideanLin
        (Matrix.kronecker (isometryMatrix φA)
          (M * isometryMatrix φB - isometryMatrix φB * N)) ψ := by
  rw [isometryTensor_eq_toEuclideanLin, isometryTensor_eq_toEuclideanLin]
  unfold applyOperatorToState
  rw [← toEuclideanLin_mul_apply, ← toEuclideanLin_mul_apply, ← LinearMap.sub_apply,
    ← map_sub]
  congr 1
  unfold heteroKron Matrix.kronecker
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    Matrix.mul_one, kroneckerMap_sub_right]

omit [DecidableEq κA] [DecidableEq κB] in
/-- Formalization-only: the squared norm of a left-placed rectangular tensor
image, when its Gram matrix is a real multiple of the Gram matrix of a local
operator. -/
theorem norm_sq_toEuclideanLin_kron_left
    (E : Matrix κA ιA ℂ) (VB : Matrix κB ιB ℂ) (hVB : VBᴴ * VB = 1) (K : Op ιA) (c : ℝ)
    (hE : Eᴴ * E = ((c : ℝ) : ℂ) • (Kᴴ * K)) (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    ‖Matrix.toEuclideanLin (Matrix.kronecker E VB) ψ‖ ^ 2 =
      c * ‖applyOperatorToState (heteroKron K (1 : Op ιB)) ψ‖ ^ 2 := by
  have hW : (Matrix.kronecker E VB)ᴴ * Matrix.kronecker E VB =
      ((c : ℝ) : ℂ) • ((heteroKron K (1 : Op ιB))ᴴ * heteroKron K (1 : Op ιB)) := by
    unfold heteroKron Matrix.kronecker
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      hE, hVB, Matrix.one_mul, Matrix.smul_kronecker]
  rw [norm_toEuclideanLin_sq, hW, norm_applyOperatorToState_sq]
  unfold applyOperatorToState
  rw [map_smul, LinearMap.smul_apply, inner_smul_right, Complex.re_ofReal_mul]

omit [DecidableEq κA] [DecidableEq κB] in
/-- Formalization-only: the squared norm of a right-placed rectangular tensor
image, when its Gram matrix is a real multiple of the Gram matrix of a local
operator. -/
theorem norm_sq_toEuclideanLin_kron_right
    (VA : Matrix κA ιA ℂ) (hVA : VAᴴ * VA = 1) (E : Matrix κB ιB ℂ) (K : Op ιB) (c : ℝ)
    (hE : Eᴴ * E = ((c : ℝ) : ℂ) • (Kᴴ * K)) (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    ‖Matrix.toEuclideanLin (Matrix.kronecker VA E) ψ‖ ^ 2 =
      c * ‖applyOperatorToState (heteroKron (1 : Op ιA) K) ψ‖ ^ 2 := by
  have hW : (Matrix.kronecker VA E)ᴴ * Matrix.kronecker VA E =
      ((c : ℝ) : ℂ) • ((heteroKron (1 : Op ιA) K)ᴴ * heteroKron (1 : Op ιA) K) := by
    unfold heteroKron Matrix.kronecker
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      hE, hVA, Matrix.one_mul, Matrix.kronecker_smul]
  rw [norm_toEuclideanLin_sq, hW, norm_applyOperatorToState_sq]
  unfold applyOperatorToState
  rw [map_smul, LinearMap.smul_apply, inner_smul_right, Complex.re_ofReal_mul]

/-- The transport defect of a left-placed register operator on the doubly
transported state. -/
theorem norm_sq_leftTensor_isometryTensor_defect
    (φA : EuclideanSpace ℂ ιA →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (φB : EuclideanSpace ℂ ιB →ₗᵢ[ℂ] EuclideanSpace ℂ κB)
    (M : Op κA) (N K : Op ιA) (c : ℝ)
    (hE : (M * isometryMatrix φA - isometryMatrix φA * N)ᴴ *
      (M * isometryMatrix φA - isometryMatrix φA * N) = ((c : ℝ) : ℂ) • (Kᴴ * K))
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    ‖applyOperatorToState (heteroKron M (1 : Op κB)) (isometryTensor φA φB ψ) -
        isometryTensor φA φB (applyOperatorToState (heteroKron N (1 : Op ιB)) ψ)‖ ^ 2 =
      c * ‖applyOperatorToState (heteroKron K (1 : Op ιB)) ψ‖ ^ 2 := by
  rw [leftTensor_isometryTensor_defect_eq]
  exact norm_sq_toEuclideanLin_kron_left _ _ (isometryMatrix_conjTranspose_mul φB) K c hE ψ

/-- The transport defect of a right-placed register operator on the doubly
transported state. -/
theorem norm_sq_rightTensor_isometryTensor_defect
    (φA : EuclideanSpace ℂ ιA →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (φB : EuclideanSpace ℂ ιB →ₗᵢ[ℂ] EuclideanSpace ℂ κB)
    (M : Op κB) (N K : Op ιB) (c : ℝ)
    (hE : (M * isometryMatrix φB - isometryMatrix φB * N)ᴴ *
      (M * isometryMatrix φB - isometryMatrix φB * N) = ((c : ℝ) : ℂ) • (Kᴴ * K))
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    ‖applyOperatorToState (heteroKron (1 : Op κA) M) (isometryTensor φA φB ψ) -
        isometryTensor φA φB (applyOperatorToState (heteroKron (1 : Op ιA) N) ψ)‖ ^ 2 =
      c * ‖applyOperatorToState (heteroKron (1 : Op ιA) K) ψ‖ ^ 2 := by
  rw [rightTensor_isometryTensor_defect_eq]
  exact norm_sq_toEuclideanLin_kron_right _ (isometryMatrix_conjTranspose_mul φA) _ K c hE ψ

/-! ## Magic Square specialization -/

/-- The spectral effects of a left-placed reflection are the placed spectral
effects. -/
theorem reflectionEffect_heteroKron_left (Z : Op ιA) (b : ZMod 2) :
    heteroKron (reflectionEffect Z b) (1 : Op ιB) =
      reflectionEffect (heteroKron Z (1 : Op ιB)) b := by
  rcases zmod_two_eq_zero_or_one b with rfl | rfl
  · simp only [reflectionEffect, if_pos]
    rw [heteroKron_smul_left, heteroKron_add_left, heteroKron_one_one]
  · simp only [reflectionEffect, if_neg one_ne_zero]
    rw [heteroKron_smul_left, heteroKron_sub_left, heteroKron_one_one]

/-- The spectral effects of a right-placed reflection are the placed spectral
effects. -/
theorem reflectionEffect_heteroKron_right (Z : Op ιB) (b : ZMod 2) :
    heteroKron (1 : Op ιA) (reflectionEffect Z b) =
      reflectionEffect (heteroKron (1 : Op ιA) Z) b := by
  rcases zmod_two_eq_zero_or_one b with rfl | rfl
  · simp only [reflectionEffect, if_pos]
    rw [heteroKron_smul_right, heteroKron_add_right, heteroKron_one_one]
  · simp only [reflectionEffect, if_neg one_ne_zero]
    rw [heteroKron_smul_right, heteroKron_sub_right, heteroKron_one_one]

/-- Alice's dilated variable effects are the spectral effects of her local
variable reflection. -/
theorem dilatedEffect_var_A_eq (S : Strategy msGame) (j : Fin 9) (b : ZMod 2) :
    (((msDilatedStrategy S).A (MsType.var j)).postprocess msBitOrZero).effect b =
      reflectionEffect (msLocalVarObsA S j) b := by
  rw [msLocalVarObsA, signObs_eq_obsOf_postprocess, reflectionEffect_obsOf_measurement]

/-- Bob's dilated variable effects are the spectral effects of his local
variable reflection. -/
theorem dilatedEffect_var_B_eq (S : Strategy msGame) (j : Fin 9) (b : ZMod 2) :
    (((msDilatedStrategy S).B (MsType.var j)).postprocess msBitOrZero).effect b =
      reflectionEffect (msLocalVarObsB S j) b := by
  rw [msLocalVarObsB, signObs_eq_obsOf_postprocess, reflectionEffect_obsOf_measurement]

/-- The matrix of Alice's two-qubit controlled-swap embedding. -/
theorem isometryMatrix_msAliceTwoQubitSwapIsometry (S : Strategy msGame) :
    isometryMatrix (msAliceTwoQubitSwapIsometry S) =
      twoSwapMatrix (msLocalVarObsA S 0) (msLocalVarObsA S 4)
        (msLocalCellObsA S 0 1) (msLocalCellObsA S 1 0)
        (isBinaryObservable_msLocalVarObsA S 0) (isBinaryObservable_msLocalVarObsA S 4)
        (isBinaryObservable_msLocalCellObsA S 0 1)
        (isBinaryObservable_msLocalCellObsA S 1 0) := rfl

/-- The matrix of Bob's two-qubit controlled-swap embedding. -/
theorem isometryMatrix_msBobTwoQubitSwapIsometry (S : Strategy msGame) :
    isometryMatrix (msBobTwoQubitSwapIsometry S) =
      twoSwapMatrix (msLocalVarObsB S 0) (msLocalVarObsB S 4)
        (msLocalVarObsB S 1) (msLocalVarObsB S 3)
        (isBinaryObservable_msLocalVarObsB S 0) (isBinaryObservable_msLocalVarObsB S 4)
        (isBinaryObservable_msLocalVarObsB S 1)
        (isBinaryObservable_msLocalVarObsB S 3) := rfl

/-- Alice's first logical pair, placed on the bipartite dilated space. -/
noncomputable def msJointAnticommutatorA (S : Strategy msGame) :
    Op ((msDilatedStrategy S).ιA × (msDilatedStrategy S).ιB) :=
  heteroKron (msLocalVarObsA S 0 * msLocalVarObsA S 4 +
    msLocalVarObsA S 4 * msLocalVarObsA S 0) 1

/-- Bob's first logical pair, placed on the bipartite dilated space. -/
noncomputable def msJointAnticommutatorB (S : Strategy msGame) :
    Op ((msDilatedStrategy S).ιA × (msDilatedStrategy S).ιB) :=
  heteroKron 1 (msLocalVarObsB S 0 * msLocalVarObsB S 4 +
    msLocalVarObsB S 4 * msLocalVarObsB S 0)

/-- Alice's first logical pair approximately anticommutes on the dilated state,
in the placed form used by the transport estimates. -/
theorem norm_msJointAnticommutatorA_le (S : Strategy msGame) (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) :
    ‖applyOperatorToState (msJointAnticommutatorA S) (msDilatedStrategy S).ψ‖ ≤
      624 * Real.sqrt ε := by
  have h := msVarObsA_anticommute S ε hwin
  rw [NormCloseOn, msVarObsA_eq_heteroKron, msVarObsA_eq_heteroKron,
    heteroKron_left_anticommutator] at h
  exact h

/-- Bob's first logical pair approximately anticommutes on the dilated state,
in the placed form used by the transport estimates. -/
theorem norm_msJointAnticommutatorB_le (S : Strategy msGame) (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) :
    ‖applyOperatorToState (msJointAnticommutatorB S) (msDilatedStrategy S).ψ‖ ≤
      624 * Real.sqrt ε := by
  have h := msVarObsB_anticommute S ε hwin
  rw [NormCloseOn, msVarObsB_eq_heteroKron, msVarObsB_eq_heteroKron] at h
  rw [msJointAnticommutatorB]
  have hrew : heteroKron (1 : Op (msDilatedStrategy S).ιA)
      (msLocalVarObsB S 0 * msLocalVarObsB S 4 +
        msLocalVarObsB S 4 * msLocalVarObsB S 0) =
      heteroKron 1 (msLocalVarObsB S 0) * heteroKron 1 (msLocalVarObsB S 4) -
        -(heteroKron 1 (msLocalVarObsB S 4) * heteroKron 1 (msLocalVarObsB S 0)) := by
    rw [heteroKron_mul, heteroKron_mul, one_mul, sub_neg_eq_add, ← heteroKron_add_right]
  rw [hrew]
  exact h

/-- The transport defect of Alice's variable-0 effects through her two-qubit
controlled swap is bounded by the anticommutator defect of her first logical
pair. -/
theorem norm_ms_effect_defect_A_X (S : Strategy msGame) (b : ZMod 2) :
    ‖applyOperatorToState
        (heteroKron (heteroKron (reflectionEffect (twoQubitPauliObs .X) b)
          (1 : Op (msDilatedStrategy S).ιA))
          (1 : Op ((Fin 2 → ZMod 2) × (msDilatedStrategy S).ιB)))
        (isometryTensor (msAliceTwoQubitSwapIsometry S) (msBobTwoQubitSwapIsometry S)
          (msDilatedStrategy S).ψ) -
      isometryTensor (msAliceTwoQubitSwapIsometry S) (msBobTwoQubitSwapIsometry S)
        (applyOperatorToState
          (heteroKron (reflectionEffect (msLocalVarObsA S 0) b) 1)
          (msDilatedStrategy S).ψ)‖ ≤
      ‖applyOperatorToState (msJointAnticommutatorA S) (msDilatedStrategy S).ψ‖ := by
  have hF := twoSwap_shift_defect_conjTranspose_mul (msLocalVarObsA S 0)
    (msLocalVarObsA S 4) (msLocalCellObsA S 0 1) (msLocalCellObsA S 1 0)
    (isBinaryObservable_msLocalVarObsA S 0) (isBinaryObservable_msLocalVarObsA S 4)
    (isBinaryObservable_msLocalCellObsA S 0 1) (isBinaryObservable_msLocalCellObsA S 1 0)
  rw [← isometryMatrix_msAliceTwoQubitSwapIsometry] at hF
  have hE := reflectionEffect_defect_conjTranspose_mul
    (heteroKron (twoQubitPauliObs .X) (1 : Op (msDilatedStrategy S).ιA))
    (isometryMatrix (msAliceTwoQubitSwapIsometry S)) (msLocalVarObsA S 0) b _ _ hF
  rw [← reflectionEffect_heteroKron_left] at hE
  rw [show ((4 : ℂ)⁻¹ * (2 : ℂ)⁻¹) = (((1 / 8 : ℝ) : ℝ) : ℂ) from by norm_num] at hE
  have hsq := norm_sq_leftTensor_isometryTensor_defect (msAliceTwoQubitSwapIsometry S)
    (msBobTwoQubitSwapIsometry S)
    (heteroKron (reflectionEffect (twoQubitPauliObs .X) b) 1)
    (reflectionEffect (msLocalVarObsA S 0) b)
    (msLocalVarObsA S 0 * msLocalVarObsA S 4 + msLocalVarObsA S 4 * msLocalVarObsA S 0)
    (1 / 8) hE (msDilatedStrategy S).ψ
  rw [msJointAnticommutatorA]
  nlinarith [hsq, norm_nonneg (applyOperatorToState
      (heteroKron (msLocalVarObsA S 0 * msLocalVarObsA S 4 +
        msLocalVarObsA S 4 * msLocalVarObsA S 0)
        (1 : Op (msDilatedStrategy S).ιB)) (msDilatedStrategy S).ψ),
    norm_nonneg (applyOperatorToState
        (heteroKron (heteroKron (reflectionEffect (twoQubitPauliObs .X) b)
          (1 : Op (msDilatedStrategy S).ιA))
          (1 : Op ((Fin 2 → ZMod 2) × (msDilatedStrategy S).ιB)))
        (isometryTensor (msAliceTwoQubitSwapIsometry S) (msBobTwoQubitSwapIsometry S)
          (msDilatedStrategy S).ψ) -
      isometryTensor (msAliceTwoQubitSwapIsometry S) (msBobTwoQubitSwapIsometry S)
        (applyOperatorToState
          (heteroKron (reflectionEffect (msLocalVarObsA S 0) b) 1)
          (msDilatedStrategy S).ψ))]

/-- The transport defect of Alice's variable-4 effects through her two-qubit
controlled swap vanishes. -/
theorem norm_ms_effect_defect_A_Z (S : Strategy msGame) (b : ZMod 2) :
    ‖applyOperatorToState
        (heteroKron (heteroKron (reflectionEffect (twoQubitPauliObs .Z) b)
          (1 : Op (msDilatedStrategy S).ιA))
          (1 : Op ((Fin 2 → ZMod 2) × (msDilatedStrategy S).ιB)))
        (isometryTensor (msAliceTwoQubitSwapIsometry S) (msBobTwoQubitSwapIsometry S)
          (msDilatedStrategy S).ψ) -
      isometryTensor (msAliceTwoQubitSwapIsometry S) (msBobTwoQubitSwapIsometry S)
        (applyOperatorToState
          (heteroKron (reflectionEffect (msLocalVarObsA S 4) b) 1)
          (msDilatedStrategy S).ψ)‖ ≤ 0 := by
  have hzero := twoSwap_matrix_intertwines_Z (msLocalVarObsA S 0) (msLocalVarObsA S 4)
    (msLocalCellObsA S 0 1) (msLocalCellObsA S 1 0)
    (isBinaryObservable_msLocalVarObsA S 0) (isBinaryObservable_msLocalVarObsA S 4)
    (isBinaryObservable_msLocalCellObsA S 0 1) (isBinaryObservable_msLocalCellObsA S 1 0)
  rw [← isometryMatrix_msAliceTwoQubitSwapIsometry] at hzero
  have hF : (heteroKron (twoQubitPauliObs .Z) (1 : Op (msDilatedStrategy S).ιA) *
        isometryMatrix (msAliceTwoQubitSwapIsometry S) -
      isometryMatrix (msAliceTwoQubitSwapIsometry S) * msLocalVarObsA S 4)ᴴ *
      (heteroKron (twoQubitPauliObs .Z) (1 : Op (msDilatedStrategy S).ιA) *
        isometryMatrix (msAliceTwoQubitSwapIsometry S) -
      isometryMatrix (msAliceTwoQubitSwapIsometry S) * msLocalVarObsA S 4) =
      (0 : ℂ) • ((msLocalVarObsA S 0)ᴴ * msLocalVarObsA S 0) := by
    rw [hzero, Matrix.conjTranspose_zero, Matrix.zero_mul, zero_smul]
  have hE := reflectionEffect_defect_conjTranspose_mul
    (heteroKron (twoQubitPauliObs .Z) (1 : Op (msDilatedStrategy S).ιA))
    (isometryMatrix (msAliceTwoQubitSwapIsometry S)) (msLocalVarObsA S 4) b _ _ hF
  rw [← reflectionEffect_heteroKron_left] at hE
  rw [show ((4 : ℂ)⁻¹ * (0 : ℂ)) = (((0 : ℝ) : ℝ) : ℂ) from by norm_num] at hE
  have hsq := norm_sq_leftTensor_isometryTensor_defect (msAliceTwoQubitSwapIsometry S)
    (msBobTwoQubitSwapIsometry S)
    (heteroKron (reflectionEffect (twoQubitPauliObs .Z) b) 1)
    (reflectionEffect (msLocalVarObsA S 4) b) (msLocalVarObsA S 0) 0 hE
    (msDilatedStrategy S).ψ
  nlinarith [hsq, norm_nonneg (applyOperatorToState
        (heteroKron (heteroKron (reflectionEffect (twoQubitPauliObs .Z) b)
          (1 : Op (msDilatedStrategy S).ιA))
          (1 : Op ((Fin 2 → ZMod 2) × (msDilatedStrategy S).ιB)))
        (isometryTensor (msAliceTwoQubitSwapIsometry S) (msBobTwoQubitSwapIsometry S)
          (msDilatedStrategy S).ψ) -
      isometryTensor (msAliceTwoQubitSwapIsometry S) (msBobTwoQubitSwapIsometry S)
        (applyOperatorToState
          (heteroKron (reflectionEffect (msLocalVarObsA S 4) b) 1)
          (msDilatedStrategy S).ψ))]

/-- The transport defect of Bob's variable-0 effects through his two-qubit
controlled swap is bounded by the anticommutator defect of his first logical
pair. -/
theorem norm_ms_effect_defect_B_X (S : Strategy msGame) (b : ZMod 2) :
    ‖applyOperatorToState
        (heteroKron (1 : Op ((Fin 2 → ZMod 2) × (msDilatedStrategy S).ιA))
          (heteroKron (reflectionEffect (twoQubitPauliObs .X) b)
            (1 : Op (msDilatedStrategy S).ιB)))
        (isometryTensor (msAliceTwoQubitSwapIsometry S) (msBobTwoQubitSwapIsometry S)
          (msDilatedStrategy S).ψ) -
      isometryTensor (msAliceTwoQubitSwapIsometry S) (msBobTwoQubitSwapIsometry S)
        (applyOperatorToState
          (heteroKron 1 (reflectionEffect (msLocalVarObsB S 0) b))
          (msDilatedStrategy S).ψ)‖ ≤
      ‖applyOperatorToState (msJointAnticommutatorB S) (msDilatedStrategy S).ψ‖ := by
  have hF := twoSwap_shift_defect_conjTranspose_mul (msLocalVarObsB S 0)
    (msLocalVarObsB S 4) (msLocalVarObsB S 1) (msLocalVarObsB S 3)
    (isBinaryObservable_msLocalVarObsB S 0) (isBinaryObservable_msLocalVarObsB S 4)
    (isBinaryObservable_msLocalVarObsB S 1) (isBinaryObservable_msLocalVarObsB S 3)
  rw [← isometryMatrix_msBobTwoQubitSwapIsometry] at hF
  have hE := reflectionEffect_defect_conjTranspose_mul
    (heteroKron (twoQubitPauliObs .X) (1 : Op (msDilatedStrategy S).ιB))
    (isometryMatrix (msBobTwoQubitSwapIsometry S)) (msLocalVarObsB S 0) b _ _ hF
  rw [← reflectionEffect_heteroKron_left] at hE
  rw [show ((4 : ℂ)⁻¹ * (2 : ℂ)⁻¹) = (((1 / 8 : ℝ) : ℝ) : ℂ) from by norm_num] at hE
  have hsq := norm_sq_rightTensor_isometryTensor_defect (msAliceTwoQubitSwapIsometry S)
    (msBobTwoQubitSwapIsometry S)
    (heteroKron (reflectionEffect (twoQubitPauliObs .X) b) 1)
    (reflectionEffect (msLocalVarObsB S 0) b)
    (msLocalVarObsB S 0 * msLocalVarObsB S 4 + msLocalVarObsB S 4 * msLocalVarObsB S 0)
    (1 / 8) hE (msDilatedStrategy S).ψ
  rw [msJointAnticommutatorB]
  nlinarith [hsq, norm_nonneg (applyOperatorToState
      (heteroKron (1 : Op (msDilatedStrategy S).ιA)
        (msLocalVarObsB S 0 * msLocalVarObsB S 4 +
          msLocalVarObsB S 4 * msLocalVarObsB S 0)) (msDilatedStrategy S).ψ),
    norm_nonneg (applyOperatorToState
        (heteroKron (1 : Op ((Fin 2 → ZMod 2) × (msDilatedStrategy S).ιA))
          (heteroKron (reflectionEffect (twoQubitPauliObs .X) b)
            (1 : Op (msDilatedStrategy S).ιB)))
        (isometryTensor (msAliceTwoQubitSwapIsometry S) (msBobTwoQubitSwapIsometry S)
          (msDilatedStrategy S).ψ) -
      isometryTensor (msAliceTwoQubitSwapIsometry S) (msBobTwoQubitSwapIsometry S)
        (applyOperatorToState
          (heteroKron 1 (reflectionEffect (msLocalVarObsB S 0) b))
          (msDilatedStrategy S).ψ))]

/-- The transport defect of Bob's variable-4 effects through his two-qubit
controlled swap vanishes. -/
theorem norm_ms_effect_defect_B_Z (S : Strategy msGame) (b : ZMod 2) :
    ‖applyOperatorToState
        (heteroKron (1 : Op ((Fin 2 → ZMod 2) × (msDilatedStrategy S).ιA))
          (heteroKron (reflectionEffect (twoQubitPauliObs .Z) b)
            (1 : Op (msDilatedStrategy S).ιB)))
        (isometryTensor (msAliceTwoQubitSwapIsometry S) (msBobTwoQubitSwapIsometry S)
          (msDilatedStrategy S).ψ) -
      isometryTensor (msAliceTwoQubitSwapIsometry S) (msBobTwoQubitSwapIsometry S)
        (applyOperatorToState
          (heteroKron 1 (reflectionEffect (msLocalVarObsB S 4) b))
          (msDilatedStrategy S).ψ)‖ ≤ 0 := by
  have hzero := twoSwap_matrix_intertwines_Z (msLocalVarObsB S 0) (msLocalVarObsB S 4)
    (msLocalVarObsB S 1) (msLocalVarObsB S 3)
    (isBinaryObservable_msLocalVarObsB S 0) (isBinaryObservable_msLocalVarObsB S 4)
    (isBinaryObservable_msLocalVarObsB S 1) (isBinaryObservable_msLocalVarObsB S 3)
  rw [← isometryMatrix_msBobTwoQubitSwapIsometry] at hzero
  have hF : (heteroKron (twoQubitPauliObs .Z) (1 : Op (msDilatedStrategy S).ιB) *
        isometryMatrix (msBobTwoQubitSwapIsometry S) -
      isometryMatrix (msBobTwoQubitSwapIsometry S) * msLocalVarObsB S 4)ᴴ *
      (heteroKron (twoQubitPauliObs .Z) (1 : Op (msDilatedStrategy S).ιB) *
        isometryMatrix (msBobTwoQubitSwapIsometry S) -
      isometryMatrix (msBobTwoQubitSwapIsometry S) * msLocalVarObsB S 4) =
      (0 : ℂ) • ((msLocalVarObsB S 0)ᴴ * msLocalVarObsB S 0) := by
    rw [hzero, Matrix.conjTranspose_zero, Matrix.zero_mul, zero_smul]
  have hE := reflectionEffect_defect_conjTranspose_mul
    (heteroKron (twoQubitPauliObs .Z) (1 : Op (msDilatedStrategy S).ιB))
    (isometryMatrix (msBobTwoQubitSwapIsometry S)) (msLocalVarObsB S 4) b _ _ hF
  rw [← reflectionEffect_heteroKron_left] at hE
  rw [show ((4 : ℂ)⁻¹ * (0 : ℂ)) = (((0 : ℝ) : ℝ) : ℂ) from by norm_num] at hE
  have hsq := norm_sq_rightTensor_isometryTensor_defect (msAliceTwoQubitSwapIsometry S)
    (msBobTwoQubitSwapIsometry S)
    (heteroKron (reflectionEffect (twoQubitPauliObs .Z) b) 1)
    (reflectionEffect (msLocalVarObsB S 4) b) (msLocalVarObsB S 0) 0 hE
    (msDilatedStrategy S).ψ
  nlinarith [hsq, norm_nonneg (applyOperatorToState
        (heteroKron (1 : Op ((Fin 2 → ZMod 2) × (msDilatedStrategy S).ιA))
          (heteroKron (reflectionEffect (twoQubitPauliObs .Z) b)
            (1 : Op (msDilatedStrategy S).ιB)))
        (isometryTensor (msAliceTwoQubitSwapIsometry S) (msBobTwoQubitSwapIsometry S)
          (msDilatedStrategy S).ψ) -
      isometryTensor (msAliceTwoQubitSwapIsometry S) (msBobTwoQubitSwapIsometry S)
        (applyOperatorToState
          (heteroKron 1 (reflectionEffect (msLocalVarObsB S 4) b))
          (msDilatedStrategy S).ψ))]

end

end MIPStarRE.QPBT.MagicSquareRigidity
