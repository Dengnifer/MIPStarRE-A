import MIPStarRE.QPBT.Games.DistanceTheorems
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.Dilation

/-!
# Contractions, isometries and the ground slice of the dilation

Support for the transfer step of `thm:ms-rigidity` (blueprint
`blueprint/src/chapter/ch13_qpbt_test.tex:224-253`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`):
the calculus needed to compare the dilated projective strategy of
`Rigidity/Dilation.lean` with the original strategy on states.

* Contractions: operators `K` with `Kᴴ K ≤ 1` do not increase norms; effects,
  observables of binary measurements, orthogonal projections, tensor placements,
  products and isometry conjugates are contractions.
* Matrices of isometries: `Vᴴ V = 1`, the two-sided isometry image of a state
  preserves norms, and a conjugated local operator acts on the transported state
  as the original operator acts on the original state.
* The ground projection `Π` of an enlarged local space: an orthogonal projection
  fixing the dilated state, with `Π P Π` the inflation of the compression of `P`.
* Leakage: the part `(1 - Π) P ψ'` of a dilated operator that leaves the ground
  slice is bounded by the intertwining defect of `P ⊗ 1` against any `1 ⊗ Q`,
  because `(1 - Π) ⊗ 1` annihilates `(1 ⊗ Q) ψ'`.  This is the estimate that
  replaces the `≈_δ`-preservation which Naimark dilation lacks in general
  (`references/ldt-paper/orthonormalization.tex:82-101`, blueprint
  `ch04_projective.tex:255-270`).
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

noncomputable section

/-! ## Contractions and their action on states -/

/-- Applying a product of operators is successive application. -/
theorem applyOperatorToState_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M N : Op ι) (v : EuclideanSpace ℂ ι) :
    applyOperatorToState (M * N) v =
      applyOperatorToState M (applyOperatorToState N v) := by
  unfold applyOperatorToState
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same]

/-- The identity acts trivially. -/
theorem applyOperatorToState_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : EuclideanSpace ℂ ι) :
    applyOperatorToState (1 : Op ι) v = v := by
  simp [applyOperatorToState]

/-- Operators act additively on states. -/
theorem applyOperatorToState_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Op ι) (u v : EuclideanSpace ℂ ι) :
    applyOperatorToState M (u + v) =
      applyOperatorToState M u + applyOperatorToState M v := by
  simp [applyOperatorToState]

/-- Operators act additively on differences of states. -/
theorem applyOperatorToState_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Op ι) (u v : EuclideanSpace ℂ ι) :
    applyOperatorToState M (u - v) =
      applyOperatorToState M u - applyOperatorToState M v := by
  simp [applyOperatorToState]

/-- The action on states is additive in the operator. -/
theorem applyOperatorToState_add_op {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M N : Op ι) (v : EuclideanSpace ℂ ι) :
    applyOperatorToState (M + N) v =
      applyOperatorToState M v + applyOperatorToState N v := by
  simp [applyOperatorToState]

/-- Operators annihilate the zero state. -/
theorem applyOperatorToState_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Op ι) :
    applyOperatorToState M (0 : EuclideanSpace ℂ ι) = 0 := by
  simp [applyOperatorToState]

/-- Applying a product of rectangular matrices is successive application. -/
theorem toEuclideanLin_mul_apply {m n o : Type*} [Fintype n] [Fintype o]
    [DecidableEq n] [DecidableEq o]
    (A : Matrix m n ℂ) (B : Matrix n o ℂ) (v : EuclideanSpace ℂ o) :
    Matrix.toEuclideanLin (A * B) v =
      Matrix.toEuclideanLin A (Matrix.toEuclideanLin B v) := by
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same]

/-- The squared norm of `A v` is the quadratic form of `Aᴴ A` at `v`. -/
theorem norm_toEuclideanLin_sq {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) (v : EuclideanSpace ℂ n) :
    ‖Matrix.toEuclideanLin A v‖ ^ 2 =
      (inner ℂ v (Matrix.toEuclideanLin (Aᴴ * A) v)).re := by
  rw [@norm_sq_eq_re_inner ℂ, Matrix.toEuclideanLin_conjTranspose_mul_self]
  change (inner ℂ (Matrix.toEuclideanLin A v) (Matrix.toEuclideanLin A v)).re =
    (inner ℂ v ((Matrix.toEuclideanLin A).adjoint (Matrix.toEuclideanLin A v))).re
  rw [LinearMap.adjoint_inner_right]

/-- A rectangular matrix `A` with `Aᴴ A = 1` preserves norms. -/
theorem norm_toEuclideanLin_of_conjTranspose_mul_eq_one {m n : Type*} [Fintype m]
    [Fintype n] [DecidableEq n] {A : Matrix m n ℂ} (hA : Aᴴ * A = 1)
    (v : EuclideanSpace ℂ n) :
    ‖Matrix.toEuclideanLin A v‖ = ‖v‖ := by
  have h := norm_toEuclideanLin_sq A v
  have hv : (inner ℂ v v).re = ‖v‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) v
  have hone : Matrix.toEuclideanLin (1 : Matrix n n ℂ) v = v := by
    simp [Matrix.toEuclideanLin]
  rw [hA, hone, hv] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- The squared norm of `K v` is the quadratic form of `Kᴴ K` at `v`. -/
theorem norm_applyOperatorToState_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Op ι) (v : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState K v‖ ^ 2 =
      (inner ℂ v (applyOperatorToState (Kᴴ * K) v)).re :=
  norm_toEuclideanLin_sq K v

/-- An operator `K` with `Kᴴ K ≤ 1` does not increase norms. -/
theorem norm_applyOperatorToState_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Op ι} (hK : Kᴴ * K ≤ 1) (v : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState K v‖ ≤ ‖v‖ := by
  have h := quadratic_form_mono hK v
  have hv : (inner ℂ v v).re = ‖v‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) v
  rw [← norm_applyOperatorToState_sq, applyOperatorToState_one, hv] at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- The difference of two contractions at most doubles norms. -/
theorem norm_applyOperatorToState_sub_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Op ι} (hA : Aᴴ * A ≤ 1) (hB : Bᴴ * B ≤ 1) (v : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState (A - B) v‖ ≤ 2 * ‖v‖ := by
  have hsplit : applyOperatorToState (A - B) v =
      applyOperatorToState A v - applyOperatorToState B v := by
    simp [applyOperatorToState]
  rw [hsplit]
  calc ‖applyOperatorToState A v - applyOperatorToState B v‖ ≤
        ‖applyOperatorToState A v‖ + ‖applyOperatorToState B v‖ := norm_sub_le _ _
    _ ≤ ‖v‖ + ‖v‖ := add_le_add (norm_applyOperatorToState_le hA v)
        (norm_applyOperatorToState_le hB v)
    _ = 2 * ‖v‖ := by ring

/-- Orthogonal projections are contractions. -/
theorem conjTranspose_mul_le_one_of_isProj {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P : Op ι} (hP : IsProj P) : Pᴴ * P ≤ 1 := by
  have hstar : Pᴴ = P := by
    rw [← Matrix.star_eq_conjTranspose]
    exact hP.isSelfAdjoint.star_eq
  rw [hstar, hP.isIdempotentElem.eq]
  exact sub_nonneg.mp hP.one_sub.nonneg

/-- Products of contractions are contractions. -/
theorem conjTranspose_mul_le_one_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Op ι} (hA : Aᴴ * A ≤ 1) (hB : Bᴴ * B ≤ 1) :
    (A * B)ᴴ * (A * B) ≤ 1 := by
  have h1 : (1 - Aᴴ * A).PosSemidef := Matrix.le_iff.mp hA
  have h2 := h1.conjTranspose_mul_mul_same B
  have h3 : Bᴴ * (1 - Aᴴ * A) * B = Bᴴ * B - (A * B)ᴴ * (A * B) := by
    rw [Matrix.conjTranspose_mul]
    noncomm_ring
  refine le_trans ?_ hB
  rw [Matrix.le_iff, ← h3]
  exact h2

/-- Effects of a measurement are contractions. -/
theorem conjTranspose_mul_le_one_of_effect {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι] (M : MIPStarRE.Quantum.Measurement α ι) (a : α) :
    (M.effect a)ᴴ * M.effect a ≤ 1 := by
  rw [measurement_effect_hermitian]
  exact le_trans (sq_le_self (M.pos a) (measurement_effect_le_one M a))
    (measurement_effect_le_one M a)

/-- The observable of a binary measurement is a contraction: writing
`E = M_0`, the observable is `2E - 1` and `1 - (2E - 1)² = 4(E - E²) ≥ 0`. -/
theorem conjTranspose_mul_le_one_of_obsOf {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : MIPStarRE.Quantum.Measurement (ZMod 2) ι) :
    (obsOf M)ᴴ * obsOf M ≤ 1 := by
  have hsum : M.effect 0 + M.effect 1 = 1 := by
    have h : ∑ a : Fin 2, M.effect a = 1 := M.sum_eq_one
    rwa [Fin.sum_univ_two] at h
  have hobs : obsOf M = M.effect 0 + M.effect 0 - 1 := by
    unfold obsOf
    rw [← hsum]
    abel
  have hH : (M.effect 0)ᴴ = M.effect 0 := measurement_effect_hermitian M 0
  have hsq : 0 ≤ M.effect 0 - M.effect 0 * M.effect 0 :=
    sub_nonneg.mpr (sq_le_self (M.pos 0) (measurement_effect_le_one M 0))
  rw [hobs]
  have hid : (M.effect 0 + M.effect 0 - 1)ᴴ * (M.effect 0 + M.effect 0 - 1) =
      1 - (4 : ℕ) • (M.effect 0 - M.effect 0 * M.effect 0) := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add,
      Matrix.conjTranspose_one, hH]
    noncomm_ring
  rw [hid]
  exact sub_le_self _ (nsmul_nonneg hsq 4)

/-- Left placement preserves contractions. -/
theorem conjTranspose_mul_le_one_leftTensor {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB] {A : Op ιA} (hA : Aᴴ * A ≤ 1) :
    (heteroKron A (1 : Op ιB))ᴴ * heteroKron A (1 : Op ιB) ≤ 1 := by
  change (leftTensor (ι₂ := ιB) A)ᴴ * leftTensor (ι₂ := ιB) A ≤ 1
  rw [leftTensor_conjTranspose, leftTensor_mul_leftTensor]
  exact leftTensor_le_one hA

/-- Right placement preserves contractions. -/
theorem conjTranspose_mul_le_one_rightTensor {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB] {B : Op ιB} (hB : Bᴴ * B ≤ 1) :
    (heteroKron (1 : Op ιA) B)ᴴ * heteroKron (1 : Op ιA) B ≤ 1 := by
  change (rightTensor (ι₁ := ιA) B)ᴴ * rightTensor (ι₁ := ιA) B ≤ 1
  rw [rightTensor_conjTranspose, rightTensor_mul_rightTensor]
  exact rightTensor_le_one hB

/-! ## Kronecker algebra of placed operators

The mixed-product rule `heteroKron_mul` and the identity `heteroKron_one_one`
are the shared tensor-placement lemmas of `MIPStarRE/QPBT/Games/Defs.lean`; the
identities below extend them with the additive facts used by the transfer
step. -/

/-- Tensor placement is additive in the left factor. -/
theorem heteroKron_add_left {ιA ιB : Type*} (A B : Op ιA) (C : Op ιB) :
    heteroKron (A + B) C = heteroKron A C + heteroKron B C := by
  ext p q
  simp [heteroKron, Matrix.kronecker, add_mul]

/-- Tensor placement is additive in the right factor. -/
theorem heteroKron_add_right {ιA ιB : Type*} (A : Op ιA) (B C : Op ιB) :
    heteroKron A (B + C) = heteroKron A B + heteroKron A C := by
  ext p q
  simp [heteroKron, Matrix.kronecker, mul_add]

/-- Tensor placement respects differences in the left factor. -/
theorem heteroKron_sub_left {ιA ιB : Type*} (A B : Op ιA) (C : Op ιB) :
    heteroKron (A - B) C = heteroKron A C - heteroKron B C := by
  ext p q
  simp [heteroKron, Matrix.kronecker, sub_mul]

/-- Tensor placement respects differences in the right factor. -/
theorem heteroKron_sub_right {ιA ιB : Type*} (A : Op ιA) (B C : Op ιB) :
    heteroKron A (B - C) = heteroKron A B - heteroKron A C := by
  ext p q
  simp [heteroKron, Matrix.kronecker, mul_sub]

/-- Tensor placement is additive over finite sums in the left factor. -/
theorem heteroKron_finset_sum_left {β ιA ιB : Type*} (s : Finset β)
    (A : β → Op ιA) (C : Op ιB) :
    heteroKron (∑ b ∈ s, A b) C = ∑ b ∈ s, heteroKron (A b) C := by
  ext p q
  simp [heteroKron, Matrix.kronecker, Matrix.sum_apply, Finset.sum_mul]

/-- Tensor placement is additive over finite sums in the right factor. -/
theorem heteroKron_finset_sum_right {β ιA ιB : Type*} (s : Finset β)
    (A : Op ιA) (C : β → Op ιB) :
    heteroKron A (∑ b ∈ s, C b) = ∑ b ∈ s, heteroKron A (C b) := by
  ext p q
  simp [heteroKron, Matrix.kronecker, Matrix.sum_apply, Finset.mul_sum]

/-- The quadratic form is additive over finite sums of operators. -/
theorem stateQForm_finset_sum {β ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (s : Finset β) (M : β → Op ι) :
    stateQForm ψ (∑ b ∈ s, M b) = ∑ b ∈ s, stateQForm ψ (M b) := by
  simp [stateQForm, applyOperatorToState]

/-- The average over the one-point uniform distribution is the sum over the
outcomes. -/
theorem opFamilyDistSq_uniform_unit {γ ι : Type*} [Fintype γ] [Fintype ι]
    [DecidableEq ι] (M N : Unit → γ → Op ι) (ψ : EuclideanSpace ℂ ι) :
    opFamilyDistSq (uniformDistribution Unit) M N ψ =
      ∑ c : γ, ‖applyOperatorToState (M () c - N () c) ψ‖ ^ 2 := by
  unfold opFamilyDistSq avgOver
  simp [uniformDistribution, Distribution.uniformOnFinset_weight]

/-! ## Matrices of isometries -/

/-- The matrix of an isometry is a matrix isometry. -/
theorem isometryMatrix_conjTranspose_mul {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι']
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ι') :
    (isometryMatrix φ)ᴴ * isometryMatrix φ = 1 := by
  apply Matrix.toEuclideanLin.injective
  have hM : Matrix.toEuclideanLin (isometryMatrix φ) = φ.toLinearMap :=
    Matrix.toEuclideanLin.apply_symm_apply φ.toLinearMap
  calc
    Matrix.toEuclideanLin ((isometryMatrix φ)ᴴ * isometryMatrix φ) =
        (Matrix.toEuclideanLin (isometryMatrix φ)).adjoint.comp
          (Matrix.toEuclideanLin (isometryMatrix φ)) :=
      Matrix.toEuclideanLin_conjTranspose_mul_self _
    _ = φ.toLinearMap.adjoint.comp φ.toLinearMap := by rw [hM]
    _ = 1 := φ.adjoint_comp_self'
    _ = Matrix.toEuclideanLin (1 : Matrix ι ι ℂ) := by
      rw [Matrix.toEuclideanLin, Matrix.toLpLin_one]
      rfl

/-- The range projection `V Vᴴ` of a matrix isometry is at most the identity. -/
theorem isometryMatrix_mul_conjTranspose_le_one {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι']
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ι') :
    isometryMatrix φ * (isometryMatrix φ)ᴴ ≤ 1 := by
  have hproj : IsProj (isometryMatrix φ * (isometryMatrix φ)ᴴ) := by
    constructor
    · change (isometryMatrix φ * (isometryMatrix φ)ᴴ) *
        (isometryMatrix φ * (isometryMatrix φ)ᴴ) = isometryMatrix φ * (isometryMatrix φ)ᴴ
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (isometryMatrix φ)ᴴ,
        isometryMatrix_conjTranspose_mul, Matrix.one_mul]
    · change star (isometryMatrix φ * (isometryMatrix φ)ᴴ) =
        isometryMatrix φ * (isometryMatrix φ)ᴴ
      simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul]
  exact sub_nonneg.mp hproj.one_sub.nonneg

/-- Conjugation by an isometry preserves contractions. -/
theorem conjTranspose_mul_le_one_conjIsometry {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι']
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ι') {A : Op ι} (hA : Aᴴ * A ≤ 1) :
    (conjIsometry φ A)ᴴ * conjIsometry φ A ≤ 1 := by
  rw [conjIsometry_eq]
  have h1 : (isometryMatrix φ * A * (isometryMatrix φ)ᴴ)ᴴ *
      (isometryMatrix φ * A * (isometryMatrix φ)ᴴ) =
      isometryMatrix φ * (Aᴴ * A) * (isometryMatrix φ)ᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (isometryMatrix φ)ᴴ (isometryMatrix φ),
      isometryMatrix_conjTranspose_mul, Matrix.one_mul]
  rw [h1]
  calc isometryMatrix φ * (Aᴴ * A) * (isometryMatrix φ)ᴴ ≤
        isometryMatrix φ * (1 : Op ι) * (isometryMatrix φ)ᴴ := by
        rw [Matrix.le_iff]
        have h := (Matrix.le_iff.mp hA).mul_mul_conjTranspose_same (isometryMatrix φ)
        convert h using 1
        simp [Matrix.mul_sub, Matrix.sub_mul]
    _ = isometryMatrix φ * (isometryMatrix φ)ᴴ := by rw [Matrix.mul_one]
    _ ≤ 1 := isometryMatrix_mul_conjTranspose_le_one φ

/-- Conjugation by an isometry is multiplicative. -/
theorem conjIsometry_mul {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι']
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ι') (A B : Op ι) :
    conjIsometry φ A * conjIsometry φ B = conjIsometry φ (A * B) := by
  simp only [conjIsometry_eq, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (isometryMatrix φ)ᴴ (isometryMatrix φ),
    isometryMatrix_conjTranspose_mul, Matrix.one_mul]

/-- Conjugation by an isometry is additive. -/
theorem conjIsometry_sub {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι']
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ι') (A B : Op ι) :
    conjIsometry φ (A - B) = conjIsometry φ A - conjIsometry φ B := by
  simp only [conjIsometry_eq, Matrix.mul_sub, Matrix.sub_mul]

/-- The two-sided isometry image of a state is the action of the Kronecker
product of the two isometry matrices. -/
theorem isometryTensor_eq_toEuclideanLin {ιA ιB κA κB : Type}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]
    (φA : EuclideanSpace ℂ ιA →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (φB : EuclideanSpace ℂ ιB →ₗᵢ[ℂ] EuclideanSpace ℂ κB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    isometryTensor φA φB ψ =
      Matrix.toEuclideanLin
        (Matrix.kronecker (isometryMatrix φA) (isometryMatrix φB)) ψ := by
  ext p
  rw [isometryTensor_apply_eq]
  simp [Matrix.toEuclideanLin, Matrix.mulVec, dotProduct]

/-- The Kronecker product of two matrix isometries is a matrix isometry. -/
theorem kronecker_isometryMatrix_conjTranspose_mul {ιA ιB κA κB : Type}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]
    (φA : EuclideanSpace ℂ ιA →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (φB : EuclideanSpace ℂ ιB →ₗᵢ[ℂ] EuclideanSpace ℂ κB) :
    (Matrix.kronecker (isometryMatrix φA) (isometryMatrix φB))ᴴ *
      Matrix.kronecker (isometryMatrix φA) (isometryMatrix φB) = 1 := by
  unfold Matrix.kronecker
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    isometryMatrix_conjTranspose_mul, isometryMatrix_conjTranspose_mul,
    Matrix.one_kronecker_one]

/-- The two-sided isometry image preserves norms. -/
theorem norm_isometryTensor {ιA ιB κA κB : Type}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]
    (φA : EuclideanSpace ℂ ιA →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (φB : EuclideanSpace ℂ ιB →ₗᵢ[ℂ] EuclideanSpace ℂ κB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    ‖isometryTensor φA φB ψ‖ = ‖ψ‖ := by
  rw [isometryTensor_eq_toEuclideanLin]
  exact norm_toEuclideanLin_of_conjTranspose_mul_eq_one
    (kronecker_isometryMatrix_conjTranspose_mul φA φB) ψ

/-- A left-placed conjugated operator acts on the transported state as the
left-placed original operator acts on the original state. -/
theorem applyOperatorToState_leftTensor_conjIsometry {ιA ιB κA κB : Type}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]
    (φA : EuclideanSpace ℂ ιA →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (φB : EuclideanSpace ℂ ιB →ₗᵢ[ℂ] EuclideanSpace ℂ κB)
    (X : Op ιA) (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    applyOperatorToState (heteroKron (conjIsometry φA X) 1) (isometryTensor φA φB ψ) =
      isometryTensor φA φB (applyOperatorToState (heteroKron X 1) ψ) := by
  rw [isometryTensor_eq_toEuclideanLin, isometryTensor_eq_toEuclideanLin]
  unfold applyOperatorToState
  rw [← toEuclideanLin_mul_apply, ← toEuclideanLin_mul_apply]
  refine congrArg (fun M => Matrix.toEuclideanLin M ψ) ?_
  unfold heteroKron Matrix.kronecker
  rw [conjIsometry_eq, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.mul_assoc, isometryMatrix_conjTranspose_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_one]

/-- A right-placed conjugated operator acts on the transported state as the
right-placed original operator acts on the original state. -/
theorem applyOperatorToState_rightTensor_conjIsometry {ιA ιB κA κB : Type}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]
    (φA : EuclideanSpace ℂ ιA →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (φB : EuclideanSpace ℂ ιB →ₗᵢ[ℂ] EuclideanSpace ℂ κB)
    (Y : Op ιB) (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    applyOperatorToState (heteroKron 1 (conjIsometry φB Y)) (isometryTensor φA φB ψ) =
      isometryTensor φA φB (applyOperatorToState (heteroKron 1 Y) ψ) := by
  rw [isometryTensor_eq_toEuclideanLin, isometryTensor_eq_toEuclideanLin]
  unfold applyOperatorToState
  rw [← toEuclideanLin_mul_apply, ← toEuclideanLin_mul_apply]
  refine congrArg (fun M => Matrix.toEuclideanLin M ψ) ?_
  unfold heteroKron Matrix.kronecker
  rw [conjIsometry_eq, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.mul_assoc, isometryMatrix_conjTranspose_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_one]

/-! ## The ground projection -/

/-- The orthogonal projection of an enlarged local space onto its ground slice,
namely the inflation of the identity.  Formalization-only support for the
transfer step of `thm:ms-rigidity`, blueprint `ch13_qpbt_test.tex:224-253`. -/
def groundProjection (ι α : Type) [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] : Op (ι × Option α) :=
  naimarkInflation (α := α) (1 : Op ι)

/-- Inflation is multiplicative. -/
theorem naimarkInflation_mul {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (M N : Op ι) :
    naimarkInflation (α := α) M * naimarkInflation (α := α) N =
      naimarkInflation (α := α) (M * N) := by
  ext p q
  simp only [Matrix.mul_apply, naimarkInflation_apply, Fintype.sum_prod_type,
    Fintype.sum_option]
  by_cases hp : p.2 = none <;> by_cases hq : q.2 = none <;> simp [hp, hq]

/-- Inflation commutes with the conjugate transpose. -/
theorem naimarkInflation_conjTranspose {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (M : Op ι) :
    (naimarkInflation (α := α) M)ᴴ = naimarkInflation (α := α) Mᴴ := by
  ext p q
  simp only [Matrix.conjTranspose_apply, naimarkInflation_apply]
  by_cases hp : p.2 = none <;> by_cases hq : q.2 = none <;> simp [hp, hq]

/-- The ground projection is an orthogonal projection. -/
theorem isProj_groundProjection (ι α : Type) [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] : IsProj (groundProjection ι α) := by
  constructor
  · change groundProjection ι α * groundProjection ι α = groundProjection ι α
    rw [groundProjection, naimarkInflation_mul, Matrix.mul_one]
  · change star (groundProjection ι α) = groundProjection ι α
    rw [Matrix.star_eq_conjTranspose, groundProjection, naimarkInflation_conjTranspose,
      Matrix.conjTranspose_one]

/-- Inflating the compression of an operator to the ground slice is compressing
it by the ground projection. -/
theorem naimarkInflation_naimarkCompression {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (P : Op (ι × Option α)) :
    naimarkInflation (α := α) (naimarkCompression (α := α) P) =
      groundProjection ι α * P * groundProjection ι α := by
  ext p q
  simp only [Matrix.mul_apply, naimarkInflation_apply, naimarkCompression_apply,
    groundProjection, Fintype.sum_prod_type, Fintype.sum_option, Matrix.one_apply]
  by_cases hp : p.2 = none <;> by_cases hq : q.2 = none <;> simp [hp, hq]

/-- Compression to the ground slice commutes with finite sums. -/
theorem naimarkCompression_finset_sum {ι α β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (s : Finset β) (M : β → Op (ι × Option α)) :
    naimarkCompression (α := α) (∑ b ∈ s, M b) =
      ∑ b ∈ s, naimarkCompression (α := α) (M b) := by
  ext i j
  simp [Matrix.sum_apply]

/-- The dilated state lies in the ground slice on Alice's side. -/
theorem applyOperatorToState_leftTensor_groundProjection (α : Type) [Fintype α]
    [DecidableEq α] {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB]
    [DecidableEq ιB] (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    applyOperatorToState (heteroKron (groundProjection ιA α) 1) (naimarkDilatedState α ψ) =
      naimarkDilatedState α ψ := by
  have hfull : applyOperatorToState
      (heteroKron (groundProjection ιA α) (groundProjection ιB α))
      (naimarkDilatedState α ψ) = naimarkDilatedState α ψ := by
    rw [groundProjection, groundProjection, applyOperatorToState_heteroKron_naimarkInflation,
      heteroKron_one_one, applyOperatorToState_one]
  conv_lhs => rw [← hfull]
  rw [← applyOperatorToState_mul, heteroKron_mul,
    (isProj_groundProjection ιA α).isIdempotentElem.eq, Matrix.one_mul]
  exact hfull

/-- The dilated state lies in the ground slice on Bob's side. -/
theorem applyOperatorToState_rightTensor_groundProjection (α : Type) [Fintype α]
    [DecidableEq α] {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB]
    [DecidableEq ιB] (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    applyOperatorToState (heteroKron 1 (groundProjection ιB α)) (naimarkDilatedState α ψ) =
      naimarkDilatedState α ψ := by
  have hfull : applyOperatorToState
      (heteroKron (groundProjection ιA α) (groundProjection ιB α))
      (naimarkDilatedState α ψ) = naimarkDilatedState α ψ := by
    rw [groundProjection, groundProjection, applyOperatorToState_heteroKron_naimarkInflation,
      heteroKron_one_one, applyOperatorToState_one]
  conv_lhs => rw [← hfull]
  rw [← applyOperatorToState_mul, heteroKron_mul,
    (isProj_groundProjection ιB α).isIdempotentElem.eq, Matrix.one_mul]
  exact hfull

/-- The complement of the ground slice annihilates the dilated state on Alice's
side. -/
theorem applyOperatorToState_leftTensor_one_sub_groundProjection (α : Type) [Fintype α]
    [DecidableEq α] {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB]
    [DecidableEq ιB] (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    applyOperatorToState (heteroKron (1 - groundProjection ιA α) 1)
      (naimarkDilatedState α ψ) = 0 := by
  have h : heteroKron (1 - groundProjection ιA α) (1 : Op (ιB × Option α)) =
      1 - heteroKron (groundProjection ιA α) 1 := by
    rw [heteroKron_sub_left, heteroKron_one_one]
  have hsub : applyOperatorToState (1 - heteroKron (groundProjection ιA α) 1)
      (naimarkDilatedState α ψ) =
      applyOperatorToState 1 (naimarkDilatedState α ψ) -
        applyOperatorToState (heteroKron (groundProjection ιA α) 1)
          (naimarkDilatedState α ψ) := by
    simp [applyOperatorToState]
  rw [h, hsub, applyOperatorToState_one, applyOperatorToState_leftTensor_groundProjection,
    sub_self]

/-- The complement of the ground slice annihilates the dilated state on Bob's
side. -/
theorem applyOperatorToState_rightTensor_one_sub_groundProjection (α : Type) [Fintype α]
    [DecidableEq α] {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB]
    [DecidableEq ιB] (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    applyOperatorToState (heteroKron 1 (1 - groundProjection ιB α))
      (naimarkDilatedState α ψ) = 0 := by
  have h : heteroKron (1 : Op (ιA × Option α)) (1 - groundProjection ιB α) =
      1 - heteroKron 1 (groundProjection ιB α) := by
    rw [heteroKron_sub_right, heteroKron_one_one]
  have hsub : applyOperatorToState (1 - heteroKron 1 (groundProjection ιB α))
      (naimarkDilatedState α ψ) =
      applyOperatorToState 1 (naimarkDilatedState α ψ) -
        applyOperatorToState (heteroKron 1 (groundProjection ιB α))
          (naimarkDilatedState α ψ) := by
    simp [applyOperatorToState]
  rw [h, hsub, applyOperatorToState_one, applyOperatorToState_rightTensor_groundProjection,
    sub_self]

/-! ## Leakage out of the ground slice is bounded by the intertwining defect -/

/-- The leakage of a left-placed operator `P` out of the ground slice on the
dilated state is at most the intertwining defect of `P ⊗ 1` against any
right-placed operator `1 ⊗ Q`, because `(1 - Π) ⊗ 1` annihilates `1 ⊗ Q ψ'`.
This is the estimate replacing the `≈_δ` preservation that Naimark dilation
lacks (`references/ldt-paper/orthonormalization.tex:82-101`). -/
theorem norm_leftTensor_one_sub_groundProjection_mul_le (α : Type) [Fintype α]
    [DecidableEq α] {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB]
    [DecidableEq ιB] (ψ : EuclideanSpace ℂ (ιA × ιB))
    (P : Op (ιA × Option α)) (Q : Op (ιB × Option α)) :
    ‖applyOperatorToState (heteroKron ((1 - groundProjection ιA α) * P) 1)
        (naimarkDilatedState α ψ)‖ ≤
      ‖applyOperatorToState (heteroKron P 1 - heteroKron 1 Q)
        (naimarkDilatedState α ψ)‖ := by
  set ψ' := naimarkDilatedState α ψ
  set L : Op ((ιA × Option α) × (ιB × Option α)) :=
    heteroKron (1 - groundProjection ιA α) 1
  have hL0 : applyOperatorToState L ψ' = 0 :=
    applyOperatorToState_leftTensor_one_sub_groundProjection α ψ
  have hLcontr : Lᴴ * L ≤ 1 :=
    conjTranspose_mul_le_one_leftTensor
      (conjTranspose_mul_le_one_of_isProj (isProj_groundProjection ιA α).one_sub)
  have hsplit : heteroKron ((1 - groundProjection ιA α) * P)
      (1 : Op (ιB × Option α)) = L * heteroKron P 1 := by
    rw [heteroKron_mul, Matrix.one_mul]
  have hcomm : L * heteroKron 1 Q = heteroKron 1 Q * L := by
    rw [heteroKron_mul, heteroKron_mul, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_one]
  have key : applyOperatorToState (heteroKron ((1 - groundProjection ιA α) * P) 1) ψ' =
      applyOperatorToState L
        (applyOperatorToState (heteroKron P 1 - heteroKron 1 Q) ψ') := by
    rw [hsplit, applyOperatorToState_mul]
    have hdec : applyOperatorToState (heteroKron P 1) ψ' =
        applyOperatorToState (heteroKron P 1 - heteroKron 1 Q) ψ' +
          applyOperatorToState (heteroKron 1 Q) ψ' := by
      simp [applyOperatorToState]
    rw [hdec, applyOperatorToState_add, ← applyOperatorToState_mul L (heteroKron 1 Q), hcomm,
      applyOperatorToState_mul, hL0, applyOperatorToState_zero, add_zero]
  rw [key]
  exact norm_applyOperatorToState_le hLcontr _

/-- The leakage of a right-placed operator `Q` out of the ground slice on the
dilated state is at most its intertwining defect against any left-placed
operator. -/
theorem norm_rightTensor_one_sub_groundProjection_mul_le (α : Type) [Fintype α]
    [DecidableEq α] {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB]
    [DecidableEq ιB] (ψ : EuclideanSpace ℂ (ιA × ιB))
    (P : Op (ιA × Option α)) (Q : Op (ιB × Option α)) :
    ‖applyOperatorToState (heteroKron 1 ((1 - groundProjection ιB α) * Q))
        (naimarkDilatedState α ψ)‖ ≤
      ‖applyOperatorToState (heteroKron P 1 - heteroKron 1 Q)
        (naimarkDilatedState α ψ)‖ := by
  set ψ' := naimarkDilatedState α ψ
  set L : Op ((ιA × Option α) × (ιB × Option α)) :=
    heteroKron 1 (1 - groundProjection ιB α)
  have hL0 : applyOperatorToState L ψ' = 0 :=
    applyOperatorToState_rightTensor_one_sub_groundProjection α ψ
  have hLcontr : Lᴴ * L ≤ 1 :=
    conjTranspose_mul_le_one_rightTensor
      (conjTranspose_mul_le_one_of_isProj (isProj_groundProjection ιB α).one_sub)
  have hsplit : heteroKron (1 : Op (ιA × Option α))
      ((1 - groundProjection ιB α) * Q) = L * heteroKron 1 Q := by
    rw [heteroKron_mul, Matrix.one_mul]
  have hcomm : L * heteroKron P 1 = heteroKron P 1 * L := by
    rw [heteroKron_mul, heteroKron_mul, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_one]
  have key : applyOperatorToState (heteroKron 1 ((1 - groundProjection ιB α) * Q)) ψ' =
      applyOperatorToState L
        (applyOperatorToState (heteroKron 1 Q - heteroKron P 1) ψ') := by
    rw [hsplit, applyOperatorToState_mul]
    have hdec : applyOperatorToState (heteroKron 1 Q) ψ' =
        applyOperatorToState (heteroKron 1 Q - heteroKron P 1) ψ' +
          applyOperatorToState (heteroKron P 1) ψ' := by
      simp [applyOperatorToState]
    rw [hdec, applyOperatorToState_add, ← applyOperatorToState_mul L (heteroKron P 1), hcomm,
      applyOperatorToState_mul, hL0, applyOperatorToState_zero, add_zero]
  have hneg : -applyOperatorToState (heteroKron P 1 - heteroKron 1 Q) ψ' =
      applyOperatorToState (heteroKron 1 Q - heteroKron P 1) ψ' := by
    simp [applyOperatorToState]
  rw [key]
  calc ‖applyOperatorToState L
          (applyOperatorToState (heteroKron 1 Q - heteroKron P 1) ψ')‖ ≤
        ‖applyOperatorToState (heteroKron 1 Q - heteroKron P 1) ψ'‖ :=
        norm_applyOperatorToState_le hLcontr _
    _ = ‖applyOperatorToState (heteroKron P 1 - heteroKron 1 Q) ψ'‖ := by
        rw [← hneg, norm_neg]

end

end MIPStarRE.QPBT.MagicSquareRigidity
