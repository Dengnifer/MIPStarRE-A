import MIPStarRE.QPBT.Test.MagicSquareTheorems.PerfectStrategy.Observables
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.Anticommutation
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.Transfer

/-!
# Swap-isometry extraction for Magic Square rigidity

This module constructs the local swap isometries used in the finite-dimensional
proof of Magic Square rigidity.  A reflection `Z` splits a local vector into its
two eigenspaces, while a second reflection `X` identifies the negative
eigenspace with the residual copy of the original Hilbert space.  Crucially,
the resulting map is an exact isometry even when `X` and `Z` anticommute only on
the strategy state.

The final section specializes this construction to the distinguished local
reflections of both players in the projectively dilated Magic Square strategy.
A joint two-EPR specialization is not stated here: the current symmetric game
does not relate the two players' variable representations.  The resulting
two-copy obstruction is recorded in
`audits/2026-09-04_magic-square-rigidity-orientation-obstruction.md`.

## References

The target statement is `thm:ms-rigidity` in
`blueprint/src/chapter/ch13_qpbt_test.tex:224-253`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`.
The concrete binary Pauli projectors and EPR vector are those of
`references/qpbt-paper/04_preliminaries.tex:1097-1262`.  The cited robust
self-test is Coladangelo--Stark, arXiv:1709.09267v2, Theorem 6.9.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

private theorem sum_zmod_two {M : Type*} [AddCommMonoid M] (f : ZMod 2 → M) :
    ∑ b, f b = f 0 + f 1 := by
  calc
    ∑ b, f b = ∑ i : Fin 2, f (ZMod.finEquiv 2 i) := by
      exact Fintype.sum_equiv (ZMod.finEquiv 2).symm f
        (fun i : Fin 2 => f (ZMod.finEquiv 2 i)) (fun _ => rfl)
    _ = f (ZMod.finEquiv 2 0) + f (ZMod.finEquiv 2 1) := Fin.sum_univ_two _
    _ = f 0 + f 1 := by rfl

/-! ## The one-qubit swap isometry -/

/-- The linear controlled-swap map associated with two local operators.  For a
binary output `b`, its residual component is `X^b P_b(Z) psi`, where `P_b(Z)`
is the spectral effect of the reflection `Z`. -/
def binarySwapMap {ι : Type} [Fintype ι] [DecidableEq ι]
    (X Z : Op ι) :
    EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ (ZMod 2 × ι) where
  toFun ψ := (EuclideanSpace.equiv (ZMod 2 × ι) ℂ).symm
    (fun bi => applyOperatorToState (X ^ bi.1.val * reflectionEffect Z bi.1) ψ bi.2)
  map_add' ψ ξ := by
    apply (EuclideanSpace.equiv (ZMod 2 × ι) ℂ).injective
    funext bi
    simp only [ContinuousLinearEquiv.apply_symm_apply]
    unfold applyOperatorToState
    rw [map_add]
    rfl
  map_smul' c ψ := by
    apply (EuclideanSpace.equiv (ZMod 2 × ι) ℂ).injective
    funext bi
    simp only [ContinuousLinearEquiv.apply_symm_apply, RingHom.id_apply]
    unfold applyOperatorToState
    rw [map_smul]
    rfl

/-- The controlled-swap map preserves norms whenever both controlling
operators are reflections.  No anticommutation assumption is needed. -/
theorem binarySwapMap_norm {ι : Type} [Fintype ι] [DecidableEq ι]
    (X Z : Op ι) (hX : IsReflection X) (hZ : IsReflection Z)
    (ψ : EuclideanSpace ℂ ι) :
    ‖binarySwapMap X Z ψ‖ = ‖ψ‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  change
    (∑ bi : ZMod 2 × ι,
      ‖applyOperatorToState (X ^ bi.1.val * reflectionEffect Z bi.1) ψ bi.2‖ ^ 2) =
      ∑ i : ι, ‖ψ i‖ ^ 2
  rw [Fintype.sum_prod_type, sum_zmod_two]
  simp only [ZMod.val_zero, pow_zero, one_mul, ZMod.val_one, pow_one]
  rw [show
      ∑ i : ι, ‖applyOperatorToState (reflectionEffect Z 0) ψ i‖ ^ 2 =
        ‖applyOperatorToState (reflectionEffect Z 0) ψ‖ ^ 2 by
          exact (EuclideanSpace.norm_sq_eq _).symm,
    show
      ∑ i : ι, ‖applyOperatorToState (X * reflectionEffect Z 1) ψ i‖ ^ 2 =
        ‖applyOperatorToState (X * reflectionEffect Z 1) ψ‖ ^ 2 by
          exact (EuclideanSpace.norm_sq_eq _).symm,
    show ∑ i : ι, ‖ψ i‖ ^ 2 = ‖ψ‖ ^ 2 by
      exact (EuclideanSpace.norm_sq_eq _).symm,
    norm_applyOperatorToState_isometry_mul hX.isometry]
  have hplus : applyOperatorToState (reflectionEffect Z 0) ψ =
      (2 : ℂ)⁻¹ • (ψ + applyOperatorToState Z ψ) := by
    simp [reflectionEffect, applyOperatorToState_smul,
      applyOperatorToState_add_op, applyOperatorToState_one]
  have hminus : applyOperatorToState (reflectionEffect Z 1) ψ =
      (2 : ℂ)⁻¹ • (ψ - applyOperatorToState Z ψ) := by
    simp [reflectionEffect, applyOperatorToState_smul,
      applyOperatorToState_sub_op, applyOperatorToState_one]
  rw [hplus, hminus, norm_smul, norm_smul]
  rw [show ‖(2 : ℂ)⁻¹‖ = (2 : ℝ)⁻¹ by norm_num]
  have hZnorm := norm_applyOperatorToState_of_isometry hZ.isometry ψ
  have hpara := parallelogram_law_with_norm_mul ℂ ψ (applyOperatorToState Z ψ)
  rw [hZnorm] at hpara
  nlinarith [hpara]

/-- The local controlled-swap map bundled as a linear isometric embedding. -/
noncomputable def binarySwapIsometry {ι : Type} [Fintype ι] [DecidableEq ι]
    (X Z : Op ι) (hX : IsReflection X) (hZ : IsReflection Z) :
    EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ (ZMod 2 × ι) where
  toLinearMap := binarySwapMap X Z
  norm_map' := binarySwapMap_norm X Z hX hZ

/-- Coordinate formula for the binary swap isometry. -/
@[simp]
theorem binarySwapIsometry_apply {ι : Type} [Fintype ι] [DecidableEq ι]
    (X Z : Op ι) (hX : IsReflection X) (hZ : IsReflection Z)
    (ψ : EuclideanSpace ℂ ι) (b : ZMod 2) (i : ι) :
    binarySwapIsometry X Z hX hZ ψ (b, i) =
      applyOperatorToState (X ^ b.val * reflectionEffect Z b) ψ i := rfl

/-! ## Binary Pauli actions on the extracted register -/

/-- The Pauli `X` matrix in the binary computational basis. -/
def swapPauliX : Op (ZMod 2) :=
  fun b c => if b = c then 0 else 1

/-- The Pauli `Z` matrix in the binary computational basis. -/
def swapPauliZ : Op (ZMod 2) :=
  fun b c => if b = c then if b = 0 then 1 else -1 else 0

/-- The extracted binary `X` matrix is a reflection. -/
theorem isReflection_swapPauliX : IsReflection swapPauliX := by
  constructor
  · ext b c
    rcases zmod_two_eq_zero_or_one b with rfl | rfl <;>
      rcases zmod_two_eq_zero_or_one c with rfl | rfl <;>
        norm_num [swapPauliX, Matrix.conjTranspose_apply]
  · ext b c
    simp only [Matrix.mul_apply]
    rw [sum_zmod_two]
    rcases zmod_two_eq_zero_or_one b with rfl | rfl <;>
      rcases zmod_two_eq_zero_or_one c with rfl | rfl <;>
        norm_num [swapPauliX, Matrix.one_apply]

/-- The extracted binary `Z` matrix is a reflection. -/
theorem isReflection_swapPauliZ : IsReflection swapPauliZ := by
  constructor
  · ext b c
    rcases zmod_two_eq_zero_or_one b with rfl | rfl <;>
      rcases zmod_two_eq_zero_or_one c with rfl | rfl <;>
        norm_num [swapPauliZ, Matrix.conjTranspose_apply]
  · ext b c
    simp only [Matrix.mul_apply]
    rw [sum_zmod_two]
    rcases zmod_two_eq_zero_or_one b with rfl | rfl <;>
      rcases zmod_two_eq_zero_or_one c with rfl | rfl <;>
        norm_num [swapPauliZ, Matrix.one_apply]

/-- The extracted binary Pauli matrices anticommute. -/
theorem swapPauliX_mul_swapPauliZ :
    swapPauliX * swapPauliZ = -(swapPauliZ * swapPauliX) := by
  ext b c
  change (∑ k, swapPauliX b k * swapPauliZ k c) =
    -(∑ k, swapPauliZ b k * swapPauliX k c)
  rw [sum_zmod_two, sum_zmod_two]
  rcases zmod_two_eq_zero_or_one b with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one c with rfl | rfl <;>
      norm_num [swapPauliX, swapPauliZ]

/-- Acting by extracted `Z` multiplies the binary component by its sign. -/
theorem apply_swapPauliZ_left {ι : Type} [Fintype ι] [DecidableEq ι]
    (ξ : EuclideanSpace ℂ (ZMod 2 × ι)) (b : ZMod 2) (i : ι) :
    applyOperatorToState (heteroKron swapPauliZ (1 : Op ι)) ξ (b, i) =
      ((bitSign b : ℝ) : ℂ) * ξ (b, i) := by
  unfold applyOperatorToState
  change (∑ p : ZMod 2 × ι, heteroKron swapPauliZ 1 (b, i) p * ξ p) = _
  rw [Fintype.sum_prod_type]
  rcases zmod_two_eq_zero_or_one b with rfl | rfl <;>
    simp [heteroKron, swapPauliZ, bitSign, ZMod.val_one, Matrix.one_apply]

/-- Acting by extracted `X` exchanges the two binary components. -/
theorem apply_swapPauliX_left {ι : Type} [Fintype ι] [DecidableEq ι]
    (ξ : EuclideanSpace ℂ (ZMod 2 × ι)) (b : ZMod 2) (i : ι) :
    applyOperatorToState (heteroKron swapPauliX (1 : Op ι)) ξ (b, i) =
      ξ (b + 1, i) := by
  unfold applyOperatorToState
  change (∑ p : ZMod 2 × ι, heteroKron swapPauliX 1 (b, i) p * ξ p) = _
  rw [Fintype.sum_prod_type]
  rcases zmod_two_eq_zero_or_one b with rfl | rfl <;>
    simp only [heteroKron]
  all_goals rw [sum_zmod_two]
  all_goals norm_num [swapPauliX, Matrix.one_apply]
  all_goals rw [show (2 : ZMod 2) = 0 by decide]

private theorem reflectionEffect_zero_mul_reflection
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (Z : Op ι) (hZ : IsReflection Z) :
    reflectionEffect Z 0 * Z = reflectionEffect Z 0 := by
  simp only [reflectionEffect, if_pos, Matrix.smul_mul]
  rw [add_mul, one_mul, hZ.mul_self_eq_one]
  rw [add_comm]

private theorem reflectionEffect_one_mul_reflection
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (Z : Op ι) (hZ : IsReflection Z) :
    reflectionEffect Z 1 * Z = -reflectionEffect Z 1 := by
  simp only [reflectionEffect, if_neg one_ne_zero, Matrix.smul_mul]
  rw [sub_mul, one_mul, hZ.mul_self_eq_one]
  module

/-- The controlled-swap isometry transports its controlling reflection exactly
to Pauli `Z` on the extracted binary register. -/
theorem binarySwap_intertwines_Z {ι : Type} [Fintype ι] [DecidableEq ι]
    (X Z : Op ι) (hX : IsReflection X) (hZ : IsReflection Z)
    (ψ : EuclideanSpace ℂ ι) :
    binarySwapIsometry X Z hX hZ (applyOperatorToState Z ψ) =
      applyOperatorToState (heteroKron swapPauliZ (1 : Op ι))
        (binarySwapIsometry X Z hX hZ ψ) := by
  ext bi
  rcases bi with ⟨b, i⟩
  rw [apply_swapPauliZ_left]
  rcases zmod_two_eq_zero_or_one b with rfl | rfl
  · simp only [binarySwapIsometry_apply, ZMod.val_zero, pow_zero, one_mul]
    rw [← applyOperatorToState_mul, reflectionEffect_zero_mul_reflection Z hZ]
    norm_num [bitSign]
  · simp only [binarySwapIsometry_apply, ZMod.val_one, pow_one]
    rw [← applyOperatorToState_mul, mul_assoc,
      reflectionEffect_one_mul_reflection Z hZ]
    norm_num [bitSign, ZMod.val_one, applyOperatorToState_neg_op]

private theorem reflectionEffect_zero_mul_X_sub_X_mul_one
    {ι : Type} [Fintype ι] [DecidableEq ι] (X Z : Op ι) :
    reflectionEffect Z 0 * X - X * reflectionEffect Z 1 =
      (2 : ℂ)⁻¹ • (X * Z - -(Z * X)) := by
  simp only [reflectionEffect, if_pos, if_neg one_ne_zero]
  calc
    ((2 : ℂ)⁻¹ • (1 + Z)) * X - X * ((2 : ℂ)⁻¹ • (1 - Z)) =
        (2 : ℂ)⁻¹ • ((1 + Z) * X - X * (1 - Z)) := by
      rw [Matrix.smul_mul, Matrix.mul_smul]
      module
    _ = (2 : ℂ)⁻¹ • (X * Z - -(Z * X)) := by
      congr 1
      noncomm_ring

private theorem X_mul_reflectionEffect_one_mul_X_sub_zero
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (X Z : Op ι) (hX : IsReflection X) :
    X * reflectionEffect Z 1 * X - reflectionEffect Z 0 =
      -(2 : ℂ)⁻¹ • (X * (X * Z - -(Z * X))) := by
  simp only [reflectionEffect, if_pos, if_neg one_ne_zero]
  calc
    X * ((2 : ℂ)⁻¹ • (1 - Z)) * X - (2 : ℂ)⁻¹ • (1 + Z) =
        (2 : ℂ)⁻¹ • (X * (1 - Z) * X - (1 + Z)) := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
      module
    _ = (2 : ℂ)⁻¹ • (-(X * (X * Z - -(Z * X)))) := by
      congr 1
      have hXXZ : X * (X * Z) = Z := by
        rw [← Matrix.mul_assoc, hX.mul_self_eq_one, one_mul]
      noncomm_ring [hX.mul_self_eq_one, hXXZ]
    _ = -(2 : ℂ)⁻¹ • (X * (X * Z - -(Z * X))) := by
      module

/-- The failure of the controlled-swap isometry to transport `X` to extracted
Pauli `X` is bounded by the anticommutator defect of `X` and `Z` on the input
vector. -/
theorem norm_binarySwap_intertwines_X_sub_le {ι : Type} [Fintype ι]
    [DecidableEq ι] (X Z : Op ι) (hX : IsReflection X) (hZ : IsReflection Z)
    (ψ : EuclideanSpace ℂ ι) :
    ‖binarySwapIsometry X Z hX hZ (applyOperatorToState X ψ) -
        applyOperatorToState (heteroKron swapPauliX (1 : Op ι))
          (binarySwapIsometry X Z hX hZ ψ)‖ ≤
      ‖applyOperatorToState (X * Z - -(Z * X)) ψ‖ := by
  let d := applyOperatorToState (X * Z - -(Z * X)) ψ
  have hcoord0 : ∀ i : ι,
      (binarySwapIsometry X Z hX hZ (applyOperatorToState X ψ) -
          applyOperatorToState (heteroKron swapPauliX (1 : Op ι))
            (binarySwapIsometry X Z hX hZ ψ)) (0, i) =
        (2 : ℂ)⁻¹ * d i := by
    intro i
    rw [PiLp.sub_apply, apply_swapPauliX_left]
    simp only [zero_add, binarySwapIsometry_apply, ZMod.val_zero, pow_zero,
      one_mul, ZMod.val_one, pow_one]
    change
      (applyOperatorToState (reflectionEffect Z 0) (applyOperatorToState X ψ) -
        applyOperatorToState (X * reflectionEffect Z 1) ψ) i = _
    rw [← applyOperatorToState_mul, ← applyOperatorToState_sub_op,
      reflectionEffect_zero_mul_X_sub_X_mul_one]
    rw [applyOperatorToState_smul]
    rfl
  have hcoord1 : ∀ i : ι,
      (binarySwapIsometry X Z hX hZ (applyOperatorToState X ψ) -
          applyOperatorToState (heteroKron swapPauliX (1 : Op ι))
            (binarySwapIsometry X Z hX hZ ψ)) (1, i) =
        -(2 : ℂ)⁻¹ * applyOperatorToState X d i := by
    intro i
    rw [PiLp.sub_apply, apply_swapPauliX_left]
    have htwo : (1 : ZMod 2) + 1 = 0 := by decide
    simp only [htwo, binarySwapIsometry_apply, ZMod.val_one, pow_one,
      ZMod.val_zero, pow_zero, one_mul]
    change
      (applyOperatorToState (X * reflectionEffect Z 1)
          (applyOperatorToState X ψ) -
        applyOperatorToState (reflectionEffect Z 0) ψ) i = _
    rw [← applyOperatorToState_mul, ← applyOperatorToState_sub_op,
      X_mul_reflectionEffect_one_mul_X_sub_zero X Z hX]
    rw [applyOperatorToState_smul, applyOperatorToState_mul]
    rfl
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  rw [EuclideanSpace.norm_sq_eq]
  change
    ∑ bi : ZMod 2 × ι,
      ‖(binarySwapIsometry X Z hX hZ (applyOperatorToState X ψ) -
          applyOperatorToState (heteroKron swapPauliX (1 : Op ι))
            (binarySwapIsometry X Z hX hZ ψ)) bi‖ ^ 2 ≤ ‖d‖ ^ 2
  rw [Fintype.sum_prod_type, sum_zmod_two]
  simp_rw [hcoord0, hcoord1, norm_mul, norm_neg,
    show ‖(2 : ℂ)⁻¹‖ = (2 : ℝ)⁻¹ by norm_num]
  simp_rw [mul_pow]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [show ∑ i : ι, ‖d i‖ ^ 2 = ‖d‖ ^ 2 by
      exact (EuclideanSpace.norm_sq_eq _).symm,
    show ∑ i : ι, ‖applyOperatorToState X d i‖ ^ 2 =
        ‖applyOperatorToState X d‖ ^ 2 by
      exact (EuclideanSpace.norm_sq_eq _).symm,
    norm_applyOperatorToState_of_isometry hX.isometry]
  nlinarith [sq_nonneg ‖d‖]

/-! ## Local Magic Square specializations -/

/-- Alice's local reflection for a variable question of the projectively
dilated strategy, before tensor placement on the bipartite space. -/
noncomputable def msLocalVarObsA (S : Strategy msGame) (j : Fin 9) :
    Op (msDilatedStrategy S).ιA :=
  signObs ((msDilatedStrategy S).A (.var j)) msBitOrZero

/-- Bob's local reflection for a variable question of the projectively
dilated strategy, before tensor placement on the bipartite space. -/
noncomputable def msLocalVarObsB (S : Strategy msGame) (j : Fin 9) :
    Op (msDilatedStrategy S).ιB :=
  signObs ((msDilatedStrategy S).B (.var j)) msBitOrZero

/-- Alice's dilated local variable observable is a reflection. -/
theorem isReflection_msLocalVarObsA (S : Strategy msGame) (j : Fin 9) :
    IsReflection (msLocalVarObsA S j) :=
  isReflection_signObs _ (msDilatedStrategy_isProjective_A S _) _

/-- Bob's dilated local variable observable is a reflection. -/
theorem isReflection_msLocalVarObsB (S : Strategy msGame) (j : Fin 9) :
    IsReflection (msLocalVarObsB S j) :=
  isReflection_signObs _ (msDilatedStrategy_isProjective_B S _) _

/-- Alice's exact binary controlled-swap embedding for the distinguished
variable-0 and variable-4 reflections. -/
noncomputable def msAliceBinarySwapIsometry (S : Strategy msGame) :
    EuclideanSpace ℂ (msDilatedStrategy S).ιA →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ZMod 2 × (msDilatedStrategy S).ιA) :=
  binarySwapIsometry (msLocalVarObsA S 0) (msLocalVarObsA S 4)
    (isReflection_msLocalVarObsA S 0) (isReflection_msLocalVarObsA S 4)

/-- Bob's exact binary controlled-swap embedding for the distinguished
variable-0 and variable-4 reflections. -/
noncomputable def msBobBinarySwapIsometry (S : Strategy msGame) :
    EuclideanSpace ℂ (msDilatedStrategy S).ιB →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ZMod 2 × (msDilatedStrategy S).ιB) :=
  binarySwapIsometry (msLocalVarObsB S 0) (msLocalVarObsB S 4)
    (isReflection_msLocalVarObsB S 0) (isReflection_msLocalVarObsB S 4)

end

end MIPStarRE.QPBT.MagicSquareRigidity
