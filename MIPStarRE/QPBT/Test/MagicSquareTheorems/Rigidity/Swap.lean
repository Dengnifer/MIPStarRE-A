import MIPStarRE.QPBT.Test.MagicSquareTheorems.PerfectStrategy.Observables
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.Anticommutation

/-!
# Swap-isometry extraction for Magic Square rigidity

This module constructs the local swap isometries used in the finite-dimensional
proof of Magic Square rigidity.  A binary observable `Z` splits a local vector
into its two eigenspaces, while a second binary observable `X` identifies the
negative eigenspace with the residual copy of the original Hilbert space.
Crucially, the resulting map is an exact isometry even when `X` and `Z`
anticommute only on the strategy state.

The final section specializes this construction to the distinguished local
binary observables of both players in the projectively dilated Magic Square
strategy.  A joint two-EPR specialization is not stated here: the current
symmetric game does not relate the two players' variable representations.  The
resulting two-copy obstruction is recorded in
`audits/2026-09-04_magic-square-rigidity-orientation-obstruction.md`.

## References

The target statement is blueprint `thm:ms-rigidity`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`.
The concrete binary Pauli projectors and EPR vector are those of
`references/qpbt-paper/04_preliminaries.tex:1097-1262`.  The cited robust
self-test is Coladangelo--Stark, arXiv:1709.09267v2, Theorem 6.9.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-! ## The one-qubit swap isometry -/

/-- Formalization-only linear controlled-swap map supporting
`thm:ms-rigidity`.  For a binary output `b`, its residual component is
`X^b P_b(Z) psi`, where `P_b(Z)` is the spectral effect of the binary observable
`Z`. -/
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

/-- Formalization-only support for `thm:ms-rigidity`: the controlled-swap map
preserves norms whenever both controlling operators are binary observables.  No
anticommutation assumption is needed. -/
theorem binarySwapMap_norm {ι : Type} [Fintype ι] [DecidableEq ι]
    (X Z : Op ι) (hX : IsBinaryObservable X) (hZ : IsBinaryObservable Z)
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
    simp [reflectionEffect, applyOperatorToState]
  rw [hplus, hminus, norm_smul, norm_smul]
  rw [show ‖(2 : ℂ)⁻¹‖ = (2 : ℝ)⁻¹ by norm_num]
  have hZnorm := norm_applyOperatorToState_of_isometry hZ.isometry ψ
  have hpara := parallelogram_law_with_norm_mul ℂ ψ (applyOperatorToState Z ψ)
  rw [hZnorm] at hpara
  nlinarith [hpara]

/-- Formalization-only local controlled-swap map for `thm:ms-rigidity`, bundled
as a linear isometric embedding. -/
noncomputable def binarySwapIsometry {ι : Type} [Fintype ι] [DecidableEq ι]
    (X Z : Op ι) (hX : IsBinaryObservable X) (hZ : IsBinaryObservable Z) :
    EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ (ZMod 2 × ι) where
  toLinearMap := binarySwapMap X Z
  norm_map' := binarySwapMap_norm X Z hX hZ

/-- Formalization-only coordinate formula for the binary swap isometry used in
`thm:ms-rigidity`. -/
@[simp]
theorem binarySwapIsometry_apply {ι : Type} [Fintype ι] [DecidableEq ι]
    (X Z : Op ι) (hX : IsBinaryObservable X) (hZ : IsBinaryObservable Z)
    (ψ : EuclideanSpace ℂ ι) (b : ZMod 2) (i : ι) :
    binarySwapIsometry X Z hX hZ ψ (b, i) =
      applyOperatorToState (X ^ b.val * reflectionEffect Z b) ψ i := rfl

/-! ## Binary Pauli actions on the extracted register -/

/-- Formalization-only support for `thm:ms-rigidity`: the canonical binary
shift Pauli operator is a binary observable. -/
theorem isBinaryObservable_binaryTauShift :
    IsBinaryObservable (tauShift (K := ZMod 2) 1) :=
  ⟨binaryTauShift_conjTranspose, binaryTauShift_sq⟩

/-- Formalization-only support for `thm:ms-rigidity`: the canonical binary
phase Pauli operator is a binary observable. -/
theorem isBinaryObservable_binaryTauPhase :
    IsBinaryObservable (tauPhase (K := ZMod 2) 1) :=
  ⟨binaryTauPhase_conjTranspose, binaryTauPhase_sq⟩

/-- Formalization-only Pauli-action formula for `thm:ms-rigidity`: acting by
the binary phase operator multiplies the extracted component by its sign. -/
theorem apply_binaryTauPhase_left {ι : Type} [Fintype ι] [DecidableEq ι]
    (ξ : EuclideanSpace ℂ (ZMod 2 × ι)) (b : ZMod 2) (i : ι) :
    applyOperatorToState
        (heteroKron (tauPhase (K := ZMod 2) 1) (1 : Op ι)) ξ (b, i) =
      ((bitSign b : ℝ) : ℂ) * ξ (b, i) := by
  unfold applyOperatorToState
  change
    (∑ p : ZMod 2 × ι,
      heteroKron (tauPhase (K := ZMod 2) 1) 1 (b, i) p * ξ p) = _
  rw [Fintype.sum_prod_type]
  rcases zmod_two_eq_zero_or_one b with rfl | rfl <;>
    simp [heteroKron, tauPhase, phaseSign, bitSign, ZMod.val_one,
      Matrix.one_apply]

/-- Formalization-only Pauli-action formula for `thm:ms-rigidity`: acting by
the binary shift operator exchanges the two extracted components. -/
theorem apply_binaryTauShift_left {ι : Type} [Fintype ι] [DecidableEq ι]
    (ξ : EuclideanSpace ℂ (ZMod 2 × ι)) (b : ZMod 2) (i : ι) :
    applyOperatorToState
        (heteroKron (tauShift (K := ZMod 2) 1) (1 : Op ι)) ξ (b, i) =
      ξ (b + 1, i) := by
  unfold applyOperatorToState
  change
    (∑ p : ZMod 2 × ι,
      heteroKron (tauShift (K := ZMod 2) 1) 1 (b, i) p * ξ p) = _
  rw [Fintype.sum_prod_type]
  rcases zmod_two_eq_zero_or_one b with rfl | rfl
  · simp only [heteroKron]
    rw [sum_zmod_two]
    simp +decide [tauShift, Matrix.one_apply]
  · rw [show (1 : ZMod 2) + 1 = 0 by decide]
    simp only [heteroKron]
    rw [sum_zmod_two]
    simp +decide [tauShift, Matrix.one_apply]

/-- Formalization-only spectral identity for `thm:ms-rigidity`: the positive
spectral effect of a binary observable absorbs that observable. -/
theorem reflectionEffect_zero_mul_reflection
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (Z : Op ι) (hZ : IsBinaryObservable Z) :
    reflectionEffect Z 0 * Z = reflectionEffect Z 0 := by
  simp only [reflectionEffect, if_pos, Matrix.smul_mul]
  rw [add_mul, one_mul, hZ.mul_self_eq_one]
  rw [add_comm]

/-- Formalization-only spectral identity for `thm:ms-rigidity`: the negative
spectral effect of a binary observable anti-absorbs that observable. -/
theorem reflectionEffect_one_mul_reflection
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (Z : Op ι) (hZ : IsBinaryObservable Z) :
    reflectionEffect Z 1 * Z = -reflectionEffect Z 1 := by
  simp only [reflectionEffect, if_neg one_ne_zero, Matrix.smul_mul]
  rw [sub_mul, one_mul, hZ.mul_self_eq_one]
  module

/-- Formalization-only intertwining identity for `thm:ms-rigidity`: the
controlled-swap isometry transports its controlling binary observable exactly
to the canonical phase Pauli operator on the extracted register. -/
theorem binarySwap_intertwines_Z {ι : Type} [Fintype ι] [DecidableEq ι]
    (X Z : Op ι) (hX : IsBinaryObservable X) (hZ : IsBinaryObservable Z)
    (ψ : EuclideanSpace ℂ ι) :
    binarySwapIsometry X Z hX hZ (applyOperatorToState Z ψ) =
      applyOperatorToState
        (heteroKron (tauPhase (K := ZMod 2) 1) (1 : Op ι))
        (binarySwapIsometry X Z hX hZ ψ) := by
  ext bi
  rcases bi with ⟨b, i⟩
  rw [apply_binaryTauPhase_left]
  rcases zmod_two_eq_zero_or_one b with rfl | rfl
  · simp only [binarySwapIsometry_apply, ZMod.val_zero, pow_zero, one_mul]
    rw [← MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul,
      reflectionEffect_zero_mul_reflection Z hZ]
    norm_num [bitSign]
  · simp only [binarySwapIsometry_apply, ZMod.val_one, pow_one]
    rw [← MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul, mul_assoc,
      reflectionEffect_one_mul_reflection Z hZ]
    norm_num [bitSign, ZMod.val_one, applyOperatorToState]

/-- Formalization-only spectral identity for `thm:ms-rigidity`: the difference
between the positive spectral effect of a binary observable multiplied by a
second binary observable on the right and its negative spectral effect
multiplied by that observable on the left is half the anticommutator of the
two observables. -/
theorem reflectionEffect_zero_mul_X_sub_X_mul_one
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

/-- Formalization-only spectral identity for `thm:ms-rigidity`: conjugating the
negative spectral effect of a binary observable by a second binary observable
returns the positive spectral effect up to half the anticommutator of the
two observables. -/
theorem X_mul_reflectionEffect_one_mul_X_sub_zero
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (X Z : Op ι) (hX : IsBinaryObservable X) :
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

/-- Formalization-only transport estimate for `thm:ms-rigidity`: the failure of
the controlled-swap isometry to transport `X` to the canonical shift Pauli
operator is bounded by the anticommutator defect of `X` and `Z` on the input
vector. -/
theorem norm_binarySwap_intertwines_X_sub_le {ι : Type} [Fintype ι]
    [DecidableEq ι] (X Z : Op ι) (hX : IsBinaryObservable X) (hZ : IsBinaryObservable Z)
    (ψ : EuclideanSpace ℂ ι) :
    ‖binarySwapIsometry X Z hX hZ (applyOperatorToState X ψ) -
        applyOperatorToState
          (heteroKron (tauShift (K := ZMod 2) 1) (1 : Op ι))
          (binarySwapIsometry X Z hX hZ ψ)‖ ≤
      ‖applyOperatorToState (X * Z - -(Z * X)) ψ‖ := by
  let d := applyOperatorToState (X * Z - -(Z * X)) ψ
  have apply_sub (M N : Op ι) :
      applyOperatorToState (M - N) ψ =
        applyOperatorToState M ψ - applyOperatorToState N ψ := by
    simp [applyOperatorToState]
  have hcoord0 : ∀ i : ι,
      (binarySwapIsometry X Z hX hZ (applyOperatorToState X ψ) -
          applyOperatorToState
            (heteroKron (tauShift (K := ZMod 2) 1) (1 : Op ι))
            (binarySwapIsometry X Z hX hZ ψ)) (0, i) =
        (2 : ℂ)⁻¹ * d i := by
    intro i
    rw [PiLp.sub_apply, apply_binaryTauShift_left]
    simp only [zero_add, binarySwapIsometry_apply, ZMod.val_zero, pow_zero,
      one_mul, ZMod.val_one, pow_one]
    change
      (applyOperatorToState (reflectionEffect Z 0) (applyOperatorToState X ψ) -
        applyOperatorToState (X * reflectionEffect Z 1) ψ) i = _
    rw [← MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul, ← apply_sub,
      reflectionEffect_zero_mul_X_sub_X_mul_one]
    rw [applyOperatorToState_smul]
    rfl
  have hcoord1 : ∀ i : ι,
      (binarySwapIsometry X Z hX hZ (applyOperatorToState X ψ) -
          applyOperatorToState
            (heteroKron (tauShift (K := ZMod 2) 1) (1 : Op ι))
            (binarySwapIsometry X Z hX hZ ψ)) (1, i) =
        -(2 : ℂ)⁻¹ * applyOperatorToState X d i := by
    intro i
    rw [PiLp.sub_apply, apply_binaryTauShift_left]
    have htwo : (1 : ZMod 2) + 1 = 0 := by decide
    simp only [htwo, binarySwapIsometry_apply, ZMod.val_one, pow_one,
      ZMod.val_zero, pow_zero, one_mul]
    change
      (applyOperatorToState (X * reflectionEffect Z 1)
          (applyOperatorToState X ψ) -
        applyOperatorToState (reflectionEffect Z 0) ψ) i = _
    rw [← MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul, ← apply_sub,
      X_mul_reflectionEffect_one_mul_X_sub_zero X Z hX]
    rw [applyOperatorToState_smul,
      MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul]
    rfl
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  rw [EuclideanSpace.norm_sq_eq]
  change
    ∑ bi : ZMod 2 × ι,
      ‖(binarySwapIsometry X Z hX hZ (applyOperatorToState X ψ) -
          applyOperatorToState
            (heteroKron (tauShift (K := ZMod 2) 1) (1 : Op ι))
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

/-- Formalization-only local binary observable supporting `thm:ms-rigidity`,
for Alice's variable question in the projectively dilated strategy before
tensor placement on the bipartite space. -/
noncomputable def msLocalVarObsA (S : Strategy msGame) (j : Fin 9) :
    Op (msDilatedStrategy S).ιA :=
  signObs ((msDilatedStrategy S).A (.var j)) msBitOrZero

/-- Formalization-only local binary observable supporting `thm:ms-rigidity`,
for Bob's variable question in the projectively dilated strategy before tensor
placement on the bipartite space. -/
noncomputable def msLocalVarObsB (S : Strategy msGame) (j : Fin 9) :
    Op (msDilatedStrategy S).ιB :=
  signObs ((msDilatedStrategy S).B (.var j)) msBitOrZero

/-- Formalization-only support for `thm:ms-rigidity`: Alice's dilated local
variable observable is binary. -/
theorem isBinaryObservable_msLocalVarObsA (S : Strategy msGame) (j : Fin 9) :
    IsBinaryObservable (msLocalVarObsA S j) :=
  isBinaryObservable_signObs _ (msDilatedStrategy_isProjective_A S _) _

/-- Formalization-only support for `thm:ms-rigidity`: Bob's dilated local
variable observable is binary. -/
theorem isBinaryObservable_msLocalVarObsB (S : Strategy msGame) (j : Fin 9) :
    IsBinaryObservable (msLocalVarObsB S j) :=
  isBinaryObservable_signObs _ (msDilatedStrategy_isProjective_B S _) _

/-- Formalization-only local isometry supporting `thm:ms-rigidity`: Alice's
exact binary controlled-swap embedding for the distinguished variable-0 and
variable-4 observables. -/
noncomputable def msAliceBinarySwapIsometry (S : Strategy msGame) :
    EuclideanSpace ℂ (msDilatedStrategy S).ιA →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ZMod 2 × (msDilatedStrategy S).ιA) :=
  binarySwapIsometry (msLocalVarObsA S 0) (msLocalVarObsA S 4)
    (isBinaryObservable_msLocalVarObsA S 0)
    (isBinaryObservable_msLocalVarObsA S 4)

/-- Formalization-only local isometry supporting `thm:ms-rigidity`: Bob's exact
binary controlled-swap embedding for the distinguished variable-0 and
variable-4 observables. -/
noncomputable def msBobBinarySwapIsometry (S : Strategy msGame) :
    EuclideanSpace ℂ (msDilatedStrategy S).ιB →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ZMod 2 × (msDilatedStrategy S).ιB) :=
  binarySwapIsometry (msLocalVarObsB S 0) (msLocalVarObsB S 4)
    (isBinaryObservable_msLocalVarObsB S 0)
    (isBinaryObservable_msLocalVarObsB S 4)

end

end MIPStarRE.QPBT.MagicSquareRigidity
