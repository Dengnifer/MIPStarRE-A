import MIPStarRE.QPBT.Algebra.Pauli
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Basic
import MIPStarRE.Quantum.FiniteMatrix.Order

/-!
# Perfect strategies for the Magic Square game

This file contains the state of the perfect strategy and states the
construction from two anticommuting consistent binary measurements.

## References

The source statement is `thm:ms-from-ac` in
`blueprint/src/chapter/ch13_qpbt_test.tex:257-267`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:654-722`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-- The state of the perfect strategy constructed in `thm:ms-from-ac`. -/
noncomputable def msPerfectState (ι : Type*) [Fintype ι] [DecidableEq ι]
    [Nonempty ι] : EuclideanSpace ℂ ((ι × ZMod 2) × (ι × ZMod 2)) :=
  reindexState prodShuffle (vecTensor (eprState ι) (eprState (ZMod 2)))

private theorem msPerfectState_eq_eprState
    (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    msPerfectState ι = eprState (ι × ZMod 2) := by
  apply (EuclideanSpace.equiv ((ι × ZMod 2) × (ι × ZMod 2)) ℂ).injective
  funext p
  rcases p with ⟨⟨i, b⟩, ⟨j, c⟩⟩
  by_cases hij : i = j
  · subst j
    by_cases hbc : b = c
    · subst c
      simp only [msPerfectState, reindexState, vecTensor, eprState,
        ContinuousLinearEquiv.apply_symm_apply]
      simp only [prodShuffle, Equiv.coe_fn_symm_mk, if_pos]
      change
        (Real.sqrt (Fintype.card ι : ℝ) : ℂ)⁻¹ *
            (Real.sqrt (Fintype.card (ZMod 2) : ℝ) : ℂ)⁻¹ =
          (Real.sqrt (Fintype.card (ι × ZMod 2) : ℝ) : ℂ)⁻¹
      rw [Fintype.card_prod, Nat.cast_mul, Real.sqrt_mul (by positivity)]
      push_cast
      rw [mul_inv_rev]
      ring
    · simp [msPerfectState, reindexState, vecTensor, eprState, prodShuffle, hbc]
  · simp [msPerfectState, reindexState, vecTensor, eprState, prodShuffle, hij]

private theorem reindexState_prodComm_eprState
    (V : Type*) [Fintype V] [DecidableEq V] [Nonempty V] :
    reindexState (Equiv.prodComm V V) (eprState V) = eprState V := by
  apply (EuclideanSpace.equiv (V × V) ℂ).injective
  funext p
  rcases p with ⟨i, j⟩
  simp only [reindexState, eprState, ContinuousLinearEquiv.apply_symm_apply,
    Equiv.prodComm, Equiv.coe_fn_symm_mk]
  by_cases hij : i = j
  · subst j
    simp
  · have hji : j ≠ i := fun h => hij h.symm
    simp [hij, hji]

private theorem epr_action_eq_of_transpose
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (E : Op V) (hE : Eᵀ = E) :
    (heteroKron E 1).mulVec (eprState V) =
      (heteroKron 1 E).mulVec (eprState V) := by
  ext p
  rcases p with ⟨i, j⟩
  simpa [heteroKron, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    eprState, Matrix.one_apply] using congrFun (congrFun hE j) i

private theorem transpose_eq_of_epr_action
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (E : Op V)
    (hE : (heteroKron E 1).mulVec (eprState V) =
      (heteroKron 1 E).mulVec (eprState V)) :
    Eᵀ = E := by
  ext i j
  have hij := congrFun hE (j, i)
  simp [heteroKron, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, eprState]
    at hij
  simp [Matrix.one_apply] at hij
  simp only [Matrix.transpose_apply]
  simpa using hij

private theorem sum_zmod_two {M : Type*} [AddCommMonoid M] (f : ZMod 2 → M) :
    ∑ b, f b = f 0 + f 1 := by
  calc
    ∑ b, f b = ∑ i : Fin 2, f (ZMod.finEquiv 2 i) := by
      exact Fintype.sum_equiv (ZMod.finEquiv 2).symm f
        (fun i : Fin 2 => f (ZMod.finEquiv 2 i)) (fun _ => rfl)
    _ = f (ZMod.finEquiv 2 0) + f (ZMod.finEquiv 2 1) := Fin.sum_univ_two _
    _ = f 0 + f 1 := by rfl

private theorem zmod_two_eq_zero_or_one (b : ZMod 2) : b = 0 ∨ b = 1 := by
  by_cases hb : b = 0
  · exact Or.inl hb
  · right
    have hval_ne : b.val ≠ 0 := (ZMod.val_ne_zero b).mpr hb
    have hval_lt : b.val < 2 := ZMod.val_lt b
    have hval : b.val = 1 := by omega
    exact (ZMod.val_eq_one (by omega) b).mp hval

private theorem binary_effects_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (M : Measurement (ZMod 2) V) :
    M.effect 0 + M.effect 1 = 1 := by
  rw [← sum_zmod_two M.effect]
  exact M.sum_eq_one

private theorem binary_effects_orthogonal
    {V : Type*} [Fintype V] [DecidableEq V]
    (M : Measurement (ZMod 2) V)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) :
    M.effect 0 * M.effect 1 = 0 ∧ M.effect 1 * M.effect 0 = 0 := by
  have hsum := binary_effects_sum M
  have hcomp : M.effect 1 = 1 - M.effect 0 := by
    rw [← hsum]
    abel
  constructor
  · rw [hcomp]
    exact (hM 0).mul_one_sub_self
  · rw [hcomp]
    exact (hM 0).one_sub_mul_self

private theorem obsOf_conjTranspose
    {V : Type*} [Fintype V] [DecidableEq V]
    (M : Measurement (ZMod 2) V)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) :
    (obsOf M)ᴴ = obsOf M := by
  rw [obsOf, Matrix.conjTranspose_sub,
    (hM 0).isSelfAdjoint.isHermitian.eq,
    (hM 1).isSelfAdjoint.isHermitian.eq]

private theorem obsOf_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    (M : Measurement (ZMod 2) V)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) :
    obsOf M * obsOf M = 1 := by
  rcases binary_effects_orthogonal M hM with ⟨h01, h10⟩
  calc
    obsOf M * obsOf M =
        M.effect 0 * M.effect 0 - M.effect 0 * M.effect 1 -
          M.effect 1 * M.effect 0 + M.effect 1 * M.effect 1 := by
      simp only [obsOf]
      noncomm_ring
    _ = M.effect 0 + M.effect 1 := by
      rw [(hM 0).isIdempotentElem.eq, (hM 1).isIdempotentElem.eq, h01, h10]
      abel
    _ = 1 := binary_effects_sum M

/-- The effect with eigenvalue `(-1)^b` for a Hermitian involution. -/
private noncomputable def reflectionEffect {V : Type*} [Fintype V]
    [DecidableEq V] (O : Op V) (b : ZMod 2) : Op V :=
  if b = 0 then (2 : ℂ)⁻¹ • (1 + O) else (2 : ℂ)⁻¹ • (1 - O)

private theorem reflectionEffect_isProj
    {V : Type*} [Fintype V] [DecidableEq V]
    (O : Op V) (hO : Oᴴ = O) (hO_sq : O * O = 1) (b : ZMod 2) :
    IsProj (reflectionEffect O b) := by
  have hplus : (1 + O) * (1 + O) = (2 : ℂ) • (1 + O) := by
    calc
      (1 + O) * (1 + O) = 1 + O + O + O * O := by noncomm_ring
      _ = (2 : ℂ) • (1 + O) := by rw [hO_sq]; module
  have hminus : (1 - O) * (1 - O) = (2 : ℂ) • (1 - O) := by
    calc
      (1 - O) * (1 - O) = 1 - O - O + O * O := by noncomm_ring
      _ = (2 : ℂ) • (1 - O) := by rw [hO_sq]; module
  refine isStarProjection_iff'.2 ⟨?_, ?_⟩
  · rcases zmod_two_eq_zero_or_one b with rfl | rfl
    · simp only [reflectionEffect, if_pos]
      rw [smul_mul_smul, hplus, smul_smul]
      norm_num
    · simp only [reflectionEffect, if_neg one_ne_zero]
      rw [smul_mul_smul, hminus, smul_smul]
      norm_num
  · rcases zmod_two_eq_zero_or_one b with rfl | rfl
    · simp [reflectionEffect, Matrix.star_eq_conjTranspose, hO]
    · simp [reflectionEffect, Matrix.star_eq_conjTranspose, hO]

/-- The binary projective measurement associated with a Hermitian involution. -/
private noncomputable def reflectionMeasurement
    {V : Type*} [Fintype V] [DecidableEq V]
    (O : Op V) (hO : Oᴴ = O) (hO_sq : O * O = 1) :
    Measurement (ZMod 2) V :=
  Measurement.ofSumEqOne (reflectionEffect O)
    (fun b => (reflectionEffect_isProj O hO hO_sq b).nonneg)
    (by
      rw [sum_zmod_two]
      simp [reflectionEffect]
      module)

private theorem reflectionMeasurement_projective
    {V : Type*} [Fintype V] [DecidableEq V]
    (O : Op V) (hO : Oᴴ = O) (hO_sq : O * O = 1) :
    MIPStarRE.QPBT.Measurement.IsProjective
      (reflectionMeasurement O hO hO_sq) :=
  reflectionEffect_isProj O hO hO_sq

private theorem reflectionEffect_obsOf
    {V : Type*} [Fintype V] [DecidableEq V]
    (O : Op V) (hO : Oᴴ = O) (hO_sq : O * O = 1) :
    obsOf (reflectionMeasurement O hO hO_sq) = O := by
  change reflectionEffect O 0 - reflectionEffect O 1 = O
  simp only [reflectionEffect, if_pos, if_neg one_ne_zero]
  norm_num
  module

private theorem reflectionEffect_obsOf_measurement
    {V : Type*} [Fintype V] [DecidableEq V]
    (M : Measurement (ZMod 2) V) (b : ZMod 2) :
    reflectionEffect (obsOf M) b = M.effect b := by
  have hsum := binary_effects_sum M
  rcases zmod_two_eq_zero_or_one b with rfl | rfl
  · simp only [reflectionEffect, if_pos, obsOf]
    rw [show (1 : Op V) = M.effect 0 + M.effect 1 from hsum.symm]
    module
  · simp only [reflectionEffect, if_neg one_ne_zero, obsOf]
    rw [show (1 : Op V) = M.effect 0 + M.effect 1 from hsum.symm]
    module

/-- The real Pauli `X` matrix on the binary register. -/
private def qubitX : Op (ZMod 2) :=
  fun i j => if i = j then 0 else 1

/-- The real Pauli `Z` matrix on the binary register. -/
private def qubitZ : Op (ZMod 2) :=
  fun i j => if i = j then if i = 0 then 1 else -1 else 0

private theorem qubitX_conjTranspose : qubitXᴴ = qubitX := by
  ext i j
  rcases zmod_two_eq_zero_or_one i with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one j with rfl | rfl <;>
      norm_num [qubitX, Matrix.conjTranspose_apply]

private theorem qubitZ_conjTranspose : qubitZᴴ = qubitZ := by
  ext i j
  rcases zmod_two_eq_zero_or_one i with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one j with rfl | rfl <;>
      norm_num [qubitZ, Matrix.conjTranspose_apply]

private theorem qubitX_transpose : qubitXᵀ = qubitX := by
  ext i j
  rcases zmod_two_eq_zero_or_one i with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one j with rfl | rfl <;>
      norm_num [qubitX, Matrix.transpose_apply]

private theorem qubitZ_transpose : qubitZᵀ = qubitZ := by
  ext i j
  rcases zmod_two_eq_zero_or_one i with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one j with rfl | rfl <;>
      norm_num [qubitZ, Matrix.transpose_apply]

private theorem qubitX_sq : qubitX * qubitX = 1 := by
  ext i j
  simp only [Matrix.mul_apply]
  rw [sum_zmod_two]
  rcases zmod_two_eq_zero_or_one i with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one j with rfl | rfl <;>
      norm_num [qubitX, Matrix.one_apply]

private theorem qubitZ_sq : qubitZ * qubitZ = 1 := by
  ext i j
  simp only [Matrix.mul_apply]
  rw [sum_zmod_two]
  rcases zmod_two_eq_zero_or_one i with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one j with rfl | rfl <;>
      norm_num [qubitZ, Matrix.one_apply]

private theorem qubitX_mul_qubitZ : qubitX * qubitZ = -(qubitZ * qubitX) := by
  ext i j
  change (∑ k, qubitX i k * qubitZ k j) = -(∑ k, qubitZ i k * qubitX k j)
  rw [sum_zmod_two, sum_zmod_two]
  rcases zmod_two_eq_zero_or_one i with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one j with rfl | rfl <;>
      norm_num [qubitX, qubitZ]

private theorem heteroKron_mul
    {V W : Type*} [Fintype V] [Fintype W]
    (A B : Op V) (C D : Op W) :
    heteroKron A C * heteroKron B D = heteroKron (A * B) (C * D) := by
  exact (Matrix.mul_kronecker_mul A B C D).symm

private theorem heteroKron_conjTranspose
    {V W : Type*} (A : Op V) (B : Op W) :
    (heteroKron A B)ᴴ = heteroKron Aᴴ Bᴴ := by
  exact Matrix.conjTranspose_kronecker A B

private theorem heteroKron_transpose
    {V W : Type*} (A : Op V) (B : Op W) :
    (heteroKron A B)ᵀ = heteroKron Aᵀ Bᵀ := by
  ext i j
  rfl

private theorem heteroKron_neg_neg
    {V W : Type*} (A : Op V) (B : Op W) :
    heteroKron (-A) (-B) = heteroKron A B := by
  ext i j
  simp [heteroKron]

private theorem heteroKron_neg_left
    {V W : Type*} (A : Op V) (B : Op W) :
    heteroKron (-A) B = -heteroKron A B := by
  ext i j
  simp [heteroKron]

private theorem heteroKron_neg_right
    {V W : Type*} (A : Op V) (B : Op W) :
    heteroKron A (-B) = -heteroKron A B := by
  ext i j
  simp [heteroKron]

private theorem heteroKron_one_one
    {V W : Type*} [DecidableEq V] [DecidableEq W] :
    heteroKron (1 : Op V) (1 : Op W) = 1 := by
  exact Matrix.one_kronecker_one

private theorem anti_mul_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    (A B : Op V) (hA : A * A = 1) (hB : B * B = 1)
    (hAB : A * B = -(B * A)) :
    (A * B) * (A * B) = -1 := by
  have hBA : B * A = -(A * B) := by
    rw [hAB]
    simp
  calc
    (A * B) * (A * B) = A * (B * A) * B := by noncomm_ring
    _ = -(A * A) * (B * B) := by rw [hBA]; noncomm_ring
    _ = -1 := by rw [hA, hB]; simp

private theorem anti_mul_conjTranspose
    {V : Type*} [Fintype V]
    (A B : Op V) (hA : Aᴴ = A) (hB : Bᴴ = B)
    (hAB : A * B = -(B * A)) :
    (A * B)ᴴ = -(A * B) := by
  rw [Matrix.conjTranspose_mul, hA, hB]
  rw [hAB]
  simp

private theorem anti_mul_transpose
    {V : Type*} [Fintype V]
    (A B : Op V) (hA : Aᵀ = A) (hB : Bᵀ = B)
    (hAB : A * B = -(B * A)) :
    (A * B)ᵀ = -(A * B) := by
  rw [Matrix.transpose_mul, hA, hB]
  rw [hAB]
  simp

/-- The nine observables in the operator table of `thm:ms-from-ac`. -/
private def msCellObservable
    {V : Type*} [Fintype V] [DecidableEq V]
    (OA OB : Op V) : Fin 9 → Op (V × ZMod 2) :=
  ![heteroKron OA 1, heteroKron 1 qubitX, heteroKron OA qubitX,
    heteroKron 1 qubitZ, heteroKron OB 1, heteroKron OB qubitZ,
    heteroKron OA qubitZ, heteroKron OB qubitX,
    heteroKron (OA * OB) (qubitZ * qubitX)]

private theorem msCellObservable_conjTranspose
    {V : Type*} [Fintype V] [DecidableEq V]
    (OA OB : Op V) (hOA : OAᴴ = OA) (hOB : OBᴴ = OB)
    (hac : OA * OB = -(OB * OA)) (j : Fin 9) :
    (msCellObservable OA OB j)ᴴ = msCellObservable OA OB j := by
  have hAB := anti_mul_conjTranspose OA OB hOA hOB hac
  have hZX := anti_mul_conjTranspose qubitZ qubitX qubitZ_conjTranspose
    qubitX_conjTranspose (by
      rw [qubitX_mul_qubitZ]
      simp)
  fin_cases j <;>
    simp [msCellObservable, heteroKron_conjTranspose, hOA, hOB,
      qubitX_conjTranspose, qubitZ_conjTranspose, hAB, hZX,
      heteroKron_neg_neg]

private theorem msCellObservable_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    (OA OB : Op V) (hOA : OA * OA = 1) (hOB : OB * OB = 1)
    (hac : OA * OB = -(OB * OA)) (j : Fin 9) :
    msCellObservable OA OB j * msCellObservable OA OB j = 1 := by
  have hAB := anti_mul_sq OA OB hOA hOB hac
  have hZX := anti_mul_sq qubitZ qubitX qubitZ_sq qubitX_sq (by
    rw [qubitX_mul_qubitZ]
    simp)
  fin_cases j <;>
    simp [msCellObservable, heteroKron_mul, hOA, hOB, qubitX_sq,
      qubitZ_sq, hAB, hZX, heteroKron_neg_neg, heteroKron_one_one]

private theorem msCellObservable_transpose
    {V : Type*} [Fintype V] [DecidableEq V]
    (OA OB : Op V) (hOA : OAᵀ = OA) (hOB : OBᵀ = OB)
    (hac : OA * OB = -(OB * OA)) (j : Fin 9) :
    (msCellObservable OA OB j)ᵀ = msCellObservable OA OB j := by
  have hAB := anti_mul_transpose OA OB hOA hOB hac
  have hZX := anti_mul_transpose qubitZ qubitX qubitZ_transpose
    qubitX_transpose (by
      rw [qubitX_mul_qubitZ]
      simp)
  fin_cases j <;>
    simp [msCellObservable, heteroKron_transpose, hOA, hOB,
      qubitX_transpose, qubitZ_transpose, hAB, hZX,
      heteroKron_neg_neg]

private theorem msConstraintObservable_commute
    {V : Type*} [Fintype V] [DecidableEq V]
    (OA OB : Op V) (hOA : OA * OA = 1) (hOB : OB * OB = 1)
    (hac : OA * OB = -(OB * OA)) (i : Fin 6) (k l : Fin 3) :
    Commute (msCellObservable OA OB (msConstraintVars i k))
      (msCellObservable OA OB (msConstraintVars i l)) := by
  have hA_BA : OA * (OB * OA) = -OB := by
    calc
      OA * (OB * OA) = (OA * OB) * OA := (mul_assoc _ _ _).symm
      _ = (-(OB * OA)) * OA := by rw [hac]
      _ = -OB := by rw [neg_mul, mul_assoc, hOA, mul_one]
  have hBA_A : OB * OA * OA = OB := by rw [mul_assoc, hOA, mul_one]
  have hB_BA : OB * (OB * OA) = OA := by rw [← mul_assoc, hOB, one_mul]
  have hBA_B : OB * OA * OB = -OA := by
    calc
      OB * OA * OB = OB * (OA * OB) := mul_assoc _ _ _
      _ = OB * (-(OB * OA)) := by rw [hac]
      _ = -OA := by rw [mul_neg, ← mul_assoc, hOB, one_mul]
  have hZ_ZX : qubitZ * (qubitZ * qubitX) = qubitX := by
    rw [← mul_assoc, qubitZ_sq, one_mul]
  have hZX_Z : qubitZ * qubitX * qubitZ = -qubitX := by
    calc
      qubitZ * qubitX * qubitZ = -(qubitX * qubitZ) * qubitZ := by
        rw [show qubitZ * qubitX = -(qubitX * qubitZ) by
          rw [qubitX_mul_qubitZ]
          simp]
      _ = -qubitX := by rw [neg_mul, mul_assoc, qubitZ_sq, mul_one]
  have hX_ZX : qubitX * (qubitZ * qubitX) = -qubitZ := by
    calc
      qubitX * (qubitZ * qubitX) = (qubitX * qubitZ) * qubitX :=
        (mul_assoc _ _ _).symm
      _ = (-(qubitZ * qubitX)) * qubitX := by rw [qubitX_mul_qubitZ]
      _ = -qubitZ := by rw [neg_mul, mul_assoc, qubitX_sq, mul_one]
  have hZX_X : qubitZ * qubitX * qubitX = qubitZ := by
    rw [mul_assoc, qubitX_sq, mul_one]
  fin_cases i <;> fin_cases k <;> fin_cases l <;>
    simp [commute_iff_eq, msConstraintVars, msCellObservable,
      heteroKron_mul, hOA, hOB, hac, qubitX_sq, qubitZ_sq,
      qubitX_mul_qubitZ, hA_BA, hBA_A, hB_BA, hBA_B, hZ_ZX,
      hZX_Z, hX_ZX, hZX_X, heteroKron_neg_left,
      heteroKron_neg_right]

private theorem msConstraintObservable_product
    {V : Type*} [Fintype V] [DecidableEq V]
    (OA OB : Op V) (hOA : OA * OA = 1) (hOB : OB * OB = 1)
    (hac : OA * OB = -(OB * OA)) (i : Fin 6) :
    msCellObservable OA OB (msConstraintVars i 0) *
        msCellObservable OA OB (msConstraintVars i 1) *
    msCellObservable OA OB (msConstraintVars i 2) =
      if i = 5 then -1 else 1 := by
  have hAB := anti_mul_sq OA OB hOA hOB hac
  have hZX := anti_mul_sq qubitZ qubitX qubitZ_sq qubitX_sq (by
    rw [qubitX_mul_qubitZ]
    simp)
  fin_cases i <;>
    simp [msConstraintVars, msCellObservable, heteroKron_mul, hOA, hOB,
      qubitX_sq, qubitZ_sq, qubitX_mul_qubitZ, hAB, hZX,
      heteroKron_neg_left, heteroKron_neg_right,
      heteroKron_one_one]

private theorem binary_effect_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    (M : Measurement (ZMod 2) V)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M)
    (a b : ZMod 2) :
    M.effect a * M.effect b = if a = b then M.effect a else 0 := by
  rcases binary_effects_orthogonal M hM with ⟨h01, h10⟩
  rcases zmod_two_eq_zero_or_one a with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one b with rfl | rfl <;>
      simp [(hM _).isIdempotentElem.eq, h01, h10]

private theorem reflectionEffect_commute
    {V : Type*} [Fintype V] [DecidableEq V]
    {O P : Op V} (hOP : Commute O P) (a b : ZMod 2) :
    Commute (reflectionEffect O a) (reflectionEffect P b) := by
  rw [commute_iff_eq]
  rcases zmod_two_eq_zero_or_one a with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one b with rfl | rfl <;>
      simp only [reflectionEffect, if_pos, if_neg one_ne_zero]
  all_goals rw [smul_mul_smul, smul_mul_smul]
  all_goals congr 1
  all_goals noncomm_ring [hOP.eq]

private theorem reflectionEffect_commute_obs
    {V : Type*} [Fintype V] [DecidableEq V]
    {O P : Op V} (hOP : Commute O P) (a : ZMod 2) :
    Commute (reflectionEffect O a) P := by
  rw [commute_iff_eq]
  rcases zmod_two_eq_zero_or_one a with rfl | rfl <;>
    simp only [reflectionEffect, if_pos, if_neg one_ne_zero]
  all_goals rw [smul_mul_assoc, mul_smul_comm]
  all_goals congr 1
  all_goals noncomm_ring [hOP.eq]

private theorem reflectionEffect_mul_obs_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (O : Op V) (hO : O * O = 1) :
    reflectionEffect O 0 * O = reflectionEffect O 0 := by
  simp only [reflectionEffect, if_pos]
  rw [smul_mul_assoc, add_mul, one_mul, hO]
  module

private theorem reflectionEffect_mul_obs_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (O : Op V) (hO : O * O = 1) :
    reflectionEffect O 1 * O = -reflectionEffect O 1 := by
  simp only [reflectionEffect, if_neg one_ne_zero]
  rw [smul_mul_assoc, sub_mul, one_mul, hO]
  module

private theorem mul_reflectionEffect_zero_of_eigen_pos
    {V : Type*} [Fintype V] [DecidableEq V]
    (E O : Op V) (hEO : E * O = E) :
    E * reflectionEffect O 0 = E := by
  simp only [reflectionEffect, if_pos]
  rw [mul_smul_comm, mul_add, mul_one, hEO]
  module

private theorem mul_reflectionEffect_one_of_eigen_neg
    {V : Type*} [Fintype V] [DecidableEq V]
    (E O : Op V) (hEO : E * O = -E) :
    E * reflectionEffect O 1 = E := by
  simp only [reflectionEffect, if_neg one_ne_zero]
  rw [mul_smul_comm, mul_sub, mul_one, hEO]
  module

private theorem reflection_pair_mul_observables
    {V : Type*} [Fintype V]
    (P0 P1 O0 O1 : Op V) (s0 s1 : ℂ)
    (h10 : Commute P1 O0)
    (h0 : P0 * O0 = s0 • P0) (h1 : P1 * O1 = s1 • P1) :
    (P0 * P1) * (O0 * O1) = (s0 * s1) • (P0 * P1) := by
  calc
    (P0 * P1) * (O0 * O1) = P0 * (P1 * O0) * O1 := by noncomm_ring
    _ = P0 * (O0 * P1) * O1 := by rw [h10.eq]
    _ = (P0 * O0) * (P1 * O1) := by noncomm_ring
    _ = (s0 • P0) * (s1 • P1) := by rw [h0, h1]
    _ = (s0 * s1) • (P0 * P1) := by rw [smul_mul_smul]

private theorem reflection_pair_absorbs_parity_effect
    {V : Type*} [Fintype V] [DecidableEq V]
    (O0 O1 O2 : Op V)
    (hO0 : O0 * O0 = 1) (hO1 : O1 * O1 = 1)
    (h01 : Commute O0 O1)
    (p b0 b1 : ZMod 2)
    (hp : (p = 0 ∧ O0 * O1 * O2 = 1) ∨
      (p = 1 ∧ O0 * O1 * O2 = -1)) :
    (reflectionEffect O0 b0 * reflectionEffect O1 b1) *
        reflectionEffect O2 (p - b0 - b1) =
      reflectionEffect O0 b0 * reflectionEffect O1 b1 := by
  rcases hp with ⟨rfl, hprod⟩ | ⟨rfl, hprod⟩
  · have hO2eq : O2 = O0 * O1 := by
      calc
        O2 = (O0 * O0) * (O1 * O1) * O2 := by rw [hO0, hO1]; simp
        _ = O0 * (O0 * O1) * O1 * O2 := by noncomm_ring
        _ = O0 * (O1 * O0) * O1 * O2 := by rw [h01.eq]
        _ = O0 * O1 * (O0 * O1 * O2) := by noncomm_ring
        _ = O0 * O1 := by rw [hprod]; simp
    rcases zmod_two_eq_zero_or_one b0 with rfl | rfl <;>
      rcases zmod_two_eq_zero_or_one b1 with rfl | rfl
    · apply mul_reflectionEffect_zero_of_eigen_pos
      rw [hO2eq]
      simpa using reflection_pair_mul_observables
        (reflectionEffect O0 0) (reflectionEffect O1 0) O0 O1 1 1
        (reflectionEffect_commute_obs h01.symm 0)
        (by simpa using reflectionEffect_mul_obs_zero O0 hO0)
        (by simpa using reflectionEffect_mul_obs_zero O1 hO1)
    · apply mul_reflectionEffect_one_of_eigen_neg
      rw [hO2eq]
      simpa using reflection_pair_mul_observables
        (reflectionEffect O0 0) (reflectionEffect O1 1) O0 O1 1 (-1)
        (reflectionEffect_commute_obs h01.symm 1)
        (by simpa using reflectionEffect_mul_obs_zero O0 hO0)
        (by simpa using reflectionEffect_mul_obs_one O1 hO1)
    · apply mul_reflectionEffect_one_of_eigen_neg
      rw [hO2eq]
      simpa using reflection_pair_mul_observables
        (reflectionEffect O0 1) (reflectionEffect O1 0) O0 O1 (-1) 1
        (reflectionEffect_commute_obs h01.symm 0)
        (by simpa using reflectionEffect_mul_obs_one O0 hO0)
        (by simpa using reflectionEffect_mul_obs_zero O1 hO1)
    · apply mul_reflectionEffect_zero_of_eigen_pos
      rw [hO2eq]
      simpa using reflection_pair_mul_observables
        (reflectionEffect O0 1) (reflectionEffect O1 1) O0 O1 (-1) (-1)
        (reflectionEffect_commute_obs h01.symm 1)
        (by simpa using reflectionEffect_mul_obs_one O0 hO0)
        (by simpa using reflectionEffect_mul_obs_one O1 hO1)
  · have hO2eq : O2 = -(O0 * O1) := by
      calc
        O2 = (O0 * O0) * (O1 * O1) * O2 := by rw [hO0, hO1]; simp
        _ = O0 * (O0 * O1) * O1 * O2 := by noncomm_ring
        _ = O0 * (O1 * O0) * O1 * O2 := by rw [h01.eq]
        _ = O0 * O1 * (O0 * O1 * O2) := by noncomm_ring
        _ = -(O0 * O1) := by rw [hprod]; simp
    rcases zmod_two_eq_zero_or_one b0 with rfl | rfl <;>
      rcases zmod_two_eq_zero_or_one b1 with rfl | rfl
    · apply mul_reflectionEffect_one_of_eigen_neg
      rw [hO2eq, mul_neg]
      have hpair := reflection_pair_mul_observables
        (reflectionEffect O0 0) (reflectionEffect O1 0) O0 O1 1 1
        (reflectionEffect_commute_obs h01.symm 0)
        (by simpa using reflectionEffect_mul_obs_zero O0 hO0)
        (by simpa using reflectionEffect_mul_obs_zero O1 hO1)
      rw [hpair]
      simp
    · apply mul_reflectionEffect_zero_of_eigen_pos
      rw [hO2eq, mul_neg]
      have hpair := reflection_pair_mul_observables
        (reflectionEffect O0 0) (reflectionEffect O1 1) O0 O1 1 (-1)
        (reflectionEffect_commute_obs h01.symm 1)
        (by simpa using reflectionEffect_mul_obs_zero O0 hO0)
        (by simpa using reflectionEffect_mul_obs_one O1 hO1)
      rw [hpair]
      simp
    · apply mul_reflectionEffect_zero_of_eigen_pos
      rw [hO2eq, mul_neg]
      have hpair := reflection_pair_mul_observables
        (reflectionEffect O0 1) (reflectionEffect O1 0) O0 O1 (-1) 1
        (reflectionEffect_commute_obs h01.symm 0)
        (by simpa using reflectionEffect_mul_obs_one O0 hO0)
        (by simpa using reflectionEffect_mul_obs_zero O1 hO1)
      rw [hpair]
      simp
    · apply mul_reflectionEffect_one_of_eigen_neg
      rw [hO2eq, mul_neg]
      have hpair := reflection_pair_mul_observables
        (reflectionEffect O0 1) (reflectionEffect O1 1) O0 O1 (-1) (-1)
        (reflectionEffect_commute_obs h01.symm 1)
        (by simpa using reflectionEffect_mul_obs_one O0 hO0)
        (by simpa using reflectionEffect_mul_obs_one O1 hO1)
      rw [hpair]
      simp

/-- The joint measurement of two commuting binary projective measurements. -/
private noncomputable def binaryJointMeasurement
    {V : Type*} [Fintype V] [DecidableEq V]
    (M N : Measurement (ZMod 2) V)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M)
    (hN : MIPStarRE.QPBT.Measurement.IsProjective N)
    (hcomm : ∀ a b, Commute (M.effect a) (N.effect b)) :
    Measurement (ZMod 2 × ZMod 2) V :=
  Measurement.ofSumEqOne
    (fun ab => M.effect ab.1 * N.effect ab.2)
    (fun ab => (hM ab.1).mul (hN ab.2) (hcomm ab.1 ab.2) |>.nonneg)
    (by
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum]
      rw [N.sum_eq_one]
      simp [M.sum_eq_one])

private theorem binaryJointMeasurement_projective
    {V : Type*} [Fintype V] [DecidableEq V]
    (M N : Measurement (ZMod 2) V)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M)
    (hN : MIPStarRE.QPBT.Measurement.IsProjective N)
    (hcomm : ∀ a b, Commute (M.effect a) (N.effect b)) :
    MIPStarRE.QPBT.Measurement.IsProjective
      (binaryJointMeasurement M N hM hN hcomm) :=
  fun ab => (hM ab.1).mul (hN ab.2) (hcomm ab.1 ab.2)

private theorem binaryJointMeasurement_mul_first
    {V : Type*} [Fintype V] [DecidableEq V]
    (M N : Measurement (ZMod 2) V)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M)
    (hN : MIPStarRE.QPBT.Measurement.IsProjective N)
    (hcomm : ∀ a b, Commute (M.effect a) (N.effect b))
    (ab : ZMod 2 × ZMod 2) (b : ZMod 2) :
    (binaryJointMeasurement M N hM hN hcomm).effect ab * M.effect b =
      if ab.1 = b then
        (binaryJointMeasurement M N hM hN hcomm).effect ab else 0 := by
  change (M.effect ab.1 * N.effect ab.2) * M.effect b =
    if ab.1 = b then M.effect ab.1 * N.effect ab.2 else 0
  calc
    (M.effect ab.1 * N.effect ab.2) * M.effect b =
        M.effect ab.1 * (N.effect ab.2 * M.effect b) := mul_assoc _ _ _
    _ = M.effect ab.1 * (M.effect b * N.effect ab.2) := by
      rw [(hcomm b ab.2).symm.eq]
    _ = (M.effect ab.1 * M.effect b) * N.effect ab.2 :=
      (mul_assoc _ _ _).symm
    _ = _ := by
      rw [binary_effect_mul M hM]
      by_cases h : ab.1 = b
      · simp only [if_pos h]
      · simp only [if_neg h, zero_mul]

private theorem binaryJointMeasurement_mul_second
    {V : Type*} [Fintype V] [DecidableEq V]
    (M N : Measurement (ZMod 2) V)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M)
    (hN : MIPStarRE.QPBT.Measurement.IsProjective N)
    (hcomm : ∀ a b, Commute (M.effect a) (N.effect b))
    (ab : ZMod 2 × ZMod 2) (b : ZMod 2) :
    (binaryJointMeasurement M N hM hN hcomm).effect ab * N.effect b =
      if ab.2 = b then
        (binaryJointMeasurement M N hM hN hcomm).effect ab else 0 := by
  change (M.effect ab.1 * N.effect ab.2) * N.effect b =
    if ab.2 = b then M.effect ab.1 * N.effect ab.2 else 0
  rw [mul_assoc, binary_effect_mul N hN]
  by_cases h : ab.2 = b
  · simp only [if_pos h]
  · simp only [if_neg h, mul_zero]

private theorem postprocess_effect_of_injective
    {α β V : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [Fintype V] [DecidableEq V]
    (M : Measurement α V) (f : α → β) (hf : Function.Injective f) (a : α) :
    (M.postprocess f).effect (f a) = M.effect a := by
  simp only [Measurement.postprocess_effect, Finset.sum_filter]
  rw [Fintype.sum_eq_single a]
  · simp
  · intro b hba
    have hfb : f b ≠ f a := fun h => hba (hf h)
    simp [hfb]

private theorem postprocess_effect_eq_zero_of_notMem
    {α β V : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [Fintype V] [DecidableEq V]
    (M : Measurement α V) (f : α → β) {b : β}
    (hb : b ∉ Set.range f) :
    (M.postprocess f).effect b = 0 := by
  rw [Measurement.postprocess_effect]
  apply Finset.sum_eq_zero
  intro a ha
  exact (hb ⟨a, (Finset.mem_filter.mp ha).2⟩).elim

private theorem postprocess_projective_of_injective
    {α β V : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [Fintype V] [DecidableEq V]
    (M : Measurement α V) (hM : MIPStarRE.QPBT.Measurement.IsProjective M)
    (f : α → β) (hf : Function.Injective f) :
    MIPStarRE.QPBT.Measurement.IsProjective (M.postprocess f) := by
  intro b
  by_cases hb : b ∈ Set.range f
  · rcases hb with ⟨a, rfl⟩
    rw [postprocess_effect_of_injective M f hf a]
    exact hM a
  · rw [postprocess_effect_eq_zero_of_notMem M f hb]
    exact IsStarProjection.zero _

/-- Encode two freely chosen bits as the unique triple of the prescribed parity. -/
private def parityTriple (i : Fin 6) (ab : ZMod 2 × ZMod 2) : Fin 3 → ZMod 2 :=
  ![ab.1, ab.2, msParity i - ab.1 - ab.2]

private theorem parityTriple_injective (i : Fin 6) :
    Function.Injective (parityTriple i) := by
  intro ab cd h
  apply Prod.ext
  · exact congrFun h 0
  · exact congrFun h 1

private theorem parityTriple_sum (i : Fin 6) (ab : ZMod 2 × ZMod 2) :
    ∑ k : Fin 3, parityTriple i ab k = msParity i := by
  rw [Fin.sum_univ_three]
  simp [parityTriple]

private theorem bit_embedding_injective :
    Function.Injective (MsAnswer.bit : ZMod 2 → MsAnswer) := by
  intro a b h
  exact MsAnswer.bit.inj h

private theorem triple_embedding_injective (i : Fin 6) :
    Function.Injective (fun ab => MsAnswer.triple (parityTriple i ab)) := by
  intro ab cd h
  apply parityTriple_injective i
  exact MsAnswer.triple.inj h

/-- The binary measurement associated with a cell of the operator table. -/
private noncomputable def msCellMeasurement
    {V : Type*} [Fintype V] [DecidableEq V]
    (OA OB : Op V) (hOA : OAᴴ = OA) (hOB : OBᴴ = OB)
    (hOA_sq : OA * OA = 1) (hOB_sq : OB * OB = 1)
    (hac : OA * OB = -(OB * OA)) (j : Fin 9) :
    Measurement (ZMod 2) (V × ZMod 2) :=
  reflectionMeasurement (msCellObservable OA OB j)
    (msCellObservable_conjTranspose OA OB hOA hOB hac j)
    (msCellObservable_sq OA OB hOA_sq hOB_sq hac j)

@[simp]
private theorem msCellMeasurement_effect
    {V : Type*} [Fintype V] [DecidableEq V]
    (OA OB : Op V) (hOA : OAᴴ = OA) (hOB : OBᴴ = OB)
    (hOA_sq : OA * OA = 1) (hOB_sq : OB * OB = 1)
    (hac : OA * OB = -(OB * OA)) (j : Fin 9) (b : ZMod 2) :
    (msCellMeasurement OA OB hOA hOB hOA_sq hOB_sq hac j).effect b =
      reflectionEffect (msCellObservable OA OB j) b :=
  rfl

private theorem msCellMeasurement_projective
    {V : Type*} [Fintype V] [DecidableEq V]
    (OA OB : Op V) (hOA : OAᴴ = OA) (hOB : OBᴴ = OB)
    (hOA_sq : OA * OA = 1) (hOB_sq : OB * OB = 1)
    (hac : OA * OB = -(OB * OA)) (j : Fin 9) :
    MIPStarRE.QPBT.Measurement.IsProjective
      (msCellMeasurement OA OB hOA hOB hOA_sq hOB_sq hac j) :=
  reflectionMeasurement_projective (msCellObservable OA OB j)
    (msCellObservable_conjTranspose OA OB hOA hOB hac j)
    (msCellObservable_sq OA OB hOA_sq hOB_sq hac j)

private theorem reflectionEffect_transpose
    {V : Type*} [Fintype V] [DecidableEq V]
    (O : Op V) (hO : Oᵀ = O) (b : ZMod 2) :
    (reflectionEffect O b)ᵀ = reflectionEffect O b := by
  rcases zmod_two_eq_zero_or_one b with rfl | rfl <;>
    simp [reflectionEffect, Matrix.transpose_add, Matrix.transpose_sub, hO]

private theorem msCellMeasurement_transpose
    {V : Type*} [Fintype V] [DecidableEq V]
    (OA OB : Op V) (hOA : OAᴴ = OA) (hOB : OBᴴ = OB)
    (hOA_sq : OA * OA = 1) (hOB_sq : OB * OB = 1)
    (hOA_t : OAᵀ = OA) (hOB_t : OBᵀ = OB)
    (hac : OA * OB = -(OB * OA)) (j : Fin 9) (b : ZMod 2) :
    ((msCellMeasurement OA OB hOA hOB hOA_sq hOB_sq hac j).effect b)ᵀ =
      (msCellMeasurement OA OB hOA hOB hOA_sq hOB_sq hac j).effect b := by
  rw [msCellMeasurement_effect]
  exact reflectionEffect_transpose _
    (msCellObservable_transpose OA OB hOA_t hOB_t hac j) b

/-- The joint measurement of the first two cells in a Magic Square constraint. -/
private noncomputable def msConstraintJoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin 9 → Measurement (ZMod 2) V)
    (hP : ∀ j, MIPStarRE.QPBT.Measurement.IsProjective (P j))
    (hcomm : ∀ i k l a b,
      Commute ((P (msConstraintVars i k)).effect a)
        ((P (msConstraintVars i l)).effect b))
    (i : Fin 6) : Measurement (ZMod 2 × ZMod 2) V :=
  binaryJointMeasurement (P (msConstraintVars i 0))
    (P (msConstraintVars i 1)) (hP _) (hP _) (hcomm i 0 1)

/-- The global Magic Square measurement family induced by the nine cell measurements. -/
private noncomputable def msStrategyMeasurement
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin 9 → Measurement (ZMod 2) V)
    (hP : ∀ j, MIPStarRE.QPBT.Measurement.IsProjective (P j))
    (hcomm : ∀ i k l a b,
      Commute ((P (msConstraintVars i k)).effect a)
        ((P (msConstraintVars i l)).effect b)) :
    MsType → Measurement MsAnswer V
  | .var j => (P j).postprocess MsAnswer.bit
  | .constraint i =>
      (msConstraintJoint P hP hcomm i).postprocess
        (fun ab => .triple (parityTriple i ab))

private theorem msStrategyMeasurement_var_bit
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin 9 → Measurement (ZMod 2) V)
    (hP : ∀ j, MIPStarRE.QPBT.Measurement.IsProjective (P j))
    (hcomm : ∀ i k l a b,
      Commute ((P (msConstraintVars i k)).effect a)
        ((P (msConstraintVars i l)).effect b))
    (j : Fin 9) (b : ZMod 2) :
    (msStrategyMeasurement P hP hcomm (.var j)).effect (.bit b) =
      (P j).effect b := by
  exact postprocess_effect_of_injective (P j) MsAnswer.bit
    bit_embedding_injective b

private theorem msStrategyMeasurement_var_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin 9 → Measurement (ZMod 2) V)
    (hP : ∀ j, MIPStarRE.QPBT.Measurement.IsProjective (P j))
    (hcomm : ∀ i k l a b,
      Commute ((P (msConstraintVars i k)).effect a)
        ((P (msConstraintVars i l)).effect b))
    (j : Fin 9) {a : MsAnswer}
    (ha : a ∉ Set.range (MsAnswer.bit : ZMod 2 → MsAnswer)) :
    (msStrategyMeasurement P hP hcomm (.var j)).effect a = 0 := by
  exact postprocess_effect_eq_zero_of_notMem (P j) MsAnswer.bit ha

private theorem msStrategyMeasurement_constraint_triple
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin 9 → Measurement (ZMod 2) V)
    (hP : ∀ j, MIPStarRE.QPBT.Measurement.IsProjective (P j))
    (hcomm : ∀ i k l a b,
      Commute ((P (msConstraintVars i k)).effect a)
        ((P (msConstraintVars i l)).effect b))
    (i : Fin 6) (ab : ZMod 2 × ZMod 2) :
    (msStrategyMeasurement P hP hcomm (.constraint i)).effect
        (.triple (parityTriple i ab)) =
      (msConstraintJoint P hP hcomm i).effect ab := by
  exact postprocess_effect_of_injective (msConstraintJoint P hP hcomm i)
    (fun cd => MsAnswer.triple (parityTriple i cd))
    (triple_embedding_injective i) ab

private theorem msStrategyMeasurement_constraint_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin 9 → Measurement (ZMod 2) V)
    (hP : ∀ j, MIPStarRE.QPBT.Measurement.IsProjective (P j))
    (hcomm : ∀ i k l a b,
      Commute ((P (msConstraintVars i k)).effect a)
        ((P (msConstraintVars i l)).effect b))
    (i : Fin 6) {a : MsAnswer}
    (ha : a ∉ Set.range (fun ab => MsAnswer.triple (parityTriple i ab))) :
    (msStrategyMeasurement P hP hcomm (.constraint i)).effect a = 0 := by
  exact postprocess_effect_eq_zero_of_notMem (msConstraintJoint P hP hcomm i)
    (fun ab => MsAnswer.triple (parityTriple i ab)) ha

private theorem msStrategyMeasurement_projective
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin 9 → Measurement (ZMod 2) V)
    (hP : ∀ j, MIPStarRE.QPBT.Measurement.IsProjective (P j))
    (hcomm : ∀ i k l a b,
      Commute ((P (msConstraintVars i k)).effect a)
        ((P (msConstraintVars i l)).effect b))
    (x : MsType) :
    MIPStarRE.QPBT.Measurement.IsProjective
      (msStrategyMeasurement P hP hcomm x) := by
  cases x with
  | var j =>
      exact postprocess_projective_of_injective (P j) (hP j)
        MsAnswer.bit bit_embedding_injective
  | constraint i =>
      apply postprocess_projective_of_injective
      · exact binaryJointMeasurement_projective _ _ (hP _) (hP _)
          (hcomm i 0 1)
      · exact triple_embedding_injective i

private theorem postprocess_effect_transpose
    {α β V : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [Fintype V] [DecidableEq V]
    (M : Measurement α V) (f : α → β)
    (hM : ∀ a, (M.effect a)ᵀ = M.effect a) (b : β) :
    ((M.postprocess f).effect b)ᵀ = (M.postprocess f).effect b := by
  rw [Measurement.postprocess_effect]
  ext r c
  simp only [Matrix.transpose_apply]
  rw [Matrix.sum_apply, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  exact congrFun (congrFun (hM a) r) c

private theorem msConstraintJoint_effect_transpose
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin 9 → Measurement (ZMod 2) V)
    (hP : ∀ j, MIPStarRE.QPBT.Measurement.IsProjective (P j))
    (hcomm : ∀ i k l a b,
      Commute ((P (msConstraintVars i k)).effect a)
        ((P (msConstraintVars i l)).effect b))
    (hPt : ∀ j b, ((P j).effect b)ᵀ = (P j).effect b)
    (i : Fin 6) (ab : ZMod 2 × ZMod 2) :
    ((msConstraintJoint P hP hcomm i).effect ab)ᵀ =
      (msConstraintJoint P hP hcomm i).effect ab := by
  change (((P (msConstraintVars i 0)).effect ab.1 *
    (P (msConstraintVars i 1)).effect ab.2)ᵀ) = _
  rw [Matrix.transpose_mul, hPt, hPt]
  exact (hcomm i 0 1 ab.1 ab.2).symm.eq

private theorem msConstraintObservable_product_parity
    {V : Type*} [Fintype V] [DecidableEq V]
    (OA OB : Op V) (hOA : OA * OA = 1) (hOB : OB * OB = 1)
    (hac : OA * OB = -(OB * OA)) (i : Fin 6) :
    (msParity i = 0 ∧
      msCellObservable OA OB (msConstraintVars i 0) *
          msCellObservable OA OB (msConstraintVars i 1) *
          msCellObservable OA OB (msConstraintVars i 2) = 1) ∨
    (msParity i = 1 ∧
      msCellObservable OA OB (msConstraintVars i 0) *
          msCellObservable OA OB (msConstraintVars i 1) *
          msCellObservable OA OB (msConstraintVars i 2) = -1) := by
  have hprod := msConstraintObservable_product OA OB hOA hOB hac i
  fin_cases i <;> simpa [msParity] using hprod

private theorem msCellConstraintJoint_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    (OA OB : Op V) (hOA : OAᴴ = OA) (hOB : OBᴴ = OB)
    (hOA_sq : OA * OA = 1) (hOB_sq : OB * OB = 1)
    (hac : OA * OB = -(OB * OA))
    (i : Fin 6) (k : Fin 3) (ab : ZMod 2 × ZMod 2) (b : ZMod 2) :
    let P := msCellMeasurement OA OB hOA hOB hOA_sq hOB_sq hac
    (msConstraintJoint P
        (msCellMeasurement_projective OA OB hOA hOB hOA_sq hOB_sq hac)
        (fun i k l a b => reflectionEffect_commute
          (msConstraintObservable_commute OA OB hOA_sq hOB_sq hac i k l) a b)
        i).effect ab * (P (msConstraintVars i k)).effect b =
      if parityTriple i ab k = b then
        (msConstraintJoint P
          (msCellMeasurement_projective OA OB hOA hOB hOA_sq hOB_sq hac)
          (fun i k l a b => reflectionEffect_commute
            (msConstraintObservable_commute OA OB hOA_sq hOB_sq hac i k l) a b)
          i).effect ab else 0 := by
  let P := msCellMeasurement OA OB hOA hOB hOA_sq hOB_sq hac
  let hP := msCellMeasurement_projective OA OB hOA hOB hOA_sq hOB_sq hac
  let hcomm : ∀ i k l a b,
      Commute ((P (msConstraintVars i k)).effect a)
        ((P (msConstraintVars i l)).effect b) :=
    fun i k l a b => reflectionEffect_commute
      (msConstraintObservable_commute OA OB hOA_sq hOB_sq hac i k l) a b
  fin_cases k
  · simpa [parityTriple, msConstraintJoint, P, hP, hcomm] using
      binaryJointMeasurement_mul_first (P (msConstraintVars i 0))
        (P (msConstraintVars i 1)) (hP _) (hP _) (hcomm i 0 1) ab b
  · simpa [parityTriple, msConstraintJoint, P, hP, hcomm] using
      binaryJointMeasurement_mul_second (P (msConstraintVars i 0))
        (P (msConstraintVars i 1)) (hP _) (hP _) (hcomm i 0 1) ab b
  · change
      (reflectionEffect (msCellObservable OA OB (msConstraintVars i 0)) ab.1 *
          reflectionEffect (msCellObservable OA OB (msConstraintVars i 1)) ab.2) *
          reflectionEffect (msCellObservable OA OB (msConstraintVars i 2)) b =
        if msParity i - ab.1 - ab.2 = b then
          reflectionEffect (msCellObservable OA OB (msConstraintVars i 0)) ab.1 *
            reflectionEffect (msCellObservable OA OB (msConstraintVars i 1)) ab.2
        else 0
    by_cases hb : msParity i - ab.1 - ab.2 = b
    · rw [if_pos hb]
      subst b
      exact reflection_pair_absorbs_parity_effect
        (msCellObservable OA OB (msConstraintVars i 0))
        (msCellObservable OA OB (msConstraintVars i 1))
        (msCellObservable OA OB (msConstraintVars i 2))
        (msCellObservable_sq OA OB hOA_sq hOB_sq hac _)
        (msCellObservable_sq OA OB hOA_sq hOB_sq hac _)
        (msConstraintObservable_commute OA OB hOA_sq hOB_sq hac i 0 1)
        (msParity i) ab.1 ab.2
        (msConstraintObservable_product_parity OA OB hOA_sq hOB_sq hac i)
    · rw [if_neg hb]
      have habsorb := reflection_pair_absorbs_parity_effect
        (msCellObservable OA OB (msConstraintVars i 0))
        (msCellObservable OA OB (msConstraintVars i 1))
        (msCellObservable OA OB (msConstraintVars i 2))
        (msCellObservable_sq OA OB hOA_sq hOB_sq hac _)
        (msCellObservable_sq OA OB hOA_sq hOB_sq hac _)
        (msConstraintObservable_commute OA OB hOA_sq hOB_sq hac i 0 1)
        (msParity i) ab.1 ab.2
        (msConstraintObservable_product_parity OA OB hOA_sq hOB_sq hac i)
      rw [← habsorb, mul_assoc]
      rw [show reflectionEffect
          (msCellObservable OA OB (msConstraintVars i 2))
            (msParity i - ab.1 - ab.2) *
          reflectionEffect (msCellObservable OA OB (msConstraintVars i 2)) b = 0 by
        change
          (reflectionMeasurement
            (msCellObservable OA OB (msConstraintVars i 2))
            (msCellObservable_conjTranspose OA OB hOA hOB hac _)
            (msCellObservable_sq OA OB hOA_sq hOB_sq hac _)).effect
              (msParity i - ab.1 - ab.2) *
            (reflectionMeasurement
              (msCellObservable OA OB (msConstraintVars i 2))
              (msCellObservable_conjTranspose OA OB hOA hOB hac _)
              (msCellObservable_sq OA OB hOA_sq hOB_sq hac _)).effect b = 0
        rw [binary_effect_mul
          (reflectionMeasurement
            (msCellObservable OA OB (msConstraintVars i 2))
            (msCellObservable_conjTranspose OA OB hOA hOB hac _)
            (msCellObservable_sq OA OB hOA_sq hOB_sq hac _))
          (reflectionMeasurement_projective
            (msCellObservable OA OB (msConstraintVars i 2))
            (msCellObservable_conjTranspose OA OB hOA hOB hac _)
            (msCellObservable_sq OA OB hOA_sq hOB_sq hac _))
          (msParity i - ab.1 - ab.2) b]
        simp [hb]]
      simp

private theorem msConstraintVars_injective (i : Fin 6) :
    Function.Injective (msConstraintVars i) := by
  intro k l h
  fin_cases i <;> fin_cases k <;> fin_cases l <;>
    simp [msConstraintVars] at h ⊢

private theorem msConstraintVars_exists_iff
    (i : Fin 6) (k : Fin 3) (β : Fin 3 → ZMod 2) (b : ZMod 2) :
    (∃ l : Fin 3, msConstraintVars i l = msConstraintVars i k ∧ β l = b) ↔
      β k = b := by
  constructor
  · rintro ⟨l, hl, hlb⟩
    rwa [msConstraintVars_injective i hl] at hlb
  · intro h
    exact ⟨k, rfl, h⟩

private theorem msStrategyMeasurement_incident_commute
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin 9 → Measurement (ZMod 2) V)
    (hP : ∀ j, MIPStarRE.QPBT.Measurement.IsProjective (P j))
    (hcomm : ∀ i k l a b,
      Commute ((P (msConstraintVars i k)).effect a)
        ((P (msConstraintVars i l)).effect b))
    (i : Fin 6) (k : Fin 3) (a b : MsAnswer) :
    Commute ((msStrategyMeasurement P hP hcomm (.constraint i)).effect a)
      ((msStrategyMeasurement P hP hcomm
        (.var (msConstraintVars i k))).effect b) := by
  by_cases ha : a ∈ Set.range (fun ab => MsAnswer.triple (parityTriple i ab))
  · rcases ha with ⟨ab, rfl⟩
    rw [msStrategyMeasurement_constraint_triple]
    by_cases hb : b ∈ Set.range (MsAnswer.bit : ZMod 2 → MsAnswer)
    · rcases hb with ⟨c, rfl⟩
      rw [msStrategyMeasurement_var_bit]
      change Commute
        ((P (msConstraintVars i 0)).effect ab.1 *
          (P (msConstraintVars i 1)).effect ab.2)
        ((P (msConstraintVars i k)).effect c)
      exact (hcomm i 0 k ab.1 c).mul_left (hcomm i 1 k ab.2 c)
    · rw [msStrategyMeasurement_var_zero _ _ _ _ hb]
      exact Commute.zero_right _
  · rw [msStrategyMeasurement_constraint_zero _ _ _ _ ha]
    exact Commute.zero_left _

private theorem msStrategyMeasurement_rejected_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin 9 → Measurement (ZMod 2) V)
    (hP : ∀ j, MIPStarRE.QPBT.Measurement.IsProjective (P j))
    (hcomm : ∀ i k l a b,
      Commute ((P (msConstraintVars i k)).effect a)
        ((P (msConstraintVars i l)).effect b))
    (hmul : ∀ i k ab b,
      (msConstraintJoint P hP hcomm i).effect ab *
          (P (msConstraintVars i k)).effect b =
        if parityTriple i ab k = b then
          (msConstraintJoint P hP hcomm i).effect ab else 0)
    (i : Fin 6) (k : Fin 3) (a b : MsAnswer)
    (hrej : msWinPredicate (.constraint i) (.var (msConstraintVars i k)) a b = false) :
    ((msStrategyMeasurement P hP hcomm (.constraint i)).effect a) *
      ((msStrategyMeasurement P hP hcomm
        (.var (msConstraintVars i k))).effect b) = 0 := by
  by_cases ha : a ∈ Set.range (fun ab => MsAnswer.triple (parityTriple i ab))
  · rcases ha with ⟨ab, rfl⟩
    rw [msStrategyMeasurement_constraint_triple]
    by_cases hb : b ∈ Set.range (MsAnswer.bit : ZMod 2 → MsAnswer)
    · rcases hb with ⟨c, rfl⟩
      rw [msStrategyMeasurement_var_bit]
      have hne : parityTriple i ab k ≠ c := by
        simpa [msWinPredicate, parityTriple_sum,
          msConstraintVars_exists_iff] using hrej
      rw [hmul i k ab c]
      simp [hne]
    · rw [msStrategyMeasurement_var_zero _ _ _ _ hb]
      simp
  · rw [msStrategyMeasurement_constraint_zero _ _ _ _ ha]
    simp

private theorem msStrategyMeasurement_rejected_mul_reverse
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin 9 → Measurement (ZMod 2) V)
    (hP : ∀ j, MIPStarRE.QPBT.Measurement.IsProjective (P j))
    (hcomm : ∀ i k l a b,
      Commute ((P (msConstraintVars i k)).effect a)
        ((P (msConstraintVars i l)).effect b))
    (hmul : ∀ i k ab b,
      (msConstraintJoint P hP hcomm i).effect ab *
          (P (msConstraintVars i k)).effect b =
        if parityTriple i ab k = b then
          (msConstraintJoint P hP hcomm i).effect ab else 0)
    (i : Fin 6) (k : Fin 3) (a b : MsAnswer)
    (hrej : msWinPredicate (.var (msConstraintVars i k)) (.constraint i) a b = false) :
    ((msStrategyMeasurement P hP hcomm
        (.var (msConstraintVars i k))).effect a) *
      ((msStrategyMeasurement P hP hcomm (.constraint i)).effect b) = 0 := by
  rw [(msStrategyMeasurement_incident_commute P hP hcomm i k b a).symm.eq]
  exact msStrategyMeasurement_rejected_mul P hP hcomm hmul i k b a
    (by simpa [msWinPredicate_symm] using hrej)

private theorem msGame_support_incidence (x y : MsType)
    (hxy : (x, y) ∈ msGameSymm.μ.support) :
    (∃ i : Fin 6, ∃ k : Fin 3,
      x = .constraint i ∧ y = .var (msConstraintVars i k)) ∨
      ∃ i : Fin 6, ∃ k : Fin 3,
        x = .var (msConstraintVars i k) ∧ y = .constraint i := by
  change (x, y) ∈
    Finset.univ.filter (fun ab : MsType × MsType =>
      Sym2.mk ab.1 ab.2 ∈ msEdges) at hxy
  have hedge : Sym2.mk x y ∈ msEdges := (Finset.mem_filter.mp hxy).2
  rw [msEdges] at hedge
  rcases Finset.mem_image.mp hedge with ⟨⟨i, k⟩, _, hik⟩
  rcases Sym2.eq_iff.mp hik with hik | hik
  · left
    exact ⟨i, k, hik.1.symm, hik.2.symm⟩
  · right
    exact ⟨i, k, hik.2.symm, hik.1.symm⟩

private theorem msGame_positive_incidence (x y : MsType)
    (hxy : 0 < msGameSymm.μ.weight (x, y)) :
    (∃ i : Fin 6, ∃ k : Fin 3,
      x = .constraint i ∧ y = .var (msConstraintVars i k)) ∨
      ∃ i : Fin 6, ∃ k : Fin 3,
        x = .var (msConstraintVars i k) ∧ y = .constraint i := by
  apply msGame_support_incidence x y
  by_contra hnot
  rw [msGameSymm.μ.outsideSupport (x, y) hnot] at hxy
  exact (lt_irrefl 0 hxy)

private theorem msStrategyMeasurement_commuting
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin 9 → Measurement (ZMod 2) V)
    (hP : ∀ j, MIPStarRE.QPBT.Measurement.IsProjective (P j))
    (hcomm : ∀ i k l a b,
      Commute ((P (msConstraintVars i k)).effect a)
        ((P (msConstraintVars i l)).effect b)) :
    IsCommutingOn msGameSymm.μ
      (msStrategyMeasurement P hP hcomm)
      (msStrategyMeasurement P hP hcomm) := by
  intro x y hxy a b
  rcases msGame_positive_incidence x y hxy with hxy | hxy
  · rcases hxy with ⟨i, k, rfl, rfl⟩
    exact msStrategyMeasurement_incident_commute P hP hcomm i k a b
  · rcases hxy with ⟨i, k, rfl, rfl⟩
    exact (msStrategyMeasurement_incident_commute P hP hcomm i k b a).symm

private theorem msStrategyMeasurement_rejected_mul_on_support
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin 9 → Measurement (ZMod 2) V)
    (hP : ∀ j, MIPStarRE.QPBT.Measurement.IsProjective (P j))
    (hcomm : ∀ i k l a b,
      Commute ((P (msConstraintVars i k)).effect a)
        ((P (msConstraintVars i l)).effect b))
    (hmul : ∀ i k ab b,
      (msConstraintJoint P hP hcomm i).effect ab *
          (P (msConstraintVars i k)).effect b =
        if parityTriple i ab k = b then
          (msConstraintJoint P hP hcomm i).effect ab else 0)
    (x y : MsType) (hxy : (x, y) ∈ msGameSymm.μ.support)
    (a b : MsAnswer) (hrej : msWinPredicate x y a b = false) :
    ((msStrategyMeasurement P hP hcomm x).effect a) *
      ((msStrategyMeasurement P hP hcomm y).effect b) = 0 := by
  rcases msGame_support_incidence x y hxy with hxy | hxy
  · rcases hxy with ⟨i, k, rfl, rfl⟩
    exact msStrategyMeasurement_rejected_mul P hP hcomm hmul i k a b hrej
  · rcases hxy with ⟨i, k, rfl, rfl⟩
    exact msStrategyMeasurement_rejected_mul_reverse P hP hcomm hmul i k a b hrej

private theorem msStrategyMeasurement_effect_transpose
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin 9 → Measurement (ZMod 2) V)
    (hP : ∀ j, MIPStarRE.QPBT.Measurement.IsProjective (P j))
    (hcomm : ∀ i k l a b,
      Commute ((P (msConstraintVars i k)).effect a)
        ((P (msConstraintVars i l)).effect b))
    (hPt : ∀ j b, ((P j).effect b)ᵀ = (P j).effect b)
    (x : MsType) (a : MsAnswer) :
    ((msStrategyMeasurement P hP hcomm x).effect a)ᵀ =
      (msStrategyMeasurement P hP hcomm x).effect a := by
  cases x with
  | var j =>
      exact postprocess_effect_transpose (P j) MsAnswer.bit (hPt j) a
  | constraint i =>
      exact postprocess_effect_transpose (msConstraintJoint P hP hcomm i)
        (fun ab => .triple (parityTriple i ab))
        (msConstraintJoint_effect_transpose P hP hcomm hPt i) a

private theorem heteroKron_mulVec_epr_eq_zero_of_mul_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (E F : Op V) (hFt : Fᵀ = F) (hEF : E * F = 0) :
    (heteroKron E F).mulVec (eprState V) = 0 := by
  have hfactor : heteroKron E F =
      heteroKron E 1 * heteroKron 1 F := by
    rw [heteroKron_mul]
    simp
  rw [hfactor, ← Matrix.mulVec_mulVec,
    ← epr_action_eq_of_transpose F hFt, Matrix.mulVec_mulVec,
    heteroKron_mul, hEF]
  have hz : heteroKron (0 : Op V) (1 : Op V) = 0 := by
    ext ⟨i, k⟩ ⟨j, l⟩
    simp [heteroKron, Matrix.kronecker, Matrix.kroneckerMap_apply]
  simp only [mul_one]
  rw [hz]
  exact Matrix.zero_mulVec _

private theorem sum_heteroKron_measurement_effects
    {V : Type*} [Fintype V] [DecidableEq V]
    {A B : Type*} [Fintype A] [Fintype B]
    (M : Measurement A V) (N : Measurement B V) :
    ∑ a : A, ∑ b : B, heteroKron (M.effect a) (N.effect b) = 1 := by
  calc
    ∑ a : A, ∑ b : B, heteroKron (M.effect a) (N.effect b) =
        heteroKron (∑ a : A, M.effect a) (∑ b : B, N.effect b) := by
      ext p q
      rcases p with ⟨p₁, p₂⟩
      rcases q with ⟨q₁, q₂⟩
      simp only [heteroKron, Matrix.kronecker, Matrix.kroneckerMap_apply,
        Matrix.sum_apply]
      exact (Finset.sum_mul_sum Finset.univ Finset.univ
        (fun a => M.effect a p₁ q₁) (fun b => N.effect b p₂ q₂)).symm
    _ = heteroKron 1 1 := by rw [M.sum_eq_one, N.sum_eq_one]
    _ = 1 := heteroKron_one_one

private theorem sum_apply_measurement_effects
    {V : Type*} [Fintype V] [DecidableEq V]
    {A B : Type*} [Fintype A] [Fintype B]
    (M : Measurement A V) (N : Measurement B V)
    (psi : EuclideanSpace ℂ (V × V)) :
    ∑ a : A, ∑ b : B,
        applyOperatorToState (heteroKron (M.effect a) (N.effect b)) psi = psi := by
  calc
    ∑ a : A, ∑ b : B,
        applyOperatorToState (heteroKron (M.effect a) (N.effect b)) psi =
      applyOperatorToState
        (∑ a : A, ∑ b : B, heteroKron (M.effect a) (N.effect b)) psi := by
          simp [applyOperatorToState]
    _ = applyOperatorToState 1 psi := by
      rw [sum_heteroKron_measurement_effects M N]
    _ = psi := by simp [applyOperatorToState]

private theorem sum_born_weights_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    {A B : Type*} [Fintype A] [Fintype B]
    (M : Measurement A V) (N : Measurement B V)
    (psi : EuclideanSpace ℂ (V × V)) (hpsi : ‖psi‖ = 1) :
    ∑ a : A, ∑ b : B,
        (inner ℂ psi
          (applyOperatorToState
            (heteroKron (M.effect a) (N.effect b)) psi)).re = 1 := by
  calc
    ∑ a : A, ∑ b : B,
        (inner ℂ psi
          (applyOperatorToState
            (heteroKron (M.effect a) (N.effect b)) psi)).re =
      (inner ℂ psi
        (∑ a : A, ∑ b : B,
          applyOperatorToState
            (heteroKron (M.effect a) (N.effect b)) psi)).re := by
              simp only [inner_sum, Complex.re_sum]
    _ = (inner ℂ psi psi).re := by rw [sum_apply_measurement_effects M N psi]
    _ = 1 := by
      calc
        (inner ℂ psi psi).re = ‖psi‖ ^ 2 :=
          inner_self_eq_norm_sq (𝕜 := ℂ) psi
        _ = 1 := by simp [hpsi]

private theorem rejected_born_weight_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Fin 9 → Measurement (ZMod 2) V)
    (hP : ∀ j, MIPStarRE.QPBT.Measurement.IsProjective (P j))
    (hcomm : ∀ i k l a b,
      Commute ((P (msConstraintVars i k)).effect a)
        ((P (msConstraintVars i l)).effect b))
    (hmul : ∀ i k ab b,
      (msConstraintJoint P hP hcomm i).effect ab *
          (P (msConstraintVars i k)).effect b =
        if parityTriple i ab k = b then
          (msConstraintJoint P hP hcomm i).effect ab else 0)
    (hPt : ∀ j b, ((P j).effect b)ᵀ = (P j).effect b)
    (x y : MsType) (hxy : (x, y) ∈ msGameSymm.μ.support)
    (a b : MsAnswer) (hrej : msWinPredicate x y a b = false) :
    (inner ℂ (eprState V)
      (applyOperatorToState
        (heteroKron
          ((msStrategyMeasurement P hP hcomm x).effect a)
          ((msStrategyMeasurement P hP hcomm y).effect b))
        (eprState V))).re = 0 := by
  have hmul_zero :=
    msStrategyMeasurement_rejected_mul_on_support
      P hP hcomm hmul x y hxy a b hrej
  have hright_transpose :=
    msStrategyMeasurement_effect_transpose P hP hcomm hPt y b
  have hzero := heteroKron_mulVec_epr_eq_zero_of_mul_eq_zero
    ((msStrategyMeasurement P hP hcomm x).effect a)
    ((msStrategyMeasurement P hP hcomm y).effect b)
    hright_transpose hmul_zero
  have hacted :
      applyOperatorToState
        (heteroKron
          ((msStrategyMeasurement P hP hcomm x).effect a)
          ((msStrategyMeasurement P hP hcomm y).effect b))
        (eprState V) = 0 := by
    rw [applyOperatorToState, Matrix.toLpLin_apply, hzero]
    rfl
  rw [hacted]
  simp

private theorem accepted_born_weights_eq_one
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Fin 9 → Measurement (ZMod 2) V)
    (hP : ∀ j, MIPStarRE.QPBT.Measurement.IsProjective (P j))
    (hcomm : ∀ i k l a b,
      Commute ((P (msConstraintVars i k)).effect a)
        ((P (msConstraintVars i l)).effect b))
    (hmul : ∀ i k ab b,
      (msConstraintJoint P hP hcomm i).effect ab *
          (P (msConstraintVars i k)).effect b =
        if parityTriple i ab k = b then
          (msConstraintJoint P hP hcomm i).effect ab else 0)
    (hPt : ∀ j b, ((P j).effect b)ᵀ = (P j).effect b)
    (x y : MsType) (hxy : (x, y) ∈ msGameSymm.μ.support) :
    ∑ a : MsAnswer, ∑ b : MsAnswer,
      (if msWinPredicate x y a b then
        (inner ℂ (eprState V)
          (applyOperatorToState
            (heteroKron
              ((msStrategyMeasurement P hP hcomm x).effect a)
              ((msStrategyMeasurement P hP hcomm y).effect b))
            (eprState V))).re
      else 0) = 1 := by
  calc
    ∑ a : MsAnswer, ∑ b : MsAnswer,
        (if msWinPredicate x y a b then
          (inner ℂ (eprState V)
            (applyOperatorToState
              (heteroKron
                ((msStrategyMeasurement P hP hcomm x).effect a)
                ((msStrategyMeasurement P hP hcomm y).effect b))
              (eprState V))).re
        else 0) =
      ∑ a : MsAnswer, ∑ b : MsAnswer,
        (inner ℂ (eprState V)
          (applyOperatorToState
            (heteroKron
              ((msStrategyMeasurement P hP hcomm x).effect a)
              ((msStrategyMeasurement P hP hcomm y).effect b))
            (eprState V))).re := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      by_cases hab : msWinPredicate x y a b = true
      · simp [hab]
      · have hab_false := Bool.eq_false_of_not_eq_true hab
        rw [rejected_born_weight_eq_zero
          P hP hcomm hmul hPt x y hxy a b hab_false]
        simp [hab_false]
    _ = 1 := sum_born_weights_eq_one
      (msStrategyMeasurement P hP hcomm x)
      (msStrategyMeasurement P hP hcomm y)
      (eprState V) (eprState_norm V)

private theorem reflectionEffect_heteroKron_one
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (O : Op V) (b : ZMod 2) :
    reflectionEffect (heteroKron O (1 : Op W)) b =
      heteroKron (reflectionEffect O b) (1 : Op W) := by
  rcases zmod_two_eq_zero_or_one b with rfl | rfl <;>
    ext ⟨i, k⟩ ⟨j, l⟩ <;>
      by_cases hkl : k = l <;> by_cases hij : i = j <;>
        simp [reflectionEffect, heteroKron, Matrix.kronecker,
          Matrix.kroneckerMap_apply, hkl, hij]
  all_goals ring

/-- `thm:ms-from-ac`: any anticommuting pair of projective binary
measurements, consistent on an EPR state, extends to a value-one SPCC Magic
Square strategy. Blueprint `ch13_qpbt_test.tex:257-267`, paper
`08_classical_and_quantum_low_degree_tests.tex:654-722`.

The local index type is arbitrary, finite, and nonempty; no field model or QPBT
parameter is assumed. The equality `hι` identifies the target local Hilbert
space with the constructed tensor factor. -/
theorem exists_ms_perfect_strategy_of_anticommuting
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A B : Measurement (ZMod 2) ι)
    (hA : MIPStarRE.QPBT.Measurement.IsProjective A)
    (hB : MIPStarRE.QPBT.Measurement.IsProjective B)
    (hcA : MIPStarRE.QPBT.Measurement.IsConsistentOn A (eprState ι))
    (hcB : MIPStarRE.QPBT.Measurement.IsConsistentOn B (eprState ι))
    (hac : obsOf A * obsOf B = -(obsOf B * obsOf A)) :
    ∃ S : SymmetricStrategy msGameSymm, ∃ hι : S.ι = (ι × ZMod 2),
      S.IsSPCC ∧ S.toStrategy.value = 1 ∧
      reindexState (Equiv.prodCongr (Equiv.cast hι) (Equiv.cast hι)) S.ψ =
        msPerfectState ι ∧
      ∀ b : ZMod 2,
        reindexOp (Equiv.cast hι.symm) ((S.M (.var 0)).effect (.bit b)) =
            heteroKron (A.effect b) (1 : Op (ZMod 2)) ∧
          reindexOp (Equiv.cast hι.symm) ((S.M (.var 4)).effect (.bit b)) =
            heteroKron (B.effect b) (1 : Op (ZMod 2)) := by
  have hAt : ∀ b, (A.effect b)ᵀ = A.effect b := fun b =>
    transpose_eq_of_epr_action (A.effect b) (hcA b)
  have hBt : ∀ b, (B.effect b)ᵀ = B.effect b := fun b =>
    transpose_eq_of_epr_action (B.effect b) (hcB b)
  have hOAt : (obsOf A)ᵀ = obsOf A := by
    rw [obsOf, Matrix.transpose_sub, hAt 0, hAt 1]
  have hOBt : (obsOf B)ᵀ = obsOf B := by
    rw [obsOf, Matrix.transpose_sub, hBt 0, hBt 1]
  let P := msCellMeasurement (obsOf A) (obsOf B)
    (obsOf_conjTranspose A hA) (obsOf_conjTranspose B hB)
    (obsOf_sq A hA) (obsOf_sq B hB) hac
  let hP := msCellMeasurement_projective (obsOf A) (obsOf B)
    (obsOf_conjTranspose A hA) (obsOf_conjTranspose B hB)
    (obsOf_sq A hA) (obsOf_sq B hB) hac
  let hcomm : ∀ i k l a b,
      Commute ((P (msConstraintVars i k)).effect a)
        ((P (msConstraintVars i l)).effect b) :=
    fun i k l a b => reflectionEffect_commute
      (msConstraintObservable_commute (obsOf A) (obsOf B)
        (obsOf_sq A hA) (obsOf_sq B hB) hac i k l) a b
  let hPt : ∀ j b, ((P j).effect b)ᵀ = (P j).effect b :=
    msCellMeasurement_transpose (obsOf A) (obsOf B)
      (obsOf_conjTranspose A hA) (obsOf_conjTranspose B hB)
      (obsOf_sq A hA) (obsOf_sq B hB) hOAt hOBt hac
  let hmul : ∀ i k ab b,
      (msConstraintJoint P hP hcomm i).effect ab *
          (P (msConstraintVars i k)).effect b =
        if parityTriple i ab k = b then
          (msConstraintJoint P hP hcomm i).effect ab else 0 :=
    msCellConstraintJoint_mul (obsOf A) (obsOf B)
      (obsOf_conjTranspose A hA) (obsOf_conjTranspose B hB)
      (obsOf_sq A hA) (obsOf_sq B hB) hac
  let M := msStrategyMeasurement P hP hcomm
  let S : SymmetricStrategy msGameSymm :=
    { ι := ι × ZMod 2
      ψ := eprState (ι × ZMod 2)
      ψ_norm := eprState_norm (ι × ZMod 2)
      ψ_swap := reindexState_prodComm_eprState (ι × ZMod 2)
      M := M }
  refine ⟨S, rfl, ?_, ?_, ?_, ?_⟩
  · refine ⟨msStrategyMeasurement_projective P hP hcomm, ?_,
      msStrategyMeasurement_commuting P hP hcomm⟩
    intro x a
    exact epr_action_eq_of_transpose _
      (msStrategyMeasurement_effect_transpose P hP hcomm hPt x a)
  · change avgOver msGameSymm.μ (fun xy =>
      ∑ a : MsAnswer, ∑ b : MsAnswer,
        (if msWinPredicate xy.1 xy.2 a b then
          (inner ℂ (eprState (ι × ZMod 2))
            (applyOperatorToState
              (heteroKron ((M xy.1).effect a) ((M xy.2).effect b))
              (eprState (ι × ZMod 2)))).re
        else 0)) = 1
    calc
      avgOver msGameSymm.μ (fun xy =>
          ∑ a : MsAnswer, ∑ b : MsAnswer,
            (if msWinPredicate xy.1 xy.2 a b then
              (inner ℂ (eprState (ι × ZMod 2))
                (applyOperatorToState
                  (heteroKron ((M xy.1).effect a) ((M xy.2).effect b))
                  (eprState (ι × ZMod 2)))).re
            else 0)) = avgOver msGameSymm.μ (fun _ => 1) := by
        apply avgOver_congr_on_support
        rintro ⟨x, y⟩ hxy
        exact accepted_born_weights_eq_one P hP hcomm hmul hPt x y hxy
      _ = 1 := avgOver_const_of_isProbability _ msGameSymm.μ_prob 1
  · change eprState (ι × ZMod 2) = msPerfectState ι
    exact (msPerfectState_eq_eprState ι).symm
  · intro b
    constructor
    · simp only [S, Equiv.cast_refl, reindexOp]
      rw [msStrategyMeasurement_var_bit P hP hcomm]
      change reflectionEffect
          (heteroKron (obsOf A) (1 : Op (ZMod 2))) b =
        heteroKron (A.effect b) (1 : Op (ZMod 2))
      rw [reflectionEffect_heteroKron_one,
        reflectionEffect_obsOf_measurement]
    · simp only [S, Equiv.cast_refl, reindexOp]
      rw [msStrategyMeasurement_var_bit P hP hcomm]
      change reflectionEffect
          (heteroKron (obsOf B) (1 : Op (ZMod 2))) b =
        heteroKron (B.effect b) (1 : Op (ZMod 2))
      rw [reflectionEffect_heteroKron_one,
        reflectionEffect_obsOf_measurement]

end

end MIPStarRE.QPBT
