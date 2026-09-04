import MIPStarRE.QPBT.Observables.WinImplications.CommutingObs
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.Anticommutation
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.AnticommutatorB

/-!
# Approximate anticommutation of the point observables on anticommuting tuples

This module carries out the anticommuting half of the proof of Equation
`eq:pts-obs-commutation` in `lem:qld-win-implications-obs`. The Magic Square
approximate anticommutation of the variable observables is read back from the
projective dilation on which it is proved, and transported to Alice's point
observables through item 7 of `lem:qld-win-implications`.

## References

The declarations support `lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:342-362`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace WinImplications

/-! ## Reading the dilation back on the original space -/

/-- The matrix of the identity isometry is the identity matrix.
Formalization-only support for `thm:ms-rigidity`, blueprint
`ch13_qpbt_test.tex:266-288`. -/
theorem isometryMatrix_id {ι : Type} [Fintype ι] [DecidableEq ι] :
    MagicSquareRigidity.isometryMatrix
      (LinearIsometry.id (R := ℂ) (E := EuclideanSpace ℂ ι)) = 1 := by
  ext k i
  rw [MagicSquareRigidity.isometryMatrix_apply]
  simp [Matrix.one_apply, EuclideanSpace.equiv]

/-- Conjugation by the identity isometry is the identity. Formalization-only
support for `thm:ms-rigidity`, blueprint `ch13_qpbt_test.tex:266-288`. -/
theorem conjIsometry_id {ι : Type} [Fintype ι] [DecidableEq ι] (M : Op ι) :
    conjIsometry (LinearIsometry.id (R := ℂ) (E := EuclideanSpace ℂ ι)) M = M := by
  rw [MagicSquareRigidity.conjIsometry_eq, isometryMatrix_id]
  simp

/-- The two-sided identity isometry fixes every bipartite state.
Formalization-only support for `thm:ms-rigidity`, blueprint
`ch13_qpbt_test.tex:266-288`. -/
theorem isometryTensor_id {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB] (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    isometryTensor (LinearIsometry.id (R := ℂ) (E := EuclideanSpace ℂ ιA))
      (LinearIsometry.id (R := ℂ) (E := EuclideanSpace ℂ ιB)) ψ = ψ := by
  ext p
  rw [MagicSquareRigidity.isometryTensor_apply_eq, isometryMatrix_id,
    isometryMatrix_id]
  rw [show Matrix.kronecker (1 : Op ιA) (1 : Op ιB) = 1 from
    Matrix.one_kronecker_one]
  simp [Matrix.one_apply]

/-- Inflation to the ground slice is multiplicative. Formalization-only support
for `thm:ms-rigidity`, blueprint `ch13_qpbt_test.tex:266-288`. -/
theorem naimarkInflation_mul {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (M N : Op ι) :
    MagicSquareRigidity.naimarkInflation (α := α) M *
        MagicSquareRigidity.naimarkInflation (α := α) N =
      MagicSquareRigidity.naimarkInflation (α := α) (M * N) := by
  classical
  ext p q
  simp only [Matrix.mul_apply, MagicSquareRigidity.naimarkInflation_apply]
  by_cases hp : p.2 = none
  · by_cases hq : q.2 = none
    · simp [hp, hq, Fintype.sum_prod_type]
    · simp [hq]
  · simp [hp]

/-- Inflation to the ground slice is additive. Formalization-only support for
`thm:ms-rigidity`, blueprint `ch13_qpbt_test.tex:266-288`. -/
theorem naimarkInflation_add {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (M N : Op ι) :
    MagicSquareRigidity.naimarkInflation (α := α) M +
        MagicSquareRigidity.naimarkInflation (α := α) N =
      MagicSquareRigidity.naimarkInflation (α := α) (M + N) := by
  ext p q
  by_cases h : p.2 = none ∧ q.2 = none <;> simp [h]

/-- An operator inflated on the second factor acts on the dilated state exactly
as the original operator acts on the original state. Formalization-only support
for `thm:ms-rigidity`, blueprint `ch13_qpbt_test.tex:266-288`. -/
theorem applyOperatorToState_heteroKron_one_naimarkInflation
    (α : Type) [Fintype α] [DecidableEq α]
    {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (N : Op ιB) (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    applyOperatorToState
        (heteroKron (1 : Op (ιA × Option α))
          (MagicSquareRigidity.naimarkInflation (α := α) N))
        (MagicSquareRigidity.naimarkDilatedState α ψ) =
      MagicSquareRigidity.naimarkDilatedState α
        (applyOperatorToState (heteroKron (1 : Op ιA) N) ψ) := by
  classical
  ext p
  rw [MagicSquareRigidity.applyOperatorToState_naimarkDilatedState,
    MagicSquareRigidity.naimarkDilatedState_apply]
  obtain ⟨⟨i, oa⟩, ⟨j, ob⟩⟩ := p
  by_cases hoa : oa = none
  · by_cases hob : ob = none
    · subst hoa
      subst hob
      simp [heteroKron, applyOperatorToState, Matrix.mulVec, dotProduct,
        Fintype.sum_prod_type, Matrix.one_apply]
    · simp [hob, heteroKron]
  · simp [hoa, heteroKron]

/-- The state-dependent norm of an operator inflated on the second factor,
measured on the dilated state, is the norm of the original operator on the
original state. Formalization-only support for `thm:ms-rigidity`, blueprint
`ch13_qpbt_test.tex:266-288`. -/
theorem norm_heteroKron_one_naimarkInflation
    (α : Type) [Fintype α] [DecidableEq α]
    {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (N : Op ιB) (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    ‖applyOperatorToState
        (heteroKron (1 : Op (ιA × Option α))
          (MagicSquareRigidity.naimarkInflation (α := α) N))
        (MagicSquareRigidity.naimarkDilatedState α ψ)‖ =
      ‖applyOperatorToState (heteroKron (1 : Op ιA) N) ψ‖ := by
  rw [applyOperatorToState_heteroKron_one_naimarkInflation,
    MagicSquareRigidity.naimarkDilatedState_norm]

/-! ## The Magic Square anticommutation on the undilated strategy -/

/-- Bob's Magic Square variable reflections are the placed observables of his
totalized variable measurements on the dilated strategy. Formalization-only
support for `thm:ms-rigidity`, blueprint `ch13_qpbt_test.tex:266-288`. -/
theorem msVarObsB_eq (S : Strategy msGame) (j : Fin 9) :
    MagicSquareRigidity.msVarObsB S j =
      heteroKron (1 : Op (S.ιA × Option MsAnswer))
        (MagicSquareRigidity.dilatedObsB S (.var j) msBitOrZero) := by
  rw [MagicSquareRigidity.msVarObsB,
    MagicSquareRigidity.signObs_eq_obsOf_postprocess]
  rfl

/-- Bob's Magic Square variable observables approximately anticommute on the
strategy state. The approximate anticommutation is proved on the projective
dilation and read back through the ground slice. Paper
`14_analysis_of_the_pauli_basis_test.tex:342-356`, blueprint
`ch13_qpbt_test.tex:266-288` and `ch14_qpbt_observables.tex:761-794`. -/
theorem msVarObs_anticommutator_le (S : Strategy msGame) (ε : ℝ) (hε : 0 ≤ ε)
    (hwin : 1 - ε ≤ S.value) :
    ‖applyOperatorToState
        (heteroKron (1 : Op S.ιA)
          (obsOf ((S.B (.var 0)).postprocess msBitOrZero) *
              obsOf ((S.B (.var 4)).postprocess msBitOrZero) +
            obsOf ((S.B (.var 4)).postprocess msBitOrZero) *
              obsOf ((S.B (.var 0)).postprocess msBitOrZero)))
        S.ψ‖ ^ 2 ≤ 1183680 * ε := by
  classical
  set xi : EuclideanSpace ℂ
      ((S.ιA × Option MsAnswer) × (S.ιB × Option MsAnswer)) :=
    MagicSquareRigidity.naimarkDilatedState MsAnswer S.ψ with hxidef
  have hxi : ‖isometryTensor
      (LinearIsometry.id (R := ℂ)
        (E := EuclideanSpace ℂ (S.ιA × Option MsAnswer)))
      (LinearIsometry.id (R := ℂ)
        (E := EuclideanSpace ℂ (S.ιB × Option MsAnswer))) xi - xi‖ ≤ 0 := by
    rw [isometryTensor_id, sub_self, norm_zero]
  have htrans := MagicSquareRigidity.ms_anticommutator_transfer_B S
    (LinearIsometry.id (R := ℂ)
      (E := EuclideanSpace ℂ (S.ιA × Option MsAnswer)))
    (LinearIsometry.id (R := ℂ)
      (E := EuclideanSpace ℂ (S.ιB × Option MsAnswer))) xi ε 0 hwin hxi
  simp only [MagicSquareRigidity.conjIsometry_comp_naimarkEmbedding,
    conjIsometry_id, MagicSquareRigidity.opDistSq_uniform_unit] at htrans
  rw [hxidef] at htrans
  have hL : heteroKron (1 : Op (S.ιA × Option MsAnswer))
        (MagicSquareRigidity.naimarkInflation (α := MsAnswer)
          (obsOf ((S.B (.var 0)).postprocess msBitOrZero))) *
        heteroKron 1 (MagicSquareRigidity.naimarkInflation (α := MsAnswer)
          (obsOf ((S.B (.var 4)).postprocess msBitOrZero))) -
      -(heteroKron 1 (MagicSquareRigidity.naimarkInflation (α := MsAnswer)
          (obsOf ((S.B (.var 4)).postprocess msBitOrZero))) *
        heteroKron 1 (MagicSquareRigidity.naimarkInflation (α := MsAnswer)
          (obsOf ((S.B (.var 0)).postprocess msBitOrZero)))) =
      heteroKron (1 : Op (S.ιA × Option MsAnswer))
        (MagicSquareRigidity.naimarkInflation (α := MsAnswer)
          (obsOf ((S.B (.var 0)).postprocess msBitOrZero) *
              obsOf ((S.B (.var 4)).postprocess msBitOrZero) +
            obsOf ((S.B (.var 4)).postprocess msBitOrZero) *
              obsOf ((S.B (.var 0)).postprocess msBitOrZero))) := by
    simp only [heteroKron_mul, one_mul, sub_neg_eq_add, naimarkInflation_mul,
      ← MagicSquareRigidity.heteroKron_add_right, naimarkInflation_add]
  rw [hL, norm_heteroKron_one_naimarkInflation] at htrans
  have hclose := MagicSquareRigidity.msVarObsB_anticommute S ε hwin
  rw [msVarObsB_eq, msVarObsB_eq] at hclose
  have hnorm : ‖applyOperatorToState
      (heteroKron (1 : Op (S.ιA × Option MsAnswer))
          (MagicSquareRigidity.dilatedObsB S (.var 0) msBitOrZero) *
        heteroKron 1
          (MagicSquareRigidity.dilatedObsB S (.var 4) msBitOrZero) -
        -(heteroKron 1
            (MagicSquareRigidity.dilatedObsB S (.var 4) msBitOrZero) *
          heteroKron 1
            (MagicSquareRigidity.dilatedObsB S (.var 0) msBitOrZero)))
      (MagicSquareRigidity.naimarkDilatedState MsAnswer S.ψ)‖ ≤
        624 * Real.sqrt ε := hclose
  have hsq : ‖applyOperatorToState
      (heteroKron (1 : Op (S.ιA × Option MsAnswer))
          (MagicSquareRigidity.dilatedObsB S (.var 0) msBitOrZero) *
        heteroKron 1
          (MagicSquareRigidity.dilatedObsB S (.var 4) msBitOrZero) -
        -(heteroKron 1
            (MagicSquareRigidity.dilatedObsB S (.var 4) msBitOrZero) *
          heteroKron 1
            (MagicSquareRigidity.dilatedObsB S (.var 0) msBitOrZero)))
      (MagicSquareRigidity.naimarkDilatedState MsAnswer S.ψ)‖ ^ 2 ≤
        389376 * ε := by
    have hnn : (0 : ℝ) ≤ 624 * Real.sqrt ε := by positivity
    calc _ ≤ (624 * Real.sqrt ε) ^ 2 :=
          (sq_le_sq₀ (norm_nonneg _) hnn).2 hnorm
      _ = 389376 * ε := by
          rw [mul_pow, Real.sq_sqrt hε]
          ring
  have h48 : (48 : ℝ) * 0 ^ 2 = 0 := by norm_num
  rw [h48, add_zero] at htrans
  refine le_trans htrans ?_
  linarith

/-- An operator inflated on the first factor acts on the dilated state exactly
as the original operator acts on the original state. Formalization-only support
for `thm:ms-rigidity`, blueprint `ch13_qpbt_test.tex:266-288`. -/
theorem applyOperatorToState_heteroKron_naimarkInflation_one
    (α : Type) [Fintype α] [DecidableEq α]
    {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : Op ιA) (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    applyOperatorToState
        (heteroKron (MagicSquareRigidity.naimarkInflation (α := α) M)
          (1 : Op (ιB × Option α)))
        (MagicSquareRigidity.naimarkDilatedState α ψ) =
      MagicSquareRigidity.naimarkDilatedState α
        (applyOperatorToState (heteroKron M (1 : Op ιB)) ψ) := by
  classical
  ext p
  rw [MagicSquareRigidity.applyOperatorToState_naimarkDilatedState,
    MagicSquareRigidity.naimarkDilatedState_apply]
  obtain ⟨⟨i, oa⟩, ⟨j, ob⟩⟩ := p
  by_cases hoa : oa = none
  · by_cases hob : ob = none
    · subst hoa
      subst hob
      simp [heteroKron, applyOperatorToState, Matrix.mulVec, dotProduct,
        Fintype.sum_prod_type, Matrix.one_apply]
    · simp [hob, heteroKron]
  · simp [hoa, heteroKron]

/-- The state-dependent norm of an operator inflated on the first factor,
measured on the dilated state, is the norm of the original operator on the
original state. Formalization-only support for `thm:ms-rigidity`, blueprint
`ch13_qpbt_test.tex:266-288`. -/
theorem norm_heteroKron_naimarkInflation_one
    (α : Type) [Fintype α] [DecidableEq α]
    {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : Op ιA) (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    ‖applyOperatorToState
        (heteroKron (MagicSquareRigidity.naimarkInflation (α := α) M)
          (1 : Op (ιB × Option α)))
        (MagicSquareRigidity.naimarkDilatedState α ψ)‖ =
      ‖applyOperatorToState (heteroKron M (1 : Op ιB)) ψ‖ := by
  rw [applyOperatorToState_heteroKron_naimarkInflation_one,
    MagicSquareRigidity.naimarkDilatedState_norm]

/-- Alice's Magic Square variable reflections are the placed observables of her
totalized variable measurements on the dilated strategy. Formalization-only
support for `thm:ms-rigidity`, blueprint `ch13_qpbt_test.tex:266-288`. -/
theorem msVarObsA_eq (S : Strategy msGame) (j : Fin 9) :
    MagicSquareRigidity.msVarObsA S j =
      heteroKron (MagicSquareRigidity.dilatedObsA S (.var j))
        (1 : Op (S.ιB × Option MsAnswer)) := by
  rw [MagicSquareRigidity.msVarObsA,
    MagicSquareRigidity.signObs_eq_obsOf_postprocess]
  rfl

/-- Alice's Magic Square variable observables approximately anticommute on the
strategy state. This is the first-factor companion of the anticommutation
input, proved on the projective dilation and read back through the ground
slice. Paper `14_analysis_of_the_pauli_basis_test.tex:342-356`, blueprint
`ch13_qpbt_test.tex:266-288` and `ch14_qpbt_observables.tex:761-794`. -/
theorem msVarObsA_anticommutator_le (S : Strategy msGame) (ε : ℝ) (hε : 0 ≤ ε)
    (hwin : 1 - ε ≤ S.value) :
    ‖applyOperatorToState
        (heteroKron
          (obsOf ((S.A (.var 0)).postprocess msBitOrZero) *
              obsOf ((S.A (.var 4)).postprocess msBitOrZero) +
            obsOf ((S.A (.var 4)).postprocess msBitOrZero) *
              obsOf ((S.A (.var 0)).postprocess msBitOrZero))
          (1 : Op S.ιB))
        S.ψ‖ ^ 2 ≤ 1183680 * ε := by
  classical
  set xi : EuclideanSpace ℂ
      ((S.ιA × Option MsAnswer) × (S.ιB × Option MsAnswer)) :=
    MagicSquareRigidity.naimarkDilatedState MsAnswer S.ψ with hxidef
  have hxi : ‖isometryTensor
      (LinearIsometry.id (R := ℂ)
        (E := EuclideanSpace ℂ (S.ιA × Option MsAnswer)))
      (LinearIsometry.id (R := ℂ)
        (E := EuclideanSpace ℂ (S.ιB × Option MsAnswer))) xi - xi‖ ≤ 0 := by
    rw [isometryTensor_id, sub_self, norm_zero]
  have htrans := MagicSquareRigidity.ms_anticommutator_transfer_A S
    (LinearIsometry.id (R := ℂ)
      (E := EuclideanSpace ℂ (S.ιA × Option MsAnswer)))
    (LinearIsometry.id (R := ℂ)
      (E := EuclideanSpace ℂ (S.ιB × Option MsAnswer))) xi ε 0 hwin hxi
  simp only [MagicSquareRigidity.conjIsometry_comp_naimarkEmbedding,
    conjIsometry_id, MagicSquareRigidity.opDistSq_uniform_unit] at htrans
  rw [hxidef] at htrans
  have hL : heteroKron
        (MagicSquareRigidity.naimarkInflation (α := MsAnswer)
          (obsOf ((S.A (.var 0)).postprocess msBitOrZero)))
        (1 : Op (S.ιB × Option MsAnswer)) *
        heteroKron (MagicSquareRigidity.naimarkInflation (α := MsAnswer)
          (obsOf ((S.A (.var 4)).postprocess msBitOrZero))) 1 -
      -(heteroKron (MagicSquareRigidity.naimarkInflation (α := MsAnswer)
          (obsOf ((S.A (.var 4)).postprocess msBitOrZero))) 1 *
        heteroKron (MagicSquareRigidity.naimarkInflation (α := MsAnswer)
          (obsOf ((S.A (.var 0)).postprocess msBitOrZero))) 1) =
      heteroKron
        (MagicSquareRigidity.naimarkInflation (α := MsAnswer)
          (obsOf ((S.A (.var 0)).postprocess msBitOrZero) *
              obsOf ((S.A (.var 4)).postprocess msBitOrZero) +
            obsOf ((S.A (.var 4)).postprocess msBitOrZero) *
              obsOf ((S.A (.var 0)).postprocess msBitOrZero)))
        (1 : Op (S.ιB × Option MsAnswer)) := by
    simp only [heteroKron_mul, one_mul, sub_neg_eq_add, naimarkInflation_mul,
      ← MagicSquareRigidity.heteroKron_add_left, naimarkInflation_add]
  rw [hL, norm_heteroKron_naimarkInflation_one] at htrans
  have hclose := MagicSquareRigidity.msVarObsA_anticommute S ε hwin
  rw [msVarObsA_eq, msVarObsA_eq] at hclose
  have hnorm : ‖applyOperatorToState
      (heteroKron (MagicSquareRigidity.dilatedObsA S (.var 0))
          (1 : Op (S.ιB × Option MsAnswer)) *
        heteroKron (MagicSquareRigidity.dilatedObsA S (.var 4)) 1 -
        -(heteroKron (MagicSquareRigidity.dilatedObsA S (.var 4)) 1 *
          heteroKron (MagicSquareRigidity.dilatedObsA S (.var 0)) 1))
      (MagicSquareRigidity.naimarkDilatedState MsAnswer S.ψ)‖ ≤
        624 * Real.sqrt ε := hclose
  have hsq : ‖applyOperatorToState
      (heteroKron (MagicSquareRigidity.dilatedObsA S (.var 0))
          (1 : Op (S.ιB × Option MsAnswer)) *
        heteroKron (MagicSquareRigidity.dilatedObsA S (.var 4)) 1 -
        -(heteroKron (MagicSquareRigidity.dilatedObsA S (.var 4)) 1 *
          heteroKron (MagicSquareRigidity.dilatedObsA S (.var 0)) 1))
      (MagicSquareRigidity.naimarkDilatedState MsAnswer S.ψ)‖ ^ 2 ≤
        389376 * ε := by
    have hnn : (0 : ℝ) ≤ 624 * Real.sqrt ε := by positivity
    calc _ ≤ (624 * Real.sqrt ε) ^ 2 :=
          (sq_le_sq₀ (norm_nonneg _) hnn).2 hnorm
      _ = 389376 * ε := by
          rw [mul_pow, Real.sq_sqrt hε]
          ring
  have h48 : (48 : ℝ) * 0 ^ 2 = 0 := by norm_num
  rw [h48, add_zero] at htrans
  refine le_trans htrans ?_
  linarith

/-! ## Reflections and the product transfer -/

/-- The tensor placement respects the adjoint. Formalization-only support for
`fact:add-a-proj`, blueprint `ch12_qpbt_games.tex:305-321`. -/
theorem heteroKron_conjTranspose {ιA ιB : Type*} (A : Op ιA) (B : Op ιB) :
    (heteroKron A B)ᴴ = heteroKron Aᴴ Bᴴ := by
  ext i j
  simp [heteroKron, Matrix.kronecker, Matrix.conjTranspose_apply]

/-- Placing an isometry on the first factor gives an isometry.
Formalization-only support for `fact:add-a-proj`, blueprint
`ch12_qpbt_games.tex:305-321`. -/
theorem heteroKron_left_isometry {ιA ιB : Type*} [DecidableEq ιA]
    [DecidableEq ιB] [Fintype ιA] [Fintype ιB] (A : Op ιA)
    (hA : Aᴴ * A = 1) :
    (heteroKron A (1 : Op ιB))ᴴ * heteroKron A 1 = 1 := by
  rw [heteroKron_conjTranspose, heteroKron_mul, hA, Matrix.conjTranspose_one,
    one_mul, heteroKron_one_one]

/-- Placing an isometry on the second factor gives an isometry.
Formalization-only support for `fact:add-a-proj`, blueprint
`ch12_qpbt_games.tex:305-321`. -/
theorem heteroKron_right_isometry {ιA ιB : Type*} [DecidableEq ιA]
    [DecidableEq ιB] [Fintype ιA] [Fintype ιB] (B : Op ιB)
    (hB : Bᴴ * B = 1) :
    (heteroKron (1 : Op ιA) B)ᴴ * heteroKron 1 B = 1 := by
  rw [heteroKron_conjTranspose, heteroKron_mul, hB, Matrix.conjTranspose_one,
    one_mul, heteroKron_one_one]

/-- The observable of a binary projective measurement is a reflection.
Formalization-only support for `lem:povm-to-obs`, blueprint
`ch14_qpbt_observables.tex:365-382`. -/
theorem obsOf_conjTranspose_mul_self {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : MIPStarRE.Quantum.Measurement (ZMod 2) ι)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) :
    (obsOf M)ᴴ * obsOf M = 1 := by
  have hsum : M.effect 0 + M.effect 1 = 1 := by
    have := M.sum_eq_one
    rwa [sum_over_zmodTwo] at this
  have h01 : M.effect 0 * M.effect 1 = 0 :=
    DistanceCalculus.projective_effect_mul_effect_eq_zero M hM (by decide)
  have h10 : M.effect 1 * M.effect 0 = 0 :=
    DistanceCalculus.projective_effect_mul_effect_eq_zero M hM (by decide)
  have hherm : (obsOf M)ᴴ = obsOf M := by
    rw [obsOf, Matrix.conjTranspose_sub]
    rw [(Matrix.nonneg_iff_posSemidef.mp (M.pos 0)).isHermitian.eq,
      (Matrix.nonneg_iff_posSemidef.mp (M.pos 1)).isHermitian.eq]
  rw [hherm, obsOf, sub_mul, mul_sub, mul_sub, h01, h10,
    (hM 0).isIdempotentElem.eq, (hM 1).isIdempotentElem.eq]
  rw [sub_zero, zero_sub, sub_neg_eq_add]
  exact hsum

/-- Transferring a product across the tensor factors costs the two individual
distances: if `A` on the first factor is close to `B` on the second and `C` on
the first is close to `D` on the second, then `A * C` on the first factor is
close to `D * B` on the second. The second factor's product is read in the
reversed order because the correspondence between the two factors determined by
the state is an antihomomorphism, so it carries a product of first-factor
operators to the product of their partners taken in the opposite order.

This is the isometry case of `fact:add-a-proj` applied twice and combined with
the triangle inequality; `fact:add-a-proj` itself is blueprint
`ch12_qpbt_games.tex:305-321`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:352-362`. -/
theorem norm_product_transfer_le {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB] (A C : Op ιA) (B D : Op ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB))
    (hA : (heteroKron A (1 : Op ιB))ᴴ * heteroKron A 1 = 1)
    (hD : (heteroKron (1 : Op ιA) D)ᴴ * heteroKron 1 D = 1) :
    ‖applyOperatorToState
        (heteroKron (A * C) (1 : Op ιB) - heteroKron 1 (D * B)) ψ‖ ≤
      ‖applyOperatorToState
        (heteroKron C (1 : Op ιB) - heteroKron 1 D) ψ‖ +
      ‖applyOperatorToState
        (heteroKron A (1 : Op ιB) - heteroKron 1 B) ψ‖ := by
  have hsplit : heteroKron (A * C) (1 : Op ιB) - heteroKron 1 (D * B) =
      heteroKron A 1 * (heteroKron C (1 : Op ιB) - heteroKron 1 D) +
        heteroKron 1 D * (heteroKron A (1 : Op ιB) - heteroKron 1 B) := by
    rw [mul_sub, mul_sub, heteroKron_mul, heteroKron_mul, heteroKron_mul,
      heteroKron_mul]
    simp only [mul_one, one_mul]
    abel
  rw [hsplit, MagicSquareRigidity.applyOperatorToState_add_op]
  refine le_trans (norm_add_le _ _) ?_
  rw [MagicSquareRigidity.norm_applyOperatorToState_isometry_mul hA,
    MagicSquareRigidity.norm_applyOperatorToState_isometry_mul hD]

/-! ## From the Magic Square variables to the point observables -/

/-- The signed sum of the effects of a binary measurement is its observable.
Formalization-only support for `lem:povm-to-obs`, blueprint
`ch14_qpbt_observables.tex:365-382`. -/
theorem sum_phaseSign_smul_effect_eq_obsOf {ι : Type*} [Fintype ι]
    [DecidableEq ι] (M : MIPStarRE.Quantum.Measurement (ZMod 2) ι) :
    ∑ b : ZMod 2, phaseSign b • M.effect b = obsOf M := by
  rw [sum_over_zmodTwo, obsOf]
  have hzero : phaseSign (0 : ZMod 2) = 1 := by simp [phaseSign]
  have hone : phaseSign (1 : ZMod 2) = -1 := by
    have h : (1 : ZMod 2) ≠ 0 := by decide
    simp [phaseSign, h]
  rw [hzero, hone, one_smul, neg_one_smul]
  abel

/-- The strategy point observable is the observable of the trace-coarse-grained
point measurement. This is `def:strategy-observables` read through
`lem:povm-to-obs`, paper
`14_analysis_of_the_pauli_basis_test.tex:174-190`, blueprint
`ch14_qpbt_observables.tex:573-610`. -/
theorem pointObs_eq_obsOf {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (side : PlayerSide) (W : PauliKind)
    (r : PauliScalar P) (u : Fin P.m → PauliScalar P) :
    S.pointObs side W r u = obsOf (S.pointTraceMeas side W u r) := by
  rw [pointObs_eq_traceMeas_obs, sum_phaseSign_smul_effect_eq_obsOf]

/-- The strategy point observable is a reflection. Paper
`14_analysis_of_the_pauli_basis_test.tex:174-190`, blueprint
`ch14_qpbt_observables.tex:573-610`. -/
theorem pointObs_conjTranspose_mul_self {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (side : PlayerSide) (W : PauliKind)
    (r : PauliScalar P) (u : Fin P.m → PauliScalar P) :
    (S.pointObs side W r u)ᴴ * S.pointObs side W r u = 1 := by
  rw [(S.pointObs_isHermitian side W r u).eq]
  exact S.pointObs_sq_eq_one side W r u

/-- Consistency of two oppositely placed binary measurements bounds the
operator distance of their observables. This is `lem:povm-to-obs` in the form
used by Equations `eq:lc-11a` and `eq:lc-11b`; the statement is generic in the
two tensor factors and the state. Paper
`14_analysis_of_the_pauli_basis_test.tex:342-348`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem obsDist_le_of_consistencyDefect {X ιL ιR : Type*}
    [Fintype X] [DecidableEq X] [Fintype ιL] [DecidableEq ιL]
    [Fintype ιR] [DecidableEq ιR] (μ : Distribution X)
    (M : X → MIPStarRE.Quantum.Measurement (ZMod 2) ιL)
    (N : X → MIPStarRE.Quantum.Measurement (ZMod 2) ιR)
    (χ : EuclideanSpace ℂ (ιL × ιR)) {c : ℝ}
    (h : consistencyDefect μ (fun x a => heteroKron ((M x).effect a) 1)
      (fun x a => heteroKron 1 ((N x).effect a)) χ ≤ c) :
    opDistSq μ (fun x => heteroKron (obsOf (M x)) (1 : Op ιR))
      (fun x => heteroKron (1 : Op ιL) (obsOf (N x))) χ ≤ 4 * c := by
  classical
  set A : X → MIPStarRE.Quantum.Measurement (ZMod 2) (ιL × ιR) := fun x =>
    DistanceCalculus.leftPlacedMeasurement (ιB := ιR) (M x) with hAdef
  set B : X → MIPStarRE.Quantum.Measurement (ZMod 2) (ιL × ιR) := fun x =>
    DistanceCalculus.rightPlacedMeasurement (ιA := ιL) (N x) with hBdef
  have hfam : opFamilyDistSq μ
      (fun x b => (A x).effect b) (fun x b => (B x).effect b) χ ≤ 2 * c :=
    opFamilyDistSq_placed_le_of_consistencyDefect_le μ M N χ h
  have hobs := povm_to_obs_of_measurements μ A B phaseSign norm_phaseSign χ
  have hleft : ∀ x, (∑ b : ZMod 2, phaseSign b • (A x).effect b) =
      heteroKron (obsOf (M x)) (1 : Op ιR) := by
    intro x
    rw [← sum_phaseSign_smul_effect_eq_obsOf, heteroKron_left_sum_smul]
    rfl
  have hright : ∀ x, (∑ b : ZMod 2, phaseSign b • (B x).effect b) =
      heteroKron (1 : Op ιL) (obsOf (N x)) := by
    intro x
    rw [← sum_phaseSign_smul_effect_eq_obsOf, heteroKron_right_sum_smul]
    rfl
  have hrw : opDistSq μ (fun x => heteroKron (obsOf (M x)) (1 : Op ιR))
      (fun x => heteroKron (1 : Op ιL) (obsOf (N x))) χ =
    opDistSq μ (fun x => ∑ b : ZMod 2, phaseSign b • (A x).effect b)
      (fun x => ∑ b : ZMod 2, phaseSign b • (B x).effect b) χ := by
    congr 1 <;> funext x
    · exact (hleft x).symm
    · exact (hright x).symm
  rw [hrw]
  have hcast : (Fintype.card (ZMod 2) : ℝ) = 2 := by simp
  calc
    _ ≤ (Fintype.card (ZMod 2) : ℝ) * opFamilyDistSq μ
        (fun x b => (A x).effect b) (fun x b => (B x).effect b) χ := hobs
    _ ≤ 2 * (2 * c) := by
      rw [hcast]
      exact mul_le_mul_of_nonneg_left hfam (by norm_num)
    _ = 4 * c := by ring

/-! ## The anticommuting half of the twisted commutation -/

/-- The unit-alphabet operator distance written as an average of squared
state-dependent norms. Formalization-only support for `def:povm-distance`,
blueprint `ch12_qpbt_games.tex:234-241`. -/
theorem opDistSq_eq_avgOver {X ι : Type*} [Fintype X] [DecidableEq X]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (M N : X → Op ι) (ψ : EuclideanSpace ℂ ι) :
    opDistSq μ M N ψ =
      avgOver μ (fun x => ‖applyOperatorToState (M x - N x) ψ‖ ^ 2) := by
  unfold opDistSq opFamilyDistSq
  simp

/-- Every strategy value is at most one. Formalization-only support for
`def:tensor-product-value`, blueprint `ch12_qpbt_games.tex:71-82`. -/
theorem strategy_value_le_one {G : Game} (S : Strategy G) : S.value ≤ 1 := by
  have h := rejectionMass_eq_one_sub_value S
  have hnn : (0 : ℝ) ≤ avgOver G.μ (fun questions =>
      outcomeEventWeight S questions.1 questions.2 fun a b =>
        G.decide questions.1 questions.2 a b = false) :=
    avgOver_nonneg _ _ (fun _ => outcome_event_weight_nonneg S _ _ _)
  rw [h] at hnn
  linarith

/-- The Magic Square value defect of a tuple is nonnegative and admissible as
an error parameter for the rigidity input. Formalization-only support for
`eq:qld-implication-ms-anticomm`, paper
`14_analysis_of_the_pauli_basis_test.tex:349-356`. -/
theorem msValueAt_defect_nonneg {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (ω : PauliTuple P) :
    0 ≤ 1 - S.msValueAt ω ∧
      1 - (1 - S.msValueAt ω) ≤ (S.msStrategyAt ω).value := by
  have hle := strategy_value_le_one (S.msStrategyAt ω)
  have heq : S.msValueAt ω = (S.msStrategyAt ω).value := rfl
  constructor
  · rw [heq]; linarith
  · rw [heq]; linarith

/-- The Magic Square variable observables induced by the test strategy at one
tuple approximately anticommute on Bob's factor, with error the tuple's Magic
Square defect. This is Equation `eq:qld-implication-ms-anticomm` before
averaging, paper `14_analysis_of_the_pauli_basis_test.tex:349-356`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem msVarBitObs_anticommutator_le {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (ω : PauliTuple P) :
    ‖applyOperatorToState
        (heteroKron (1 : Op S.toStrategy.ιA)
          (obsOf (S.msVarBitMeas .bob 0 ω) * obsOf (S.msVarBitMeas .bob 4 ω) +
            obsOf (S.msVarBitMeas .bob 4 ω) * obsOf (S.msVarBitMeas .bob 0 ω)))
        S.toStrategy.ψ‖ ^ 2 ≤ 1183680 * (1 - S.msValueAt ω) := by
  obtain ⟨hnn, hwin⟩ := msValueAt_defect_nonneg S ω
  exact msVarObs_anticommutator_le (S.msStrategyAt ω) (1 - S.msValueAt ω) hnn
    hwin

/-- The first-factor companion of the previous estimate: the Magic Square
variable observables of Alice approximately anticommute at one tuple. Paper
`14_analysis_of_the_pauli_basis_test.tex:349-356`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem msVarBitObsA_anticommutator_le {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (ω : PauliTuple P) :
    ‖applyOperatorToState
        (heteroKron
          (obsOf (S.msVarBitMeas .alice 0 ω) *
              obsOf (S.msVarBitMeas .alice 4 ω) +
            obsOf (S.msVarBitMeas .alice 4 ω) *
              obsOf (S.msVarBitMeas .alice 0 ω))
          (1 : Op S.toStrategy.ιB))
        S.toStrategy.ψ‖ ^ 2 ≤ 1183680 * (1 - S.msValueAt ω) := by
  obtain ⟨hnn, hwin⟩ := msValueAt_defect_nonneg S ω
  exact msVarObsA_anticommutator_le (S.msStrategyAt ω) (1 - S.msValueAt ω) hnn
    hwin

/-- The two point observables approximately anticommute once each of them is
close to a Magic Square variable observable on the opposite factor and those
two anticommute. This is the anticommuting half of Equation
`eq:pts-obs-commutation`, stated generically in the two tensor factors and the
state. Paper `14_analysis_of_the_pauli_basis_test.tex:342-362`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem obs_anticommutator_avg_le {P : AdmissibleParams} {ιL ιR : Type}
    [Fintype ιL] [DecidableEq ιL] [Fintype ιR] [DecidableEq ιR]
    (OX OZ : PauliTuple P → Op ιL) (V0 V4 : PauliTuple P → Op ιR)
    (χ : EuclideanSpace ℂ (ιL × ιR)) {cd cv : ℝ}
    (hOX : ∀ ω, (OX ω)ᴴ * OX ω = 1) (hOZ : ∀ ω, (OZ ω)ᴴ * OZ ω = 1)
    (hV0 : ∀ ω, (V0 ω)ᴴ * V0 ω = 1) (hV4 : ∀ ω, (V4 ω)ᴴ * V4 ω = 1)
    (h0 : avgOver (anticommTupleDist P) (fun ω => ‖applyOperatorToState
        (heteroKron (OX ω) (1 : Op ιR) -
          heteroKron (1 : Op ιL) (V0 ω)) χ‖ ^ 2) ≤ cd)
    (h4 : avgOver (anticommTupleDist P) (fun ω => ‖applyOperatorToState
        (heteroKron (OZ ω) (1 : Op ιR) -
          heteroKron (1 : Op ιL) (V4 ω)) χ‖ ^ 2) ≤ cd)
    (hv : avgOver (anticommTupleDist P) (fun ω => ‖applyOperatorToState
        (heteroKron (1 : Op ιL) (V0 ω * V4 ω + V4 ω * V0 ω)) χ‖ ^ 2) ≤ cv) :
    avgOver (anticommTupleDist P) (fun ω => ‖applyOperatorToState
      (heteroKron (OX ω * OZ ω) (1 : Op ιR) +
        heteroKron (OZ ω * OX ω) (1 : Op ιR)) χ‖ ^ 2) ≤
      24 * cd + 3 * cv := by
  classical
  have hpoint : ∀ ω : PauliTuple P,
      ‖applyOperatorToState
          (heteroKron (OX ω * OZ ω) (1 : Op ιR) +
            heteroKron (OZ ω * OX ω) (1 : Op ιR)) χ‖ ^ 2 ≤
        12 * ‖applyOperatorToState (heteroKron (OX ω) (1 : Op ιR) -
            heteroKron (1 : Op ιL) (V0 ω)) χ‖ ^ 2 +
        12 * ‖applyOperatorToState (heteroKron (OZ ω) (1 : Op ιR) -
            heteroKron (1 : Op ιL) (V4 ω)) χ‖ ^ 2 +
        3 * ‖applyOperatorToState
            (heteroKron (1 : Op ιL) (V0 ω * V4 ω + V4 ω * V0 ω)) χ‖ ^ 2 := by
    intro ω
    have h1 := norm_product_transfer_le (OX ω) (OZ ω) (V0 ω) (V4 ω) χ
      (heteroKron_left_isometry (OX ω) (hOX ω))
      (heteroKron_right_isometry (V4 ω) (hV4 ω))
    have h2 := norm_product_transfer_le (OZ ω) (OX ω) (V4 ω) (V0 ω) χ
      (heteroKron_left_isometry (OZ ω) (hOZ ω))
      (heteroKron_right_isometry (V0 ω) (hV0 ω))
    have hdecomp : heteroKron (OX ω * OZ ω) (1 : Op ιR) +
        heteroKron (OZ ω * OX ω) (1 : Op ιR) =
      (heteroKron (OX ω * OZ ω) (1 : Op ιR) -
          heteroKron (1 : Op ιL) (V4 ω * V0 ω)) +
        (heteroKron (OZ ω * OX ω) (1 : Op ιR) -
          heteroKron (1 : Op ιL) (V0 ω * V4 ω)) +
        heteroKron (1 : Op ιL) (V0 ω * V4 ω + V4 ω * V0 ω) := by
      rw [MagicSquareRigidity.heteroKron_add_right]
      abel
    set t1 : ℝ := ‖applyOperatorToState (heteroKron (OX ω) (1 : Op ιR) -
      heteroKron (1 : Op ιL) (V0 ω)) χ‖ with ht1
    set t2 : ℝ := ‖applyOperatorToState (heteroKron (OZ ω) (1 : Op ιR) -
      heteroKron (1 : Op ιL) (V4 ω)) χ‖ with ht2
    set t3 : ℝ := ‖applyOperatorToState
      (heteroKron (1 : Op ιL) (V0 ω * V4 ω + V4 ω * V0 ω)) χ‖ with ht3
    set t0 : ℝ := ‖applyOperatorToState (heteroKron (OX ω * OZ ω) (1 : Op ιR) +
      heteroKron (OZ ω * OX ω) (1 : Op ιR)) χ‖ with ht0
    have hsum : t0 ≤
        ‖applyOperatorToState (heteroKron (OX ω * OZ ω) (1 : Op ιR) -
            heteroKron (1 : Op ιL) (V4 ω * V0 ω)) χ‖ +
          ‖applyOperatorToState (heteroKron (OZ ω * OX ω) (1 : Op ιR) -
            heteroKron (1 : Op ιL) (V0 ω * V4 ω)) χ‖ + t3 := by
      rw [ht0, ht3, hdecomp, MagicSquareRigidity.applyOperatorToState_add_op,
        MagicSquareRigidity.applyOperatorToState_add_op]
      exact le_trans (norm_add_le _ _)
        (add_le_add (norm_add_le _ _) le_rfl)
    have ht0nn : (0 : ℝ) ≤ t0 := by rw [ht0]; exact norm_nonneg _
    have ht1nn : (0 : ℝ) ≤ t1 := by rw [ht1]; exact norm_nonneg _
    have ht2nn : (0 : ℝ) ≤ t2 := by rw [ht2]; exact norm_nonneg _
    have ht3nn : (0 : ℝ) ≤ t3 := by rw [ht3]; exact norm_nonneg _
    have hbound : t0 ≤ 2 * t1 + 2 * t2 + t3 := by linarith
    have key : t0 ^ 2 ≤ 12 * t1 ^ 2 + 12 * t2 ^ 2 + 3 * t3 ^ 2 := by
      nlinarith [hbound, ht0nn, ht1nn, ht2nn, ht3nn,
        sq_nonneg (t1 - t2), sq_nonneg (2 * t1 - t3), sq_nonneg (2 * t2 - t3)]
    rw [ht0, ht1, ht2, ht3] at key
    exact key
  calc
    _ ≤ avgOver (anticommTupleDist P) (fun ω =>
        12 * ‖applyOperatorToState (heteroKron (OX ω) (1 : Op ιR) -
            heteroKron (1 : Op ιL) (V0 ω)) χ‖ ^ 2 +
        12 * ‖applyOperatorToState (heteroKron (OZ ω) (1 : Op ιR) -
            heteroKron (1 : Op ιL) (V4 ω)) χ‖ ^ 2 +
        3 * ‖applyOperatorToState
          (heteroKron (1 : Op ιL) (V0 ω * V4 ω + V4 ω * V0 ω)) χ‖ ^ 2) :=
      avgOver_mono _ _ _ hpoint
    _ = 12 * avgOver (anticommTupleDist P) (fun ω =>
          ‖applyOperatorToState (heteroKron (OX ω) (1 : Op ιR) -
            heteroKron (1 : Op ιL) (V0 ω)) χ‖ ^ 2) +
        12 * avgOver (anticommTupleDist P) (fun ω =>
          ‖applyOperatorToState (heteroKron (OZ ω) (1 : Op ιR) -
            heteroKron (1 : Op ιL) (V4 ω)) χ‖ ^ 2) +
        3 * avgOver (anticommTupleDist P) (fun ω =>
          ‖applyOperatorToState
            (heteroKron (1 : Op ιL)
              (V0 ω * V4 ω + V4 ω * V0 ω)) χ‖ ^ 2) := by
      rw [avgOver_add, avgOver_add, avgOver_const_mul, avgOver_const_mul,
        avgOver_const_mul]
    _ ≤ 24 * cd + 3 * cv := by linarith

/-- The observable of a binary projective measurement obtained from a strategy
measurement by two postprocessings is a reflection. Formalization-only support
for `eq:qld-implication-ms-anticomm`, blueprint
`ch14_qpbt_observables.tex:761-794`. The projectivity of the underlying
strategy measurement is unfolded here because the corresponding named lemma,
`strategyMeasurement_isProjective`, is private at
`MIPStarRE/QPBT/Observables/Defs.lean:788`; promoting it is issue #204. -/
theorem msVarBitObs_conjTranspose_mul_self {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (side : PlayerSide) (j : Fin 9)
    (ω : PauliTuple P) :
    (obsOf (S.msVarBitMeas side j ω))ᴴ *
      obsOf (S.msVarBitMeas side j ω) = 1 := by
  refine obsOf_conjTranspose_mul_self (S.msVarBitMeas side j ω) ?_
  refine postprocess_isProjective _ (postprocess_isProjective _ ?_ _) _
  cases side with
  | alice => exact S.isProjective.1 _
  | bob => exact S.isProjective.2 _

/-- The observable of a trace-coarse-grained point measurement is a
reflection. Paper `14_analysis_of_the_pauli_basis_test.tex:174-190`,
blueprint `ch14_qpbt_observables.tex:573-610`. -/
theorem pointTraceObs_conjTranspose_mul_self {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (side : PlayerSide) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) (r : PauliScalar P) :
    (obsOf (S.pointTraceMeas side W u r))ᴴ *
      obsOf (S.pointTraceMeas side W u r) = 1 := by
  rw [← pointObs_eq_obsOf]
  exact pointObs_conjTranspose_mul_self S side W r u

/-- The point observables approximately anticommute on anticommuting tuples.
This is the anticommuting half of Equation `eq:pts-obs-commutation`, paper
`14_analysis_of_the_pauli_basis_test.tex:342-362`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem exists_pointObs_anticommutator_anticomm_le :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε), 0 ≤ ε →
      avgOver (anticommTupleDist P) (fun ω =>
        ‖applyOperatorToState
          (heteroKron (S.pointObs .alice .X ω.2.2.1 ω.1 *
              S.pointObs .alice .Z ω.2.2.2 ω.2.1) (1 : Op S.toStrategy.ιB) +
            heteroKron (S.pointObs .alice .Z ω.2.2.2 ω.2.1 *
              S.pointObs .alice .X ω.2.2.1 ω.1) (1 : Op S.toStrategy.ιB))
          S.toStrategy.ψ‖ ^ 2) ≤ C * ε := by
  classical
  obtain ⟨Cms, hCms, hms⟩ := win_ms_cons_proof
  obtain ⟨Cv, hCv, hv⟩ := win_magic_square_proof
  refine ⟨96 * Cms + 3551040 * Cv, by nlinarith, ?_⟩
  intro P ε S hε
  simp only [pointObs_eq_obsOf]
  have hdist : ∀ W : PauliKind,
      avgOver (anticommTupleDist P) (fun ω => ‖applyOperatorToState
        (heteroKron (ιA := S.toStrategy.ιA) (ιB := S.toStrategy.ιB)
            (obsOf (S.pointTraceMeas .alice W (selectedTuplePoint W ω)
              (selectedTupleScalar W ω))) 1 -
          heteroKron (ιA := S.toStrategy.ιA) (ιB := S.toStrategy.ιB) 1
            (obsOf (S.msVarBitMeas .bob (selectedMsVar W) ω)))
        S.toStrategy.ψ‖ ^ 2) ≤ 4 * (Cms * ε) := by
    intro W
    have h := obsDist_le_of_consistencyDefect
      (ιL := S.toStrategy.ιA) (ιR := S.toStrategy.ιB) (anticommTupleDist P)
      (fun ω => S.pointTraceMeas .alice W (selectedTuplePoint W ω)
        (selectedTupleScalar W ω))
      (fun ω => S.msVarBitMeas .bob (selectedMsVar W) ω) S.toStrategy.ψ
      (hms P ε S hε W)
    rw [opDistSq_eq_avgOver] at h
    exact h
  have hdefect : avgOver (anticommTupleDist P)
      (fun ω => 1 - S.msValueAt ω) ≤ Cv * ε := by
    have hprob := anticommTupleDist_isProbability P
    have hsplit : avgOver (anticommTupleDist P)
        (fun ω => 1 - S.msValueAt ω) =
        1 - avgOver (anticommTupleDist P) S.msValueAt := by
      rw [avgOver_sub, avgOver_const_of_isProbability _ hprob]
    rw [hsplit]
    exact le_of_abs_le (hv P ε S hε)
  have hmsavg : avgOver (anticommTupleDist P) (fun ω =>
      ‖applyOperatorToState
        (heteroKron (ιA := S.toStrategy.ιA) (ιB := S.toStrategy.ιB) 1
          (obsOf (S.msVarBitMeas .bob 0 ω) * obsOf (S.msVarBitMeas .bob 4 ω) +
            obsOf (S.msVarBitMeas .bob 4 ω) *
              obsOf (S.msVarBitMeas .bob 0 ω)))
        S.toStrategy.ψ‖ ^ 2) ≤ 1183680 * (Cv * ε) := by
    calc
      _ ≤ avgOver (anticommTupleDist P)
          (fun ω => 1183680 * (1 - S.msValueAt ω)) :=
        avgOver_mono _ _ _ (fun ω => msVarBitObs_anticommutator_le S ω)
      _ = 1183680 * avgOver (anticommTupleDist P)
          (fun ω => 1 - S.msValueAt ω) := avgOver_const_mul _ _ _
      _ ≤ 1183680 * (Cv * ε) :=
        mul_le_mul_of_nonneg_left hdefect (by norm_num)
  have hmain := obs_anticommutator_avg_le (ιL := S.toStrategy.ιA)
    (ιR := S.toStrategy.ιB)
    (fun ω => obsOf (S.pointTraceMeas .alice .X ω.1 ω.2.2.1))
    (fun ω => obsOf (S.pointTraceMeas .alice .Z ω.2.1 ω.2.2.2))
    (fun ω => obsOf (S.msVarBitMeas .bob 0 ω))
    (fun ω => obsOf (S.msVarBitMeas .bob 4 ω)) S.toStrategy.ψ
    (fun ω => pointTraceObs_conjTranspose_mul_self S .alice .X ω.1 ω.2.2.1)
    (fun ω => pointTraceObs_conjTranspose_mul_self S .alice .Z ω.2.1 ω.2.2.2)
    (fun ω => msVarBitObs_conjTranspose_mul_self S .bob 0 ω)
    (fun ω => msVarBitObs_conjTranspose_mul_self S .bob 4 ω)
    (hdist .X) (hdist .Z) hmsavg
  exact le_trans hmain (le_of_eq (by ring))

end WinImplications

end

end MIPStarRE.QPBT
