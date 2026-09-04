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
`blueprint/src/chapter/ch14_qpbt_observables.tex:683-733`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:342-362`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace WinImplications

/-! ## Reading the dilation back on the original space -/

/-- The right tensor placement is additive in its right factor.
Formalization-only support for `thm:ms-rigidity`, blueprint
`ch13_qpbt_test.tex:224-253`. -/
theorem heteroKron_add_right {ιA ιB : Type*} (A : Op ιA) (M N : Op ιB) :
    heteroKron A M + heteroKron A N = heteroKron A (M + N) := by
  ext i j
  simp [heteroKron, Matrix.kronecker, mul_add]

/-- The matrix of the identity isometry is the identity matrix.
Formalization-only support for `thm:ms-rigidity`, blueprint
`ch13_qpbt_test.tex:224-253`. -/
theorem isometryMatrix_id {ι : Type} [Fintype ι] [DecidableEq ι] :
    MagicSquareRigidity.isometryMatrix
      (LinearIsometry.id (R := ℂ) (E := EuclideanSpace ℂ ι)) = 1 := by
  ext k i
  rw [MagicSquareRigidity.isometryMatrix_apply]
  simp [Matrix.one_apply, EuclideanSpace.equiv]

/-- Conjugation by the identity isometry is the identity. Formalization-only
support for `thm:ms-rigidity`, blueprint `ch13_qpbt_test.tex:224-253`. -/
theorem conjIsometry_id {ι : Type} [Fintype ι] [DecidableEq ι] (M : Op ι) :
    conjIsometry (LinearIsometry.id (R := ℂ) (E := EuclideanSpace ℂ ι)) M = M := by
  rw [MagicSquareRigidity.conjIsometry_eq, isometryMatrix_id]
  simp

/-- The two-sided identity isometry fixes every bipartite state.
Formalization-only support for `thm:ms-rigidity`, blueprint
`ch13_qpbt_test.tex:224-253`. -/
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
for `thm:ms-rigidity`, blueprint `ch13_qpbt_test.tex:224-253`. -/
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
`thm:ms-rigidity`, blueprint `ch13_qpbt_test.tex:224-253`. -/
theorem naimarkInflation_add {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (M N : Op ι) :
    MagicSquareRigidity.naimarkInflation (α := α) M +
        MagicSquareRigidity.naimarkInflation (α := α) N =
      MagicSquareRigidity.naimarkInflation (α := α) (M + N) := by
  ext p q
  by_cases h : p.2 = none ∧ q.2 = none <;> simp [h]

/-- An operator inflated on the second factor acts on the dilated state exactly
as the original operator acts on the original state. Formalization-only support
for `thm:ms-rigidity`, blueprint `ch13_qpbt_test.tex:224-253`. -/
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
`ch13_qpbt_test.tex:224-253`. -/
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
totalized variable measurements on the dilated strategy. -/
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
`ch13_qpbt_test.tex:224-253` and `ch14_qpbt_observables.tex:683-733`. -/
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
      heteroKron_add_right, naimarkInflation_add]
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

/-! ## Reflections and the product transfer -/

/-- The tensor placement respects the adjoint. Formalization-only support for
`fact:add-a-proj`, blueprint `ch12_qpbt_games.tex:339-350`. -/
theorem heteroKron_conjTranspose {ιA ιB : Type*} (A : Op ιA) (B : Op ιB) :
    (heteroKron A B)ᴴ = heteroKron Aᴴ Bᴴ := by
  ext i j
  simp [heteroKron, Matrix.kronecker, Matrix.conjTranspose_apply]

/-- Placing an isometry on the first factor gives an isometry.
Formalization-only support for `fact:add-a-proj`, blueprint
`ch12_qpbt_games.tex:339-350`. -/
theorem heteroKron_left_isometry {ιA ιB : Type*} [DecidableEq ιA]
    [DecidableEq ιB] [Fintype ιA] [Fintype ιB] (A : Op ιA)
    (hA : Aᴴ * A = 1) :
    (heteroKron A (1 : Op ιB))ᴴ * heteroKron A 1 = 1 := by
  rw [heteroKron_conjTranspose, heteroKron_mul, hA, Matrix.conjTranspose_one,
    one_mul, heteroKron_one_one]

/-- Placing an isometry on the second factor gives an isometry.
Formalization-only support for `fact:add-a-proj`, blueprint
`ch12_qpbt_games.tex:339-350`. -/
theorem heteroKron_right_isometry {ιA ιB : Type*} [DecidableEq ιA]
    [DecidableEq ιB] [Fintype ιA] [Fintype ιB] (B : Op ιB)
    (hB : Bᴴ * B = 1) :
    (heteroKron (1 : Op ιA) B)ᴴ * heteroKron 1 B = 1 := by
  rw [heteroKron_conjTranspose, heteroKron_mul, hB, Matrix.conjTranspose_one,
    one_mul, heteroKron_one_one]

/-- The observable of a binary projective measurement is a reflection.
Formalization-only support for `lem:povm-to-obs`, blueprint
`ch14_qpbt_observables.tex:361-378`. -/
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
distances, with the second factor's product read in the reversed order. This is
`fact:add-a-proj`, blueprint `ch12_qpbt_games.tex:339-350`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:352-362`; the reversed
order records that the transfer map is an antihomomorphism. -/
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

/-- The signed sum of the effects of a binary measurement is its observable. -/
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

/-- On anticommuting tuples, Alice's point observable is close to Bob's Magic
Square variable observable. This is Equations `eq:lc-11a` and `eq:lc-11b`,
paper `14_analysis_of_the_pauli_basis_test.tex:342-348`, blueprint
`ch14_qpbt_observables.tex:683-733`. -/
theorem exists_pointObs_msVarObs_dist_le :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε), 0 ≤ ε →
      ∀ W : PauliKind,
      opDistSq (anticommTupleDist P)
        (fun ω => heteroKron (S.pointObs .alice W
          (selectedTupleScalar W ω) (selectedTuplePoint W ω))
          (1 : Op S.toStrategy.ιB))
        (fun ω => heteroKron (1 : Op S.toStrategy.ιA)
          (obsOf (S.msVarBitMeas .bob (selectedMsVar W) ω)))
        S.toStrategy.ψ ≤ C * ε := by
  classical
  obtain ⟨Cms, hCms, hms⟩ := win_ms_cons_proof
  refine ⟨4 * Cms, by linarith, ?_⟩
  intro P ε S hε W
  set μ := anticommTupleDist P with hμ
  set A : PauliTuple P →
      MIPStarRE.Quantum.Measurement (ZMod 2)
        (S.toStrategy.ιA × S.toStrategy.ιB) := fun ω =>
    DistanceCalculus.leftPlacedMeasurement (ιB := S.toStrategy.ιB)
      (S.pointTraceMeas .alice W (selectedTuplePoint W ω)
        (selectedTupleScalar W ω)) with hAdef
  set B : PauliTuple P →
      MIPStarRE.Quantum.Measurement (ZMod 2)
        (S.toStrategy.ιA × S.toStrategy.ιB) := fun ω =>
    DistanceCalculus.rightPlacedMeasurement (ιA := S.toStrategy.ιA)
      (S.msVarBitMeas .bob (selectedMsVar W) ω) with hBdef
  have hfam : opFamilyDistSq μ
      (fun ω b => (A ω).effect b) (fun ω b => (B ω).effect b)
      S.toStrategy.ψ ≤ 2 * (Cms * ε) :=
    opFamilyDistSq_placed_le_of_consistencyDefect_le μ
      (fun ω => S.pointTraceMeas .alice W (selectedTuplePoint W ω)
        (selectedTupleScalar W ω))
      (fun ω => S.msVarBitMeas .bob (selectedMsVar W) ω) S.toStrategy.ψ
      (hms P ε S hε W)
  have hobs := povm_to_obs_of_measurements μ A B phaseSign norm_phaseSign
    S.toStrategy.ψ
  have hleft : ∀ ω,
      (∑ b : ZMod 2, phaseSign b • (A ω).effect b) =
        heteroKron (S.pointObs .alice W (selectedTupleScalar W ω)
          (selectedTuplePoint W ω)) (1 : Op S.toStrategy.ιB) := by
    intro ω
    rw [pointObs_eq_traceMeas_obs, heteroKron_left_sum_smul]
    rfl
  have hright : ∀ ω,
      (∑ b : ZMod 2, phaseSign b • (B ω).effect b) =
        heteroKron (1 : Op S.toStrategy.ιA)
          (obsOf (S.msVarBitMeas .bob (selectedMsVar W) ω)) := by
    intro ω
    rw [← sum_phaseSign_smul_effect_eq_obsOf, heteroKron_right_sum_smul]
    rfl
  have hrw : opDistSq μ
      (fun ω => heteroKron (S.pointObs .alice W (selectedTupleScalar W ω)
        (selectedTuplePoint W ω)) (1 : Op S.toStrategy.ιB))
      (fun ω => heteroKron (1 : Op S.toStrategy.ιA)
        (obsOf (S.msVarBitMeas .bob (selectedMsVar W) ω)))
      S.toStrategy.ψ =
    opDistSq μ (fun ω => ∑ b : ZMod 2, phaseSign b • (A ω).effect b)
      (fun ω => ∑ b : ZMod 2, phaseSign b • (B ω).effect b)
      S.toStrategy.ψ := by
    congr 1 <;> funext ω
    · exact (hleft ω).symm
    · exact (hright ω).symm
  rw [hrw]
  have hcast : (Fintype.card (ZMod 2) : ℝ) = 2 := by simp
  calc
    _ ≤ (Fintype.card (ZMod 2) : ℝ) * opFamilyDistSq μ
        (fun ω b => (A ω).effect b) (fun ω b => (B ω).effect b)
        S.toStrategy.ψ := hobs
    _ ≤ 2 * (2 * (Cms * ε)) := by
      rw [hcast]
      exact mul_le_mul_of_nonneg_left hfam (by norm_num)
    _ = 4 * Cms * ε := by ring

/-! ## The anticommuting half of the twisted commutation -/

/-- The unit-alphabet operator distance written as an average of squared
state-dependent norms. Formalization-only support for `def:povm-distance`,
blueprint `ch12_qpbt_games.tex:219-226`. -/
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

/-- The Magic Square variable observables induced by the test strategy at one
tuple approximately anticommute, with error the tuple's Magic Square defect.
This is Equation `eq:qld-implication-ms-anticomm` before averaging, paper
`14_analysis_of_the_pauli_basis_test.tex:349-356`, blueprint
`ch14_qpbt_observables.tex:683-733`. -/
theorem msVarBitObs_anticommutator_le {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (ω : PauliTuple P) :
    ‖applyOperatorToState
        (heteroKron (1 : Op S.toStrategy.ιA)
          (obsOf (S.msVarBitMeas .bob 0 ω) * obsOf (S.msVarBitMeas .bob 4 ω) +
            obsOf (S.msVarBitMeas .bob 4 ω) * obsOf (S.msVarBitMeas .bob 0 ω)))
        S.toStrategy.ψ‖ ^ 2 ≤ 1183680 * (1 - S.msValueAt ω) := by
  have hle := strategy_value_le_one (S.msStrategyAt ω)
  have hnn : (0 : ℝ) ≤ 1 - S.msValueAt ω := by
    have : S.msValueAt ω = (S.msStrategyAt ω).value := rfl
    rw [this]
    linarith
  have hwin : 1 - (1 - S.msValueAt ω) ≤ (S.msStrategyAt ω).value := by
    have : S.msValueAt ω = (S.msStrategyAt ω).value := rfl
    rw [this]
    linarith
  exact msVarObs_anticommutator_le (S.msStrategyAt ω) (1 - S.msValueAt ω) hnn
    hwin

/-- The point observables approximately anticommute on anticommuting tuples.
This is the anticommuting half of Equation `eq:pts-obs-commutation`, paper
`14_analysis_of_the_pauli_basis_test.tex:342-362`, blueprint
`ch14_qpbt_observables.tex:683-733`. -/
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
  obtain ⟨Cd, hCd, hd⟩ := exists_pointObs_msVarObs_dist_le
  obtain ⟨Cv, hCv, hv⟩ := win_magic_square_proof
  refine ⟨24 * Cd + 3551040 * Cv, by nlinarith, ?_⟩
  intro P ε S hε
  set ιA := S.toStrategy.ιA with hιA
  set ιB := S.toStrategy.ιB with hιB
  set μ := anticommTupleDist P with hμ
  have hpoint : ∀ ω : PauliTuple P,
      ‖applyOperatorToState
          (heteroKron (S.pointObs .alice .X ω.2.2.1 ω.1 *
              S.pointObs .alice .Z ω.2.2.2 ω.2.1) (1 : Op ιB) +
            heteroKron (S.pointObs .alice .Z ω.2.2.2 ω.2.1 *
              S.pointObs .alice .X ω.2.2.1 ω.1) (1 : Op ιB))
          S.toStrategy.ψ‖ ^ 2 ≤
        12 * ‖applyOperatorToState
            (heteroKron (ιA := ιA) (ιB := ιB)
                (S.pointObs .alice .X ω.2.2.1 ω.1) 1 -
              heteroKron (ιA := ιA) (ιB := ιB) 1
                (obsOf (S.msVarBitMeas .bob 0 ω))) S.toStrategy.ψ‖ ^ 2 +
        12 * ‖applyOperatorToState
            (heteroKron (ιA := ιA) (ιB := ιB)
                (S.pointObs .alice .Z ω.2.2.2 ω.2.1) 1 -
              heteroKron (ιA := ιA) (ιB := ιB) 1
                (obsOf (S.msVarBitMeas .bob 4 ω))) S.toStrategy.ψ‖ ^ 2 +
        3 * ‖applyOperatorToState
            (heteroKron (ιA := ιA) (ιB := ιB) 1
              (obsOf (S.msVarBitMeas .bob 0 ω) *
                  obsOf (S.msVarBitMeas .bob 4 ω) +
                obsOf (S.msVarBitMeas .bob 4 ω) *
                  obsOf (S.msVarBitMeas .bob 0 ω))) S.toStrategy.ψ‖ ^ 2 := by
    intro ω
    set X : Op ιA := S.pointObs .alice .X ω.2.2.1 ω.1 with hX
    set Z : Op ιA := S.pointObs .alice .Z ω.2.2.2 ω.2.1 with hZ
    set V0 : Op ιB := obsOf (S.msVarBitMeas .bob 0 ω) with hV0
    set V4 : Op ιB := obsOf (S.msVarBitMeas .bob 4 ω) with hV4
    have hXh : Xᴴ = X := (S.pointObs_isHermitian .alice .X ω.2.2.1 ω.1).eq
    have hZh : Zᴴ = Z := (S.pointObs_isHermitian .alice .Z ω.2.2.2 ω.2.1).eq
    have hXref : Xᴴ * X = 1 := by
      rw [hXh]
      exact S.pointObs_sq_eq_one .alice .X ω.2.2.1 ω.1
    have hZref : Zᴴ * Z = 1 := by
      rw [hZh]
      exact S.pointObs_sq_eq_one .alice .Z ω.2.2.2 ω.2.1
    have hV0ref : V0ᴴ * V0 = 1 :=
      obsOf_conjTranspose_mul_self (S.msVarBitMeas .bob 0 ω)
        (postprocess_isProjective _ (postprocess_isProjective _
          (S.isProjective.2 _) _) _)
    have hV4ref : V4ᴴ * V4 = 1 :=
      obsOf_conjTranspose_mul_self (S.msVarBitMeas .bob 4 ω)
        (postprocess_isProjective _ (postprocess_isProjective _
          (S.isProjective.2 _) _) _)
    have h1 := norm_product_transfer_le X Z V0 V4 S.toStrategy.ψ
      (heteroKron_left_isometry X hXref) (heteroKron_right_isometry V4 hV4ref)
    have h2 := norm_product_transfer_le Z X V4 V0 S.toStrategy.ψ
      (heteroKron_left_isometry Z hZref) (heteroKron_right_isometry V0 hV0ref)
    have hdecomp : heteroKron (ιA := ιA) (ιB := ιB) (X * Z) 1 +
        heteroKron (ιA := ιA) (ιB := ιB) (Z * X) 1 =
      (heteroKron (ιA := ιA) (ιB := ιB) (X * Z) 1 -
          heteroKron (ιA := ιA) (ιB := ιB) 1 (V4 * V0)) +
        (heteroKron (ιA := ιA) (ιB := ιB) (Z * X) 1 -
          heteroKron (ιA := ιA) (ιB := ιB) 1 (V0 * V4)) +
        heteroKron (ιA := ιA) (ιB := ιB) 1 (V0 * V4 + V4 * V0) := by
      rw [← heteroKron_add_right]
      abel
    set t1 : ℝ := ‖applyOperatorToState
      (heteroKron (ιA := ιA) (ιB := ιB) X 1 -
        heteroKron (ιA := ιA) (ιB := ιB) 1 V0) S.toStrategy.ψ‖ with ht1
    set t2 : ℝ := ‖applyOperatorToState
      (heteroKron (ιA := ιA) (ιB := ιB) Z 1 -
        heteroKron (ιA := ιA) (ιB := ιB) 1 V4) S.toStrategy.ψ‖ with ht2
    set t3 : ℝ := ‖applyOperatorToState
      (heteroKron (ιA := ιA) (ιB := ιB) 1 (V0 * V4 + V4 * V0))
      S.toStrategy.ψ‖ with ht3
    set t0 : ℝ := ‖applyOperatorToState
      (heteroKron (ιA := ιA) (ιB := ιB) (X * Z) 1 +
        heteroKron (ιA := ιA) (ιB := ιB) (Z * X) 1) S.toStrategy.ψ‖ with ht0
    have hsum : t0 ≤
        ‖applyOperatorToState (heteroKron (ιA := ιA) (ιB := ιB) (X * Z) 1 -
            heteroKron (ιA := ιA) (ιB := ιB) 1 (V4 * V0)) S.toStrategy.ψ‖ +
          ‖applyOperatorToState (heteroKron (ιA := ιA) (ιB := ιB) (Z * X) 1 -
            heteroKron (ιA := ιA) (ιB := ιB) 1 (V0 * V4)) S.toStrategy.ψ‖ +
          t3 := by
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
  have hdX : avgOver μ (fun ω => ‖applyOperatorToState
      (heteroKron (ιA := ιA) (ιB := ιB)
          (S.pointObs .alice .X ω.2.2.1 ω.1) 1 -
        heteroKron (ιA := ιA) (ιB := ιB) 1
          (obsOf (S.msVarBitMeas .bob 0 ω))) S.toStrategy.ψ‖ ^ 2) ≤
      Cd * ε := by
    have h := hd P ε S hε .X
    rw [opDistSq_eq_avgOver] at h
    exact h
  have hdZ : avgOver μ (fun ω => ‖applyOperatorToState
      (heteroKron (ιA := ιA) (ιB := ιB)
          (S.pointObs .alice .Z ω.2.2.2 ω.2.1) 1 -
        heteroKron (ιA := ιA) (ιB := ιB) 1
          (obsOf (S.msVarBitMeas .bob 4 ω))) S.toStrategy.ψ‖ ^ 2) ≤
      Cd * ε := by
    have h := hd P ε S hε .Z
    rw [opDistSq_eq_avgOver] at h
    exact h
  have hdefect : avgOver μ (fun ω => 1 - S.msValueAt ω) ≤ Cv * ε := by
    have hprob := anticommTupleDist_isProbability P
    have hsplit : avgOver μ (fun ω => 1 - S.msValueAt ω) =
        1 - avgOver μ S.msValueAt := by
      rw [avgOver_sub, avgOver_const_of_isProbability μ hprob]
    rw [hsplit]
    exact le_of_abs_le (hv P ε S hε)
  have hms : avgOver μ (fun ω => ‖applyOperatorToState
      (heteroKron (ιA := ιA) (ιB := ιB) 1
        (obsOf (S.msVarBitMeas .bob 0 ω) * obsOf (S.msVarBitMeas .bob 4 ω) +
          obsOf (S.msVarBitMeas .bob 4 ω) * obsOf (S.msVarBitMeas .bob 0 ω)))
      S.toStrategy.ψ‖ ^ 2) ≤ 1183680 * (Cv * ε) := by
    calc
      _ ≤ avgOver μ (fun ω => 1183680 * (1 - S.msValueAt ω)) := by
        apply avgOver_mono
        intro ω
        exact msVarBitObs_anticommutator_le S ω
      _ = 1183680 * avgOver μ (fun ω => 1 - S.msValueAt ω) :=
        avgOver_const_mul _ _ _
      _ ≤ 1183680 * (Cv * ε) :=
        mul_le_mul_of_nonneg_left hdefect (by norm_num)
  calc
    _ ≤ avgOver μ (fun ω =>
        12 * ‖applyOperatorToState
            (heteroKron (ιA := ιA) (ιB := ιB)
                (S.pointObs .alice .X ω.2.2.1 ω.1) 1 -
              heteroKron (ιA := ιA) (ιB := ιB) 1
                (obsOf (S.msVarBitMeas .bob 0 ω))) S.toStrategy.ψ‖ ^ 2 +
        12 * ‖applyOperatorToState
            (heteroKron (ιA := ιA) (ιB := ιB)
                (S.pointObs .alice .Z ω.2.2.2 ω.2.1) 1 -
              heteroKron (ιA := ιA) (ιB := ιB) 1
                (obsOf (S.msVarBitMeas .bob 4 ω))) S.toStrategy.ψ‖ ^ 2 +
        3 * ‖applyOperatorToState
            (heteroKron (ιA := ιA) (ιB := ιB) 1
              (obsOf (S.msVarBitMeas .bob 0 ω) *
                  obsOf (S.msVarBitMeas .bob 4 ω) +
                obsOf (S.msVarBitMeas .bob 4 ω) *
                  obsOf (S.msVarBitMeas .bob 0 ω))) S.toStrategy.ψ‖ ^ 2) :=
      avgOver_mono _ _ _ hpoint
    _ = 12 * avgOver μ (fun ω => ‖applyOperatorToState
            (heteroKron (ιA := ιA) (ιB := ιB)
                (S.pointObs .alice .X ω.2.2.1 ω.1) 1 -
              heteroKron (ιA := ιA) (ιB := ιB) 1
                (obsOf (S.msVarBitMeas .bob 0 ω))) S.toStrategy.ψ‖ ^ 2) +
        12 * avgOver μ (fun ω => ‖applyOperatorToState
            (heteroKron (ιA := ιA) (ιB := ιB)
                (S.pointObs .alice .Z ω.2.2.2 ω.2.1) 1 -
              heteroKron (ιA := ιA) (ιB := ιB) 1
                (obsOf (S.msVarBitMeas .bob 4 ω))) S.toStrategy.ψ‖ ^ 2) +
        3 * avgOver μ (fun ω => ‖applyOperatorToState
            (heteroKron (ιA := ιA) (ιB := ιB) 1
              (obsOf (S.msVarBitMeas .bob 0 ω) *
                  obsOf (S.msVarBitMeas .bob 4 ω) +
                obsOf (S.msVarBitMeas .bob 4 ω) *
                  obsOf (S.msVarBitMeas .bob 0 ω))) S.toStrategy.ψ‖ ^ 2) := by
      rw [avgOver_add, avgOver_add, avgOver_const_mul, avgOver_const_mul,
        avgOver_const_mul]
    _ ≤ (24 * Cd + 3551040 * Cv) * ε := by nlinarith [hdX, hdZ, hms]

end WinImplications

end

end MIPStarRE.QPBT
