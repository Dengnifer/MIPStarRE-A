import MIPStarRE.QPBT.Test.MagicSquareTheorems.PerfectStrategy.Observables

/-!
# Measurements of the perfect Magic Square strategy

This module turns the operator table of `thm:ms-from-ac` into a measurement
family.  It forms the joint measurement of two commuting binary projective
measurements, records the post-processing identities for injective
relabellings, encodes a constraint answer as the parity triple determined by
two freely chosen bits, and assembles the nine cell measurements into the
Magic Square measurement family, closing with the multiplication rule relating
a constraint outcome to the outcomes of its incident variables.

## References

The source statement is `thm:ms-from-ac` in
`blueprint/src/chapter/ch13_qpbt_test.tex:257-267`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:654-722`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

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
def parityTriple (i : Fin 6) (ab : ZMod 2 × ZMod 2) : Fin 3 → ZMod 2 :=
  ![ab.1, ab.2, msParity i - ab.1 - ab.2]

private theorem parityTriple_injective (i : Fin 6) :
    Function.Injective (parityTriple i) := by
  intro ab cd h
  apply Prod.ext
  · exact congrFun h 0
  · exact congrFun h 1

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (`thm:ms-from-ac`, blueprint
`ch13_qpbt_test.tex:257-267`): the triple encoding two freely chosen bits sums
to the parity `msParity i` prescribed by the constraint. -/
theorem parityTriple_sum (i : Fin 6) (ab : ZMod 2 × ZMod 2) :
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
noncomputable def msCellMeasurement
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

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (`thm:ms-from-ac`, blueprint
`ch13_qpbt_test.tex:257-267`): each of the nine cell measurements of the Magic
Square strategy is projective. -/
theorem msCellMeasurement_projective
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

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (`thm:ms-from-ac`, blueprint
`ch13_qpbt_test.tex:257-267`): every effect of a cell measurement is symmetric
whenever `OA` and `OB` are symmetric. -/
theorem msCellMeasurement_transpose
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
noncomputable def msConstraintJoint
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
noncomputable def msStrategyMeasurement
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

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (`thm:ms-from-ac`, blueprint
`ch13_qpbt_test.tex:257-267`): on a variable question the global measurement
family reproduces the corresponding cell measurement: its effect at the answer
`bit b` is the effect of `P j` at `b`. -/
theorem msStrategyMeasurement_var_bit
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

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (`thm:ms-from-ac`, blueprint
`ch13_qpbt_test.tex:257-267`): on a variable question the global measurement
family assigns the zero effect to every answer outside the range of
`MsAnswer.bit`. -/
theorem msStrategyMeasurement_var_zero
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

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (`thm:ms-from-ac`, blueprint
`ch13_qpbt_test.tex:257-267`): on a constraint question the effect at the answer
triple encoding the bits `ab` equals the effect at `ab` of the joint measurement
of the first two cells of that constraint. -/
theorem msStrategyMeasurement_constraint_triple
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

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (`thm:ms-from-ac`, blueprint
`ch13_qpbt_test.tex:257-267`): on a constraint question the global measurement
family assigns the zero effect to every answer that is not a parity triple of
the constraint. -/
theorem msStrategyMeasurement_constraint_zero
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

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (`thm:ms-from-ac`, blueprint
`ch13_qpbt_test.tex:257-267`): the global Magic Square measurement family is
projective at every question. -/
theorem msStrategyMeasurement_projective
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

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (`thm:ms-from-ac`, blueprint
`ch13_qpbt_test.tex:257-267`): post-processing a measurement along a relabelling
of outcomes preserves symmetry of its effects. -/
theorem postprocess_effect_transpose
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

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (`thm:ms-from-ac`, blueprint
`ch13_qpbt_test.tex:257-267`): the effects of the joint measurement of the first
two cells of a constraint are symmetric whenever the underlying cell effects
are. -/
theorem msConstraintJoint_effect_transpose
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

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (`thm:ms-from-ac`, blueprint
`ch13_qpbt_test.tex:257-267`): multiplying a constraint effect at `ab` by the
effect of an incident cell measurement at `b` returns the constraint effect when
`b` is the bit that the parity triple assigns to that cell, and `0` otherwise;
this is the consistency of the constraint answer with its variable answers. -/
theorem msCellConstraintJoint_mul
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

end

end MIPStarRE.QPBT
