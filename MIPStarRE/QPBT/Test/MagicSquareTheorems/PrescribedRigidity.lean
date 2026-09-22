import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.PrescribedProducts

/-!
# Prescribed-answer Magic Square rigidity with separate errors

One witness extracts the state and Bob's variables from value alone. Alice's
variable comparisons have an additional linear agreement term. Both
prescribed anticommutators depend only on value, including on the ideal state.

## References

`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:620-646`,
`docs/paper-gaps/qpbt_ms-rigidity-symmetric-strategies.tex`, issue #701.
The unrestricted printed claim remains unasserted and refuted.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum MagicSquareRigidity

noncomputable section

/-- Alice's prescribed anticommutator transfers from the original state
to the ideal state with an additive norm cost of eight times the state error. -/
theorem ms_prescribed_anticommutator_distance_A_le (S : Strategy msGame)
    (w : MsRigidityWitness S) (ε s : ℝ) (hε : 0 ≤ ε) (hwin : 1 - ε ≤ S.value)
    (hs : ‖isometryTensor w.φA w.φB S.ψ - idealMsState w.aux‖ ≤ s) :
    msPrescribedAnticommutatorDistanceA S w ≤
      (1148 * Real.sqrt ε + 8 * s) ^ 2 := by
  let X := heteroKron (conjIsometry w.φA (obsOf ((S.A (.var 0)).postprocess msBitOrZero)))
    (1 : Op ((Fin 2 → ZMod 2) × w.ιB''))
  let Z := heteroKron (conjIsometry w.φA (obsOf ((S.A (.var 4)).postprocess msBitOrZero)))
    (1 : Op ((Fin 2 → ZMod 2) × w.ιB''))
  let R := heteroKron (conjIsometry w.φA (msWrongFormEffect (S.A (.var 0))))
    (1 : Op ((Fin 2 → ZMod 2) × w.ιB''))
  let T := heteroKron (conjIsometry w.φA (msWrongFormEffect (S.A (.var 4))))
    (1 : Op ((Fin 2 → ZMod 2) × w.ιB''))
  let K := (X - R) * (Z - T) + (Z - T) * (X - R)
  have hK (v : EuclideanSpace ℂ
      (((Fin 2 → ZMod 2) × w.ιA'') × ((Fin 2 → ZMod 2) × w.ιB''))) :
      ‖applyOperatorToState K v‖ ≤ 8 * ‖v‖ :=
    norm_anticommutator_sub_apply_le X Z R T v
      (conjTranspose_mul_le_one_leftTensor (conjTranspose_mul_le_one_conjIsometry _
        (conjTranspose_mul_le_one_of_obsOf _)))
      (conjTranspose_mul_le_one_leftTensor (conjTranspose_mul_le_one_conjIsometry _
        (conjTranspose_mul_le_one_of_obsOf _)))
      (conjTranspose_mul_le_one_leftTensor (conjTranspose_mul_le_one_conjIsometry _
        (conjTranspose_mul_le_one_of_effect
          ((S.A (.var 0)).postprocess wrongVariableAnswer) true)))
      (conjTranspose_mul_le_one_leftTensor (conjTranspose_mul_le_one_conjIsometry _
        (conjTranspose_mul_le_one_of_effect
          ((S.A (.var 4)).postprocess wrongVariableAnswer) true)))
  have he : K =
      heteroKron (conjIsometry w.φA
        (msPrescribedObservable (S.A (.var 0)) * msPrescribedObservable (S.A (.var 4)) +
          msPrescribedObservable (S.A (.var 4)) * msPrescribedObservable (S.A (.var 0))))
        (1 : Op ((Fin 2 → ZMod 2) × w.ιB'')) := by
    have hadd (M N : Op S.ιA) : conjIsometry w.φA (M + N) =
        conjIsometry w.φA M + conjIsometry w.φA N := by
      simp only [conjIsometry_eq, Matrix.add_mul, Matrix.mul_add]
    dsimp only [K, X, Z, R, T]
    simp only [ms_prescribed_observable_eq, ← heteroKron_sub_left, ← conjIsometry_sub,
      heteroKron_mul, one_mul, conjIsometry_mul, ← heteroKron_add_left, ← hadd]
    rfl
  have hu : ‖applyOperatorToState K (isometryTensor w.φA w.φB S.ψ)‖ ≤
      1148 * Real.sqrt ε := by
    rw [he, applyOperatorToState_leftTensor_conjIsometry, norm_isometryTensor]
    exact ms_prescribed_anticommutator_norm_A S ε hε hwin
  have hnorm : ‖applyOperatorToState K (idealMsState w.aux)‖ ≤
      1148 * Real.sqrt ε + 8 * s := by
    have hv : ‖idealMsState w.aux - isometryTensor w.φA w.φB S.ψ‖ ≤ s := by
      rwa [norm_sub_rev]
    have hd := hK (idealMsState w.aux - isometryTensor w.φA w.φB S.ψ)
    rw [applyOperatorToState_sub] at hd
    have hn := norm_sub_le (applyOperatorToState K (idealMsState w.aux) -
      applyOperatorToState K (isometryTensor w.φA w.φB S.ψ))
      (-applyOperatorToState K (isometryTensor w.φA w.φB S.ψ))
    simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at hn
    linarith
  have hdist : msPrescribedAnticommutatorDistanceA S w =
      ‖applyOperatorToState K (idealMsState w.aux)‖ ^ 2 := by
    simp only [msPrescribedAnticommutatorDistanceA, opDistSq_uniform_unit,
      sub_neg_eq_add, ms_prescribed_observable_eq, conjIsometry_sub,
      heteroKron_sub_left]
    rfl
  rw [hdist]
  exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2

/-- Bob's prescribed anticommutator transfers from the original state
to the ideal state with an additive norm cost of eight times the state error. -/
theorem ms_prescribed_anticommutator_distance_B_le (S : Strategy msGame)
    (w : MsRigidityWitness S) (ε s : ℝ) (hε : 0 ≤ ε) (hwin : 1 - ε ≤ S.value)
    (hs : ‖isometryTensor w.φA w.φB S.ψ - idealMsState w.aux‖ ≤ s) :
    msPrescribedAnticommutatorDistanceB S w ≤
      (1148 * Real.sqrt ε + 8 * s) ^ 2 := by
  let X := heteroKron (1 : Op ((Fin 2 → ZMod 2) × w.ιA''))
    (conjIsometry w.φB (obsOf ((S.B (.var 0)).postprocess msBitOrZero)))
  let Z := heteroKron (1 : Op ((Fin 2 → ZMod 2) × w.ιA''))
    (conjIsometry w.φB (obsOf ((S.B (.var 4)).postprocess msBitOrZero)))
  let R := heteroKron (1 : Op ((Fin 2 → ZMod 2) × w.ιA''))
    (conjIsometry w.φB (msWrongFormEffect (S.B (.var 0))))
  let T := heteroKron (1 : Op ((Fin 2 → ZMod 2) × w.ιA''))
    (conjIsometry w.φB (msWrongFormEffect (S.B (.var 4))))
  let K := (X - R) * (Z - T) + (Z - T) * (X - R)
  have hK (v : EuclideanSpace ℂ
      (((Fin 2 → ZMod 2) × w.ιA'') × ((Fin 2 → ZMod 2) × w.ιB''))) :
      ‖applyOperatorToState K v‖ ≤ 8 * ‖v‖ :=
    norm_anticommutator_sub_apply_le X Z R T v
      (conjTranspose_mul_le_one_rightTensor (conjTranspose_mul_le_one_conjIsometry _
        (conjTranspose_mul_le_one_of_obsOf _)))
      (conjTranspose_mul_le_one_rightTensor (conjTranspose_mul_le_one_conjIsometry _
        (conjTranspose_mul_le_one_of_obsOf _)))
      (conjTranspose_mul_le_one_rightTensor (conjTranspose_mul_le_one_conjIsometry _
        (conjTranspose_mul_le_one_of_effect
          ((S.B (.var 0)).postprocess wrongVariableAnswer) true)))
      (conjTranspose_mul_le_one_rightTensor (conjTranspose_mul_le_one_conjIsometry _
        (conjTranspose_mul_le_one_of_effect
          ((S.B (.var 4)).postprocess wrongVariableAnswer) true)))
  have he : K =
      heteroKron (1 : Op ((Fin 2 → ZMod 2) × w.ιA'')) (conjIsometry w.φB
        (msPrescribedObservable (S.B (.var 0)) * msPrescribedObservable (S.B (.var 4)) +
          msPrescribedObservable (S.B (.var 4)) * msPrescribedObservable (S.B (.var 0)))) := by
    have hadd (M N : Op S.ιB) : conjIsometry w.φB (M + N) =
        conjIsometry w.φB M + conjIsometry w.φB N := by
      simp only [conjIsometry_eq, Matrix.add_mul, Matrix.mul_add]
    dsimp only [K, X, Z, R, T]
    simp only [ms_prescribed_observable_eq, ← heteroKron_sub_right, ← conjIsometry_sub,
      heteroKron_mul, one_mul, conjIsometry_mul, ← heteroKron_add_right, ← hadd]
    rfl
  have hu : ‖applyOperatorToState K (isometryTensor w.φA w.φB S.ψ)‖ ≤
      1148 * Real.sqrt ε := by
    rw [he, applyOperatorToState_rightTensor_conjIsometry, norm_isometryTensor]
    exact ms_prescribed_anticommutator_norm_B S ε hε hwin
  have hnorm : ‖applyOperatorToState K (idealMsState w.aux)‖ ≤
      1148 * Real.sqrt ε + 8 * s := by
    have hv : ‖idealMsState w.aux - isometryTensor w.φA w.φB S.ψ‖ ≤ s := by
      rwa [norm_sub_rev]
    have hd := hK (idealMsState w.aux - isometryTensor w.φA w.φB S.ψ)
    rw [applyOperatorToState_sub] at hd
    have hn := norm_sub_le (applyOperatorToState K (idealMsState w.aux) -
      applyOperatorToState K (isometryTensor w.φA w.φB S.ψ))
      (-applyOperatorToState K (isometryTensor w.φA w.φB S.ψ))
    simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at hn
    linarith
  have hdist : msPrescribedAnticommutatorDistanceB S w =
      ‖applyOperatorToState K (idealMsState w.aux)‖ ^ 2 := by
    simp only [msPrescribedAnticommutatorDistanceB, opDistSq_uniform_unit,
      sub_neg_eq_add, ms_prescribed_observable_eq, conjIsometry_sub,
      heteroKron_sub_right]
    rfl
  rw [hdist]
  exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2

/-- All seven prescribed-answer estimates, with separate dependence on value
and agreement. The state error is Euclidean; all six operator errors are
squared state-dependent distances. The two Alice measurement bounds alone
contain agreement. This is a proved correction candidate, not an assertion
that the unrestricted printed theorem is true. -/
theorem exists_ms_prescribed_rigidity_separate_errors (S : Strategy msGame)
    (ε : ℝ) (hε : 0 ≤ ε) (hwin : 1 - ε ≤ S.value) :
    ∃ w : MsRigidityWitness S,
      ‖isometryTensor w.φA w.φB S.ψ - idealMsState w.aux‖ ≤ 155904 * Real.sqrt ε ∧
      (∀ W : PauliKind, msPrescribedOperatorDistanceB S w (msPauliCell W) W ≤
        5 * 10 ^ 12 * ε) ∧
      (∀ W : PauliKind, msPrescribedOperatorDistanceA S w (msPauliCell W) W ≤
        15 * 10 ^ 12 * ε + 6 * msVariableConsistencyDefect S (msPauliCell W)) ∧
      msPrescribedAnticommutatorDistanceA S w ≤ 4 * 10 ^ 12 * ε ∧
      msPrescribedAnticommutatorDistanceB S w ≤ 4 * 10 ^ 12 * ε := by
  obtain ⟨w, hs, hb, ha⟩ := exists_ms_prescribed_measurements_with_agreement S ε hε hwin
  refine ⟨w, hs, hb, ha, ?_, ?_⟩
  · have ht := ms_prescribed_anticommutator_distance_A_le S w ε _ hε hwin hs
    nlinarith only [ht, Real.sq_sqrt hε, hε]
  · have ht := ms_prescribed_anticommutator_distance_B_le S w ε _ hε hwin hs
    nlinarith only [ht, Real.sq_sqrt hε, hε]

/-- The prescribed-answer counterpart of the existing agreement-controlled
rigidity theorem, with all seven printed quantities and their norm conventions.

**Scope restriction:** The two completed-variable agreement bounds are extra
hypotheses relative to the refuted printed assertion. Their role and the
stronger separate-error theorem are recorded in
`docs/paper-gaps/qpbt_ms-rigidity-symmetric-strategies.tex`, issue #701.
Malformed answers and product transfers are derived internally from value. -/
theorem exists_ms_rigidity_prescribed_answers :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (ε δ : ℝ), 0 ≤ ε → 0 ≤ δ →
      ∀ S : Strategy msGame, 1 - ε ≤ S.value →
        msVariableConsistencyDefect S 0 ≤ δ → msVariableConsistencyDefect S 4 ≤ δ →
        ∃ w : MsRigidityWitness S,
          ‖isometryTensor w.φA w.φB S.ψ - idealMsState w.aux‖ ≤
            C * (Real.sqrt ε + Real.sqrt δ) ∧
          msPrescribedOperatorDistanceA S w 0 .X ≤ C * (Real.sqrt ε + Real.sqrt δ) ∧
          msPrescribedOperatorDistanceA S w 4 .Z ≤ C * (Real.sqrt ε + Real.sqrt δ) ∧
          msPrescribedOperatorDistanceB S w 0 .X ≤ C * (Real.sqrt ε + Real.sqrt δ) ∧
          msPrescribedOperatorDistanceB S w 4 .Z ≤ C * (Real.sqrt ε + Real.sqrt δ) ∧
          msPrescribedAnticommutatorDistanceA S w ≤ C * (Real.sqrt ε + Real.sqrt δ) ∧
          msPrescribedAnticommutatorDistanceB S w ≤ C * (Real.sqrt ε + Real.sqrt δ) := by
  refine ⟨2 * 10 ^ 13, by norm_num, fun ε δ hε hδ S hwin hd0 hd4 => ?_⟩
  have hv : 0 ≤ S.value := by
    unfold Strategy.value
    apply avgOver_nonneg
    intro xy
    apply Finset.sum_nonneg
    intro a _
    apply Finset.sum_nonneg
    intro b _
    split
    · exact outcomeWeight_nonneg S xy.1 xy.2 a b
    · exact le_rfl
  have he : 0 ≤ min ε 1 := le_min hε zero_le_one
  have hw : 1 - min ε 1 ≤ S.value := by
    by_cases h : ε ≤ 1
    · simpa only [min_eq_left h] using hwin
    · simpa only [min_eq_right (le_of_not_ge h), sub_self] using hv
  have heroot : Real.sqrt (min ε 1) ≤ Real.sqrt ε := Real.sqrt_le_sqrt (min_le_left _ _)
  have hele : min ε 1 ≤ Real.sqrt ε := by
    have hsq := Real.sq_sqrt he
    have hroot := Real.sqrt_nonneg (min ε 1)
    have hcap := min_le_right ε (1 : ℝ)
    nlinarith
  have hdefect (j : Fin 9) : msVariableConsistencyDefect S j ≤ 8 :=
    opFamilyDistSq_uniform_unit_binary_le _ _ _ S.ψ_norm
      (fun b => conjTranspose_mul_le_one_leftTensor
        (conjTranspose_mul_le_one_of_effect ((S.A (.var j)).postprocess msBitOrZero) b))
      (fun b => conjTranspose_mul_le_one_rightTensor
        (conjTranspose_mul_le_one_of_effect ((S.B (.var j)).postprocess msBitOrZero) b))
  have hdroot (j : Fin 9) (hj : msVariableConsistencyDefect S j ≤ δ) :
      msVariableConsistencyDefect S j ≤ 8 * Real.sqrt δ := by
    by_cases h : δ ≤ 1
    · nlinarith [Real.sq_sqrt hδ, Real.sqrt_nonneg δ]
    · have hh := Real.sqrt_le_sqrt (le_of_not_ge h)
      rw [Real.sqrt_one] at hh
      nlinarith [hdefect j]
  obtain ⟨w, hs, hb, ha, hacA, hacB⟩ :=
    exists_ms_prescribed_rigidity_separate_errors S (min ε 1) he hw
  have hA0 := ha .X
  have hA4 := ha .Z
  have hB0 := hb .X
  have hB4 := hb .Z
  simp only [msPauliCell] at hA0 hA4 hB0 hB4
  have hse := Real.sqrt_nonneg ε
  have hsd := Real.sqrt_nonneg δ
  refine ⟨w, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith [hdroot 0 hd0]
  · nlinarith [hdroot 4 hd4]
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith

end

end MIPStarRE.QPBT
