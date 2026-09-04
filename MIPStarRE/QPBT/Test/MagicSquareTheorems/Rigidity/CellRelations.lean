import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.Reflections

/-!
# The Magic Square cell relations on the dilated strategy

Every question of the projectively dilated Magic Square strategy carries a
complete projective measurement, so each binary relabelling of its answers
produces a reflection.  Three reflections are attached to a constraint question,
one for each cell of the row or column, and one reflection is attached to each
variable question; the three reflections of a constraint commute exactly and
their product, in any order, is the reflection of the sum of the three reported
bits.  Reflections of the two players commute exactly.

The value-to-parity relations are converted here into operator estimates on the
dilated state, with explicit constants: the six row and column products are
close to the sign prescribed by the corresponding linear equation, and the two
reflections that the two players attach to a common cell are close to each
other.  The two logical Pauli pairs are the reflections at the cells labelled by
the paper's first and fifth variables.

## References

The statement supported here is `thm:ms-rigidity` in
`blueprint/src/chapter/ch13_qpbt_test.tex:224-253`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`,
proved in Coladangelo--Stark, arXiv:1709.09267v2, Theorem 6.9.  The variable and
constraint indices are zero-based, so the paper's first and fifth variables are
the cells `0` and `4`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-! ## Deviation of a sign observable from a comparison observable -/

/-- The sign of a binary value is `1` or `-1`. -/
theorem bit_sign_eq_one_or_neg_one (b : ZMod 2) : bitSign b = 1 ∨ bitSign b = -1 := by
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) b with h | h <;> rw [h]
  · left
    norm_num [bitSign]
  · right
    norm_num [bitSign, ZMod.val_one]

/-- The sign is injective on binary values. -/
theorem bit_sign_injective : Function.Injective bitSign := by
  intro b c hbc
  by_contra hne
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) b with hb | hb <;>
    rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) c with hc | hc
  · exact hne (hb.trans hc.symm)
  · rw [hb, hc] at hbc
    norm_num [bitSign, ZMod.val_one] at hbc
  · rw [hb, hc] at hbc
    norm_num [bitSign, ZMod.val_one] at hbc
  · exact hne (hb.trans hc.symm)

section SignDefect

variable {G : Game}

/-- Two sign observables of the two players, placed on the composite space,
differ in the state-dependent norm by at most twice the square root of the Born
mass of the answer pairs on which the two labels disagree.  This is the estimate
that turns every mass of the value-to-parity layer into an operator relation of
`thm:ms-rigidity`, blueprint `ch13_qpbt_test.tex:224-253`. -/
theorem norm_alice_sub_bob_signObs_sq_le (T : Strategy G) (x : G.QuestionA)
    (y : G.QuestionB) (hA : MIPStarRE.QPBT.Measurement.IsProjective (T.A x))
    (hB : MIPStarRE.QPBT.Measurement.IsProjective (T.B y))
    (f : G.AnswerA → ZMod 2) (g : G.AnswerB → ZMod 2) :
    ‖applyOperatorToState (heteroKron (signObs (T.A x) f) 1 -
        heteroKron 1 (signObs (T.B y) g)) T.ψ‖ ^ 2 ≤
      4 * outcomeEventWeight T x y (fun a b => f a ≠ g b) := by
  classical
  have hAone : (1 : Op T.ιA) = ∑ a, (1 : ℂ) • (T.A x).effect a := by
    simpa using smul_one_eq_sum_smul_effect (T.A x) (1 : ℂ)
  have hBone : (1 : Op T.ιB) = ∑ b, (1 : ℂ) • (T.B y).effect b := by
    simpa using smul_one_eq_sum_smul_effect (T.B y) (1 : ℂ)
  have hexpand : heteroKron (signObs (T.A x) f) 1 - heteroKron 1 (signObs (T.B y) g) =
      ∑ a, ∑ b, ((bitSign (f a) - bitSign (g b) : ℝ) : ℂ) •
        heteroKron ((T.A x).effect a) ((T.B y).effect b) := by
    rw [signObs, signObs]
    nth_rewrite 1 [hBone]
    nth_rewrite 1 [hAone]
    rw [joint_expand, joint_expand, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← sub_smul]
    congr 1
    push_cast
    ring
  rw [hexpand]
  refine norm_apply_joint_defect_sq_le T x y hA hB
    (fun a b => bitSign (f a) - bitSign (g b)) (fun a b => f a ≠ g b) ?_ ?_
  · intro a b
    rcases bit_sign_eq_one_or_neg_one (f a) with h1 | h1 <;>
      rcases bit_sign_eq_one_or_neg_one (g b) with h2 | h2 <;>
        simp only [h1, h2] <;> norm_num
  · intro a b hab
    rw [not_not] at hab
    rw [hab, sub_self]

/-- Alice's sign observable deviates from a constant sign by at most twice the
square root of the mass of the answers carrying the other label. -/
theorem norm_alice_signObs_sub_const_sq_le (T : Strategy G) (x : G.QuestionA)
    (y : G.QuestionB) (hA : MIPStarRE.QPBT.Measurement.IsProjective (T.A x))
    (hB : MIPStarRE.QPBT.Measurement.IsProjective (T.B y))
    (f : G.AnswerA → ZMod 2) (c : ZMod 2) :
    ‖applyOperatorToState (heteroKron (signObs (T.A x) f) 1 -
        ((bitSign c : ℝ) : ℂ) • (1 : Op (T.ιA × T.ιB))) T.ψ‖ ^ 2 ≤
      4 * aliceEventWeight T x (fun a => f a ≠ c) := by
  classical
  have hconst : heteroKron (1 : Op T.ιA) (signObs (T.B y) (fun _ => c)) =
      ((bitSign c : ℝ) : ℂ) • (1 : Op (T.ιA × T.ιB)) := by
    rw [signObs, ← smul_one_eq_sum_smul_effect (T.B y) (((bitSign c : ℝ) : ℂ)),
      heteroKron_smul_right, heteroKron_one_one]
  have h := norm_alice_sub_bob_signObs_sq_le T x y hA hB f (fun _ => c)
  rw [hconst] at h
  refine le_trans h (le_of_eq ?_)
  congr 1
  exact outcome_event_weight_left_eq T x y (fun a => f a ≠ c)

/-- Bob's sign observable deviates from a constant sign by at most twice the
square root of the mass of the answers carrying the other label. -/
theorem norm_bob_signObs_sub_const_sq_le (T : Strategy G) (x : G.QuestionA)
    (y : G.QuestionB) (hA : MIPStarRE.QPBT.Measurement.IsProjective (T.A x))
    (hB : MIPStarRE.QPBT.Measurement.IsProjective (T.B y))
    (g : G.AnswerB → ZMod 2) (c : ZMod 2) :
    ‖applyOperatorToState (((bitSign c : ℝ) : ℂ) • (1 : Op (T.ιA × T.ιB)) -
        heteroKron 1 (signObs (T.B y) g)) T.ψ‖ ^ 2 ≤
      4 * bobEventWeight T y (fun b => c ≠ g b) := by
  classical
  have hconst : heteroKron (signObs (T.A x) (fun _ => c)) (1 : Op T.ιB) =
      ((bitSign c : ℝ) : ℂ) • (1 : Op (T.ιA × T.ιB)) := by
    rw [signObs, ← smul_one_eq_sum_smul_effect (T.A x) (((bitSign c : ℝ) : ℂ)),
      heteroKron_smul_left, heteroKron_one_one]
  have h := norm_alice_sub_bob_signObs_sq_le T x y hA hB (fun _ => c) g
  rw [hconst] at h
  refine le_trans h (le_of_eq ?_)
  congr 1
  exact outcome_event_weight_right_eq T x y (fun b => c ≠ g b)

end SignDefect

/-! ## Comparison of Born masses with the game error -/

/-- Formalization-only: a squared state-dependent bound by four times a mass
which is itself bounded by `36 * ε` yields closeness at scale `12 * sqrt ε`. -/
private theorem normCloseOn_of_sq_le {ι : Type} [Fintype ι] [DecidableEq ι]
    {ψ : EuclideanSpace ℂ ι} {M N : Op ι} {m ε : ℝ}
    (hsq : ‖applyOperatorToState (M - N) ψ‖ ^ 2 ≤ 4 * m) (hm0 : 0 ≤ m)
    (hm : m ≤ 36 * ε) : NormCloseOn ψ (12 * Real.sqrt ε) M N := by
  have hε : (0 : ℝ) ≤ ε := by
    have h36 : (0 : ℝ) ≤ 36 * ε := le_trans hm0 hm
    linarith
  have hbound : ‖applyOperatorToState (M - N) ψ‖ ^ 2 ≤ (12 * Real.sqrt ε) ^ 2 := by
    have hsq' : (12 * Real.sqrt ε) ^ 2 = 144 * ε := by
      rw [mul_pow, Real.sq_sqrt hε]
      ring
    rw [hsq']
    linarith
  calc ‖applyOperatorToState (M - N) ψ‖
      = Real.sqrt (‖applyOperatorToState (M - N) ψ‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((12 * Real.sqrt ε) ^ 2) := Real.sqrt_le_sqrt hbound
    _ = 12 * Real.sqrt ε := Real.sqrt_sq (by positivity)

/-- Formalization-only: monotonicity of Alice's marginal event mass. -/
private theorem alice_event_weight_mono (T : Strategy msGame) (x : MsType)
    (E F : MsAnswer → Prop) [DecidablePred E] [DecidablePred F]
    (h : ∀ a, E a → F a) : aliceEventWeight T x E ≤ aliceEventWeight T x F := by
  rw [← outcome_event_weight_left_eq T x x E, ← outcome_event_weight_left_eq T x x F]
  exact outcome_event_weight_mono T x x _ _ fun a _ ha => h a ha

/-- Formalization-only: monotonicity of Bob's marginal event mass. -/
private theorem bob_event_weight_mono (T : Strategy msGame) (y : MsType)
    (E F : MsAnswer → Prop) [DecidablePred E] [DecidablePred F]
    (h : ∀ b, E b → F b) : bobEventWeight T y E ≤ bobEventWeight T y F := by
  rw [← outcome_event_weight_right_eq T y y E, ← outcome_event_weight_right_eq T y y F]
  exact outcome_event_weight_mono T y y _ _ fun _ b hb => h b hb

/-! ## The Magic Square reflections of the dilated strategy -/

/-- Alice's cell reflection at one position of a constraint question of the
dilated strategy, placed on its composite space.  This is a pre-isometry
observable of `msDilatedStrategy S`; the state-dependent relations below
evaluate it on `(msDilatedStrategy S).ψ`.  It is not the paper's post-isometry
operator $\tilde A$.  The post-isometry operators on the ideal state in
`thm:ms-rigidity` arise later by conjugating with the local isometries and using
the transfer theorems of issue #104.  Formalization-only operator-relation
support for blueprint `ch13_qpbt_test.tex:224-253` and paper
`08_classical_and_quantum_low_degree_tests.tex:612-652`. -/
noncomputable def msCellObsA (S : Strategy msGame) (i : Fin 6) (k : Fin 3) :
    Op ((msDilatedStrategy S).ιA × (msDilatedStrategy S).ιB) :=
  heteroKron (signObs ((msDilatedStrategy S).A (MsType.constraint i))
    (constraintBitOrZero k)) 1

/-- Bob's cell reflection at one position of a constraint question of the
dilated strategy, placed on its composite space.  This is a pre-isometry
observable of `msDilatedStrategy S`; the state-dependent relations below
evaluate it on `(msDilatedStrategy S).ψ`.  It is not the paper's post-isometry
operator $\tilde B$.  The post-isometry operators on the ideal state in
`thm:ms-rigidity` arise later by conjugating with the local isometries and using
the transfer theorems of issue #104.  Formalization-only operator-relation
support for blueprint `ch13_qpbt_test.tex:224-253` and paper
`08_classical_and_quantum_low_degree_tests.tex:612-652`. -/
noncomputable def msCellObsB (S : Strategy msGame) (i : Fin 6) (k : Fin 3) :
    Op ((msDilatedStrategy S).ιA × (msDilatedStrategy S).ιB) :=
  heteroKron 1 (signObs ((msDilatedStrategy S).B (MsType.constraint i))
    (constraintBitOrZero k))

/-- Alice's reflection at a variable question of the dilated strategy, placed on
the composite space. -/
noncomputable def msVarObsA (S : Strategy msGame) (j : Fin 9) :
    Op ((msDilatedStrategy S).ιA × (msDilatedStrategy S).ιB) :=
  heteroKron (signObs ((msDilatedStrategy S).A (MsType.var j)) msBitOrZero) 1

/-- Bob's reflection at a variable question of the dilated strategy, placed on
the composite space. -/
noncomputable def msVarObsB (S : Strategy msGame) (j : Fin 9) :
    Op ((msDilatedStrategy S).ιA × (msDilatedStrategy S).ιB) :=
  heteroKron 1 (signObs ((msDilatedStrategy S).B (MsType.var j)) msBitOrZero)

/-- Alice's variable reflection is the observable of the binary measurement
obtained from her variable question by folding malformed answers to zero. -/
theorem msVarObsA_eq_obsOf (S : Strategy msGame) (j : Fin 9) :
    msVarObsA S j =
      heteroKron (obsOf (((msDilatedStrategy S).A (MsType.var j)).postprocess msBitOrZero))
        1 := by
  rw [msVarObsA, signObs_eq_obsOf_postprocess]

/-- Bob's variable reflection is the observable of the binary measurement
obtained from his variable question by folding malformed answers to zero. -/
theorem msVarObsB_eq_obsOf (S : Strategy msGame) (j : Fin 9) :
    msVarObsB S j =
      heteroKron 1
        (obsOf (((msDilatedStrategy S).B (MsType.var j)).postprocess msBitOrZero)) := by
  rw [msVarObsB, signObs_eq_obsOf_postprocess]

/-- Alice's cell operators are binary observables. -/
theorem isBinaryObservable_msCellObsA (S : Strategy msGame) (i : Fin 6) (k : Fin 3) :
    IsBinaryObservable (msCellObsA S i k) :=
  isBinaryObservable_heteroKron_one
    (isBinaryObservable_signObs _ (msDilatedStrategy_isProjective_A S _) _)

/-- Bob's cell operators are binary observables. -/
theorem isBinaryObservable_msCellObsB (S : Strategy msGame) (i : Fin 6) (k : Fin 3) :
    IsBinaryObservable (msCellObsB S i k) :=
  isBinaryObservable_one_heteroKron
    (isBinaryObservable_signObs _ (msDilatedStrategy_isProjective_B S _) _)

/-- Alice's variable operators are binary observables. -/
theorem isBinaryObservable_msVarObsA (S : Strategy msGame) (j : Fin 9) :
    IsBinaryObservable (msVarObsA S j) :=
  isBinaryObservable_heteroKron_one
    (isBinaryObservable_signObs _ (msDilatedStrategy_isProjective_A S _) _)

/-- Bob's variable operators are binary observables. -/
theorem isBinaryObservable_msVarObsB (S : Strategy msGame) (j : Fin 9) :
    IsBinaryObservable (msVarObsB S j) :=
  isBinaryObservable_one_heteroKron
    (isBinaryObservable_signObs _ (msDilatedStrategy_isProjective_B S _) _)

/-- The three cell reflections of one constraint question commute exactly. -/
theorem msCellObsA_comm (S : Strategy msGame) (i : Fin 6) (k l : Fin 3) :
    msCellObsA S i k * msCellObsA S i l = msCellObsA S i l * msCellObsA S i k := by
  rw [msCellObsA, msCellObsA, heteroKron_mul, heteroKron_mul,
    signObs_comm _ (msDilatedStrategy_isProjective_A S _)]

/-- The three cell reflections of one constraint question commute exactly, on
Bob's side as well. -/
theorem msCellObsB_comm (S : Strategy msGame) (i : Fin 6) (k l : Fin 3) :
    msCellObsB S i k * msCellObsB S i l = msCellObsB S i l * msCellObsB S i k := by
  rw [msCellObsB, msCellObsB, heteroKron_mul, heteroKron_mul,
    signObs_comm _ (msDilatedStrategy_isProjective_B S _)]

/-- Alice's cell reflection commutes exactly with Bob's variable reflection. -/
theorem msCellObsA_comm_msVarObsB (S : Strategy msGame) (i : Fin 6) (k : Fin 3)
    (j : Fin 9) :
    msCellObsA S i k * msVarObsB S j = msVarObsB S j * msCellObsA S i k :=
  heteroKron_comm _ _

/-- Alice's variable reflection commutes exactly with Bob's cell reflection. -/
theorem msVarObsA_comm_msCellObsB (S : Strategy msGame) (j : Fin 9) (i : Fin 6)
    (k : Fin 3) :
    msVarObsA S j * msCellObsB S i k = msCellObsB S i k * msVarObsA S j :=
  heteroKron_comm _ _

/-- Alice's cell reflection commutes exactly with Bob's cell reflection. -/
theorem msCellObsA_comm_msCellObsB (S : Strategy msGame) (i : Fin 6) (k : Fin 3)
    (i' : Fin 6) (k' : Fin 3) :
    msCellObsA S i k * msCellObsB S i' k' = msCellObsB S i' k' * msCellObsA S i k :=
  heteroKron_comm _ _

/-- Alice's variable reflection commutes exactly with Bob's variable
reflection. -/
theorem msVarObsA_comm_msVarObsB (S : Strategy msGame) (j j' : Fin 9) :
    msVarObsA S j * msVarObsB S j' = msVarObsB S j' * msVarObsA S j :=
  heteroKron_comm _ _

/-! ## The six row and column product relations -/

/-- The sum of the three answer bits reported for a constraint question, with
malformed answers contributing zero. -/
def constraintBitSum (a : MsAnswer) : ZMod 2 :=
  constraintBitOrZero 0 a + constraintBitOrZero 1 a + constraintBitOrZero 2 a

/-- An answer whose three reported bits do not sum to the prescribed parity is a
parity failure in the sense of the value-to-parity layer. -/
theorem constraintParityFailure_of_bitSum_ne (i : Fin 6) (a : MsAnswer)
    (h : constraintBitSum a ≠ msParity i) : ConstraintParityFailure i a := by
  cases a with
  | bit γ => exact wrong_constraint_answer_implies_parity_failure i (MsAnswer.bit γ) rfl
  | triple β =>
      intro hprod
      apply h
      have hsum : bitSign (∑ k : Fin 3, β k) = bitSign (msParity i) := by
        rw [bit_sign_sum_fin_three]
        exact hprod
      have hbit := bit_sign_injective hsum
      rw [Fin.sum_univ_three] at hbit
      exact hbit

/-- The product of Alice's three cell reflections of a constraint question is
the reflection attached to the sum of the three reported bits. -/
theorem msCellObsA_prod (S : Strategy msGame) (i : Fin 6) :
    msCellObsA S i 0 * msCellObsA S i 1 * msCellObsA S i 2 =
      heteroKron (signObs ((msDilatedStrategy S).A (MsType.constraint i))
        constraintBitSum) 1 := by
  rw [msCellObsA, msCellObsA, msCellObsA, heteroKron_mul, heteroKron_mul,
    signObs_mul _ (msDilatedStrategy_isProjective_A S _),
    signObs_mul _ (msDilatedStrategy_isProjective_A S _), mul_one, one_mul]
  rfl

/-- The product of Bob's three cell reflections of a constraint question is the
reflection attached to the sum of the three reported bits. -/
theorem msCellObsB_prod (S : Strategy msGame) (i : Fin 6) :
    msCellObsB S i 0 * msCellObsB S i 1 * msCellObsB S i 2 =
      heteroKron 1 (signObs ((msDilatedStrategy S).B (MsType.constraint i))
        constraintBitSum) := by
  rw [msCellObsB, msCellObsB, msCellObsB, heteroKron_mul, heteroKron_mul,
    signObs_mul _ (msDilatedStrategy_isProjective_B S _),
    signObs_mul _ (msDilatedStrategy_isProjective_B S _), mul_one, one_mul]
  rfl

/-- Formalization-only: nonnegativity of Alice's marginal event mass. -/
private theorem alice_event_weight_nonneg (T : Strategy msGame) (x : MsType)
    (E : MsAnswer → Prop) [DecidablePred E] : 0 ≤ aliceEventWeight T x E := by
  rw [← outcome_event_weight_left_eq T x x E]
  exact outcome_event_weight_nonneg T x x _

/-- Formalization-only: nonnegativity of Bob's marginal event mass. -/
private theorem bob_event_weight_nonneg (T : Strategy msGame) (y : MsType)
    (E : MsAnswer → Prop) [DecidablePred E] : 0 ≤ bobEventWeight T y E := by
  rw [← outcome_event_weight_right_eq T y y E]
  exact outcome_event_weight_nonneg T y y _

/-- Each of the six row and column relations holds for Alice's cell reflections
on the dilated state, with the sign prescribed by the corresponding linear
equation and with error `12 * sqrt ε`.  This is the first operator consequence
of `thm:ms-rigidity`, blueprint `ch13_qpbt_test.tex:224-253`. -/
theorem msCellObsA_prod_close (S : Strategy msGame) (ε : ℝ) (hwin : 1 - ε ≤ S.value)
    (i : Fin 6) :
    NormCloseOn (msDilatedStrategy S).ψ (12 * Real.sqrt ε)
      (msCellObsA S i 0 * msCellObsA S i 1 * msCellObsA S i 2)
      (((bitSign (msParity i) : ℝ) : ℂ) • 1) := by
  classical
  have hsq := norm_alice_signObs_sub_const_sq_le (msDilatedStrategy S)
    (MsType.constraint i) (MsType.constraint i)
    (msDilatedStrategy_isProjective_A S _) (msDilatedStrategy_isProjective_B S _)
    constraintBitSum (msParity i)
  rw [← msCellObsA_prod] at hsq
  refine normCloseOn_of_sq_le hsq (alice_event_weight_nonneg _ _ _) ?_
  calc aliceEventWeight (msDilatedStrategy S) (MsType.constraint i)
        (fun a => constraintBitSum a ≠ msParity i)
      ≤ aliceEventWeight (msDilatedStrategy S) (MsType.constraint i)
          (ConstraintParityFailure i) :=
        alice_event_weight_mono _ _ _ _ fun a ha =>
          constraintParityFailure_of_bitSum_ne i a ha
    _ = aliceParityFailureMass S i := ms_dilated_strategy_alice_parity_failure_mass S i
    _ ≤ 36 * ε := alice_parity_failure_mass_le S ε hwin i

/-- Each of the six row and column relations holds for Bob's cell reflections on
the dilated state, with the sign prescribed by the corresponding linear equation
and with error `12 * sqrt ε`. -/
theorem msCellObsB_prod_close (S : Strategy msGame) (ε : ℝ) (hwin : 1 - ε ≤ S.value)
    (i : Fin 6) :
    NormCloseOn (msDilatedStrategy S).ψ (12 * Real.sqrt ε)
      (((bitSign (msParity i) : ℝ) : ℂ) • 1)
      (msCellObsB S i 0 * msCellObsB S i 1 * msCellObsB S i 2) := by
  classical
  have hsq := norm_bob_signObs_sub_const_sq_le (msDilatedStrategy S)
    (MsType.constraint i) (MsType.constraint i)
    (msDilatedStrategy_isProjective_A S _) (msDilatedStrategy_isProjective_B S _)
    constraintBitSum (msParity i)
  rw [← msCellObsB_prod] at hsq
  refine normCloseOn_of_sq_le hsq (bob_event_weight_nonneg _ _ _) ?_
  calc bobEventWeight (msDilatedStrategy S) (MsType.constraint i)
        (fun b => msParity i ≠ constraintBitSum b)
      ≤ bobEventWeight (msDilatedStrategy S) (MsType.constraint i)
          (ConstraintParityFailure i) :=
        bob_event_weight_mono _ _ _ _ fun b hb =>
          constraintParityFailure_of_bitSum_ne i b (Ne.symm hb)
    _ = bobParityFailureMass S i := ms_dilated_strategy_bob_parity_failure_mass S i
    _ ≤ 36 * ε := bob_parity_failure_mass_le S ε hwin i

/-! ## Agreement of the two reflections attached to a common cell -/

/-- Alice's cell reflection agrees, on the dilated state and up to
`12 * sqrt ε`, with Bob's reflection at the same cell. -/
theorem msCellObsA_close_msVarObsB (S : Strategy msGame) (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) (i : Fin 6) (k : Fin 3) :
    NormCloseOn (msDilatedStrategy S).ψ (12 * Real.sqrt ε) (msCellObsA S i k)
      (msVarObsB S (msConstraintVars i k)) := by
  classical
  have hsq := norm_alice_sub_bob_signObs_sq_le (msDilatedStrategy S)
    (MsType.constraint i) (MsType.var (msConstraintVars i k))
    (msDilatedStrategy_isProjective_A S _) (msDilatedStrategy_isProjective_B S _)
    (constraintBitOrZero k) msBitOrZero
  refine normCloseOn_of_sq_le hsq (outcome_event_weight_nonneg _ _ _ _) ?_
  calc outcomeEventWeight (msDilatedStrategy S) (MsType.constraint i)
        (MsType.var (msConstraintVars i k))
        (fun a b => constraintBitOrZero k a ≠ msBitOrZero b)
      = forwardCellMismatchMass S i k :=
        ms_dilated_strategy_forward_cell_mismatch_mass S i k
    _ ≤ 36 * ε := forward_cell_mismatch_mass_le S ε hwin i k

/-- Alice's variable reflection agrees, on the dilated state and up to
`12 * sqrt ε`, with Bob's reflection at the same cell read from a constraint
question. -/
theorem msVarObsA_close_msCellObsB (S : Strategy msGame) (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) (i : Fin 6) (k : Fin 3) :
    NormCloseOn (msDilatedStrategy S).ψ (12 * Real.sqrt ε)
      (msVarObsA S (msConstraintVars i k)) (msCellObsB S i k) := by
  classical
  have hsq := norm_alice_sub_bob_signObs_sq_le (msDilatedStrategy S)
    (MsType.var (msConstraintVars i k)) (MsType.constraint i)
    (msDilatedStrategy_isProjective_A S _) (msDilatedStrategy_isProjective_B S _)
    msBitOrZero (constraintBitOrZero k)
  refine normCloseOn_of_sq_le hsq (outcome_event_weight_nonneg _ _ _ _) ?_
  calc outcomeEventWeight (msDilatedStrategy S) (MsType.var (msConstraintVars i k))
        (MsType.constraint i) (fun a b => msBitOrZero a ≠ constraintBitOrZero k b)
      = reverseCellMismatchMass S i k :=
        ms_dilated_strategy_reverse_cell_mismatch_mass S i k
    _ ≤ 36 * ε := reverse_cell_mismatch_mass_le S ε hwin i k

/-! ## Permuted row and column products -/

/-- The product of Alice's three cell reflections of a constraint question, in
any order in which the three positions occur once each, is the reflection
attached to the sum of the three reported bits. -/
theorem msCellObsA_prod_of (S : Strategy msGame) (i : Fin 6) (k₀ k₁ k₂ : Fin 3)
    (hsum : ∀ a, constraintBitOrZero k₀ a + constraintBitOrZero k₁ a +
      constraintBitOrZero k₂ a = constraintBitSum a) :
    msCellObsA S i k₀ * msCellObsA S i k₁ * msCellObsA S i k₂ =
      heteroKron (signObs ((msDilatedStrategy S).A (MsType.constraint i))
        constraintBitSum) 1 := by
  have hkey : signObs ((msDilatedStrategy S).A (MsType.constraint i))
        (constraintBitOrZero k₀) *
      signObs ((msDilatedStrategy S).A (MsType.constraint i)) (constraintBitOrZero k₁) *
      signObs ((msDilatedStrategy S).A (MsType.constraint i)) (constraintBitOrZero k₂) =
      signObs ((msDilatedStrategy S).A (MsType.constraint i)) constraintBitSum := by
    rw [signObs_mul _ (msDilatedStrategy_isProjective_A S _),
      signObs_mul _ (msDilatedStrategy_isProjective_A S _)]
    congr 1
    funext a
    exact hsum a
  rw [msCellObsA, msCellObsA, msCellObsA, heteroKron_mul, heteroKron_mul]
  simp only [mul_one]
  rw [hkey]

/-- The product of Bob's three cell reflections of a constraint question, in any
order in which the three positions occur once each, is the reflection attached
to the sum of the three reported bits. -/
theorem msCellObsB_prod_of (S : Strategy msGame) (i : Fin 6) (k₀ k₁ k₂ : Fin 3)
    (hsum : ∀ a, constraintBitOrZero k₀ a + constraintBitOrZero k₁ a +
      constraintBitOrZero k₂ a = constraintBitSum a) :
    msCellObsB S i k₀ * msCellObsB S i k₁ * msCellObsB S i k₂ =
      heteroKron 1 (signObs ((msDilatedStrategy S).B (MsType.constraint i))
        constraintBitSum) := by
  have hkey : signObs ((msDilatedStrategy S).B (MsType.constraint i))
        (constraintBitOrZero k₀) *
      signObs ((msDilatedStrategy S).B (MsType.constraint i)) (constraintBitOrZero k₁) *
      signObs ((msDilatedStrategy S).B (MsType.constraint i)) (constraintBitOrZero k₂) =
      signObs ((msDilatedStrategy S).B (MsType.constraint i)) constraintBitSum := by
    rw [signObs_mul _ (msDilatedStrategy_isProjective_B S _),
      signObs_mul _ (msDilatedStrategy_isProjective_B S _)]
    congr 1
    funext a
    exact hsum a
  rw [msCellObsB, msCellObsB, msCellObsB, heteroKron_mul, heteroKron_mul]
  simp only [mul_one]
  rw [hkey]

/-- Each permuted row or column product of Alice's cell reflections is close, on
the dilated state, to the sign prescribed by the corresponding linear
equation. -/
theorem msCellObsA_prod_close_of (S : Strategy msGame) (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) (i : Fin 6) (k₀ k₁ k₂ : Fin 3)
    (hsum : ∀ a, constraintBitOrZero k₀ a + constraintBitOrZero k₁ a +
      constraintBitOrZero k₂ a = constraintBitSum a) :
    NormCloseOn (msDilatedStrategy S).ψ (12 * Real.sqrt ε)
      (msCellObsA S i k₀ * msCellObsA S i k₁ * msCellObsA S i k₂)
      (((bitSign (msParity i) : ℝ) : ℂ) • 1) := by
  rw [msCellObsA_prod_of S i k₀ k₁ k₂ hsum, ← msCellObsA_prod S i]
  exact msCellObsA_prod_close S ε hwin i

/-- Each permuted row or column product of Bob's cell reflections is close, on
the dilated state, to the sign prescribed by the corresponding linear
equation. -/
theorem msCellObsB_prod_close_of (S : Strategy msGame) (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) (i : Fin 6) (k₀ k₁ k₂ : Fin 3)
    (hsum : ∀ a, constraintBitOrZero k₀ a + constraintBitOrZero k₁ a +
      constraintBitOrZero k₂ a = constraintBitSum a) :
    NormCloseOn (msDilatedStrategy S).ψ (12 * Real.sqrt ε)
      (((bitSign (msParity i) : ℝ) : ℂ) • 1)
      (msCellObsB S i k₀ * msCellObsB S i k₁ * msCellObsB S i k₂) := by
  rw [msCellObsB_prod_of S i k₀ k₁ k₂ hsum, ← msCellObsB_prod S i]
  exact msCellObsB_prod_close S ε hwin i

/-! ## The two logical Pauli pairs -/

/-- Alice's logical `X` reflection, read at the cell of the paper's first
variable.  In the ideal strategy of `thm:ms-rigidity` this is `σ^X` on the first
qubit; blueprint `ch13_qpbt_test.tex:224-253`. -/
noncomputable def msLogicalXA (S : Strategy msGame) :
    Op ((msDilatedStrategy S).ιA × (msDilatedStrategy S).ιB) := msVarObsA S 0

/-- Alice's logical `Z` reflection, read at the cell of the paper's fifth
variable.  In the ideal strategy of `thm:ms-rigidity` this is `σ^Z` on the first
qubit. -/
noncomputable def msLogicalZA (S : Strategy msGame) :
    Op ((msDilatedStrategy S).ιA × (msDilatedStrategy S).ιB) := msVarObsA S 4

/-- Bob's logical `X` reflection, read at the cell of the paper's first
variable. -/
noncomputable def msLogicalXB (S : Strategy msGame) :
    Op ((msDilatedStrategy S).ιA × (msDilatedStrategy S).ιB) := msVarObsB S 0

/-- Bob's logical `Z` reflection, read at the cell of the paper's fifth
variable. -/
noncomputable def msLogicalZB (S : Strategy msGame) :
    Op ((msDilatedStrategy S).ιA × (msDilatedStrategy S).ιB) := msVarObsB S 4

/-- Alice's logical `X` operator is a binary observable. -/
theorem isBinaryObservable_msLogicalXA (S : Strategy msGame) :
    IsBinaryObservable (msLogicalXA S) := isBinaryObservable_msVarObsA S 0

/-- Alice's logical `Z` operator is a binary observable. -/
theorem isBinaryObservable_msLogicalZA (S : Strategy msGame) :
    IsBinaryObservable (msLogicalZA S) := isBinaryObservable_msVarObsA S 4

/-- Bob's logical `X` operator is a binary observable. -/
theorem isBinaryObservable_msLogicalXB (S : Strategy msGame) :
    IsBinaryObservable (msLogicalXB S) := isBinaryObservable_msVarObsB S 0

/-- Bob's logical `Z` operator is a binary observable. -/
theorem isBinaryObservable_msLogicalZB (S : Strategy msGame) :
    IsBinaryObservable (msLogicalZB S) := isBinaryObservable_msVarObsB S 4

/-- Alice's logical `X` operator commutes exactly with Bob's logical `X`
operator. -/
theorem msLogicalXA_comm_msLogicalXB (S : Strategy msGame) :
    msLogicalXA S * msLogicalXB S = msLogicalXB S * msLogicalXA S :=
  msVarObsA_comm_msVarObsB S 0 0

/-- Alice's logical `X` operator commutes exactly with Bob's logical `Z`
operator. -/
theorem msLogicalXA_comm_msLogicalZB (S : Strategy msGame) :
    msLogicalXA S * msLogicalZB S = msLogicalZB S * msLogicalXA S :=
  msVarObsA_comm_msVarObsB S 0 4

/-- Alice's logical `Z` operator commutes exactly with Bob's logical `X`
operator. -/
theorem msLogicalZA_comm_msLogicalXB (S : Strategy msGame) :
    msLogicalZA S * msLogicalXB S = msLogicalXB S * msLogicalZA S :=
  msVarObsA_comm_msVarObsB S 4 0

/-- Alice's logical `Z` operator commutes exactly with Bob's logical `Z`
operator. -/
theorem msLogicalZA_comm_msLogicalZB (S : Strategy msGame) :
    msLogicalZA S * msLogicalZB S = msLogicalZB S * msLogicalZA S :=
  msVarObsA_comm_msVarObsB S 4 4

/-! ## Unit scalars -/

/-- The sign of a binary value has modulus one as a complex number. -/
theorem norm_bitSign_ofReal (c : ZMod 2) : ‖((bitSign c : ℝ) : ℂ)‖ = 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  rcases bit_sign_eq_one_or_neg_one c with h | h <;> rw [h] <;> norm_num

/-- The square of the sign of a binary value is one. -/
theorem bitSign_ofReal_mul_self (c : ZMod 2) :
    ((bitSign c : ℝ) : ℂ) * ((bitSign c : ℝ) : ℂ) = 1 := by
  rw [← Complex.ofReal_mul]
  rcases bit_sign_eq_one_or_neg_one c with h | h <;> rw [h] <;> norm_num

/-- Formalization-only: a sign multiple of an isometric operator is
isometric. -/
private theorem isometry_bitSign_smul {ι : Type} [Fintype ι] [DecidableEq ι]
    {c : ZMod 2} {U : Op ι} (hU : Uᴴ * U = 1) :
    (((bitSign c : ℝ) : ℂ) • U)ᴴ * (((bitSign c : ℝ) : ℂ) • U) = 1 := by
  have hstar : (((bitSign c : ℝ) : ℂ) • U)ᴴ = ((bitSign c : ℝ) : ℂ) • Uᴴ := by
    rw [← Matrix.star_eq_conjTranspose, star_smul, Matrix.star_eq_conjTranspose]
    congr 1
    simp
  rw [hstar, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hU,
    bitSign_ofReal_mul_self, one_smul]

/-! ## Building blocks of the solution-group computation -/

/-- One of Bob's three cell reflections of a constraint question is close, on
the dilated state, to the signed product of the other two. -/
theorem msCellObsB_single_close (S : Strategy msGame) (ε : ℝ) (hwin : 1 - ε ≤ S.value)
    (i : Fin 6) (k₀ k₁ k₂ : Fin 3)
    (hsum : ∀ a, constraintBitOrZero k₀ a + constraintBitOrZero k₁ a +
      constraintBitOrZero k₂ a = constraintBitSum a) :
    NormCloseOn (msDilatedStrategy S).ψ (12 * Real.sqrt ε) (msCellObsB S i k₁)
      (((bitSign (msParity i) : ℝ) : ℂ) •
        (msCellObsB S i k₀ * msCellObsB S i k₂)) := by
  have hprod := msCellObsB_prod_close_of S ε hwin i k₀ k₁ k₂ hsum
  have hX2 : msCellObsB S i k₀ * msCellObsB S i k₀ = 1 :=
    (isBinaryObservable_msCellObsB S i k₀).mul_self_eq_one
  have hZ2 : msCellObsB S i k₂ * msCellObsB S i k₂ = 1 :=
    (isBinaryObservable_msCellObsB S i k₂).mul_self_eq_one
  have hZY : msCellObsB S i k₂ * msCellObsB S i k₁ =
      msCellObsB S i k₁ * msCellObsB S i k₂ := msCellObsB_comm S i k₂ k₁
  have hZX : msCellObsB S i k₂ * msCellObsB S i k₀ =
      msCellObsB S i k₀ * msCellObsB S i k₂ := msCellObsB_comm S i k₂ k₀
  have hU : (msCellObsB S i k₂ * msCellObsB S i k₀)ᴴ *
      (msCellObsB S i k₂ * msCellObsB S i k₀) = 1 :=
    ((isBinaryObservable_msCellObsB S i k₂).mul
      (isBinaryObservable_msCellObsB S i k₀) hZX).isometry
  have e1 : (msCellObsB S i k₂ * msCellObsB S i k₀) *
      (msCellObsB S i k₀ * msCellObsB S i k₁ * msCellObsB S i k₂) = msCellObsB S i k₁ := by
    calc (msCellObsB S i k₂ * msCellObsB S i k₀) *
          (msCellObsB S i k₀ * msCellObsB S i k₁ * msCellObsB S i k₂)
        = msCellObsB S i k₂ *
            ((msCellObsB S i k₀ * msCellObsB S i k₀) * msCellObsB S i k₁) *
            msCellObsB S i k₂ := by noncomm_ring
      _ = msCellObsB S i k₂ * msCellObsB S i k₁ * msCellObsB S i k₂ := by
          rw [hX2, one_mul]
      _ = msCellObsB S i k₁ * msCellObsB S i k₂ * msCellObsB S i k₂ := by rw [hZY]
      _ = msCellObsB S i k₁ := by rw [mul_assoc, hZ2, mul_one]
  have e2 : (msCellObsB S i k₂ * msCellObsB S i k₀) *
      (((bitSign (msParity i) : ℝ) : ℂ) • (1 : Op _)) =
      ((bitSign (msParity i) : ℝ) : ℂ) • (msCellObsB S i k₀ * msCellObsB S i k₂) := by
    rw [Matrix.mul_smul, mul_one, hZX]
  have h := NormCloseOn.isometry_mul hU hprod
  rw [e1, e2] at h
  exact h.symm

/-- A product of two of Bob's cell reflections is close, on the dilated state,
to the product of Alice's variable reflections at the same two cells, taken in
the reverse order. -/
theorem msCellObsB_mul_close (S : Strategy msGame) (ε : ℝ) (hwin : 1 - ε ≤ S.value)
    (I J : Fin 6) (k l : Fin 3) :
    NormCloseOn (msDilatedStrategy S).ψ (12 * Real.sqrt ε + 12 * Real.sqrt ε)
      (msCellObsB S I k * msCellObsB S J l)
      (msVarObsA S (msConstraintVars J l) * msVarObsA S (msConstraintVars I k)) := by
  have p1 : NormCloseOn (msDilatedStrategy S).ψ (12 * Real.sqrt ε) (msCellObsB S J l)
      (msVarObsA S (msConstraintVars J l)) :=
    (msVarObsA_close_msCellObsB S ε hwin J l).symm
  have p2 : NormCloseOn (msDilatedStrategy S).ψ (12 * Real.sqrt ε) (msCellObsB S I k)
      (msVarObsA S (msConstraintVars I k)) :=
    (msVarObsA_close_msCellObsB S ε hwin I k).symm
  have h1 : NormCloseOn (msDilatedStrategy S).ψ (12 * Real.sqrt ε)
      (msCellObsB S I k * msCellObsB S J l)
      (msCellObsB S I k * msVarObsA S (msConstraintVars J l)) :=
    NormCloseOn.isometry_mul (isBinaryObservable_msCellObsB S I k).isometry p1
  have hswap : msCellObsB S I k * msVarObsA S (msConstraintVars J l) =
      msVarObsA S (msConstraintVars J l) * msCellObsB S I k :=
    (msVarObsA_comm_msCellObsB S (msConstraintVars J l) I k).symm
  rw [hswap] at h1
  exact h1.trans (NormCloseOn.isometry_mul (isBinaryObservable_msVarObsA S _).isometry p2)

/-- Two of Bob's cell reflections attached to a common cell by two different
constraint questions are close on the dilated state. -/
theorem msCellObsB_close_of_same_cell (S : Strategy msGame) (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) (I J : Fin 6) (k l : Fin 3)
    (hcell : msConstraintVars I k = msConstraintVars J l) :
    NormCloseOn (msDilatedStrategy S).ψ (12 * Real.sqrt ε + 12 * Real.sqrt ε)
      (msCellObsB S I k) (msCellObsB S J l) := by
  have p1 : NormCloseOn (msDilatedStrategy S).ψ (12 * Real.sqrt ε) (msCellObsB S I k)
      (msVarObsA S (msConstraintVars I k)) :=
    (msVarObsA_close_msCellObsB S ε hwin I k).symm
  have p2 : NormCloseOn (msDilatedStrategy S).ψ (12 * Real.sqrt ε)
      (msVarObsA S (msConstraintVars J l)) (msCellObsB S J l) :=
    msVarObsA_close_msCellObsB S ε hwin J l
  rw [hcell] at p1
  exact p1.trans p2

end

end MIPStarRE.QPBT.MagicSquareRigidity
