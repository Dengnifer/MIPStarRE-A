import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.Reflections

/-!
# Approximate anticommutation in the Magic Square game

This file carries out the operator part of the Magic Square rigidity argument on
the projective dilation of an arbitrary strategy.  Each question of the dilated
strategy carries a complete projective measurement, so every binary relabelling
of its answers produces a reflection.  Three reflections are attached to a
constraint question, one for each cell of the row or column, and one reflection
is attached to each variable question; the three reflections of a constraint
commute exactly and their product is the reflection of the sum of the three
answer bits.

The value-to-parity relations then give, on the dilated state and with explicit
constants, the six approximate row and column product relations, the approximate
agreement of the two reflections that the two players attach to a common cell,
and the approximate anticommutation of the two reflections placed at the cells
labelled by the paper's first and fifth variables.  Reflections of the two
players commute exactly.

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
private theorem closeOn_of_sq_le {ι : Type} [Fintype ι] [DecidableEq ι]
    {ψ : EuclideanSpace ℂ ι} {M N : Op ι} {m ε : ℝ}
    (hsq : ‖applyOperatorToState (M - N) ψ‖ ^ 2 ≤ 4 * m) (hm0 : 0 ≤ m)
    (hm : m ≤ 36 * ε) : CloseOn ψ (12 * Real.sqrt ε) M N := by
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

end

end MIPStarRE.QPBT.MagicSquareRigidity
