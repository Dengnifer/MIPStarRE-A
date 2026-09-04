import MIPStarRE.LDT.Basic.DistributionAvg
import MIPStarRE.LDT.Basic.TensorPlacement
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Basic

/-!
# Magic Square value-to-parity relations

This file extracts the elementary probability relations used at the start of
the Magic Square rigidity argument.  A strategy of value at least `1 - ε` has
total rejection mass at most `ε`.  Since the question distribution is
supported on at most 36 directed incidences, the rejection mass at each
incidence is at most `36 * ε`.  This controls malformed answers, consistency
of the two reported bits at every cell, and the parity product on each of the
six row or column constraints.

The arguments apply to arbitrary finite POVMs.  In particular, malformed
answers remain in the event masses when `msBitOrZero` and
`constraintBitOrZero` turn the common answer alphabet into binary outcomes.

## References

The Magic Square game is defined in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:512-610`
and `blueprint/src/chapter/ch13_qpbt_test.tex:201-222`.  These relations are the
probabilistic input to the rigidity result cited at paper lines 612-652 from
Coladangelo--Stark, Theorem 6.9.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-! ## The directed incidence distribution -/

/-- The 36 possible directed constraint-variable incidences. -/
def directedIncidence : ((Fin 6 × Fin 3) × Bool) → MsType × MsType
  | ((i, k), false) => (.constraint i, .var (msConstraintVars i k))
  | ((i, k), true) => (.var (msConstraintVars i k), .constraint i)

/-- Every question pair in the Magic Square distribution is a directed incidence. -/
theorem ms_support_subset_directedIncidences :
    (graphDistribution msEdges msEdges_nonempty).support ⊆
      (Finset.univ : Finset ((Fin 6 × Fin 3) × Bool)).image directedIncidence := by
  intro xy hxy
  have hedge : Sym2.mk xy.1 xy.2 ∈ msEdges :=
    (Finset.mem_filter.mp hxy).2
  rcases Finset.mem_image.mp hedge with ⟨ik, _hik, heq⟩
  have heq' :
      ((.constraint ik.1, .var (msConstraintVars ik.1 ik.2)) : MsType × MsType) = xy ∨
        ((.constraint ik.1, .var (msConstraintVars ik.1 ik.2)) : MsType × MsType) =
          xy.swap :=
    (Sym2.mk_eq_mk_iff (α := MsType)).mp heq
  rcases heq' with heq' | heq'
  · refine Finset.mem_image.mpr ⟨(ik, false), Finset.mem_univ _, ?_⟩
    simpa [directedIncidence] using heq'
  · refine Finset.mem_image.mpr ⟨(ik, true), Finset.mem_univ _, ?_⟩
    simpa [directedIncidence] using congrArg Prod.swap heq'

/-- The Magic Square question distribution has at most 36 support points. -/
theorem ms_support_card_le :
    (graphDistribution msEdges msEdges_nonempty).support.card ≤ 36 := by
  calc
    (graphDistribution msEdges msEdges_nonempty).support.card ≤
        ((Finset.univ : Finset ((Fin 6 × Fin 3) × Bool)).image
          directedIncidence).card :=
      Finset.card_le_card ms_support_subset_directedIncidences
    _ ≤ (Finset.univ : Finset ((Fin 6 × Fin 3) × Bool)).card :=
      Finset.card_image_le
    _ = 36 := by norm_num

/-- A constraint-to-variable incidence belongs to the question support. -/
theorem ms_forward_incidence_mem_support (i : Fin 6) (k : Fin 3) :
    (.constraint i, .var (msConstraintVars i k)) ∈
      (graphDistribution msEdges msEdges_nonempty).support := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  exact Finset.mem_image.mpr ⟨(i, k), Finset.mem_univ _, rfl⟩

/-- A variable-to-constraint incidence belongs to the question support. -/
theorem ms_reverse_incidence_mem_support (i : Fin 6) (k : Fin 3) :
    (.var (msConstraintVars i k), .constraint i) ∈
      (graphDistribution msEdges msEdges_nonempty).support := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [Sym2.eq_swap]
  exact Finset.mem_image.mpr ⟨(i, k), Finset.mem_univ _, rfl⟩

/-- Every supported question pair has probability at least `1 / 36`. -/
theorem ms_question_weight_ge {xy : MsType × MsType}
    (hxy : xy ∈ (graphDistribution msEdges msEdges_nonempty).support) :
    (1 : ℝ) / 36 ≤ (graphDistribution msEdges msEdges_nonempty).weight xy := by
  have hmemFilter :
      xy ∈ ((Finset.univ : Finset (MsType × MsType)).filter fun ab =>
        Sym2.mk ab.1 ab.2 ∈ msEdges) := hxy
  rw [show (graphDistribution msEdges msEdges_nonempty).weight xy =
      1 / ((graphDistribution msEdges msEdges_nonempty).support.card : ℝ) by
    change (Distribution.uniformOnFinset
        ((Finset.univ : Finset (MsType × MsType)).filter fun ab =>
          Sym2.mk ab.1 ab.2 ∈ msEdges)).weight xy =
      1 / (((Finset.univ : Finset (MsType × MsType)).filter fun ab =>
        Sym2.mk ab.1 ab.2 ∈ msEdges).card : ℝ)
    rw [Distribution.uniformOnFinset_weight, if_pos hmemFilter]]
  apply one_div_le_one_div_of_le
  · exact_mod_cast Finset.card_pos.mpr ⟨xy, hxy⟩
  · exact_mod_cast ms_support_card_le

/-! ## Born masses and events -/

/-- The Born mass of an answer pair conditioned on a question pair. -/
noncomputable def outcomeMass (S : Strategy msGame) (x y : MsType)
    (a b : MsAnswer) : ℝ :=
  (inner ℂ S.ψ
    (applyOperatorToState
      (heteroKron ((S.A x).effect a) ((S.B y).effect b)) S.ψ)).re

/-- Every conditioned answer-pair mass is nonnegative. -/
theorem outcomeMass_nonneg (S : Strategy msGame) (x y : MsType) (a b : MsAnswer) :
    0 ≤ outcomeMass S x y a b := by
  unfold outcomeMass applyOperatorToState
  have hpos :
      (Matrix.toEuclideanLin
        (heteroKron ((S.A x).effect a) ((S.B y).effect b))).IsPositive := by
    rw [Matrix.isPositive_toEuclideanLin_iff]
    exact Matrix.nonneg_iff_posSemidef.mp
      (kronecker_nonneg ((S.A x).pos a) ((S.B y).pos b))
  change 0 ≤ RCLike.re (inner ℂ S.ψ
    ((Matrix.toEuclideanLin
      (heteroKron ((S.A x).effect a) ((S.B y).effect b))) S.ψ))
  exact hpos.re_inner_nonneg_right S.ψ

/-- The answer-pair masses conditioned on fixed questions sum to one. -/
theorem outcomeMass_sum (S : Strategy msGame) (x y : MsType) :
    (∑ a : MsAnswer, ∑ b : MsAnswer, outcomeMass S x y a b) = 1 := by
  let A : MIPStarRE.Quantum.Measurement MsAnswer S.ιA := S.A x
  let B : MIPStarRE.Quantum.Measurement MsAnswer S.ιB := S.B y
  change (∑ a : MsAnswer, ∑ b : MsAnswer,
    (inner ℂ S.ψ
      (applyOperatorToState (heteroKron (A.effect a) (B.effect b)) S.ψ)).re) = 1
  calc
    (∑ a : MsAnswer, ∑ b : MsAnswer,
        (inner ℂ S.ψ
          (applyOperatorToState (heteroKron (A.effect a) (B.effect b)) S.ψ)).re) =
        (inner ℂ S.ψ
          (applyOperatorToState
            (∑ a : MsAnswer, ∑ b : MsAnswer,
              heteroKron (A.effect a) (B.effect b)) S.ψ)).re := by
      simp [applyOperatorToState, map_sum]
    _ = (inner ℂ S.ψ (applyOperatorToState (1 : Op (S.ιA × S.ιB)) S.ψ)).re := by
      congr 3
      calc
        (∑ a : MsAnswer, ∑ b : MsAnswer,
            heteroKron (A.effect a) (B.effect b)) =
            heteroKron (∑ a : MsAnswer, A.effect a)
              (∑ b : MsAnswer, B.effect b) := by
          calc
            _ = ∑ a : MsAnswer,
                heteroKron (A.effect a) (∑ b : MsAnswer, B.effect b) := by
              apply Finset.sum_congr rfl
              intro a _
              exact (opTensor_sum_right_univ (A.effect a) B.effect).symm
            _ = _ := (opTensor_sum_left_univ A.effect _).symm
        _ = heteroKron 1 1 := by rw [A.sum_eq_one, B.sum_eq_one]
        _ = 1 := Matrix.one_kronecker_one
    _ = 1 := by simp [applyOperatorToState, S.ψ_norm]

/-- Alice's marginal Born mass for one answer. -/
noncomputable def aliceOutcomeMass (S : Strategy msGame) (x : MsType)
    (a : MsAnswer) : ℝ :=
  (inner ℂ S.ψ
    (applyOperatorToState
      (heteroKron ((S.A x).effect a) (1 : Op S.ιB)) S.ψ)).re

/-- Bob's marginal Born mass for one answer. -/
noncomputable def bobOutcomeMass (S : Strategy msGame) (y : MsType)
    (b : MsAnswer) : ℝ :=
  (inner ℂ S.ψ
    (applyOperatorToState
      (heteroKron (1 : Op S.ιA) ((S.B y).effect b)) S.ψ)).re

/-- Summing Bob's answers gives Alice's marginal answer mass. -/
theorem sum_outcomeMass_right (S : Strategy msGame) (x y : MsType) (a : MsAnswer) :
    (∑ b : MsAnswer, outcomeMass S x y a b) = aliceOutcomeMass S x a := by
  let B : MIPStarRE.Quantum.Measurement MsAnswer S.ιB := S.B y
  change (∑ b : MsAnswer,
      (inner ℂ S.ψ
        (applyOperatorToState
          (heteroKron ((S.A x).effect a) (B.effect b)) S.ψ)).re) =
    (inner ℂ S.ψ
      (applyOperatorToState
        (heteroKron ((S.A x).effect a) (1 : Op S.ιB)) S.ψ)).re
  calc
    _ = (inner ℂ S.ψ
        (applyOperatorToState
          (∑ b : MsAnswer, heteroKron ((S.A x).effect a) (B.effect b)) S.ψ)).re := by
      simp [applyOperatorToState, map_sum]
    _ = _ := by
      congr 3
      calc
        (∑ b : MsAnswer, heteroKron ((S.A x).effect a) (B.effect b)) =
            heteroKron ((S.A x).effect a) (∑ b : MsAnswer, B.effect b) :=
          (opTensor_sum_right_univ ((S.A x).effect a) B.effect).symm
        _ = _ := by rw [B.sum_eq_one]

/-- Summing Alice's answers gives Bob's marginal answer mass. -/
theorem sum_outcomeMass_left (S : Strategy msGame) (x y : MsType) (b : MsAnswer) :
    (∑ a : MsAnswer, outcomeMass S x y a b) = bobOutcomeMass S y b := by
  let A : MIPStarRE.Quantum.Measurement MsAnswer S.ιA := S.A x
  change (∑ a : MsAnswer,
      (inner ℂ S.ψ
        (applyOperatorToState
          (heteroKron (A.effect a) ((S.B y).effect b)) S.ψ)).re) =
    (inner ℂ S.ψ
      (applyOperatorToState
        (heteroKron (1 : Op S.ιA) ((S.B y).effect b)) S.ψ)).re
  calc
    _ = (inner ℂ S.ψ
        (applyOperatorToState
          (∑ a : MsAnswer, heteroKron (A.effect a) ((S.B y).effect b)) S.ψ)).re := by
      simp [applyOperatorToState, map_sum]
    _ = _ := by
      congr 3
      calc
        (∑ a : MsAnswer, heteroKron (A.effect a) ((S.B y).effect b)) =
            heteroKron (∑ a : MsAnswer, A.effect a) ((S.B y).effect b) :=
          (opTensor_sum_left_univ A.effect ((S.B y).effect b)).symm
        _ = _ := by rw [A.sum_eq_one]

/-- The conditioned mass of a predicate on the two answers. -/
noncomputable def eventMass (S : Strategy msGame) (x y : MsType)
    (E : MsAnswer → MsAnswer → Prop) [DecidableRel E] : ℝ :=
  ∑ a : MsAnswer, ∑ b : MsAnswer, if E a b then outcomeMass S x y a b else 0

/-- The marginal mass of a predicate on Alice's answer. -/
noncomputable def aliceEventMass (S : Strategy msGame) (x : MsType)
    (E : MsAnswer → Prop) [DecidablePred E] : ℝ :=
  ∑ a : MsAnswer, if E a then aliceOutcomeMass S x a else 0

/-- The marginal mass of a predicate on Bob's answer. -/
noncomputable def bobEventMass (S : Strategy msGame) (y : MsType)
    (E : MsAnswer → Prop) [DecidablePred E] : ℝ :=
  ∑ b : MsAnswer, if E b then bobOutcomeMass S y b else 0

/-- Event masses are nonnegative. -/
theorem eventMass_nonneg (S : Strategy msGame) (x y : MsType)
    (E : MsAnswer → MsAnswer → Prop) [DecidableRel E] :
    0 ≤ eventMass S x y E := by
  unfold eventMass
  exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by
    split_ifs
    · exact outcomeMass_nonneg S x y a b
    · exact le_rfl

/-- An event depending only on Alice has its Alice marginal mass. -/
theorem eventMass_left_eq (S : Strategy msGame) (x y : MsType)
    (E : MsAnswer → Prop) [DecidablePred E] :
    eventMass S x y (fun a _ => E a) = aliceEventMass S x E := by
  unfold eventMass aliceEventMass
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : E a
  · simp [ha, sum_outcomeMass_right S x y a]
  · simp [ha]

/-- An event depending only on Bob has its Bob marginal mass. -/
theorem eventMass_right_eq (S : Strategy msGame) (x y : MsType)
    (E : MsAnswer → Prop) [DecidablePred E] :
    eventMass S x y (fun _ b => E b) = bobEventMass S y E := by
  unfold eventMass bobEventMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : E b
  · simp [hb, sum_outcomeMass_left S x y b]
  · simp [hb]

/-- Inclusion of answer events implies the corresponding mass inequality. -/
theorem eventMass_mono (S : Strategy msGame) (x y : MsType)
    (E F : MsAnswer → MsAnswer → Prop) [DecidableRel E] [DecidableRel F]
    (hEF : ∀ a b, E a b → F a b) :
    eventMass S x y E ≤ eventMass S x y F := by
  unfold eventMass
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  by_cases hE : E a b
  · simp [hE, hEF a b hE]
  · simp only [hE, ↓reduceIte]
    split_ifs
    · exact outcomeMass_nonneg S x y a b
    · exact le_rfl

/-! ## Rejection mass from the game value -/

/-- The rejection mass conditioned on a question pair. -/
noncomputable def rejectionMass (S : Strategy msGame) (x y : MsType) : ℝ :=
  eventMass S x y fun a b => msWinPredicate x y a b = false

/-- The acceptance mass conditioned on a question pair. -/
noncomputable def acceptanceMass (S : Strategy msGame) (x y : MsType) : ℝ :=
  eventMass S x y fun a b => msWinPredicate x y a b = true

/-- The rejection mass averaged over the Magic Square question distribution. -/
noncomputable def totalRejectionMass (S : Strategy msGame) : ℝ :=
  avgOver (graphDistribution msEdges msEdges_nonempty) fun xy =>
    rejectionMass S xy.1 xy.2

/-- Acceptance and rejection partition the conditioned answer mass. -/
theorem acceptanceMass_add_rejectionMass (S : Strategy msGame) (x y : MsType) :
    acceptanceMass S x y + rejectionMass S x y = 1 := by
  rw [← show (∑ a : MsAnswer, ∑ b : MsAnswer, outcomeMass S x y a b) = 1 by
    exact outcomeMass_sum S x y]
  unfold acceptanceMass rejectionMass eventMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  cases h : msWinPredicate x y a b <;> simp [h]

/-- The strategy value is the average conditioned acceptance mass. -/
theorem strategy_value_eq_acceptanceMass (S : Strategy msGame) :
    S.value = avgOver (graphDistribution msEdges msEdges_nonempty) fun xy =>
      acceptanceMass S xy.1 xy.2 := by
  rfl

/-- Total rejection mass is exactly one minus the strategy value. -/
theorem totalRejectionMass_eq_one_sub_value (S : Strategy msGame) :
    totalRejectionMass S = 1 - S.value := by
  rw [show S.value = avgOver (graphDistribution msEdges msEdges_nonempty) (fun xy =>
      acceptanceMass S xy.1 xy.2) by rfl]
  unfold totalRejectionMass
  calc
    avgOver (graphDistribution msEdges msEdges_nonempty) (fun xy =>
        rejectionMass S xy.1 xy.2) =
        avgOver (graphDistribution msEdges msEdges_nonempty) (fun xy =>
          1 - acceptanceMass S xy.1 xy.2) := by
      apply avgOver_congr
      intro xy
      linarith [show acceptanceMass S xy.1 xy.2 + rejectionMass S xy.1 xy.2 = 1 by
        exact acceptanceMass_add_rejectionMass S xy.1 xy.2]
    _ = avgOver (graphDistribution msEdges msEdges_nonempty) (fun _ => 1) -
        avgOver (graphDistribution msEdges msEdges_nonempty) (fun xy =>
          acceptanceMass S xy.1 xy.2) := avgOver_sub _ _ _
    _ = 1 - avgOver (graphDistribution msEdges msEdges_nonempty) (fun xy =>
        acceptanceMass S xy.1 xy.2) := by
      rw [avgOver_const_of_isProbability _ (by
        unfold graphDistribution
        apply Distribution.uniformOnFinset_isProbability
        refine ⟨(.constraint 0, .var (msConstraintVars 0 0)), ?_⟩
        simp [msEdges])]

/-- Total rejection mass is nonnegative. -/
theorem totalRejectionMass_nonneg (S : Strategy msGame) :
    0 ≤ totalRejectionMass S := by
  unfold totalRejectionMass
  exact avgOver_nonneg _ _ fun xy => eventMass_nonneg S xy.1 xy.2 _

/-- Value at least `1 - ε` implies total rejection mass at most `ε`. -/
theorem totalRejectionMass_le (S : Strategy msGame) (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) : totalRejectionMass S ≤ ε := by
  rw [totalRejectionMass_eq_one_sub_value]
  linarith

/-- Conditioned rejection mass is nonnegative. -/
theorem rejectionMass_nonneg (S : Strategy msGame) (x y : MsType) :
    0 ≤ rejectionMass S x y :=
  eventMass_nonneg S x y fun a b => msWinPredicate x y a b = false

/-- A supported conditioned rejection mass is at most 36 times total rejection. -/
theorem rejectionMass_le_thirtySix_mul_total (S : Strategy msGame)
    {xy : MsType × MsType}
    (hxy : xy ∈ (graphDistribution msEdges msEdges_nonempty).support) :
    rejectionMass S xy.1 xy.2 ≤ 36 * totalRejectionMass S := by
  have hrejection : 0 ≤ rejectionMass S xy.1 xy.2 :=
    rejectionMass_nonneg S xy.1 xy.2
  have hweight := ms_question_weight_ge hxy
  have hterm :
      (graphDistribution msEdges msEdges_nonempty).weight xy *
          rejectionMass S xy.1 xy.2 ≤ totalRejectionMass S := by
    unfold totalRejectionMass avgOver
    exact Finset.single_le_sum
      (fun z _ => mul_nonneg
        ((graphDistribution msEdges msEdges_nonempty).nonnegative z)
        (rejectionMass_nonneg S z.1 z.2)) hxy
  have hscaled : (1 / 36 : ℝ) * rejectionMass S xy.1 xy.2 ≤
      (graphDistribution msEdges msEdges_nonempty).weight xy *
        rejectionMass S xy.1 xy.2 :=
    mul_le_mul_of_nonneg_right hweight hrejection
  nlinarith

/-- A supported conditioned rejection mass is at most `36 * ε`. -/
theorem rejectionMass_le (S : Strategy msGame) (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) {xy : MsType × MsType}
    (hxy : xy ∈ (graphDistribution msEdges msEdges_nonempty).support) :
    rejectionMass S xy.1 xy.2 ≤ 36 * ε := by
  calc
    rejectionMass S xy.1 xy.2 ≤ 36 * totalRejectionMass S :=
      rejectionMass_le_thirtySix_mul_total S hxy
    _ ≤ 36 * ε :=
      mul_le_mul_of_nonneg_left (totalRejectionMass_le S ε hwin) (by norm_num)

/-- An event which always rejects has mass at most the conditioned rejection mass. -/
theorem eventMass_le_rejectionMass (S : Strategy msGame) (x y : MsType)
    (E : MsAnswer → MsAnswer → Prop) [DecidableRel E]
    (hE : ∀ a b, E a b → msWinPredicate x y a b = false) :
    eventMass S x y E ≤ rejectionMass S x y := by
  exact eventMass_mono S x y E _ hE

/-! ## Malformed answers and cell consistency -/

/-- The selected constraint bit, with a wrong-form single-bit answer folded to zero. -/
def constraintBitOrZero (k : Fin 3) : MsAnswer → ZMod 2
  | .triple β => β k
  | .bit _ => 0

/-- Whether an answer has the wrong form for a variable question. -/
def wrongVariableAnswer : MsAnswer → Bool
  | .triple _ => true
  | .bit _ => false

/-- Whether an answer has the wrong form for a constraint question. -/
def wrongConstraintAnswer : MsAnswer → Bool
  | .triple _ => false
  | .bit _ => true

/-- The three cells in any fixed row or column are distinct. -/
theorem constraintVars_injective (i : Fin 6) : Function.Injective (msConstraintVars i) := by
  intro k l hkl
  apply Fin.ext
  unfold msConstraintVars at hkl
  split at hkl <;> simp only [Fin.mk.injEq] at hkl ⊢ <;> omega

/-- Every Magic Square variable is incident to a row constraint. -/
theorem every_variable_is_incident (j : Fin 9) :
    ∃ i : Fin 6, ∃ k : Fin 3, msConstraintVars i k = j := by
  let i : Fin 6 := ⟨j.val / 3, by omega⟩
  let k : Fin 3 := ⟨j.val % 3, Nat.mod_lt _ (by omega)⟩
  refine ⟨i, k, ?_⟩
  apply Fin.ext
  simp only [msConstraintVars, i, k]
  rw [if_pos (by omega)]
  omega

/-- Alice's variable-answer mass folded to zero by `msBitOrZero`. -/
noncomputable def aliceVariableWrongFormMass (S : Strategy msGame) (j : Fin 9) : ℝ :=
  aliceEventMass S (.var j) fun a => wrongVariableAnswer a = true

/-- Bob's variable-answer mass folded to zero by `msBitOrZero`. -/
noncomputable def bobVariableWrongFormMass (S : Strategy msGame) (j : Fin 9) : ℝ :=
  bobEventMass S (.var j) fun b => wrongVariableAnswer b = true

/-- Alice's single-bit answer mass on a constraint question. -/
noncomputable def aliceConstraintWrongFormMass (S : Strategy msGame) (i : Fin 6) : ℝ :=
  aliceEventMass S (.constraint i) fun a => wrongConstraintAnswer a = true

/-- Bob's single-bit answer mass on a constraint question. -/
noncomputable def bobConstraintWrongFormMass (S : Strategy msGame) (i : Fin 6) : ℝ :=
  bobEventMass S (.constraint i) fun b => wrongConstraintAnswer b = true

private theorem forward_wrongVariable_rejects (i : Fin 6) (k : Fin 3)
    (a b : MsAnswer) (hb : wrongVariableAnswer b = true) :
    msWinPredicate (.constraint i) (.var (msConstraintVars i k)) a b = false := by
  cases a <;> cases b <;> simp_all [wrongVariableAnswer, msWinPredicate]

private theorem reverse_wrongVariable_rejects (i : Fin 6) (k : Fin 3)
    (a b : MsAnswer) (ha : wrongVariableAnswer a = true) :
    msWinPredicate (.var (msConstraintVars i k)) (.constraint i) a b = false := by
  cases a <;> cases b <;> simp_all [wrongVariableAnswer, msWinPredicate]

private theorem forward_wrongConstraint_rejects (i : Fin 6) (k : Fin 3)
    (a b : MsAnswer) (ha : wrongConstraintAnswer a = true) :
    msWinPredicate (.constraint i) (.var (msConstraintVars i k)) a b = false := by
  cases a <;> cases b <;> simp_all [wrongConstraintAnswer, msWinPredicate]

private theorem reverse_wrongConstraint_rejects (i : Fin 6) (k : Fin 3)
    (a b : MsAnswer) (hb : wrongConstraintAnswer b = true) :
    msWinPredicate (.var (msConstraintVars i k)) (.constraint i) a b = false := by
  cases a <;> cases b <;> simp_all [wrongConstraintAnswer, msWinPredicate]

/-- Alice's wrong-form mass at every variable question is at most `36 * ε`. -/
theorem aliceVariableWrongFormMass_le (S : Strategy msGame) (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) (j : Fin 9) :
    aliceVariableWrongFormMass S j ≤ 36 * ε := by
  rcases every_variable_is_incident j with ⟨i, k, hj⟩
  rw [← hj]
  unfold aliceVariableWrongFormMass
  rw [← eventMass_left_eq S (.var (msConstraintVars i k)) (.constraint i)]
  calc
    eventMass S (.var (msConstraintVars i k)) (.constraint i)
        (fun a _ => wrongVariableAnswer a = true) ≤
        rejectionMass S (.var (msConstraintVars i k)) (.constraint i) :=
      eventMass_le_rejectionMass S _ _ _ (reverse_wrongVariable_rejects i k)
    _ ≤ 36 * ε :=
      rejectionMass_le S ε hwin (ms_reverse_incidence_mem_support i k)

/-- Bob's wrong-form mass at every variable question is at most `36 * ε`. -/
theorem bobVariableWrongFormMass_le (S : Strategy msGame) (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) (j : Fin 9) :
    bobVariableWrongFormMass S j ≤ 36 * ε := by
  rcases every_variable_is_incident j with ⟨i, k, hj⟩
  rw [← hj]
  unfold bobVariableWrongFormMass
  rw [← eventMass_right_eq S (.constraint i) (.var (msConstraintVars i k))]
  calc
    eventMass S (.constraint i) (.var (msConstraintVars i k))
        (fun _ b => wrongVariableAnswer b = true) ≤
        rejectionMass S (.constraint i) (.var (msConstraintVars i k)) :=
      eventMass_le_rejectionMass S _ _ _ (forward_wrongVariable_rejects i k)
    _ ≤ 36 * ε :=
      rejectionMass_le S ε hwin (ms_forward_incidence_mem_support i k)

/-- Alice's wrong-form mass on every constraint question is at most `36 * ε`. -/
theorem aliceConstraintWrongFormMass_le (S : Strategy msGame) (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) (i : Fin 6) :
    aliceConstraintWrongFormMass S i ≤ 36 * ε := by
  unfold aliceConstraintWrongFormMass
  rw [← eventMass_left_eq S (.constraint i) (.var (msConstraintVars i 0))]
  calc
    eventMass S (.constraint i) (.var (msConstraintVars i 0))
        (fun a _ => wrongConstraintAnswer a = true) ≤
        rejectionMass S (.constraint i) (.var (msConstraintVars i 0)) :=
      eventMass_le_rejectionMass S _ _ _ (forward_wrongConstraint_rejects i 0)
    _ ≤ 36 * ε :=
      rejectionMass_le S ε hwin (ms_forward_incidence_mem_support i 0)

/-- Bob's wrong-form mass on every constraint question is at most `36 * ε`. -/
theorem bobConstraintWrongFormMass_le (S : Strategy msGame) (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) (i : Fin 6) :
    bobConstraintWrongFormMass S i ≤ 36 * ε := by
  unfold bobConstraintWrongFormMass
  rw [← eventMass_right_eq S (.var (msConstraintVars i 0)) (.constraint i)]
  calc
    eventMass S (.var (msConstraintVars i 0)) (.constraint i)
        (fun _ b => wrongConstraintAnswer b = true) ≤
        rejectionMass S (.var (msConstraintVars i 0)) (.constraint i) :=
      eventMass_le_rejectionMass S _ _ _ (reverse_wrongConstraint_rejects i 0)
    _ ≤ 36 * ε :=
      rejectionMass_le S ε hwin (ms_reverse_incidence_mem_support i 0)

/-- The forward-incidence mass on which the two totalized cell bits disagree. -/
noncomputable def forwardCellMismatchMass (S : Strategy msGame)
    (i : Fin 6) (k : Fin 3) : ℝ :=
  eventMass S (.constraint i) (.var (msConstraintVars i k)) fun a b =>
    constraintBitOrZero k a ≠ msBitOrZero b

/-- The reverse-incidence mass on which the two totalized cell bits disagree. -/
noncomputable def reverseCellMismatchMass (S : Strategy msGame)
    (i : Fin 6) (k : Fin 3) : ℝ :=
  eventMass S (.var (msConstraintVars i k)) (.constraint i) fun a b =>
    msBitOrZero a ≠ constraintBitOrZero k b

private theorem forward_cellMismatch_rejects (i : Fin 6) (k : Fin 3)
    (a b : MsAnswer) (hmismatch : constraintBitOrZero k a ≠ msBitOrZero b) :
    msWinPredicate (.constraint i) (.var (msConstraintVars i k)) a b = false := by
  cases a with
  | bit γa => rfl
  | triple β =>
      cases b with
      | triple βb => rfl
      | bit γ =>
          simp only [constraintBitOrZero, msBitOrZero] at hmismatch
          rw [msWinPredicate, decide_eq_false_iff_not]
          intro haccept
          rcases haccept.2 with ⟨l, hl, hbit⟩
          have hlk : l = k := constraintVars_injective i hl
          subst l
          exact hmismatch hbit

private theorem reverse_cellMismatch_rejects (i : Fin 6) (k : Fin 3)
    (a b : MsAnswer) (hmismatch : msBitOrZero a ≠ constraintBitOrZero k b) :
    msWinPredicate (.var (msConstraintVars i k)) (.constraint i) a b = false := by
  cases a with
  | triple α => rfl
  | bit γ =>
      cases b with
      | bit γb => rfl
      | triple β =>
          simp only [msBitOrZero, constraintBitOrZero] at hmismatch
          rw [msWinPredicate, decide_eq_false_iff_not]
          intro haccept
          rcases haccept.2 with ⟨l, hl, hbit⟩
          have hlk : l = k := constraintVars_injective i hl
          subst l
          exact hmismatch hbit.symm

/-- Every forward directed incidence has cell-mismatch mass at most `36 * ε`. -/
theorem forwardCellMismatchMass_le (S : Strategy msGame) (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) (i : Fin 6) (k : Fin 3) :
    forwardCellMismatchMass S i k ≤ 36 * ε := by
  unfold forwardCellMismatchMass
  calc
    eventMass S (.constraint i) (.var (msConstraintVars i k))
        (fun a b => constraintBitOrZero k a ≠ msBitOrZero b) ≤
        rejectionMass S (.constraint i) (.var (msConstraintVars i k)) :=
      eventMass_le_rejectionMass S _ _ _ (forward_cellMismatch_rejects i k)
    _ ≤ 36 * ε :=
      rejectionMass_le S ε hwin (ms_forward_incidence_mem_support i k)

/-- Every reverse directed incidence has cell-mismatch mass at most `36 * ε`. -/
theorem reverseCellMismatchMass_le (S : Strategy msGame) (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) (i : Fin 6) (k : Fin 3) :
    reverseCellMismatchMass S i k ≤ 36 * ε := by
  unfold reverseCellMismatchMass
  calc
    eventMass S (.var (msConstraintVars i k)) (.constraint i)
        (fun a b => msBitOrZero a ≠ constraintBitOrZero k b) ≤
        rejectionMass S (.var (msConstraintVars i k)) (.constraint i) :=
      eventMass_le_rejectionMass S _ _ _ (reverse_cellMismatch_rejects i k)
    _ ≤ 36 * ε :=
      rejectionMass_le S ε hwin (ms_reverse_incidence_mem_support i k)

/-! ## Row and column parity products -/

/-- The real sign `(-1)^b` associated with a binary answer. -/
def bitSign (b : ZMod 2) : ℝ :=
  (-1 : ℝ) ^ b.val

/-- The binary sign turns addition into multiplication. -/
theorem bitSign_add (b c : ZMod 2) :
    bitSign (b + c) = bitSign b * bitSign c := by
  unfold bitSign
  rw [ZMod.val_add]
  rw [← neg_one_pow_eq_pow_mod_two]
  exact pow_add _ _ _

/-- The sign of a three-bit parity is the product of the three signs. -/
theorem bitSign_sum_fin_three (β : Fin 3 → ZMod 2) :
    bitSign (∑ k : Fin 3, β k) = ∏ k : Fin 3, bitSign (β k) := by
  rw [Fin.sum_univ_three, Fin.prod_univ_three, bitSign_add, bitSign_add]

/-- A binary sign is never zero. -/
theorem bitSign_ne_zero (b : ZMod 2) : bitSign b ≠ 0 := by
  unfold bitSign
  exact pow_ne_zero _ (by norm_num)

/-- The product of the three output signs, with malformed constraint answers
assigned zero so that they remain parity failures. -/
def constraintParityProduct : MsAnswer → ℝ
  | .triple β => ∏ k : Fin 3, bitSign (β k)
  | .bit _ => 0

/-- Failure of the required sign product for one row or column constraint. -/
def constraintParityFailure (i : Fin 6) (a : MsAnswer) : Prop :=
  constraintParityProduct a ≠ bitSign (msParity i)

/-- Equality of the real parity signs is classically decidable on the finite
Magic Square answer alphabet. -/
noncomputable instance (i : Fin 6) : DecidablePred (constraintParityFailure i) :=
  fun a => Classical.propDecidable (constraintParityFailure i a)

/-- Every wrong-form constraint answer is included in the parity-failure event. -/
theorem wrongConstraintAnswer_implies_parityFailure (i : Fin 6) (a : MsAnswer)
    (ha : wrongConstraintAnswer a = true) : constraintParityFailure i a := by
  cases a with
  | triple β => simp [wrongConstraintAnswer] at ha
  | bit γ =>
      unfold constraintParityFailure constraintParityProduct
      exact (bitSign_ne_zero (msParity i)).symm

/-- Alice's local failure mass for the row or column sign product. -/
noncomputable def aliceParityFailureMass (S : Strategy msGame) (i : Fin 6) : ℝ :=
  aliceEventMass S (.constraint i) (constraintParityFailure i)

/-- Bob's local failure mass for the row or column sign product. -/
noncomputable def bobParityFailureMass (S : Strategy msGame) (i : Fin 6) : ℝ :=
  bobEventMass S (.constraint i) (constraintParityFailure i)

/-- Alice's malformed constraint mass is part of her parity-failure mass. -/
theorem aliceConstraintWrongFormMass_le_parityFailureMass (S : Strategy msGame)
    (i : Fin 6) : aliceConstraintWrongFormMass S i ≤ aliceParityFailureMass S i := by
  unfold aliceConstraintWrongFormMass aliceParityFailureMass
  rw [← eventMass_left_eq S (.constraint i) (.var (msConstraintVars i 0))]
  rw [← eventMass_left_eq S (.constraint i) (.var (msConstraintVars i 0))]
  exact eventMass_mono S _ _ _ _ fun a _ ha =>
    wrongConstraintAnswer_implies_parityFailure i a ha

/-- Bob's malformed constraint mass is part of his parity-failure mass. -/
theorem bobConstraintWrongFormMass_le_parityFailureMass (S : Strategy msGame)
    (i : Fin 6) : bobConstraintWrongFormMass S i ≤ bobParityFailureMass S i := by
  unfold bobConstraintWrongFormMass bobParityFailureMass
  rw [← eventMass_right_eq S (.var (msConstraintVars i 0)) (.constraint i)]
  rw [← eventMass_right_eq S (.var (msConstraintVars i 0)) (.constraint i)]
  exact eventMass_mono S _ _ _ _ fun _ b hb =>
    wrongConstraintAnswer_implies_parityFailure i b hb

private theorem forward_parityFailure_rejects (i : Fin 6) (k : Fin 3)
    (a b : MsAnswer) (hparity : constraintParityFailure i a) :
    msWinPredicate (.constraint i) (.var (msConstraintVars i k)) a b = false := by
  cases a with
  | bit δ => rfl
  | triple β =>
      cases b with
      | triple βb => rfl
      | bit γ =>
          rw [msWinPredicate, decide_eq_false_iff_not]
          intro haccept
          apply hparity
          unfold constraintParityProduct
          calc
            (∏ l : Fin 3, bitSign (β l)) = bitSign (∑ l : Fin 3, β l) :=
              (bitSign_sum_fin_three β).symm
            _ = bitSign (msParity i) := by rw [haccept.1]

private theorem reverse_parityFailure_rejects (i : Fin 6) (k : Fin 3)
    (a b : MsAnswer) (hparity : constraintParityFailure i b) :
    msWinPredicate (.var (msConstraintVars i k)) (.constraint i) a b = false := by
  cases a with
  | triple α => rfl
  | bit γ =>
      cases b with
      | bit δ => rfl
      | triple β =>
          rw [msWinPredicate, decide_eq_false_iff_not]
          intro haccept
          apply hparity
          unfold constraintParityProduct
          calc
            (∏ l : Fin 3, bitSign (β l)) = bitSign (∑ l : Fin 3, β l) :=
              (bitSign_sum_fin_three β).symm
            _ = bitSign (msParity i) := by rw [haccept.1]

/-- Alice satisfies each of the six row or column sign products up to mass `36 * ε`. -/
theorem aliceParityFailureMass_le (S : Strategy msGame) (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) (i : Fin 6) :
    aliceParityFailureMass S i ≤ 36 * ε := by
  unfold aliceParityFailureMass
  rw [← eventMass_left_eq S (.constraint i) (.var (msConstraintVars i 0))]
  calc
    eventMass S (.constraint i) (.var (msConstraintVars i 0))
        (fun a _ => constraintParityFailure i a) ≤
        rejectionMass S (.constraint i) (.var (msConstraintVars i 0)) :=
      eventMass_le_rejectionMass S _ _ _ (forward_parityFailure_rejects i 0)
    _ ≤ 36 * ε :=
      rejectionMass_le S ε hwin (ms_forward_incidence_mem_support i 0)

/-- Bob satisfies each of the six row or column sign products up to mass `36 * ε`. -/
theorem bobParityFailureMass_le (S : Strategy msGame) (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) (i : Fin 6) :
    bobParityFailureMass S i ≤ 36 * ε := by
  unfold bobParityFailureMass
  rw [← eventMass_right_eq S (.var (msConstraintVars i 0)) (.constraint i)]
  calc
    eventMass S (.var (msConstraintVars i 0)) (.constraint i)
        (fun _ b => constraintParityFailure i b) ≤
        rejectionMass S (.var (msConstraintVars i 0)) (.constraint i) :=
      eventMass_le_rejectionMass S _ _ _ (reverse_parityFailure_rejects i 0)
    _ ≤ 36 * ε :=
      rejectionMass_le S ε hwin (ms_reverse_incidence_mem_support i 0)

end

end MIPStarRE.QPBT.MagicSquareRigidity
