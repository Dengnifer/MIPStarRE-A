import MIPStarRE.QPBT.Observables.WinImplications.Setup

/-!
# Averaging lemmas for winning implications

This module derives the finite conditioning and fixed-edge rejection bounds
used by all seven exact winning implications.

## References

The proof infrastructure in this module supports `lem:qld-win-implications`
from `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:192-267`
and `blueprint/src/chapter/ch14_qpbt_observables.tex:505-660`.
-/

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace WinImplications

local instance pauliEdgeNonempty : Nonempty PauliEdge := pauliEdge_nonempty

theorem pauliScalar_eq_scalarQ (P : AdmissibleParams) :
    PauliScalar P = ScalarQ P.toLdParams := by
  rfl

/-- View a low-degree scalar through the definitionally equal Pauli carrier. -/
def scalarToPauli (P : AdmissibleParams) :
    ScalarQ P.toLdParams → PauliScalar P :=
  cast (pauliScalar_eq_scalarQ P).symm

/-- A fixed component of a nonnegative uniform product average is bounded by
the cardinality of the first factor times the full average. -/
theorem avgOver_uniform_fixed_le_card_mul_prod
    {X Y : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (f : X → Y → ℝ) (hf : ∀ x y, 0 ≤ f x y) (x0 : X) :
    avgOver (uniformDistribution Y) (f x0) ≤
      (Fintype.card X : ℝ) *
        avgOver (uniformDistribution (X × Y)) (fun xy => f xy.1 xy.2) := by
  rw [avgOver_uniform_prod]
  have hcard : (Fintype.card X : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hsum : (Fintype.card X : ℝ) *
      avgOver (uniformDistribution X)
        (fun x => avgOver (uniformDistribution Y) (f x)) =
      ∑ x : X, avgOver (uniformDistribution Y) (f x) := by
    unfold avgOver uniformDistribution Distribution.uniformOnFinset
    simp only [Finset.mem_univ, ↓reduceIte, Finset.card_univ]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    field_simp
  rw [hsum]
  exact Finset.single_le_sum
    (fun x _ => avgOver_nonneg (uniformDistribution Y) (f x) (hf x))
    (Finset.mem_univ x0)

/-- A finite distribution average may be extended to the full finite type. -/
theorem avgOver_eq_sum_univ {X : Type*} [Fintype X]
    (μ : Distribution X) (f : X → ℝ) :
    avgOver μ f = ∑ x : X, μ.weight x * f x := by
  classical
  unfold avgOver
  apply Finset.sum_subset (Finset.subset_univ μ.support)
  intro x _ hx
  rw [μ.outsideSupport x hx, zero_mul]

/-- Averaging against a convex mixture is the corresponding convex combination. -/
theorem avgOver_mix {X : Type*} [Finite X] [DecidableEq X]
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (μ ν : Distribution X) (f : X → ℝ) :
    avgOver (Distribution.mix t ht0 ht1 μ ν) f =
      t * avgOver μ f + (1 - t) * avgOver ν f := by
  letI := Fintype.ofFinite X
  rw [avgOver_eq_sum_univ, avgOver_eq_sum_univ, avgOver_eq_sum_univ]
  simp only [Distribution.mix]
  calc
    (∑ x, (t * μ.weight x + (1 - t) * ν.weight x) * f x) =
        (∑ x, (t * (μ.weight x * f x) + (1 - t) * (ν.weight x * f x))) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = t * (∑ x, μ.weight x * f x) +
        (1 - t) * (∑ x, ν.weight x * f x) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-- Conditioning a uniform finite law divides its gated ambient average by the event probability. -/
theorem cardRatio_mul_avgOver_filter
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (p : X → Prop) [DecidablePred p] (hp : (Finset.univ.filter p).Nonempty)
    (f : X → ℝ) :
    ((Finset.univ.filter p).card : ℝ) / Fintype.card X *
        avgOver (Distribution.uniformOnFinset (Finset.univ.filter p)) f =
      avgOver (uniformDistribution X) (fun x => if p x then f x else 0) := by
  have hcardX : (Fintype.card X : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hcardp : ((Finset.univ.filter p).card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hp
  unfold avgOver uniformDistribution
  simp only [Distribution.uniformOnFinset_support,
    Distribution.uniformOnFinset_weight, Finset.mem_filter, Finset.mem_univ,
    true_and, if_true]
  rw [Finset.card_univ]
  rw [show (∑ x ∈ Finset.univ.filter p,
      (if p x then 1 / ((Finset.univ.filter p).card : ℝ) else 0) * f x) =
      ∑ x ∈ Finset.univ.filter p,
        1 / ((Finset.univ.filter p).card : ℝ) * f x by
    apply Finset.sum_congr rfl
    intro x hx
    simp [(Finset.mem_filter.mp hx).2]]
  rw [show (∑ x ∈ Finset.univ.filter p,
      1 / ((Finset.univ.filter p).card : ℝ) * f x) =
      1 / ((Finset.univ.filter p).card : ℝ) *
        ∑ x ∈ Finset.univ.filter p, f x by
    rw [Finset.mul_sum]]
  rw [show (∑ x ∈ Finset.univ,
      1 / (Fintype.card X : ℝ) * (if p x then f x else 0)) =
      1 / (Fintype.card X : ℝ) * ∑ x ∈ Finset.univ.filter p, f x by
    rw [Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : p x <;> simp [hx]]
  field_simp

/-- Conditioning on the commuting event costs at most its reciprocal lower bound. -/
theorem avgOver_comm_le_two_mul_gated (P : AdmissibleParams)
    (f : PauliTuple P → ℝ) (hf : ∀ ω, 0 ≤ f ω) :
    avgOver (commTupleDist P) f ≤
      2 * avgOver (uniformDistribution (PauliTuple P))
        (fun ω => if IsCommuting ω then f ω else 0) := by
  have hnonempty : (Finset.univ.filter (@IsCommuting P)).Nonempty := by
    refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    simp [IsCommuting, gammaValue, fixedBinTrace, binTrace, dotProduct]
  have heq := cardRatio_mul_avgOver_filter (@IsCommuting P) hnonempty f
  change commProb P * avgOver (commTupleDist P) f = _ at heq
  have havg : 0 ≤ avgOver (commTupleDist P) f :=
    avgOver_nonneg (commTupleDist P) f hf
  nlinarith [commProb_ge_half P]

/-- Conditioning on the anticommuting event costs at most sixteen. -/
theorem avgOver_anticomm_le_sixteen_mul_gated (P : AdmissibleParams)
    (f : PauliTuple P → ℝ) (hf : ∀ ω, 0 ≤ f ω) :
    avgOver (anticommTupleDist P) f ≤
      16 * avgOver (uniformDistribution (PauliTuple P))
        (fun ω => if IsAnticommuting ω then f ω else 0) := by
  have hnonempty : (Finset.univ.filter (@IsAnticommuting P)).Nonempty := by
    by_contra h
    have hempty : Finset.univ.filter (@IsAnticommuting P) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp h
    have hprob := anticommTupleDist_isProbability P
    unfold anticommTupleDist Distribution.IsProbability Distribution.totalWeight at hprob
    rw [hempty] at hprob
    simp at hprob
  have heq := cardRatio_mul_avgOver_filter (@IsAnticommuting P) hnonempty f
  change anticommProb P * avgOver (anticommTupleDist P) f = _ at heq
  have hqpos : 0 < P.q := by
    obtain ⟨k, _, hk⟩ := P.hq
    rw [hk]
    positivity
  have hmq : P.m ≤ P.q := Nat.le_of_dvd hqpos P.hdvd
  have hprob := anticommProb_ge_of_m_le_q P hmq
  norm_num at hprob
  have havg : 0 ≤ avgOver (anticommTupleDist P) f :=
    avgOver_nonneg (anticommTupleDist P) f hf
  nlinarith

/-- Inconsistency of two postprocessed strategy measurements is the Born mass
of source outcomes whose postprocessed labels differ. -/
theorem consistencyDefect_postprocess_eq_mismatch
    {G : Game} {X β : Type*} [Fintype X] [DecidableEq X]
    [Fintype β] [DecidableEq β]
    (μ : Distribution X) (S : Strategy G)
    (qA : X → G.QuestionA) (qB : X → G.QuestionB)
    (fA : X → G.AnswerA → β) (fB : X → G.AnswerB → β) :
    consistencyDefect μ
        (fun x c => heteroKron (((S.A (qA x)).postprocess (fA x)).effect c) 1)
        (fun x c => heteroKron 1 (((S.B (qB x)).postprocess (fB x)).effect c))
        S.ψ =
      avgOver μ (fun x => outcomeEventWeight S (qA x) (qB x)
        (fun a b => fA x a ≠ fB x b)) := by
  unfold consistencyDefect outcomeEventWeight
  apply avgOver_congr
  intro x
  simp only [DistanceCalculus.consistency_term_eq_stateQForm,
    MIPStarRE.Quantum.Measurement.postprocess_effect]
  simp_rw [DistanceCalculus.placed_product_stateQForm_eq]
  have hmass (c d : β) :
      DistanceCalculus.stateQForm S.ψ
          (heteroKron
            (∑ a ∈ Finset.univ.filter (fun a => fA x a = c),
              (S.A (qA x)).effect a)
            (∑ b ∈ Finset.univ.filter (fun b => fB x b = d),
              (S.B (qB x)).effect b)) =
        ∑ a ∈ Finset.univ.filter (fun a => fA x a = c),
          ∑ b ∈ Finset.univ.filter (fun b => fB x b = d),
            outcomeWeight S (qA x) (qB x) a b := by
    have hop :
        heteroKron
            (∑ a ∈ Finset.univ.filter (fun a => fA x a = c),
              (S.A (qA x)).effect a)
            (∑ b ∈ Finset.univ.filter (fun b => fB x b = d),
              (S.B (qB x)).effect b) =
          ∑ a ∈ Finset.univ.filter (fun a => fA x a = c),
            ∑ b ∈ Finset.univ.filter (fun b => fB x b = d),
              heteroKron ((S.A (qA x)).effect a) ((S.B (qB x)).effect b) := by
      ext i j
      simp only [Matrix.sum_apply, heteroKron, Matrix.kronecker,
        Matrix.kroneckerMap_apply]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
    rw [hop]
    simp [DistanceCalculus.stateQForm, outcomeWeight, applyOperatorToState]
  simp_rw [hmass]
  symm
  calc
    (∑ a, ∑ b, if fA x a ≠ fB x b then
        outcomeWeight S (qA x) (qB x) a b else 0) =
        ∑ a, ∑ b,
          if fA x a = fB x b then 0 else outcomeWeight S (qA x) (qB x) a b := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      by_cases hab : fA x a = fB x b <;> simp [hab]
    _ = ∑ c : β, ∑ a ∈ Finset.univ.filter (fun a => fA x a = c),
          ∑ b, if fA x a = fB x b then 0 else
            outcomeWeight S (qA x) (qB x) a b := by
      exact (Finset.sum_fiberwise Finset.univ (fA x)
        (fun a => ∑ b, if fA x a = fB x b then 0 else
          outcomeWeight S (qA x) (qB x) a b)).symm
    _ = ∑ c : β, ∑ a ∈ Finset.univ.filter (fun a => fA x a = c),
          ∑ b, if c = fB x b then 0 else outcomeWeight S (qA x) (qB x) a b := by
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro a ha
      rw [(Finset.mem_filter.mp ha).2]
    _ = ∑ c : β, ∑ a ∈ Finset.univ.filter (fun a => fA x a = c),
          ∑ d : β, ∑ b ∈ Finset.univ.filter (fun b => fB x b = d),
            if c = fB x b then 0 else outcomeWeight S (qA x) (qB x) a b := by
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro a _
      exact (Finset.sum_fiberwise Finset.univ (fB x)
        (fun b => if c = fB x b then 0 else
          outcomeWeight S (qA x) (qB x) a b)).symm
    _ = ∑ c : β, ∑ a ∈ Finset.univ.filter (fun a => fA x a = c),
          ∑ d : β, ∑ b ∈ Finset.univ.filter (fun b => fB x b = d),
            if c = d then 0 else outcomeWeight S (qA x) (qB x) a b := by
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro b hb
      rw [(Finset.mem_filter.mp hb).2]
    _ = ∑ c : β, ∑ d : β,
          ∑ a ∈ Finset.univ.filter (fun a => fA x a = c),
            ∑ b ∈ Finset.univ.filter (fun b => fB x b = d),
              if c = d then 0 else outcomeWeight S (qA x) (qB x) a b := by
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]
    _ = ∑ c : β, ∑ d : β, if c = d then 0 else
          ∑ a ∈ Finset.univ.filter (fun a => fA x a = c),
            ∑ b ∈ Finset.univ.filter (fun b => fB x b = d),
              outcomeWeight S (qA x) (qB x) a b := by
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro d _
      by_cases hcd : c = d <;> simp [hcd]

/-- Two successive relabelings have the same effects as their composite. -/
theorem measurement_postprocess_comp_effect
    {d α β γ : Type*} [Fintype d] [DecidableEq d]
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ]
    (M : Measurement α d) (f : α → β) (g : β → γ) (c : γ) :
    ((M.postprocess f).postprocess g).effect c =
      (M.postprocess (g ∘ f)).effect c := by
  change (∑ b ∈ Finset.univ.filter (fun b => g b = c),
      ∑ a ∈ Finset.univ.filter (fun a => f a = b), M.effect a) =
    ∑ a ∈ Finset.univ.filter (fun a => g (f a) = c), M.effect a
  simp_rw [Finset.sum_filter]
  calc
    (∑ b, if g b = c then ∑ a, if f a = b then M.effect a else 0 else 0) =
        ∑ b, ∑ a, if g b = c then
          (if f a = b then M.effect a else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : g b = c <;> simp [hb]
    _ = ∑ a, ∑ b, if g b = c then
          (if f a = b then M.effect a else 0) else 0 := Finset.sum_comm
    _ = ∑ a, if g (f a) = c then M.effect a else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : g (f a) = c
      · rw [Finset.sum_eq_single (f a)]
        · simp [h]
        · intro b _ hba
          by_cases hgb : g b = c
          · simp only [hgb, if_true]
            split
            · rename_i hab
              exact (hba hab.symm).elim
            · rfl
          · simp [hgb]
        · simp
      · rw [Finset.sum_eq_single (f a)]
        · simp [h]
        · intro b _ hba
          by_cases hgb : g b = c
          · simp only [hgb, if_true]
            split
            · rename_i hab
              exact (hba hab.symm).elim
            · rfl
          · simp [hgb]
        · simp

/-- The consistency defect depends only on its two effect families. -/
theorem consistencyDefect_congr
    {X α ι : Type*} [Fintype X] [DecidableEq X]
    [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A A' B B' : X → α → Op ι)
    (ψ : EuclideanSpace ℂ ι)
    (hA : ∀ x a, A x a = A' x a) (hB : ∀ x a, B x a = B' x a) :
    consistencyDefect μ A B ψ = consistencyDefect μ A' B' ψ := by
  have hAf : A = A' := by
    funext x a
    exact hA x a
  have hBf : B = B' := by
    funext x a
    exact hB x a
  rw [hAf, hBf]

/-- The question pair generated by a fixed ordered Pauli edge and seed. -/
def pauliSourceQuestions (P : AdmissibleParams) (e : PauliEdge)
    (z : PauliSpace P) : PauliQuestion P × PauliQuestion P :=
  ((e.1.1, pauliCL P e.1.1 z), (e.1.2, pauliCL P e.1.2 z))

/-- Rejection mass at a fixed ordered Pauli edge and seed. -/
noncomputable def pauliRejectionAt {P : AdmissibleParams}
    (S : Strategy (pauliBasisTest P)) (e : PauliEdge) (z : PauliSpace P) : ℝ :=
  let questions := pauliSourceQuestions P e z
  outcomeEventWeight S questions.1 questions.2 fun a b =>
    (pauliBasisTest P).decide questions.1 questions.2 a b = false

/-- Rejection mass at every fixed edge and seed is nonnegative. -/
theorem pauliRejectionAt_nonneg {P : AdmissibleParams}
    (S : Strategy (pauliBasisTest P)) (e : PauliEdge) (z : PauliSpace P) :
    0 ≤ pauliRejectionAt S e z := by
  exact outcome_event_weight_nonneg S _ _ _

/-- The average rejection mass of a finite game is one minus its value. -/
theorem rejectionMass_eq_one_sub_value {G : Game} (S : Strategy G) :
    avgOver G.μ (fun questions =>
      outcomeEventWeight S questions.1 questions.2 fun a b =>
        G.decide questions.1 questions.2 a b = false) =
      1 - S.value := by
  classical
  rw [show avgOver G.μ (fun questions =>
      outcomeEventWeight S questions.1 questions.2 fun a b =>
        G.decide questions.1 questions.2 a b = false) =
      avgOver G.μ (fun questions =>
        1 - ∑ a, ∑ b,
          if G.decide questions.1 questions.2 a b then
            outcomeWeight S questions.1 questions.2 a b else 0) by
    apply avgOver_congr
    intro questions
    unfold outcomeEventWeight
    calc
      (∑ a, ∑ b, if G.decide questions.1 questions.2 a b = false then
          outcomeWeight S questions.1 questions.2 a b else 0) =
          ∑ a, ∑ b,
            (outcomeWeight S questions.1 questions.2 a b -
              if G.decide questions.1 questions.2 a b then
                outcomeWeight S questions.1 questions.2 a b else 0) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        split <;> simp_all
      _ = (∑ a, ∑ b, outcomeWeight S questions.1 questions.2 a b) -
          ∑ a, ∑ b,
            if G.decide questions.1 questions.2 a b then
              outcomeWeight S questions.1 questions.2 a b else 0 := by
        rw [show (∑ a, ∑ b,
            (outcomeWeight S questions.1 questions.2 a b -
              if G.decide questions.1 questions.2 a b then
                outcomeWeight S questions.1 questions.2 a b else 0)) =
            ∑ a, ((∑ b, outcomeWeight S questions.1 questions.2 a b) -
              ∑ b, if G.decide questions.1 questions.2 a b then
                outcomeWeight S questions.1 questions.2 a b else 0) by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_sub_distrib]]
        rw [Finset.sum_sub_distrib]
      _ = 1 - ∑ a, ∑ b,
          if G.decide questions.1 questions.2 a b then
            outcomeWeight S questions.1 questions.2 a b else 0 := by
        rw [outcomeWeight_sum_eq_one]]
  rw [avgOver_sub, avgOver_const_of_isProbability G.μ G.μ_prob]
  rfl

/-- Winning bounds the global rejection average. -/
theorem pauliRejectionAverage_le_error {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) :
    avgOver (uniformDistribution (PauliEdge × PauliSpace P))
        (fun ez => pauliRejectionAt S.toStrategy ez.1 ez.2) ≤ ε := by
  have havg : avgOver (uniformDistribution (PauliEdge × PauliSpace P))
      (fun ez => pauliRejectionAt S.toStrategy ez.1 ez.2) =
      1 - S.toStrategy.value := by
    rw [← rejectionMass_eq_one_sub_value S.toStrategy]
    unfold pauliBasisTest pauliQuestionDistribution
    rw [Distribution.avgOver_map]
    rfl
  rw [havg]
  linarith [S.win]

/-- Fixing one verifier edge costs at most the cardinality of the finite edge graph. -/
theorem fixedEdgeRejection_le_error {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (e : PauliEdge) :
    avgOver (uniformDistribution (PauliSpace P)) (pauliRejectionAt S.toStrategy e) ≤
      (Fintype.card PauliEdge : ℝ) * ε := by
  calc
    avgOver (uniformDistribution (PauliSpace P)) (pauliRejectionAt S.toStrategy e) ≤
        (Fintype.card PauliEdge : ℝ) *
          avgOver (uniformDistribution (PauliEdge × PauliSpace P))
            (fun ez => pauliRejectionAt S.toStrategy ez.1 ez.2) := by
      exact avgOver_uniform_fixed_le_card_mul_prod _
        (fun edge z => pauliRejectionAt_nonneg S.toStrategy edge z) e
    _ ≤ (Fintype.card PauliEdge : ℝ) * ε := by
      exact mul_le_mul_of_nonneg_left (pauliRejectionAverage_le_error S)
        (Nat.cast_nonneg _)


end WinImplications

end

end MIPStarRE.QPBT
