import MIPStarRE.QPBT.Observables.WinImplications.Setup

/-!
# Averaging lemmas for winning implications

This module derives the finite conditioning and fixed-edge rejection bounds
used by all seven exact winning implications.

## References

The formalization-only averaging and conditioning auxiliaries support items 1–7
of `lem:qld-win-implications`
from `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:192-267`
and blueprint `lem:qld-win-implications` and `lem:qld-win-implications-obs`.
-/

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace WinImplications

scoped instance pauliEdgeNonempty : Nonempty PauliEdge := pauliEdge_nonempty

/-- Formalization-only auxiliary for items 1–7 of `lem:qld-win-implications`:
a fixed component of a nonnegative uniform product average is bounded by
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

/-- Formalization-only auxiliary for items 1–7 of `lem:qld-win-implications`:
a finite distribution average may be extended to the full finite type. -/
theorem avgOver_eq_sum_univ {X : Type*} [Fintype X]
    (μ : Distribution X) (f : X → ℝ) :
    avgOver μ f = ∑ x : X, μ.weight x * f x := by
  classical
  exact (Distribution.sum_univ_eq_sum_support μ (fun x => μ.weight x * f x)
    (fun x hx => by rw [μ.outsideSupport x hx, zero_mul])).symm

/-- Formalization-only auxiliary for item 2 of `lem:qld-win-implications`:
averaging against a convex mixture is the corresponding convex combination. -/
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

/-- Formalization-only auxiliary for items 4–7 of `lem:qld-win-implications`:
conditioning a uniform law divides its gated ambient average by the event probability. -/
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

/-- Formalization-only auxiliary for items 1–5 and 7 of `lem:qld-win-implications`:
inconsistency of two postprocessed strategy measurements is the Born mass
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

/-- Formalization-only auxiliary for items 1–7 of `lem:qld-win-implications`:
the average rejection mass of a finite game is one minus its value. -/
theorem rejectionEventAverage_eq_one_sub_value {G : Game} (S : Strategy G) :
    avgOver G.μ (fun questions =>
      outcomeEventWeight S questions.1 questions.2 fun a b =>
        G.decide questions.1 questions.2 a b = false) =
      1 - S.value := by
  classical
  simpa only [outcomeEventWeight, Bool.eq_false_iff, ite_not] using
    MIPStarRE.QPBT.rejectionMass_eq_one_sub_value S

/-- Winning bounds the global rejection average. -/
theorem pauliRejectionAverage_le_error {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) :
    avgOver (uniformDistribution (PauliEdge × PauliSpace P))
        (fun ez => pauliRejectionAt S.toStrategy ez.1 ez.2) ≤ ε := by
  have havg : avgOver (uniformDistribution (PauliEdge × PauliSpace P))
      (fun ez => pauliRejectionAt S.toStrategy ez.1 ez.2) =
      1 - S.toStrategy.value := by
    rw [← rejectionEventAverage_eq_one_sub_value S.toStrategy]
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
