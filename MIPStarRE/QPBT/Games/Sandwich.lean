import MIPStarRE.QPBT.Games.DistanceTheorems
import MIPStarRE.QPBT.Games.ErrorFunctions

/-! # Sandwiched measurements and pasting

This module defines the ordered palindromic products used to combine
measurements and records the two quantitative consistency statements imported
by the QPBT analysis.

## References

The source results are `lem:ld-sandwich` and `lem:pasting` in
`blueprint/src/chapter/ch12_qpbt_games.tex:454-546`, with paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:465-525`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum
open DistanceCalculus

/-- Recursive form of the palindromic operator product, extending a tuple by
placing its final operator on both sides of the preceding product. -/
private noncomputable def sandwichProductCore {ι : Type*}
    [Fintype ι] [DecidableEq ι] :
    (k : ℕ) → (Γ : Fin k → Type*) →
      ((i : Fin k) → Γ i → Op ι) → ((i : Fin k) → Γ i) → Op ι
  | 0, _, _, _ => 1
  | 1, _, G, g => G 0 (g 0)
  | k + 2, Γ, G, g =>
      G (Fin.last (k + 1)) (g (Fin.last (k + 1))) *
        sandwichProductCore (k + 1) (fun i => Γ i.castSucc)
          (fun i a => G i.castSucc a) (fun i => g i.castSucc) *
        G (Fin.last (k + 1)) (g (Fin.last (k + 1)))

/-- The ordered product
`G^k_{g_k} ... G^1_{g_1} ... G^k_{g_k}` of `lem:ld-sandwich`.

**Local fix:** The source reverses the outcome indices, which is ill-typed when
the outcome families differ. This definition uses the pairing corrected in
`rem:ld-sandwich-indexing` and
`docs/paper-gaps/qpbt_ld-sandwich-indexing.tex`; blueprint statement
`ch12_qpbt_games.tex:454-480` and remark `ch12_qpbt_games.tex:485-487`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:465-501`. Tracked in
issue #16. The empty product is `1`. -/
noncomputable def sandwichProduct {k : ℕ} {X ι : Type*}
    [Fintype ι] [DecidableEq ι] {Γ : Fin k → Type*}
    (G : (i : Fin k) → X → Γ i → Op ι) (x : X)
    (g : (i : Fin k) → Γ i) : Op ι :=
  sandwichProductCore k Γ (fun i a => G i x a) g

/-- The two-family sandwiched product
`(G₂)_{g₂} (G₁)_{g₁} (G₂)_{g₂}` from `eq:pasting-2a`; blueprint
`ch12_qpbt_games.tex:517-546`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`. -/
def pastedMeasurement {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G₁ G₂ : Type*} (M₁ : G₁ → Op ι) (M₂ : G₂ → Op ι)
    (g₁ : G₁) (g₂ : G₂) : Op ι :=
  M₂ g₂ * M₁ g₁ * M₂ g₂

/-- Evaluating a tuple of codewords at a common point. This is a
formalization-only auxiliary for `lem:ld-sandwich`, blueprint
`ch12_qpbt_games.tex:454-480`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:465-495`. -/
def evalFunctionTuple {k : ℕ} {Y : Type*} {R Γ : Fin k → Type*}
    (eval : (i : Fin k) → Γ i → Y → R i) (y : Y)
    (g : (i : Fin k) → Γ i) : (i : Fin k) → R i :=
  fun i => eval i (g i) y

/-- Averaging over the product of two finite distributions is iterated
averaging. -/
private theorem avgOver_distribution_prod {X Y : Type*}
    [DecidableEq X] [DecidableEq Y] (μ : Distribution X) (ν : Distribution Y)
    (f : X × Y → ℝ) :
    avgOver (Distribution.prod μ ν) f =
      avgOver μ (fun x => avgOver ν (fun y => f (x, y))) := by
  unfold avgOver
  change (∑ p ∈ μ.support.product ν.support,
    (μ.weight p.1 * ν.weight p.2) * f p) = _
  calc
    (∑ p ∈ μ.support.product ν.support,
        (μ.weight p.1 * ν.weight p.2) * f p) =
        ∑ x ∈ μ.support, ∑ y ∈ ν.support,
          (μ.weight x * ν.weight y) * f (x, y) := by
      exact Finset.sum_product' μ.support ν.support
        (fun x y => (μ.weight x * ν.weight y) * f (x, y))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring

/-- The diagonal overlap after a common relabeling is the sum over pairs of
original outcomes with equal labels. -/
private theorem diagonal_postprocess_stateQForm_eq_pair_sum
    {α β ιA ιB : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Measurement α ιA) (B : Measurement α ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (f : α → β) :
    (∑ b : β, stateQForm ψ
      (heteroKron ((A.postprocess f).effect b) ((B.postprocess f).effect b))) =
      ∑ a : α, ∑ a' : α, if f a = f a' then
        stateQForm ψ (heteroKron (A.effect a) (B.effect a')) else 0 := by
  classical
  have hterm (b : β) : stateQForm ψ
      (heteroKron ((A.postprocess f).effect b) ((B.postprocess f).effect b)) =
      ∑ a : α, ∑ a' : α, if f a = b ∧ f a' = b then
        stateQForm ψ (heteroKron (A.effect a) (B.effect a')) else 0 := by
    rw [MIPStarRE.Quantum.Measurement.postprocess_effect,
      MIPStarRE.Quantum.Measurement.postprocess_effect,
      heteroKron_finset_sum_left, stateQForm_finset_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    by_cases hab : f a = b
    · rw [if_pos hab, heteroKron_finset_sum_right, stateQForm_finset_sum,
        Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a' _
      by_cases ha'b : f a' = b <;> simp [hab, ha'b]
    · simp [hab]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a' _
  by_cases haa' : f a = f a'
  · rw [haa']
    simp
  · apply Eq.trans (Finset.sum_eq_zero (fun b _ => by
      simp only [ite_eq_right_iff]
      intro hpair
      exact (haa' (hpair.1.trans hpair.2.symm)).elim))
    simp [haa']

/-- The consistency defect of tensor-placed local measurements is the average
of their pointwise off-diagonal tensor overlap. -/
private theorem consistencyDefect_placed_eq_avg_point
    {X α ιA ιB : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : Distribution X) (A : X → Measurement α ιA)
    (B : X → Measurement α ιB) (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    consistencyDefect μ
        (fun x a => heteroKron ((A x).effect a) 1)
        (fun x a => heteroKron 1 ((B x).effect a)) ψ =
      avgOver μ (fun x => ∑ a : α, ∑ a' : α, if a = a' then 0 else
        stateQForm ψ (heteroKron ((A x).effect a) ((B x).effect a'))) := by
  unfold consistencyDefect
  apply avgOver_congr
  intro x
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro a' _
  by_cases haa' : a = a'
  · simp [haa']
  · simp only [if_neg haa']
    rw [consistency_term_eq_stateQForm, placed_product_stateQForm_eq]

set_option maxHeartbeats 600000 in
-- Normalizing the nested finite sums requires a larger elaboration budget.
/-- Averaged diagonal overlap after evaluation exceeds the original diagonal
overlap by at most the collision probability. -/
private theorem avg_diagonal_postprocess_stateQForm_le
    {Y Γ R ιA ιB : Type*}
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype Γ] [DecidableEq Γ] [Fintype R] [DecidableEq R]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Measurement Γ ιA) (B : Measurement Γ ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (eval : Γ → Y → R) (ε : ℝ)
    (hψ : ‖ψ‖ = 1) (hε : 0 ≤ ε)
    (hcollision : ∀ g g' : Γ, g ≠ g' →
      avgOver (uniformDistribution Y)
        (fun y => if eval g y = eval g' y then 1 else 0) ≤ ε) :
    avgOver (uniformDistribution Y) (fun y =>
      ∑ r : R, stateQForm ψ
        (heteroKron
          ((A.postprocess (fun g => eval g y)).effect r)
          ((B.postprocess (fun g => eval g y)).effect r))) ≤
      (∑ g : Γ, stateQForm ψ (heteroKron (A.effect g) (B.effect g))) + ε := by
  classical
  let w : Γ → Γ → ℝ := fun g g' =>
    stateQForm ψ (heteroKron (A.effect g) (B.effect g'))
  have hw (g g' : Γ) : 0 ≤ w g g' := by
    apply stateQForm_nonneg
    exact MIPStarRE.Quantum.kronecker_nonneg (A.pos g) (B.pos g')
  have hoffdiag_le_one :
      (∑ g : Γ, ∑ g' : Γ, if g = g' then 0 else w g g') ≤ 1 := by
    let AL := leftPlacedMeasurement (ιB := ιB) A
    let BR := rightPlacedMeasurement (ιA := ιA) B
    have hpoint := point_defect_eq AL BR ψ
    simp only [AL, BR, leftPlacedMeasurement, rightPlacedMeasurement,
      MIPStarRE.Quantum.Measurement.ofSumEqOne] at hpoint
    simp_rw [placed_product_stateQForm_eq] at hpoint
    have hdiag : 0 ≤ ∑ g : Γ, w g g :=
      Finset.sum_nonneg fun g _ => hw g g
    change (∑ g : Γ, ∑ g' : Γ, if g = g' then 0 else
      stateQForm ψ (heteroKron (A.effect g) (B.effect g'))) ≤ 1
    rw [hpoint, hψ]
    norm_num
    exact hdiag
  have hdiagpart :
      (∑ g : Γ, ∑ g' : Γ, if g = g' then w g g' else 0) =
        ∑ g : Γ, w g g := by
    apply Finset.sum_congr rfl
    intro g _
    rw [Fintype.sum_eq_single g]
    · simp
    · intro g' hg'
      simp [Ne.symm hg']
  have hsplit :
      (∑ g : Γ, ∑ g' : Γ,
        if g = g' then w g g' else ε * w g g') =
      (∑ g : Γ, w g g) +
        ε * (∑ g : Γ, ∑ g' : Γ,
          if g = g' then 0 else w g g') := by
    calc
      (∑ g : Γ, ∑ g' : Γ,
          if g = g' then w g g' else ε * w g g') =
          ∑ g : Γ, ∑ g' : Γ,
            ((if g = g' then w g g' else 0) +
              ε * (if g = g' then 0 else w g g')) := by
        apply Finset.sum_congr rfl
        intro g _
        apply Finset.sum_congr rfl
        intro g' _
        by_cases hgg' : g = g' <;> simp [hgg']
      _ = (∑ g : Γ, ∑ g' : Γ,
            if g = g' then w g g' else 0) +
          ε * (∑ g : Γ, ∑ g' : Γ,
            if g = g' then 0 else w g g') := by
        simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = _ := by rw [hdiagpart]
  change avgOver (uniformDistribution Y) (fun y =>
      ∑ r : R, stateQForm ψ
        (heteroKron
          ((A.postprocess (fun g => eval g y)).effect r)
          ((B.postprocess (fun g => eval g y)).effect r))) ≤
    (∑ g : Γ, w g g) + ε
  calc
    avgOver (uniformDistribution Y) (fun y =>
        ∑ r : R, stateQForm ψ
          (heteroKron
            ((A.postprocess (fun g => eval g y)).effect r)
            ((B.postprocess (fun g => eval g y)).effect r))) =
        ∑ g : Γ, ∑ g' : Γ,
          avgOver (uniformDistribution Y) (fun y =>
            if eval g y = eval g' y then w g g' else 0) := by
      simp_rw [diagonal_postprocess_stateQForm_eq_pair_sum]
      rw [avgOver_sum]
      apply Finset.sum_congr rfl
      intro g _
      rw [avgOver_sum]
    _ ≤ ∑ g : Γ, ∑ g' : Γ,
        if g = g' then w g g' else ε * w g g' := by
      apply Finset.sum_le_sum
      intro g _
      apply Finset.sum_le_sum
      intro g' _
      by_cases hgg' : g = g'
      · subst g'
        simp only [if_pos]
        exact le_of_eq (avgOver_uniform_const (w g g))
      · rw [if_neg hgg']
        calc
          avgOver (uniformDistribution Y) (fun y =>
              if eval g y = eval g' y then w g g' else 0) =
              avgOver (uniformDistribution Y) (fun y =>
                (if eval g y = eval g' y then 1 else 0) * w g g') := by
            apply avgOver_congr
            intro y
            by_cases heq : eval g y = eval g' y <;> simp [heq]
          _ = avgOver (uniformDistribution Y)
              (fun y => if eval g y = eval g' y then 1 else 0) * w g g' :=
            avgOver_mul_const _ _ _
          _ ≤ ε * w g g' :=
            mul_le_mul_of_nonneg_right (hcollision g g' hgg') (hw g g')
    _ = (∑ g : Γ, w g g) +
        ε * (∑ g : Γ, ∑ g' : Γ,
          if g = g' then 0 else w g g') := hsplit
    _ ≤ (∑ g : Γ, w g g) + ε := by
      gcongr
      simpa using mul_le_mul_of_nonneg_left hoffdiag_le_one hε

set_option maxHeartbeats 600000 in
-- Rewriting the averaged complementary overlaps needs the same budget.
/-- Taking complements converts the diagonal-overlap estimate into a
pointwise consistency-defect estimate. -/
private theorem point_codeword_defect_le_avg_evaluated_add
    {Y Γ R ιA ιB : Type*}
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype Γ] [DecidableEq Γ] [Fintype R] [DecidableEq R]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Measurement Γ ιA) (B : Measurement Γ ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (eval : Γ → Y → R) (ε : ℝ)
    (hψ : ‖ψ‖ = 1) (hε : 0 ≤ ε)
    (hcollision : ∀ g g' : Γ, g ≠ g' →
      avgOver (uniformDistribution Y)
        (fun y => if eval g y = eval g' y then 1 else 0) ≤ ε) :
    (∑ g : Γ, ∑ g' : Γ, if g = g' then 0 else
      stateQForm ψ (heteroKron (A.effect g) (B.effect g'))) ≤
      avgOver (uniformDistribution Y) (fun y =>
        ∑ r : R, ∑ r' : R, if r = r' then 0 else
          stateQForm ψ
            (heteroKron
              ((A.postprocess (fun g => eval g y)).effect r)
              ((B.postprocess (fun g => eval g y)).effect r'))) + ε := by
  have hdiag_avg := avg_diagonal_postprocess_stateQForm_le
    A B ψ eval ε hψ hε hcollision
  have hfull := point_defect_eq
    (leftPlacedMeasurement (ιB := ιB) A)
    (rightPlacedMeasurement (ιA := ιA) B) ψ
  simp only [leftPlacedMeasurement, rightPlacedMeasurement,
    MIPStarRE.Quantum.Measurement.ofSumEqOne] at hfull
  simp_rw [placed_product_stateQForm_eq] at hfull
  have hevaluated (y : Y) := point_defect_eq
    (leftPlacedMeasurement (ιB := ιB)
      (A.postprocess (fun g => eval g y)))
    (rightPlacedMeasurement (ιA := ιA)
      (B.postprocess (fun g => eval g y))) ψ
  simp only [leftPlacedMeasurement, rightPlacedMeasurement,
    MIPStarRE.Quantum.Measurement.ofSumEqOne] at hevaluated
  simp_rw [placed_product_stateQForm_eq] at hevaluated
  have heval_avg : avgOver (uniformDistribution Y) (fun y =>
      ∑ r : R, ∑ r' : R, if r = r' then 0 else
        stateQForm ψ
          (heteroKron
            ((A.postprocess (fun g => eval g y)).effect r)
            ((B.postprocess (fun g => eval g y)).effect r'))) =
      1 - avgOver (uniformDistribution Y) (fun y =>
        ∑ r : R, stateQForm ψ
          (heteroKron
            ((A.postprocess (fun g => eval g y)).effect r)
            ((B.postprocess (fun g => eval g y)).effect r))) := by
    simp_rw [hevaluated]
    rw [avgOver_sub, avgOver_uniform_const]
    rw [hψ]
    norm_num
  rw [hfull, hψ, one_pow, heval_avg]
  linarith

set_option maxHeartbeats 600000 in
-- Expanding the two nested distribution averages needs the same budget.
/-- If distinct codewords collide under a random evaluation with probability
at most `ε`, their full-outcome consistency defect is at most the evaluated
defect plus `ε`. -/
private theorem consistencyDefect_codewords_le_evaluated_add
    {X Y Γ R ιA ιB : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype Γ] [DecidableEq Γ] [Fintype R] [DecidableEq R]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : Distribution X) (A : X → Measurement Γ ιA)
    (B : X → Measurement Γ ιB) (ψ : EuclideanSpace ℂ (ιA × ιB))
    (eval : Γ → Y → R) (ε : ℝ)
    (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1) (hε : 0 ≤ ε)
    (hcollision : ∀ g g' : Γ, g ≠ g' →
      avgOver (uniformDistribution Y)
        (fun y => if eval g y = eval g' y then 1 else 0) ≤ ε) :
    consistencyDefect μ
        (fun x g => heteroKron ((A x).effect g) 1)
        (fun x g => heteroKron 1 ((B x).effect g)) ψ ≤
      consistencyDefect (Distribution.prod μ (uniformDistribution Y))
        (fun xy r => heteroKron
          (((A xy.1).postprocess (fun g => eval g xy.2)).effect r) 1)
        (fun xy r => heteroKron 1
          (((B xy.1).postprocess (fun g => eval g xy.2)).effect r)) ψ + ε := by
  classical
  let w : X → Γ → Γ → ℝ := fun x g g' =>
    stateQForm ψ (heteroKron ((A x).effect g) ((B x).effect g'))
  have hpoint (x : X) :
      (∑ g : Γ, ∑ g' : Γ, if g = g' then 0 else w x g g') ≤
        avgOver (uniformDistribution Y) (fun y =>
          ∑ r : R, ∑ r' : R, if r = r' then 0 else
            stateQForm ψ
              (heteroKron
                (((A x).postprocess (fun g => eval g y)).effect r)
                (((B x).postprocess (fun g => eval g y)).effect r'))) + ε := by
    exact point_codeword_defect_le_avg_evaluated_add
      (A x) (B x) ψ eval ε hψ hε hcollision
  rw [consistencyDefect_placed_eq_avg_point μ A B]
  rw [consistencyDefect_placed_eq_avg_point
    (Distribution.prod μ (uniformDistribution Y))
    (fun xy => (A xy.1).postprocess (fun g => eval g xy.2))
    (fun xy => (B xy.1).postprocess (fun g => eval g xy.2))]
  change avgOver μ (fun x =>
      ∑ g : Γ, ∑ g' : Γ, if g = g' then 0 else w x g g') ≤ _
  rw [avgOver_distribution_prod]
  calc
    avgOver μ (fun x =>
        ∑ g : Γ, ∑ g' : Γ, if g = g' then 0 else w x g g') ≤
        avgOver μ (fun x =>
          avgOver (uniformDistribution Y) (fun y =>
            ∑ r : R, ∑ r' : R, if r = r' then 0 else
              stateQForm ψ
                (heteroKron
                  (((A x).postprocess (fun g => eval g y)).effect r)
                  (((B x).postprocess (fun g => eval g y)).effect r'))) + ε) := by
      apply avgOver_mono
      exact hpoint
    _ = avgOver μ (fun x =>
          avgOver (uniformDistribution Y) (fun y =>
            ∑ r : R, ∑ r' : R, if r = r' then 0 else
              stateQForm ψ
                (heteroKron
                  (((A x).postprocess (fun g => eval g y)).effect r)
                  (((B x).postprocess (fun g => eval g y)).effect r')))) +
        avgOver μ (fun _ => ε) := avgOver_add _ _ _
    _ = _ := by rw [avgOver_const_of_isProbability μ hμ]

set_option maxHeartbeats 600000 in
-- Normalizing both postprocessed defect sums needs the same budget.
/-- Averaging the fixed-map data-processing inequality over an independent
random relabeling preserves its bound. -/
private theorem consistencyDefect_prod_postprocess_le
    {X Y α β ιA ιB : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : Distribution X) (A : X → Measurement α ιA)
    (B : X → Measurement α ιB) (ψ : EuclideanSpace ℂ (ιA × ιB))
    (f : Y → α → β) :
    consistencyDefect (Distribution.prod μ (uniformDistribution Y))
        (fun xy b => heteroKron (((A xy.1).postprocess (f xy.2)).effect b) 1)
        (fun xy b => heteroKron 1 (((B xy.1).postprocess (f xy.2)).effect b)) ψ ≤
      consistencyDefect μ
        (fun x a => heteroKron ((A x).effect a) 1)
        (fun x a => heteroKron 1 ((B x).effect a)) ψ := by
  rw [consistencyDefect_placed_eq_avg_point
    (Distribution.prod μ (uniformDistribution Y))
    (fun xy => (A xy.1).postprocess (f xy.2))
    (fun xy => (B xy.1).postprocess (f xy.2))]
  rw [consistencyDefect_placed_eq_avg_point μ A B]
  rw [avgOver_distribution_prod, avgOver_comm]
  calc
    avgOver (uniformDistribution Y) (fun y => avgOver μ (fun x =>
        ∑ b : β, ∑ b' : β, if b = b' then 0 else
          stateQForm ψ
            (heteroKron
              (((A x).postprocess (f y)).effect b)
              (((B x).postprocess (f y)).effect b')))) ≤
        avgOver (uniformDistribution Y) (fun _ =>
          avgOver μ (fun x =>
            ∑ a : α, ∑ a' : α, if a = a' then 0 else
              stateQForm ψ
                (heteroKron ((A x).effect a) ((B x).effect a')))) := by
      apply avgOver_mono
      intro y
      rw [← consistencyDefect_placed_eq_avg_point μ
        (fun x => (A x).postprocess (f y))
        (fun x => (B x).postprocess (f y))]
      rw [← consistencyDefect_placed_eq_avg_point μ A B]
      exact consistencyDefect_postprocess_le μ A B ψ (f y)
    _ = _ := avgOver_uniform_const _

/-- The square root of the average squared operator distance satisfies the
ordinary triangle inequality. -/
private theorem sqrt_opFamilyDistSq_triangle {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B C : X → α → Op ι)
    (ψ : EuclideanSpace ℂ ι) :
    Real.sqrt (opFamilyDistSq μ A C ψ) ≤
      Real.sqrt (opFamilyDistSq μ A B ψ) +
        Real.sqrt (opFamilyDistSq μ B C ψ) := by
  let u : X → α → EuclideanSpace ℂ ι := fun x a =>
    applyOperatorToState (A x a - B x a) ψ
  let v : X → α → EuclideanSpace ℂ ι := fun x a =>
    applyOperatorToState (B x a - C x a) ψ
  have hpoint (x : X) (a : α) :
      ‖applyOperatorToState (A x a - C x a) ψ‖ ^ 2 ≤
        ‖u x a‖ ^ 2 + ‖v x a‖ ^ 2 + 2 * (‖u x a‖ * ‖v x a‖) := by
    have hdecomp : applyOperatorToState (A x a - C x a) ψ = u x a + v x a := by
      rw [show A x a - C x a = (A x a - B x a) + (B x a - C x a) by abel]
      simp only [u, v, applyOperatorToState, map_add, LinearMap.add_apply]
    rw [hdecomp]
    have hadd := norm_add_le (u x a) (v x a)
    nlinarith [norm_nonneg (u x a), norm_nonneg (v x a),
      norm_nonneg (u x a + v x a)]
  have hcross :
      avgOver μ (fun x => ∑ a : α, ‖u x a‖ * ‖v x a‖) ≤
        Real.sqrt (opFamilyDistSq μ A B ψ) *
          Real.sqrt (opFamilyDistSq μ B C ψ) := by
    calc
      avgOver μ (fun x => ∑ a : α, ‖u x a‖ * ‖v x a‖) ≤
          |avgOver μ (fun x => ∑ a : α, ‖u x a‖ * ‖v x a‖)| :=
        le_abs_self _
      _ ≤ Real.sqrt (avgOver μ (fun x => ∑ a : α, ‖u x a‖ ^ 2)) *
          Real.sqrt (avgOver μ (fun x => ∑ a : α, ‖v x a‖ ^ 2)) := by
        apply MIPStarRE.LDT.Preliminaries.weightedFinsetCauchySchwarz
        · intro x a
          simp only [abs_mul, abs_norm, Real.sqrt_sq_eq_abs]
          exact le_rfl
        · intro x a
          exact sq_nonneg _
        · intro x a
          exact sq_nonneg _
      _ = Real.sqrt (opFamilyDistSq μ A B ψ) *
          Real.sqrt (opFamilyDistSq μ B C ψ) := by
        rfl
  have hdist : opFamilyDistSq μ A C ψ ≤
      (Real.sqrt (opFamilyDistSq μ A B ψ) +
        Real.sqrt (opFamilyDistSq μ B C ψ)) ^ 2 := by
    unfold opFamilyDistSq
    calc
      avgOver μ (fun x =>
          ∑ a : α, ‖applyOperatorToState (A x a - C x a) ψ‖ ^ 2) ≤
          avgOver μ (fun x => ∑ a : α,
            (‖u x a‖ ^ 2 + ‖v x a‖ ^ 2 + 2 * (‖u x a‖ * ‖v x a‖))) := by
        apply avgOver_mono
        intro x
        exact Finset.sum_le_sum fun a _ => hpoint x a
      _ = avgOver μ (fun x => ∑ a : α, ‖u x a‖ ^ 2) +
          avgOver μ (fun x => ∑ a : α, ‖v x a‖ ^ 2) +
          2 * avgOver μ (fun x => ∑ a : α, ‖u x a‖ * ‖v x a‖) := by
        simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [avgOver_add, avgOver_add, avgOver_const_mul]
      _ ≤ avgOver μ (fun x => ∑ a : α, ‖u x a‖ ^ 2) +
          avgOver μ (fun x => ∑ a : α, ‖v x a‖ ^ 2) +
          2 * (Real.sqrt (opFamilyDistSq μ A B ψ) *
            Real.sqrt (opFamilyDistSq μ B C ψ)) := by
        gcongr
      _ = (Real.sqrt (opFamilyDistSq μ A B ψ) +
          Real.sqrt (opFamilyDistSq μ B C ψ)) ^ 2 := by
        change opFamilyDistSq μ A B ψ + opFamilyDistSq μ B C ψ +
          2 * (Real.sqrt (opFamilyDistSq μ A B ψ) *
            Real.sqrt (opFamilyDistSq μ B C ψ)) = _
        have hAB := Real.sq_sqrt (DistanceCalculus.opFamilyDistSq_nonneg μ A B ψ)
        have hBC := Real.sq_sqrt (DistanceCalculus.opFamilyDistSq_nonneg μ B C ψ)
        nlinarith
  calc
    Real.sqrt (opFamilyDistSq μ A C ψ) ≤
        Real.sqrt ((Real.sqrt (opFamilyDistSq μ A B ψ) +
          Real.sqrt (opFamilyDistSq μ B C ψ)) ^ 2) :=
      Real.sqrt_le_sqrt hdist
    _ = |Real.sqrt (opFamilyDistSq μ A B ψ) +
        Real.sqrt (opFamilyDistSq μ B C ψ)| := Real.sqrt_sq_eq_abs _
    _ = Real.sqrt (opFamilyDistSq μ A B ψ) +
        Real.sqrt (opFamilyDistSq μ B C ψ) := by
      rw [abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]

/-- Coarsening the outcomes of a projective measurement preserves
projectivity. -/
private theorem postprocess_isProjective {α β ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype ι] [DecidableEq ι]
    (M : Measurement α ι) (hM : MIPStarRE.QPBT.Measurement.IsProjective M)
    (f : α → β) : MIPStarRE.QPBT.Measurement.IsProjective (M.postprocess f) := by
  classical
  intro b
  refine { isIdempotentElem := ?_, isSelfAdjoint := ?_ }
  · change (M.postprocess f).effect b * (M.postprocess f).effect b =
      (M.postprocess f).effect b
    simp only [MIPStarRE.Quantum.Measurement.postprocess_effect]
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    calc
      (∑ a ∈ Finset.univ.filter (fun a => f a = b),
          ∑ a' ∈ Finset.univ.filter (fun a' => f a' = b),
            M.effect a * M.effect a') =
          ∑ a ∈ Finset.univ.filter (fun a => f a = b),
            ∑ a' ∈ Finset.univ.filter (fun a' => f a' = b),
              if a' = a then M.effect a else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro a' _
        by_cases haa' : a' = a
        · subst a'
          simp [(hM a).isIdempotentElem.eq]
        · rw [if_neg haa']
          exact DistanceCalculus.projective_effect_mul_effect_eq_zero
            M hM (Ne.symm haa')
      _ = ∑ a ∈ Finset.univ.filter (fun a => f a = b), M.effect a := by
        apply Finset.sum_congr rfl
        intro a ha
        simp [ha]
  · change ((M.postprocess f).effect b)ᴴ = (M.postprocess f).effect b
    exact
      (Matrix.nonneg_iff_posSemidef.mp ((M.postprocess f).pos b)).isHermitian.eq

/-- Performing two outcome relabelings has the same effects as their
composition. -/
private theorem postprocess_postprocess_effect {α β γ ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype ι] [DecidableEq ι]
    (M : Measurement α ι) (f : α → β) (g : β → γ) (c : γ) :
    ((M.postprocess f).postprocess g).effect c =
      (M.postprocess (fun a => g (f a))).effect c := by
  classical
  simp only [MIPStarRE.Quantum.Measurement.postprocess_effect, Finset.sum_filter]
  calc
    (∑ b : β, if g b = c then
        ∑ a : α, if f a = b then M.effect a else 0 else 0) =
        ∑ b : β, ∑ a : α,
          if g b = c ∧ f a = b then M.effect a else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases hbc : g b = c <;> simp [hbc]
    _ = ∑ a : α, ∑ b : β,
        if g b = c ∧ f a = b then M.effect a else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ a : α, if g (f a) = c then M.effect a else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases hac : g (f a) = c
      · rw [Finset.sum_eq_single (f a)]
        · simp [hac]
        · intro b _ hba
          simp [Ne.symm hba]
        · simp
      · apply Eq.trans (Finset.sum_eq_zero (fun b _ => by
          by_cases hab : f a = b
          · subst b
            simp [hac]
          · simp [hab]))
        simp [hac]
    _ = ∑ a : α, if g (f a) = c then M.effect a else 0 := rfl

/-- An injective relabeling does not merge the effect at a relabeled
outcome. -/
private theorem postprocess_effect_of_injective {α β ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype ι] [DecidableEq ι]
    (M : Measurement α ι) (f : α → β) (hf : Function.Injective f) (a : α) :
    (M.postprocess f).effect (f a) = M.effect a := by
  simp only [MIPStarRE.Quantum.Measurement.postprocess_effect, Finset.sum_filter]
  rw [Fintype.sum_eq_single a]
  · simp
  · intro z hza
    rw [if_neg]
    exact fun h => hza (hf h)

/-- The squared effects of a POVM sum to at most the identity. -/
private theorem measurement_sum_adjoint_mul_le_one {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι] (M : Measurement α ι) :
    ∑ a : α, (M.effect a)ᴴ * M.effect a ≤ 1 := by
  calc
    ∑ a : α, (M.effect a)ᴴ * M.effect a =
        ∑ a : α, M.effect a * M.effect a := by
      apply Finset.sum_congr rfl
      intro a _
      rw [DistanceCalculus.measurement_effect_hermitian]
    _ ≤ ∑ a : α, M.effect a := by
      apply Finset.sum_le_sum
      intro a _
      exact MIPStarRE.Quantum.sq_le_self (M.pos a)
        (DistanceCalculus.measurement_effect_le_one M a)
    _ = 1 := M.sum_eq_one

/-- The equal-outcome part of the tensor product of two POVMs is bounded by
the identity. -/
private theorem matched_tensor_sum_le_one {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (A : Measurement α ιA) (B : Measurement α ιB) :
    ∑ a : α, heteroKron (A.effect a) (B.effect a) ≤ 1 := by
  calc
    ∑ a : α, heteroKron (A.effect a) (B.effect a) ≤
        ∑ a : α, ∑ b : α, heteroKron (A.effect a) (B.effect b) := by
      apply Finset.sum_le_sum
      intro a _
      exact Finset.single_le_sum
        (fun b _ => MIPStarRE.Quantum.kronecker_nonneg (A.pos a) (B.pos b))
        (Finset.mem_univ a)
    _ = 1 := by
      ext i j
      simp only [Matrix.sum_apply, heteroKron, Matrix.kronecker,
        Matrix.kroneckerMap_apply]
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
      rw [show (∑ a : α, A.effect a i.1 j.1) = (1 : Op ιA) i.1 j.1 by
        simpa only [Matrix.sum_apply] using congrFun (congrFun A.sum_eq_one i.1) j.1]
      rw [show (∑ b : α, B.effect b i.2 j.2) = (1 : Op ιB) i.2 j.2 by
        simpa only [Matrix.sum_apply] using congrFun (congrFun B.sum_eq_one i.2) j.2]
      exact congrFun (congrFun
        (Matrix.one_kronecker_one (m := ιA) (n := ιB) (α := ℂ)) i) j

/-- Multiplying every effect of a POVM on the left by a fixed projective
effect preserves square-summability. -/
private theorem projective_mul_measurement_sum_adjoint_mul_le_one
    {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (P : Op ι) (hP : IsProj P) (M : Measurement α ι) :
    ∑ a : α, (P * M.effect a)ᴴ * (P * M.effect a) ≤ 1 := by
  calc
    ∑ a : α, (P * M.effect a)ᴴ * (P * M.effect a) =
        ∑ a : α, (M.effect a)ᴴ * P * M.effect a := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Matrix.conjTranspose_mul]
      rw [hP.isSelfAdjoint.isHermitian.eq]
      calc
        (M.effect a)ᴴ * P * (P * M.effect a) =
            (M.effect a)ᴴ * ((P * P) * M.effect a) := by
          simp only [mul_assoc]
        _ = (M.effect a)ᴴ * P * M.effect a := by
          rw [hP.isIdempotentElem.eq]
          exact (mul_assoc _ _ _).symm
    _ ≤ ∑ a : α, (M.effect a)ᴴ * M.effect a := by
      apply Finset.sum_le_sum
      intro a _
      simpa [Matrix.star_eq_conjTranspose] using
        star_left_conjugate_le_conjugate hP.le_one (M.effect a)
    _ ≤ 1 := measurement_sum_adjoint_mul_le_one M

/-- Tensoring two projectors gives a projector on the product space. -/
private theorem heteroKron_isProj {ιA ιB : Type*}
    [Fintype ιA] [Fintype ιB]
    {P : Op ιA} {Q : Op ιB} (hP : IsProj P) (hQ : IsProj Q) :
    IsProj (heteroKron P Q) := by
  refine { isIdempotentElem := ?_, isSelfAdjoint := ?_ }
  · change heteroKron P Q * heteroKron P Q = heteroKron P Q
    rw [heteroKron_mul, hP.isIdempotentElem.eq, hQ.isIdempotentElem.eq]
  · change (heteroKron P Q)ᴴ = heteroKron P Q
    unfold heteroKron
    simp only [Matrix.kronecker]
    rw [Matrix.conjTranspose_kronecker, hP.isSelfAdjoint.isHermitian.eq,
      hQ.isSelfAdjoint.isHermitian.eq]

/-- The squared effects in one fiber of a pair-valued measurement sum to at
most the identity. -/
private theorem measurement_pair_fiber_sum_adjoint_mul_le_one
    {α β ι : Type*} [Fintype α] [Fintype β]
    [Fintype ι] [DecidableEq ι]
    (M : Measurement (α × β) ι) (a : α) :
    ∑ b : β, (M.effect (a, b))ᴴ * M.effect (a, b) ≤ 1 := by
  have hsquare (z : α × β) : (M.effect z)ᴴ * M.effect z ≤ M.effect z := by
    rw [DistanceCalculus.measurement_effect_hermitian]
    exact MIPStarRE.Quantum.sq_le_self (M.pos z)
      (DistanceCalculus.measurement_effect_le_one M z)
  calc
    ∑ b : β, (M.effect (a, b))ᴴ * M.effect (a, b) ≤
        ∑ b : β, M.effect (a, b) := by
      exact Finset.sum_le_sum fun b _ => hsquare (a, b)
    _ ≤ ∑ a' : α, ∑ b : β, M.effect (a', b) := by
      exact Finset.single_le_sum
        (fun a' _ => Finset.sum_nonneg fun b _ => M.pos (a', b))
        (Finset.mem_univ a)
    _ = ∑ z : α × β, M.effect z := (Fintype.sum_prod_type _).symm
    _ = 1 := M.sum_eq_one

/-- A projective joint effect is selected exactly by the matching
postprocessing fiber. -/
private theorem postprocess_effect_mul_effect {α β ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype ι] [DecidableEq ι]
    (M : Measurement α ι) (hM : MIPStarRE.QPBT.Measurement.IsProjective M)
    (f : α → β) (b : β) (a : α) :
    (M.postprocess f).effect b * M.effect a =
      if f a = b then M.effect a else 0 := by
  classical
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect, Finset.sum_mul]
  calc
    (∑ z ∈ Finset.univ.filter (fun z => f z = b), M.effect z * M.effect a) =
        ∑ z ∈ Finset.univ.filter (fun z => f z = b),
          if z = a then M.effect a else 0 := by
      apply Finset.sum_congr rfl
      intro z _
      by_cases hza : z = a
      · subst z
        simp [(hM a).isIdempotentElem.eq]
      · rw [if_neg hza]
        exact DistanceCalculus.projective_effect_mul_effect_eq_zero M hM hza
    _ = if f a = b then M.effect a else 0 := by simp

/-- Right-handed form of `postprocess_effect_mul_effect`. -/
private theorem effect_mul_postprocess_effect {α β ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype ι] [DecidableEq ι]
    (M : Measurement α ι) (hM : MIPStarRE.QPBT.Measurement.IsProjective M)
    (f : α → β) (b : β) (a : α) :
    M.effect a * (M.postprocess f).effect b =
      if f a = b then M.effect a else 0 := by
  have h := congrArg Matrix.conjTranspose
    (postprocess_effect_mul_effect M hM f b a)
  rw [Matrix.conjTranspose_mul,
    DistanceCalculus.measurement_effect_hermitian M a,
    DistanceCalculus.measurement_effect_hermitian (M.postprocess f) b] at h
  by_cases hab : f a = b
  · simpa [hab, DistanceCalculus.measurement_effect_hermitian M a] using h
  · simpa [hab] using h

/-- Two compatible marginals of a joint projective measurement multiply to
the unique joint effect in their common fiber. -/
private theorem postprocess_product_eq_effect {α β γ ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype ι] [DecidableEq ι]
    (M : Measurement α ι) (hM : MIPStarRE.QPBT.Measurement.IsProjective M)
    (f : α → β) (g : α → γ) (a : α)
    (hunique : ∀ z, f z = f a → g z = g a → z = a) :
    (M.postprocess f).effect (f a) * (M.postprocess g).effect (g a) =
      M.effect a := by
  classical
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect M g (g a), Finset.mul_sum]
  calc
    (∑ z ∈ Finset.univ.filter (fun z => g z = g a),
        (M.postprocess f).effect (f a) * M.effect z) =
        ∑ z ∈ Finset.univ.filter (fun z => g z = g a),
          if f z = f a then M.effect z else 0 := by
      apply Finset.sum_congr rfl
      intro z _
      exact postprocess_effect_mul_effect M hM f (f a) z
    _ = M.effect a := by
      rw [Finset.sum_eq_single a]
      · simp
      · intro z hz hza
        rw [if_neg]
        intro hzf
        exact hza (hunique z hzf (Finset.mem_filter.mp hz).2)
      · simp

/-- Left multiplication contracts an operator-family distance when the
multipliers are square-summable on every fiber of the outcome map. -/
private theorem opFamilyDistSq_mul_fiber_le {X α Γ ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype Γ] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B : X → Measurement α ι)
    (eval : Γ → X → α) (S : X → Γ → Op ι)
    (ψ : EuclideanSpace ℂ ι) (δ : ℝ)
    (hS : ∀ x a,
      (1 - ∑ z : Γ, if eval z x = a then (S x z)ᴴ * S x z else 0).PosSemidef)
    (h : opFamilyDistSq μ (fun x a => (A x).effect a)
      (fun x a => (B x).effect a) ψ ≤ δ) :
    opFamilyDistSq μ (fun x z => S x z * (A x).effect (eval z x))
      (fun x z => S x z * (B x).effect (eval z x)) ψ ≤ δ := by
  classical
  apply le_trans ?_ h
  unfold opFamilyDistSq
  apply avgOver_mono
  intro x
  rw [show (∑ z : Γ, ‖applyOperatorToState
      (S x z * (A x).effect (eval z x) - S x z * (B x).effect (eval z x)) ψ‖ ^ 2) =
      ∑ a : α, ∑ z ∈ Finset.univ.filter (fun z => eval z x = a),
        ‖applyOperatorToState
          (S x z * ((A x).effect a - (B x).effect a)) ψ‖ ^ 2 by
    calc
      _ = ∑ a : α, ∑ z ∈ Finset.univ.filter (fun z => eval z x = a),
          ‖applyOperatorToState
            (S x z * (A x).effect (eval z x) -
              S x z * (B x).effect (eval z x)) ψ‖ ^ 2 :=
        (Finset.sum_fiberwise Finset.univ (fun z => eval z x) _).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro z hz
        rw [(Finset.mem_filter.mp hz).2]
        simp only [mul_sub]]
  apply Finset.sum_le_sum
  intro a _
  have hcontract :
      ∑ z : Γ, (if eval z x = a then S x z else 0)ᴴ *
          (if eval z x = a then S x z else 0) ≤ 1 := by
    calc
      ∑ z : Γ, (if eval z x = a then S x z else 0)ᴴ *
          (if eval z x = a then S x z else 0) =
          ∑ z : Γ, if eval z x = a then (S x z)ᴴ * S x z else 0 := by
        apply Finset.sum_congr rfl
        intro z _
        by_cases hza : eval z x = a <;> simp [hza]
      _ ≤ 1 := Matrix.le_iff.mpr (hS x a)
  have hmul := DistanceCalculus.sum_norm_mul_apply_le
    (fun z : Γ => if eval z x = a then S x z else 0)
    ((A x).effect a - (B x).effect a) ψ hcontract
  calc
    (∑ z ∈ Finset.univ.filter (fun z => eval z x = a),
        ‖applyOperatorToState
          (S x z * ((A x).effect a - (B x).effect a)) ψ‖ ^ 2) =
        ∑ z : Γ, if eval z x = a then
          ‖applyOperatorToState
            (S x z * ((A x).effect a - (B x).effect a)) ψ‖ ^ 2 else 0 := by
      rw [Finset.sum_filter]
    _ = ∑ z : Γ, ‖applyOperatorToState
        ((if eval z x = a then S x z else 0) *
          ((A x).effect a - (B x).effect a)) ψ‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro z _
      by_cases hza : eval z x = a <;> simp [hza, applyOperatorToState]
    _ ≤ ‖applyOperatorToState ((A x).effect a - (B x).effect a) ψ‖ ^ 2 := hmul

set_option maxHeartbeats 400000 in
-- The three-stage family comparison requires a larger elaboration budget.
/-- Replacing the two outer copies and the inner marginal in a joint
projective effect costs two outer distances and one inner distance. -/
private theorem sqrt_opFamilyDistSq_joint_sandwich_le
    {X α β ιA ιB : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : Distribution X) (J : X → Measurement (α × β) ιA)
    (G : X → Measurement α ιB) (P : X → Measurement β ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (q d : ℝ)
    (hJ : ∀ x, MIPStarRE.QPBT.Measurement.IsProjective (J x))
    (hG : ∀ x, MIPStarRE.QPBT.Measurement.IsProjective (G x))
    (hq : opFamilyDistSq μ
      (fun x a => heteroKron (((J x).postprocess Prod.fst).effect a) 1)
      (fun x a => heteroKron 1 ((G x).effect a)) ψ ≤ q)
    (hd : opFamilyDistSq μ
      (fun x b => heteroKron (((J x).postprocess Prod.snd).effect b) 1)
      (fun x b => heteroKron 1 ((P x).effect b)) ψ ≤ d) :
    Real.sqrt (opFamilyDistSq μ
      (fun x ab => heteroKron ((J x).effect ab) 1)
      (fun x ab => heteroKron 1
        ((G x).effect ab.1 * (P x).effect ab.2 * (G x).effect ab.1)) ψ) ≤
      2 * Real.sqrt q + Real.sqrt d := by
  classical
  let JA : X → Measurement α ιA := fun x => (J x).postprocess Prod.fst
  let JB : X → Measurement β ιA := fun x => (J x).postprocess Prod.snd
  let JL : X → Measurement (α × β) (ιA × ιB) := fun x =>
    DistanceCalculus.leftPlacedMeasurement (ιB := ιB) (J x)
  let JAL : X → Measurement α (ιA × ιB) := fun x =>
    DistanceCalculus.leftPlacedMeasurement (ιB := ιB) (JA x)
  let JBL : X → Measurement β (ιA × ιB) := fun x =>
    DistanceCalculus.leftPlacedMeasurement (ιB := ιB) (JB x)
  let GR : X → Measurement α (ιA × ιB) := fun x =>
    DistanceCalculus.rightPlacedMeasurement (ιA := ιA) (G x)
  let PR : X → Measurement β (ιA × ιB) := fun x =>
    DistanceCalculus.rightPlacedMeasurement (ιA := ιA) (P x)
  let F₀ : X → (α × β) → Op (ιA × ιB) := fun x ab => (JL x).effect ab
  let F₁ : X → (α × β) → Op (ιA × ιB) := fun x ab =>
    ((GR x).effect ab.1 * (JAL x).effect ab.1) * (JBL x).effect ab.2
  let F₂ : X → (α × β) → Op (ιA × ιB) := fun x ab =>
    ((GR x).effect ab.1 * (JAL x).effect ab.1) * (PR x).effect ab.2
  let F₃ : X → (α × β) → Op (ιA × ιB) := fun x ab =>
    ((GR x).effect ab.1 * (PR x).effect ab.2) * (GR x).effect ab.1
  have hq' : opFamilyDistSq μ (fun x a => (JAL x).effect a)
      (fun x a => (GR x).effect a) ψ ≤ q := by
    simpa [JAL, JA, GR, DistanceCalculus.leftPlacedMeasurement,
      DistanceCalculus.rightPlacedMeasurement,
      MIPStarRE.Quantum.Measurement.ofSumEqOne] using hq
  have hd' : opFamilyDistSq μ (fun x b => (JBL x).effect b)
      (fun x b => (PR x).effect b) ψ ≤ d := by
    simpa [JBL, JB, PR, DistanceCalculus.leftPlacedMeasurement,
      DistanceCalculus.rightPlacedMeasurement,
      MIPStarRE.Quantum.Measurement.ofSumEqOne] using hd
  have hS₀ (x : X) (a : α) :
      (1 - ∑ ab : α × β, if ab.1 = a then
        ((JL x).effect ab)ᴴ * (JL x).effect ab else 0).PosSemidef := by
    apply Matrix.le_iff.mp
    calc
      (∑ ab : α × β, if ab.1 = a then
          ((JL x).effect ab)ᴴ * (JL x).effect ab else 0) =
          ∑ b : β, ((JL x).effect (a, b))ᴴ * (JL x).effect (a, b) := by
        rw [Fintype.sum_prod_type]
        rw [Fintype.sum_eq_single a]
        · simp
        · intro a' ha'
          simp [ha']
      _ ≤ 1 := measurement_pair_fiber_sum_adjoint_mul_le_one (JL x) a
  have hstep₀raw : opFamilyDistSq μ
      (fun x (ab : α × β) => (JL x).effect ab * (JAL x).effect ab.1)
      (fun x (ab : α × β) => (JL x).effect ab * (GR x).effect ab.1) ψ ≤ q :=
    opFamilyDistSq_mul_fiber_le μ JAL GR
      (fun (ab : α × β) (_ : X) => ab.1)
      (fun x (ab : α × β) => (JL x).effect ab) ψ q hS₀ hq'
  have hstep₀ : opFamilyDistSq μ F₀ F₁ ψ ≤ q := by
    calc
      opFamilyDistSq μ F₀ F₁ ψ = opFamilyDistSq μ
          (fun x (ab : α × β) => (JL x).effect ab * (JAL x).effect ab.1)
          (fun x (ab : α × β) => (JL x).effect ab * (GR x).effect ab.1) ψ := by
        apply DistanceCalculus.opFamilyDistSq_congr
        · intro x ab
          symm
          simp only [F₀, JL, JAL, DistanceCalculus.leftPlacedMeasurement,
            MIPStarRE.Quantum.Measurement.ofSumEqOne]
          change heteroKron ((J x).effect ab) 1 *
              heteroKron ((JA x).effect ab.1) 1 =
            heteroKron ((J x).effect ab) 1
          rw [heteroKron_mul, effect_mul_postprocess_effect
            (J x) (hJ x) Prod.fst ab.1 ab, if_pos rfl, mul_one]
        · intro x ab
          simp only [F₁, JL, GR, JAL, JBL,
            DistanceCalculus.leftPlacedMeasurement,
            DistanceCalculus.rightPlacedMeasurement,
            MIPStarRE.Quantum.Measurement.ofSumEqOne]
          change (heteroKron 1 ((G x).effect ab.1) *
                heteroKron ((JA x).effect ab.1) 1) *
              heteroKron ((JB x).effect ab.2) 1 =
            heteroKron ((J x).effect ab) 1 *
              heteroKron 1 ((G x).effect ab.1)
          rw [heteroKron_mul, heteroKron_mul, heteroKron_mul]
          simp only [one_mul, mul_one]
          congr 1
          simpa only [JA, JB] using postprocess_product_eq_effect
            (J x) (hJ x) Prod.fst Prod.snd ab (by
              intro z hz₁ hz₂
              exact Prod.ext hz₁ hz₂)
      _ ≤ q := hstep₀raw
  have hS₁ (x : X) (b : β) :
      (1 - ∑ ab : α × β, if ab.2 = b then
        (((GR x).effect ab.1 * (JAL x).effect ab.1)ᴴ *
          ((GR x).effect ab.1 * (JAL x).effect ab.1)) else 0).PosSemidef := by
    apply Matrix.le_iff.mp
    calc
      (∑ ab : α × β, if ab.2 = b then
          (((GR x).effect ab.1 * (JAL x).effect ab.1)ᴴ *
            ((GR x).effect ab.1 * (JAL x).effect ab.1)) else 0) =
          ∑ a : α, heteroKron ((JA x).effect a) ((G x).effect a) := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro a _
        rw [Fintype.sum_eq_single b]
        · simp only [if_pos]
          have hp := heteroKron_isProj
            (postprocess_isProjective (J x) (hJ x) Prod.fst a) (hG x a)
          simp only [GR, JAL, DistanceCalculus.rightPlacedMeasurement,
            DistanceCalculus.leftPlacedMeasurement,
            MIPStarRE.Quantum.Measurement.ofSumEqOne]
          simp only [heteroKron_mul, one_mul, mul_one]
          rw [hp.isSelfAdjoint.isHermitian.eq, hp.isIdempotentElem.eq]
        · intro b' hb'
          simp [hb']
      _ ≤ 1 := matched_tensor_sum_le_one (JA x) (G x)
  have hstep₁raw : opFamilyDistSq μ
      (fun x (ab : α × β) =>
        ((GR x).effect ab.1 * (JAL x).effect ab.1) * (JBL x).effect ab.2)
      (fun x (ab : α × β) =>
        ((GR x).effect ab.1 * (JAL x).effect ab.1) * (PR x).effect ab.2)
      ψ ≤ d :=
    opFamilyDistSq_mul_fiber_le μ JBL PR
      (fun (ab : α × β) (_ : X) => ab.2)
      (fun x (ab : α × β) => (GR x).effect ab.1 * (JAL x).effect ab.1)
      ψ d hS₁ hd'
  have hstep₁ : opFamilyDistSq μ F₁ F₂ ψ ≤ d := by
    simpa only [F₁, F₂] using hstep₁raw
  have hS₂ (x : X) (a : α) :
      (1 - ∑ ab : α × β, if ab.1 = a then
        (((GR x).effect ab.1 * (PR x).effect ab.2)ᴴ *
          ((GR x).effect ab.1 * (PR x).effect ab.2)) else 0).PosSemidef := by
    apply Matrix.le_iff.mp
    calc
      (∑ ab : α × β, if ab.1 = a then
          (((GR x).effect ab.1 * (PR x).effect ab.2)ᴴ *
            ((GR x).effect ab.1 * (PR x).effect ab.2)) else 0) =
          rightTensor (ι₁ := ιA)
            (∑ b : β, ((G x).effect a * (P x).effect b)ᴴ *
              ((G x).effect a * (P x).effect b)) := by
        rw [Fintype.sum_prod_type, Fintype.sum_eq_single a]
        · simp only [if_pos]
          rw [← rightTensor_finset_sum]
          apply Finset.sum_congr rfl
          intro b _
          simp only [GR, PR, DistanceCalculus.rightPlacedMeasurement,
            MIPStarRE.Quantum.Measurement.ofSumEqOne]
          simp only [heteroKron_mul, one_mul]
          change (rightTensor (ι₁ := ιA)
              ((G x).effect a * (P x).effect b))ᴴ *
                rightTensor (ι₁ := ιA) ((G x).effect a * (P x).effect b) =
            rightTensor (ι₁ := ιA)
              (((G x).effect a * (P x).effect b)ᴴ *
                ((G x).effect a * (P x).effect b))
          rw [rightTensor_conjTranspose, rightTensor_mul_rightTensor]
        · intro a' ha'
          simp [ha']
      _ ≤ rightTensor (ι₁ := ιA) (1 : Op ιB) :=
        rightTensor_mono
          (projective_mul_measurement_sum_adjoint_mul_le_one
            ((G x).effect a) (hG x a) (P x))
      _ = 1 := rightTensor_one
  have hstep₂raw : opFamilyDistSq μ
      (fun x (ab : α × β) =>
        ((GR x).effect ab.1 * (PR x).effect ab.2) * (JAL x).effect ab.1)
      (fun x (ab : α × β) =>
        ((GR x).effect ab.1 * (PR x).effect ab.2) * (GR x).effect ab.1)
      ψ ≤ q :=
    opFamilyDistSq_mul_fiber_le μ JAL GR
      (fun (ab : α × β) (_ : X) => ab.1)
      (fun x (ab : α × β) => (GR x).effect ab.1 * (PR x).effect ab.2)
      ψ q hS₂ hq'
  have hstep₂ : opFamilyDistSq μ F₂ F₃ ψ ≤ q := by
    calc
      opFamilyDistSq μ F₂ F₃ ψ = opFamilyDistSq μ
          (fun x (ab : α × β) => ((GR x).effect ab.1 * (PR x).effect ab.2) *
            (JAL x).effect ab.1)
          (fun x (ab : α × β) => ((GR x).effect ab.1 * (PR x).effect ab.2) *
            (GR x).effect ab.1) ψ := by
        apply DistanceCalculus.opFamilyDistSq_congr
        · intro x ab
          simp only [F₂, GR, PR, JAL,
            DistanceCalculus.leftPlacedMeasurement,
            DistanceCalculus.rightPlacedMeasurement,
            MIPStarRE.Quantum.Measurement.ofSumEqOne]
          change heteroKron 1 ((G x).effect ab.1) *
              heteroKron ((JA x).effect ab.1) 1 *
                heteroKron 1 ((P x).effect ab.2) =
            (heteroKron 1 ((G x).effect ab.1) *
              heteroKron 1 ((P x).effect ab.2)) *
              heteroKron ((JA x).effect ab.1) 1
          simp only [heteroKron_mul, one_mul, mul_one]
        · intro _ _
          rfl
      _ ≤ q := hstep₂raw
  have htri₀ := sqrt_opFamilyDistSq_triangle μ F₀ F₁ F₃ ψ
  have htri₁ := sqrt_opFamilyDistSq_triangle μ F₁ F₂ F₃ ψ
  have hs₀ := Real.sqrt_le_sqrt hstep₀
  have hs₁ := Real.sqrt_le_sqrt hstep₁
  have hs₂ := Real.sqrt_le_sqrt hstep₂
  calc
    Real.sqrt (opFamilyDistSq μ
        (fun x ab => heteroKron ((J x).effect ab) 1)
        (fun x ab => heteroKron 1
          ((G x).effect ab.1 * (P x).effect ab.2 * (G x).effect ab.1)) ψ) =
        Real.sqrt (opFamilyDistSq μ F₀ F₃ ψ) := by
      apply congrArg Real.sqrt
      apply DistanceCalculus.opFamilyDistSq_congr
      · intro x ab
        rfl
      · intro x ab
        simp only [F₃, GR, PR, DistanceCalculus.rightPlacedMeasurement,
          MIPStarRE.Quantum.Measurement.ofSumEqOne]
        rw [heteroKron_mul, heteroKron_mul]
        simp
    _ ≤
        Real.sqrt (opFamilyDistSq μ F₀ F₁ ψ) +
          Real.sqrt (opFamilyDistSq μ F₁ F₃ ψ) := htri₀
    _ ≤ Real.sqrt (opFamilyDistSq μ F₀ F₁ ψ) +
        (Real.sqrt (opFamilyDistSq μ F₁ F₂ ψ) +
          Real.sqrt (opFamilyDistSq μ F₂ F₃ ψ)) := by gcongr
    _ ≤ 2 * Real.sqrt q + Real.sqrt d := by
      linarith only [hs₀, hs₁, hs₂]

/-- The palindromic effects form a POVM when each constituent measurement is
projective. This is `lem:ld-sandwich-measurement`, the measurement assertion
implicit in `lem:ld-sandwich`; blueprint `ch12_qpbt_games.tex:489-507`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:484-494`. -/
theorem sandwichProduct_isMeasurement {k : ℕ} {X ι : Type*}
    [Fintype ι] [DecidableEq ι] {Γ : Fin k → Type*}
    [∀ i, Fintype (Γ i)] (G : (i : Fin k) → X → Measurement (Γ i) ι)
    (hG : ∀ i x, MIPStarRE.QPBT.Measurement.IsProjective (G i x)) (x : X) :
    (∀ g : (i : Fin k) → Γ i,
      0 ≤ sandwichProduct (fun i x' a => (G i x').effect a) x g) ∧
      (∑ g : (i : Fin k) → Γ i,
        sandwichProduct (fun i x' a => (G i x').effect a) x g) = 1 := by
  classical
  induction k with
  | zero =>
      constructor
      · intro g
        change 0 ≤ (1 : Op ι)
        exact Matrix.PosSemidef.one.nonneg
      · simp [sandwichProduct, sandwichProductCore]
  | succ k ih =>
      cases k with
      | zero =>
          constructor
          · intro g
            change 0 ≤ (G 0 x).effect (g 0)
            exact (G 0 x).pos (g 0)
          · change
              (∑ g : (i : Fin 1) → Γ i,
                (G 0 x).effect (g 0)) = 1
            calc
              (∑ g : (i : Fin 1) → Γ i, (G 0 x).effect (g 0)) =
                  ∑ p : Γ 0 × ((i : Fin 0) → Γ i.castSucc),
                    (G 0 x).effect (((Fin.snocEquiv Γ) p) 0) := by
                exact Fintype.sum_equiv (Fin.snocEquiv Γ).symm _ _
                  (by intro g; rw [Equiv.apply_symm_apply])
              _ = ∑ a : Γ 0, (G 0 x).effect a := by
                rw [Fintype.sum_prod_type]
                apply Finset.sum_congr rfl
                intro a _
                simp only [Fintype.sum_unique]
                congr 1
              _ = 1 := (G 0 x).sum_eq_one
      | succ k =>
          have hprev := ih
            (G := fun i x' => G i.castSucc x')
            (hG := fun i x' => hG i.castSucc x')
          constructor
          · intro g
            change 0 ≤
              (G (Fin.last (k + 1)) x).effect (g (Fin.last (k + 1))) *
                sandwichProductCore (k + 1) (fun i => Γ i.castSucc)
                  (fun i a => (G i.castSucc x).effect a)
                  (fun i => g i.castSucc) *
                (G (Fin.last (k + 1)) x).effect (g (Fin.last (k + 1)))
            have hinner := hprev.1 (fun i => g i.castSucc)
            apply Matrix.nonneg_iff_posSemidef.mpr
            have hpos :
                (((G (Fin.last (k + 1)) x).effect (g (Fin.last (k + 1))))ᴴ *
                  sandwichProductCore (k + 1) (fun i => Γ i.castSucc)
                    (fun i a => (G i.castSucc x).effect a)
                    (fun i => g i.castSucc) *
                  (G (Fin.last (k + 1)) x).effect
                    (g (Fin.last (k + 1)))).PosSemidef :=
              (Matrix.nonneg_iff_posSemidef.mp hinner).conjTranspose_mul_mul_same _
            rw [MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian] at hpos
            exact hpos
          · change
              (∑ g : (i : Fin (k + 2)) → Γ i,
                sandwichProductCore (k + 2) Γ
                  (fun i a => (G i x).effect a) g) = 1
            calc
              (∑ g : (i : Fin (k + 2)) → Γ i,
                  sandwichProductCore (k + 2) Γ
                    (fun i a => (G i x).effect a) g) =
                  ∑ p : Γ (Fin.last (k + 1)) ×
                      ((i : Fin (k + 1)) → Γ i.castSucc),
                    sandwichProductCore (k + 2) Γ
                      (fun i a => (G i x).effect a) ((Fin.snocEquiv Γ) p) := by
                exact Fintype.sum_equiv (Fin.snocEquiv Γ).symm _ _
                  (by intro g; rw [Equiv.apply_symm_apply])
              _ = ∑ a : Γ (Fin.last (k + 1)),
                    ∑ g : (i : Fin (k + 1)) → Γ i.castSucc,
                      (G (Fin.last (k + 1)) x).effect a *
                        sandwichProductCore (k + 1) (fun i => Γ i.castSucc)
                          (fun i b => (G i.castSucc x).effect b) g *
                        (G (Fin.last (k + 1)) x).effect a := by
                rw [Fintype.sum_prod_type]
                apply Finset.sum_congr rfl
                intro a _
                apply Finset.sum_congr rfl
                intro g _
                simp [sandwichProductCore]
              _ = ∑ a : Γ (Fin.last (k + 1)),
                    (G (Fin.last (k + 1)) x).effect a *
                      (∑ g : (i : Fin (k + 1)) → Γ i.castSucc,
                        sandwichProductCore (k + 1) (fun i => Γ i.castSucc)
                          (fun i b => (G i.castSucc x).effect b) g) *
                      (G (Fin.last (k + 1)) x).effect a := by
                apply Finset.sum_congr rfl
                intro a _
                rw [Finset.mul_sum, Finset.sum_mul]
              _ = ∑ a : Γ (Fin.last (k + 1)),
                    (G (Fin.last (k + 1)) x).effect a := by
                have hprevSum := hprev.2
                change
                  (∑ g : (i : Fin (k + 1)) → Γ i.castSucc,
                    sandwichProductCore (k + 1) (fun i => Γ i.castSucc)
                      (fun i b => (G i.castSucc x).effect b) g) = 1 at hprevSum
                apply Finset.sum_congr rfl
                intro a _
                rw [hprevSum, mul_one,
                  (hG (Fin.last (k + 1)) x a).isIdempotentElem.eq]
              _ = 1 := (G (Fin.last (k + 1)) x).sum_eq_one

/-- Splitting the last outcome from a tuple of length at least two exposes the
recursive palindromic product. -/
private theorem sandwichProduct_snoc {k : ℕ} {X ι : Type*}
    [Fintype ι] [DecidableEq ι] {Γ : Fin (k + 2) → Type*}
    [∀ i, Fintype (Γ i)]
    (G : (i : Fin (k + 2)) → X → Measurement (Γ i) ι)
    (x : X) (p : Γ (Fin.last (k + 1)) ×
      ((i : Fin (k + 1)) → Γ i.castSucc)) :
    sandwichProduct (fun i x' a => (G i x').effect a) x
        ((Fin.snocEquiv Γ) p) =
      (G (Fin.last (k + 1)) x).effect p.1 *
        sandwichProduct (fun i x' a => (G i.castSucc x').effect a) x p.2 *
      (G (Fin.last (k + 1)) x).effect p.1 := by
  simp [sandwichProduct, sandwichProductCore]

/-- Iterating the joint replacement estimate gives a linear bound for the
square root of the distance to the palindromic measurement. -/
private theorem sqrt_opFamilyDistSq_sandwichProduct_le
    {k : ℕ} {X ιA ιB : Type*} {Γ : Fin k → Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [∀ i, Fintype (Γ i)] [∀ i, DecidableEq (Γ i)]
    (μ : Distribution X) (G : (i : Fin k) → X → Measurement (Γ i) ιB)
    (A : X → Measurement ((i : Fin k) → Γ i) ιA)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (q : ℝ)
    (hG : ∀ i x, MIPStarRE.QPBT.Measurement.IsProjective (G i x))
    (hA : ∀ x, MIPStarRE.QPBT.Measurement.IsProjective (A x))
    (hq : ∀ i, opFamilyDistSq μ
      (fun x a => heteroKron (((A x).postprocess (fun g => g i)).effect a) 1)
      (fun x a => heteroKron 1 ((G i x).effect a)) ψ ≤ q) :
    Real.sqrt (opFamilyDistSq μ
      (fun x g => heteroKron ((A x).effect g) 1)
      (fun x g => heteroKron 1
        (sandwichProduct (fun i x' a => (G i x').effect a) x g)) ψ) ≤
      2 * (k : ℝ) * Real.sqrt q := by
  classical
  induction k using Nat.twoStepInduction with
  | zero =>
      have hAone (x : X) (g : (i : Fin 0) → Γ i) : (A x).effect g = 1 := by
        calc
          (A x).effect g = (A x).effect default := by
            exact congrArg (A x).effect (Subsingleton.elim g default)
          _ = ∑ h : (i : Fin 0) → Γ i, (A x).effect h := by
            rw [Fintype.sum_unique]
          _ = 1 := (A x).sum_eq_one
      have hdistzero : opFamilyDistSq μ
          (fun x g => heteroKron ((A x).effect g) 1)
          (fun x g => heteroKron 1
            (sandwichProduct (fun i x' a => (G i x').effect a) x g)) ψ =
          opFamilyDistSq μ
            (fun (_ : X) (_ : (i : Fin 0) → Γ i) => (1 : Op (ιA × ιB)))
            (fun (_ : X) (_ : (i : Fin 0) → Γ i) => (1 : Op (ιA × ιB))) ψ := by
        apply DistanceCalculus.opFamilyDistSq_congr
        · intro x g
          simp [hAone, heteroKron_one_one]
        · intro x g
          simp [sandwichProduct, sandwichProductCore, heteroKron_one_one]
      rw [hdistzero]
      simp [opFamilyDistSq, applyOperatorToState, MIPStarRE.LDT.avgOver_zero]
  | one =>
      let e : ((i : Fin 1) → Γ i) ≃ Γ default := Equiv.piUnique Γ
      have heval : Function.Injective
          (fun g : (i : Fin 1) → Γ i => g default) := e.injective
      have hdist : opFamilyDistSq μ
          (fun x g => heteroKron ((A x).effect g) 1)
          (fun x g => heteroKron 1
            (sandwichProduct (fun i x' a => (G i x').effect a) x g)) ψ ≤ q := by
        rw [DistanceCalculus.opFamilyDistSq_reindex μ e]
        calc
          opFamilyDistSq μ
              (fun x a => heteroKron ((A x).effect (e.symm a)) 1)
              (fun x a => heteroKron 1
                (sandwichProduct (fun i x' b => (G i x').effect b) x
                  (e.symm a))) ψ =
              opFamilyDistSq μ
                (fun x a => heteroKron
                  (((A x).postprocess (fun g => g default)).effect a) 1)
                (fun x a => heteroKron 1 ((G default x).effect a)) ψ := by
            apply DistanceCalculus.opFamilyDistSq_congr
            · intro x a
              congr 1
              have heffect :=
                postprocess_effect_of_injective (A x) (fun g => g default) heval
                  (e.symm a)
              change ((A x).postprocess (fun g => g default)).effect
                (e (e.symm a)) = (A x).effect (e.symm a) at heffect
              rw [e.apply_symm_apply] at heffect
              exact heffect.symm
            · intro x a
              have hi : (0 : Fin 1) = default := Subsingleton.elim _ _
              cases hi
              change heteroKron 1 ((G default x).effect ((e.symm a) default)) =
                heteroKron 1 ((G default x).effect a)
              rw [show (e.symm a) default = a from e.apply_symm_apply a]
          _ ≤ q := hq default
      have hsqrt := Real.sqrt_le_sqrt hdist
      norm_num
      linarith [Real.sqrt_nonneg q]
  | more k _ ih =>
      let e := (Fin.snocEquiv Γ).symm
      let J : X → Measurement
          (Γ (Fin.last (k + 1)) × ((i : Fin (k + 1)) → Γ i.castSucc)) ιA :=
        fun x => (A x).postprocess e
      let Apre : X → Measurement ((i : Fin (k + 1)) → Γ i.castSucc) ιA :=
        fun x => (A x).postprocess
          (fun (g : (j : Fin (k + 2)) → Γ j) (i : Fin (k + 1)) => g i.castSucc)
      let P : X → Measurement ((i : Fin (k + 1)) → Γ i.castSucc) ιB :=
        fun x => MIPStarRE.Quantum.Measurement.ofSumEqOne
          (fun g => sandwichProduct
            (fun i x' a => (G i.castSucc x').effect a) x g)
          (sandwichProduct_isMeasurement
            (fun i x' => G i.castSucc x')
            (fun i x' => hG i.castSucc x') x).1
          (sandwichProduct_isMeasurement
            (fun i x' => G i.castSucc x')
            (fun i x' => hG i.castSucc x') x).2
      have hJ (x : X) : MIPStarRE.QPBT.Measurement.IsProjective (J x) :=
        postprocess_isProjective (A x) (hA x) e
      have hApre (x : X) : MIPStarRE.QPBT.Measurement.IsProjective (Apre x) :=
        postprocess_isProjective (A x) (hA x)
          (fun (g : (j : Fin (k + 2)) → Γ j) (i : Fin (k + 1)) => g i.castSucc)
      have hJfst (x : X) (a : Γ (Fin.last (k + 1))) :
          ((J x).postprocess Prod.fst).effect a =
            ((A x).postprocess (fun g => g (Fin.last (k + 1)))).effect a := by
        rw [postprocess_postprocess_effect]
        change ((A x).postprocess
          (fun g => ((Fin.snocEquiv Γ).symm g).1)).effect a = _
        rfl
      have hJsnd (x : X) (g : (i : Fin (k + 1)) → Γ i.castSucc) :
          ((J x).postprocess Prod.snd).effect g = (Apre x).effect g := by
        rw [postprocess_postprocess_effect]
        change ((A x).postprocess
          (fun h => ((Fin.snocEquiv Γ).symm h).2)).effect g = _
        rfl
      have hqpre : ∀ i, opFamilyDistSq μ
          (fun x a => heteroKron
            (((Apre x).postprocess (fun g => g i)).effect a) 1)
          (fun x a => heteroKron 1 ((G i.castSucc x).effect a)) ψ ≤ q := by
        intro i
        calc
          opFamilyDistSq μ
              (fun x a => heteroKron
                (((Apre x).postprocess (fun g => g i)).effect a) 1)
              (fun x a => heteroKron 1 ((G i.castSucc x).effect a)) ψ =
              opFamilyDistSq μ
                (fun x a => heteroKron
                  (((A x).postprocess (fun g => g i.castSucc)).effect a) 1)
                (fun x a => heteroKron 1 ((G i.castSucc x).effect a)) ψ := by
            apply DistanceCalculus.opFamilyDistSq_congr
            · intro x a
              congr 1
              rw [postprocess_postprocess_effect]
            · intro _ _
              rfl
          _ ≤ q := hq i.castSucc
      have hprefix := ih
        (G := fun i x => G i.castSucc x) (A := Apre)
        (hG := fun i x => hG i.castSucc x) (hA := hApre) (hq := hqpre)
      have hlast : opFamilyDistSq μ
          (fun x a => heteroKron (((J x).postprocess Prod.fst).effect a) 1)
          (fun x a => heteroKron 1 ((G (Fin.last (k + 1)) x).effect a)) ψ ≤ q := by
        calc
          opFamilyDistSq μ
              (fun x a => heteroKron (((J x).postprocess Prod.fst).effect a) 1)
              (fun x a => heteroKron 1
                ((G (Fin.last (k + 1)) x).effect a)) ψ =
              opFamilyDistSq μ
                (fun x a => heteroKron
                  (((A x).postprocess
                    (fun g => g (Fin.last (k + 1)))).effect a) 1)
                (fun x a => heteroKron 1
                  ((G (Fin.last (k + 1)) x).effect a)) ψ := by
            apply DistanceCalculus.opFamilyDistSq_congr
            · intro x a
              rw [hJfst]
            · intro _ _
              rfl
          _ ≤ q := hq (Fin.last (k + 1))
      have hprefix' : opFamilyDistSq μ
          (fun x g => heteroKron (((J x).postprocess Prod.snd).effect g) 1)
          (fun x g => heteroKron 1 ((P x).effect g)) ψ =
          opFamilyDistSq μ
            (fun x g => heteroKron ((Apre x).effect g) 1)
            (fun x g => heteroKron 1
              (sandwichProduct (fun i x' a => (G i.castSucc x').effect a)
                x g)) ψ := by
        apply DistanceCalculus.opFamilyDistSq_congr
        · intro x g
          rw [hJsnd]
        · intro x g
          rfl
      have hjoint := sqrt_opFamilyDistSq_joint_sandwich_le μ J
        (fun x => G (Fin.last (k + 1)) x) P ψ q
        (opFamilyDistSq μ
          (fun x g => heteroKron (((J x).postprocess Prod.snd).effect g) 1)
          (fun x g => heteroKron 1 ((P x).effect g)) ψ)
        hJ (fun x => hG (Fin.last (k + 1)) x) hlast le_rfl
      rw [hprefix'] at hjoint
      have hdist : opFamilyDistSq μ
          (fun x g => heteroKron ((A x).effect g) 1)
          (fun x g => heteroKron 1
            (sandwichProduct (fun i x' a => (G i x').effect a) x g)) ψ =
          opFamilyDistSq μ
            (fun x p => heteroKron ((J x).effect p) 1)
            (fun x p => heteroKron 1
              ((G (Fin.last (k + 1)) x).effect p.1 *
                (P x).effect p.2 *
                (G (Fin.last (k + 1)) x).effect p.1)) ψ := by
        rw [DistanceCalculus.opFamilyDistSq_reindex μ e]
        apply DistanceCalculus.opFamilyDistSq_congr
        · intro x p
          congr 1
          symm
          simpa only [J, e, Equiv.apply_symm_apply] using
            postprocess_effect_of_injective (A x) e e.injective (e.symm p)
        · intro x p
          congr 1
          simpa only [e, Equiv.symm_symm, Equiv.apply_symm_apply, P,
            MIPStarRE.Quantum.Measurement.ofSumEqOne] using
            sandwichProduct_snoc G x p
      rw [hdist]
      calc
        Real.sqrt (opFamilyDistSq μ
            (fun x p => heteroKron ((J x).effect p) 1)
            (fun x p => heteroKron 1
              ((G (Fin.last (k + 1)) x).effect p.1 *
                (P x).effect p.2 *
                (G (Fin.last (k + 1)) x).effect p.1)) ψ) ≤
            2 * Real.sqrt q + Real.sqrt (opFamilyDistSq μ
              (fun x g => heteroKron ((Apre x).effect g) 1)
              (fun x g => heteroKron 1
                (sandwichProduct (fun i x' a => (G i.castSucc x').effect a)
                  x g)) ψ) := hjoint
        _ ≤ 2 * ((k + 2 : ℕ) : ℝ) * Real.sqrt q := by
          norm_num [Nat.cast_add] at hprefix ⊢
          linarith

/-- The sandwiched simultaneous-measurement estimate of `lem:ld-sandwich`.
One universal asymptotic constant applies independently of the distribution,
measurements, state, and error parameters. Blueprint
`ch12_qpbt_games.tex:454-480`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:465-501`. -/
theorem consistencyDefect_sandwich_le :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧
      ∀ {k : ℕ} {X Y ιA ιB : Type*} {R Γ : Fin k → Type*}
        [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y]
        [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
        [∀ i, Fintype (R i)] [∀ i, DecidableEq (R i)]
        [∀ i, Fintype (Γ i)] [∀ i, DecidableEq (Γ i)]
        (μ : Distribution X)
        (eval : (i : Fin k) → Γ i → Y → R i)
        (G : (i : Fin k) → X → Measurement (Γ i) ιB)
        (A : X → Measurement ((i : Fin k) → Γ i) ιA)
        (ψ : EuclideanSpace ℂ (ιA × ιB)) (ε δ : ℝ),
      μ.IsProbability → ‖ψ‖ = 1 → 0 < ε → 0 ≤ δ →
      (∀ i x, MIPStarRE.QPBT.Measurement.IsProjective (G i x)) →
      (∀ x, MIPStarRE.QPBT.Measurement.IsProjective (A x)) →
      (∀ i (g g' : Γ i), g ≠ g' →
        avgOver (uniformDistribution Y)
          (fun y => if eval i g y = eval i g' y then 1 else 0) ≤ ε) →
      (∀ i, consistencyDefect (Distribution.prod μ (uniformDistribution Y))
        (fun xy a => heteroKron (((A xy.1).postprocess
          (fun g => eval i (g i) xy.2)).effect a) 1)
        (fun xy a => heteroKron 1 (((G i xy.1).postprocess
          (fun g => eval i g xy.2)).effect a)) ψ ≤ δ) →
      consistencyDefect (Distribution.prod μ (uniformDistribution Y))
        (fun xy a => heteroKron (((A xy.1).postprocess
          (evalFunctionTuple eval xy.2)).effect a) 1)
        (fun xy a => heteroKron 1 (∑ g : (i : Fin k) → Γ i,
          if evalFunctionTuple eval xy.2 g = a then
            sandwichProduct (fun i x h => (G i x).effect h) xy.1 g else 0)) ψ ≤
        C₀ * (k : ℝ) * Real.sqrt (δ + ε) := by
  refine ⟨8, by norm_num, ?_⟩
  intro k X Y ιA ιB R Γ
    _ _ _ _ _ _ _ _ _ _ _ _ _ μ eval G A ψ ε δ
    hμ hψ hε hδ hG hA hcollision hevaluated
  classical
  have herr : 0 ≤ δ + ε := add_nonneg hδ (le_of_lt hε)
  have hcodeword (i : Fin k) :
      consistencyDefect μ
          (fun x g => heteroKron
            (((A x).postprocess (fun h => h i)).effect g) 1)
          (fun x g => heteroKron 1 ((G i x).effect g)) ψ ≤ δ + ε := by
    have hcollisionStep := consistencyDefect_codewords_le_evaluated_add
      μ (fun x => (A x).postprocess (fun h => h i)) (fun x => G i x)
      ψ (eval i) ε hμ hψ (le_of_lt hε) (hcollision i)
    have hcollisionStep' :
        consistencyDefect μ
            (fun x g => heteroKron
              (((A x).postprocess (fun h => h i)).effect g) 1)
            (fun x g => heteroKron 1 ((G i x).effect g)) ψ ≤
          consistencyDefect (Distribution.prod μ (uniformDistribution Y))
            (fun xy a => heteroKron (((A xy.1).postprocess
              (fun h => eval i (h i) xy.2)).effect a) 1)
            (fun xy a => heteroKron 1 (((G i xy.1).postprocess
              (fun g => eval i g xy.2)).effect a)) ψ + ε := by
      simpa only [postprocess_postprocess_effect] using hcollisionStep
    calc
      _ ≤ _ := hcollisionStep'
      _ ≤ δ + ε := by linarith [hevaluated i]
  have hcoordinate (i : Fin k) : opFamilyDistSq μ
      (fun x g => heteroKron (((A x).postprocess (fun h => h i)).effect g) 1)
      (fun x g => heteroKron 1 ((G i x).effect g)) ψ ≤
        2 * (δ + ε) := by
    let AL : X → Measurement (Γ i) (ιA × ιB) := fun x =>
      leftPlacedMeasurement ((A x).postprocess (fun h => h i))
    let BR : X → Measurement (Γ i) (ιA × ιB) := fun x =>
      rightPlacedMeasurement (G i x)
    have hdistance := opFamilyDistSq_le_two_mul_consistencyDefect μ AL BR ψ
    have hdistance' : opFamilyDistSq μ
        (fun x g => heteroKron (((A x).postprocess (fun h => h i)).effect g) 1)
        (fun x g => heteroKron 1 ((G i x).effect g)) ψ ≤
          2 * consistencyDefect μ
            (fun x g => heteroKron
              (((A x).postprocess (fun h => h i)).effect g) 1)
            (fun x g => heteroKron 1 ((G i x).effect g)) ψ := by
      simpa only [AL, BR, leftPlacedMeasurement, rightPlacedMeasurement,
        MIPStarRE.Quantum.Measurement.ofSumEqOne] using hdistance
    exact hdistance'.trans
      (mul_le_mul_of_nonneg_left (hcodeword i) (by norm_num))
  let B : X → Measurement ((i : Fin k) → Γ i) ιB := fun x =>
    MIPStarRE.Quantum.Measurement.ofSumEqOne
      (fun g => sandwichProduct (fun i x' a => (G i x').effect a) x g)
      (sandwichProduct_isMeasurement G hG x).1
      (sandwichProduct_isMeasurement G hG x).2
  have hroot := sqrt_opFamilyDistSq_sandwichProduct_le
    μ G A ψ (2 * (δ + ε)) hG hA hcoordinate
  have hroot' : Real.sqrt (opFamilyDistSq μ
      (fun x g => heteroKron ((A x).effect g) 1)
      (fun x g => heteroKron 1 ((B x).effect g)) ψ) ≤
      4 * (k : ℝ) * Real.sqrt (δ + ε) := by
    have hsqrtTwo : Real.sqrt 2 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    have hsqrtError : Real.sqrt (2 * (δ + ε)) ≤
        2 * Real.sqrt (δ + ε) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      exact mul_le_mul_of_nonneg_right hsqrtTwo (Real.sqrt_nonneg _)
    have hrootB : Real.sqrt (opFamilyDistSq μ
        (fun x g => heteroKron ((A x).effect g) 1)
        (fun x g => heteroKron 1 ((B x).effect g)) ψ) ≤
        2 * (k : ℝ) * Real.sqrt (2 * (δ + ε)) := by
      simpa only [B, MIPStarRE.Quantum.Measurement.ofSumEqOne] using hroot
    calc
      Real.sqrt (opFamilyDistSq μ
          (fun x g => heteroKron ((A x).effect g) 1)
          (fun x g => heteroKron 1 ((B x).effect g)) ψ) ≤
          2 * (k : ℝ) * Real.sqrt (2 * (δ + ε)) := hrootB
      _ ≤ 2 * (k : ℝ) * (2 * Real.sqrt (δ + ε)) := by
        gcongr
      _ = 4 * (k : ℝ) * Real.sqrt (δ + ε) := by ring
  let AL : X → Measurement ((i : Fin k) → Γ i) (ιA × ιB) :=
    fun x => leftPlacedMeasurement (A x)
  let BR : X → Measurement ((i : Fin k) → Γ i) (ιA × ιB) :=
    fun x => rightPlacedMeasurement (B x)
  have hone : IsProj (1 : Op ιB) := IsStarProjection.one _
  have hAL (x : X) : MIPStarRE.QPBT.Measurement.IsProjective (AL x) := by
    intro g
    exact heteroKron_isProj (hA x g) hone
  have hbaseRaw := consistencyDefect_le_sqrt_of_projective_left
    μ AL BR ψ hμ hψ hAL
  have hbase : consistencyDefect μ
      (fun x g => heteroKron ((A x).effect g) 1)
      (fun x g => heteroKron 1 ((B x).effect g)) ψ ≤
      8 * (k : ℝ) * Real.sqrt (δ + ε) := by
    have hbase' : consistencyDefect μ
        (fun x g => heteroKron ((A x).effect g) 1)
        (fun x g => heteroKron 1 ((B x).effect g)) ψ ≤
        Real.sqrt (2 * opFamilyDistSq μ
          (fun x g => heteroKron ((A x).effect g) 1)
          (fun x g => heteroKron 1 ((B x).effect g)) ψ) := by
      simpa only [AL, BR, leftPlacedMeasurement, rightPlacedMeasurement,
        MIPStarRE.Quantum.Measurement.ofSumEqOne] using hbaseRaw
    have hsqrtTwo : Real.sqrt 2 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    calc
      consistencyDefect μ
          (fun x g => heteroKron ((A x).effect g) 1)
          (fun x g => heteroKron 1 ((B x).effect g)) ψ ≤
          Real.sqrt (2 * opFamilyDistSq μ
            (fun x g => heteroKron ((A x).effect g) 1)
            (fun x g => heteroKron 1 ((B x).effect g)) ψ) := hbase'
      _ = Real.sqrt 2 * Real.sqrt (opFamilyDistSq μ
          (fun x g => heteroKron ((A x).effect g) 1)
          (fun x g => heteroKron 1 ((B x).effect g)) ψ) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ 2 * Real.sqrt (opFamilyDistSq μ
          (fun x g => heteroKron ((A x).effect g) 1)
          (fun x g => heteroKron 1 ((B x).effect g)) ψ) := by
        gcongr
      _ ≤ 2 * (4 * (k : ℝ) * Real.sqrt (δ + ε)) := by
        gcongr
      _ = 8 * (k : ℝ) * Real.sqrt (δ + ε) := by ring
  have hprocessed := consistencyDefect_prod_postprocess_le
    μ A B ψ (fun y => evalFunctionTuple eval y)
  have htarget : consistencyDefect (Distribution.prod μ (uniformDistribution Y))
      (fun xy a => heteroKron (((A xy.1).postprocess
        (evalFunctionTuple eval xy.2)).effect a) 1)
      (fun xy a => heteroKron 1 (∑ g : (i : Fin k) → Γ i,
        if evalFunctionTuple eval xy.2 g = a then
          sandwichProduct (fun i x h => (G i x).effect h) xy.1 g else 0)) ψ ≤
      consistencyDefect μ
        (fun x g => heteroKron ((A x).effect g) 1)
        (fun x g => heteroKron 1 ((B x).effect g)) ψ := by
    simpa only [B, MIPStarRE.Quantum.Measurement.ofSumEqOne,
      MIPStarRE.Quantum.Measurement.postprocess_effect, Finset.sum_filter] using hprocessed
  exact htarget.trans hbase

/-- The positive-mass conditional collision bound used by `lem:pasting`.
This is a formalization-only spelling of the conditional probability in
`blueprint/src/chapter/ch12_qpbt_games.tex:517-546`, with paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`. -/
def HasConditionalCollisionBound {X Y₁ Y₂ R₂ Γ₂ : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
    [Fintype Y₂] [DecidableEq Y₂] [Fintype R₂] [DecidableEq R₂]
    [Fintype Γ₂]
    (D : Distribution ((X × Y₁) × Y₂)) (eval₂ : Γ₂ → Y₂ → R₂)
    (η : ℝ) : Prop :=
  ∀ x y₁, 0 < (D.map Prod.fst).weight (x, y₁) →
    ∀ g g' : Γ₂, g ≠ g' →
      (∑ y₂ : Y₂, D.weight ((x, y₁), y₂) *
        if eval₂ g y₂ = eval₂ g' y₂ then 1 else 0) ≤
        η * (D.map Prod.fst).weight (x, y₁)

/-- The effects obtained by sandwiching one measurement with a projective
measurement form a POVM. This is `lem:pasting-measurement`, the measurement
assertion for `eq:pasting-2a`; blueprint `ch12_qpbt_games.tex:548-567`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:514-524`. -/
theorem pastedMeasurement_isMeasurement {Γ₁ Γ₂ ι : Type*}
    [Fintype Γ₁] [Fintype Γ₂] [Fintype ι] [DecidableEq ι]
    (G₁ : Measurement Γ₁ ι) (G₂ : Measurement Γ₂ ι)
    (hG₂ : MIPStarRE.QPBT.Measurement.IsProjective G₂) :
    (∀ g : Γ₁ × Γ₂,
      0 ≤ pastedMeasurement G₁.effect G₂.effect g.1 g.2) ∧
      (∑ g : Γ₁ × Γ₂,
        pastedMeasurement G₁.effect G₂.effect g.1 g.2) = 1 := by
  constructor
  · intro g
    unfold pastedMeasurement
    apply Matrix.nonneg_iff_posSemidef.mpr
    have hpos : ((G₂.effect g.2)ᴴ * G₁.effect g.1 * G₂.effect g.2).PosSemidef :=
      (Matrix.nonneg_iff_posSemidef.mp (G₁.pos g.1)).conjTranspose_mul_mul_same
        (G₂.effect g.2)
    rw [MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian G₂ g.2] at hpos
    exact hpos
  · classical
    unfold pastedMeasurement
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    calc
      (∑ g₂ : Γ₂, ∑ g₁ : Γ₁,
          G₂.effect g₂ * G₁.effect g₁ * G₂.effect g₂) =
          ∑ g₂ : Γ₂,
            G₂.effect g₂ * (∑ g₁ : Γ₁, G₁.effect g₁) * G₂.effect g₂ := by
        apply Finset.sum_congr rfl
        intro g₂ _
        rw [Finset.mul_sum, Finset.sum_mul]
      _ = ∑ g₂ : Γ₂, G₂.effect g₂ := by
        apply Finset.sum_congr rfl
        intro g₂ _
        rw [G₁.sum_eq_one, mul_one, (hG₂ g₂).isIdempotentElem.eq]
      _ = 1 := G₂.sum_eq_one

/-- Pasting two consistent measurements yields a product-form polynomial
error. All operator families in the conclusion are the postprocessed source
families. This is `lem:pasting`, blueprint `ch12_qpbt_games.tex:517-546`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`.

**Unfaithful:** This source-shaped declaration remains admitted because the
current product-form predicate `IsPolyErr₂` makes the cited assertion false.
For every fixed `0 < δ < 1`, a two-dimensional correlated strategy can have
pasting defect `δ` for every `η > 0`, whereas `IsPolyErr₂ δp` forces
`δp η δ` to tend to zero with `η`. This is documented in
`docs/paper-gaps/qpbt_pasting-product-error.tex` and tracked by issue #196.
Elimination requires a documented correction of the multivariate polynomial
convention, or a source-level restriction coupling the two error parameters,
before formalizing the quantitative estimate of Fact 4.35. -/
theorem exists_pasting_error :
    ∃ δp : ℝ → ℝ → ℝ, IsPolyErr₂ δp ∧
      ∀ {X Y₁ Y₂ R₁ R₂ Γ₁ Γ₂ ι : Type*}
        [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
        [Fintype Y₂] [DecidableEq Y₂] [Fintype R₁] [DecidableEq R₁]
        [Fintype R₂] [DecidableEq R₂]
        [Fintype Γ₁] [DecidableEq Γ₁] [Fintype Γ₂] [DecidableEq Γ₂]
        [Fintype ι] [DecidableEq ι]
        (D : Distribution ((X × Y₁) × Y₂))
        (eval₁ : Γ₁ → Y₁ → R₁) (eval₂ : Γ₂ → Y₂ → R₂)
        (G₁ : X → Measurement Γ₁ ι) (G₂ : X → Measurement Γ₂ ι)
        (A : ((X × Y₁) × Y₂) → Measurement (R₁ × R₂) ι)
        (ψ : EuclideanSpace ℂ (ι × ι)) (η δ : ℝ),
        D.IsProbability → ‖ψ‖ = 1 → 0 ≤ η → 0 ≤ δ →
        (∀ x, MIPStarRE.QPBT.Measurement.IsProjective (G₂ x)) →
        (∀ q, MIPStarRE.QPBT.Measurement.IsProjective (A q)) →
        HasConditionalCollisionBound D eval₂ η →
        consistencyDefect D
          (fun q a₁ => heteroKron (((A q).postprocess Prod.fst).effect a₁) 1)
          (fun q a₁ => heteroKron 1 (((G₁ q.1.1).postprocess
            (fun g => eval₁ g q.1.2)).effect a₁)) ψ ≤ δ →
        consistencyDefect D
          (fun q a₂ => heteroKron (((A q).postprocess Prod.snd).effect a₂) 1)
          (fun q a₂ => heteroKron 1 (((G₂ q.1.1).postprocess
            (fun g => eval₂ g q.2)).effect a₂)) ψ ≤ δ →
        consistencyDefect D (fun q a => heteroKron ((A q).effect a) 1)
          (fun q a => heteroKron 1 ((A q).effect a)) ψ ≤ δ →
        consistencyDefect D (fun q a => heteroKron ((A q).effect a) 1)
          (fun q a => heteroKron 1 (∑ g₁ : Γ₁, ∑ g₂ : Γ₂,
            if (eval₁ g₁ q.1.2, eval₂ g₂ q.2) = a then
              pastedMeasurement (fun g => (G₁ q.1.1).effect g)
                (fun g => (G₂ q.1.1).effect g) g₁ g₂ else 0)) ψ ≤ δp η δ := by
  sorry

end MIPStarRE.QPBT
