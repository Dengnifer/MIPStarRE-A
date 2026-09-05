import MIPStarRE.QPBT.Games.Sandwich.Defs

/-! # Quantitative support for sandwiched measurements

This module develops the consistency and operator-distance estimates used
in the quantitative sandwich argument.

## References

Blueprint `blueprint/src/chapter/ch12_qpbt_games.tex:469-568`; paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:465-501`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum
open DistanceCalculus

namespace SandwichProduct

/-- Averaging over the product of two finite distributions is iterated
averaging. This is the formalization-only identity
`lem:sandwich-product-average` used in the proof of `lem:ld-sandwich`; detailed
source argument `references/neexp-paper/05_quantum_preliminaries.tex:952-994`. -/
theorem avgOver_distribution_prod {X Y : Type*}
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
original outcomes with equal labels. This is the formalization-only identity
`lem:sandwich-diagonal-postprocess` used in the proof of `lem:ld-sandwich`;
detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:952-994`. -/
theorem diagonal_postprocess_stateQForm_eq_pair_sum
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
of their pointwise off-diagonal tensor overlap. This is the formalization-only
identity `lem:sandwich-placed-defect-expansion` used in the proof of
`lem:ld-sandwich`; detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:952-994`. -/
theorem consistencyDefect_placed_eq_avg_point
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
-- Inferring finite outcome instances for the two postprocessed families is
-- expensive because both relabelings occur beneath nested outcome sums.
/-- Averaged diagonal overlap after evaluation exceeds the original diagonal
overlap by at most the collision probability. This is the formalization-only
estimate `lem:sandwich-evaluated-diagonal-overlap` used in the proof of
`lem:ld-sandwich`; detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:975-987`. -/
theorem avg_diagonal_postprocess_stateQForm_le
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
-- Inferring finite outcome instances for the complementary overlaps is
-- expensive because evaluation introduces a second finite outcome family.
/-- Taking complements converts the diagonal-overlap estimate into a
pointwise consistency-defect estimate. This is the formalization-only estimate
`lem:sandwich-point-codeword-defect` used in the proof of `lem:ld-sandwich`;
detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:975-987`. -/
theorem point_codeword_defect_le_avg_evaluated_add
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
-- Inferring finite outcome instances through both distribution averages is
-- expensive because the evaluated families depend on the sampled point.
/-- If distinct codewords collide under a random evaluation with probability
at most `ε`, their full-outcome consistency defect is at most the evaluated
defect plus `ε`. This is the formalization-only estimate
`lem:sandwich-codeword-defect` for the first step of `lem:ld-sandwich`;
detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:975-987`. -/
theorem consistencyDefect_codewords_le_evaluated_add
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
-- Inferring finite outcome instances for both postprocessed defects is
-- expensive because the relabeling varies with the independent sample.
/-- Averaging the fixed-map data-processing inequality over an independent
random relabeling preserves its bound. This is the formalization-only estimate
`lem:sandwich-random-postprocess` for the last step of `lem:ld-sandwich`;
detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:988-994`. -/
theorem consistencyDefect_prod_postprocess_le
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
ordinary triangle inequality. This is the formalization-only estimate
`lem:sandwich-root-distance-triangle` used for the repeated replacements in
`lem:ld-sandwich`; detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:930-946`. -/
theorem sqrt_opFamilyDistSq_triangle {X α ι : Type*}
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
projectivity. This is the formalization-only fact
`lem:sandwich-postprocess-projective` used in the palindromic construction of
`lem:ld-sandwich`; detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:930-946`. -/
theorem postprocess_isProjective {α β ι : Type*}
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
composition. This is the formalization-only identity
`lem:sandwich-postprocess-compose` used to align the coordinate marginals in
`lem:ld-sandwich`; detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:952-994`. -/
theorem postprocess_postprocess_effect {α β γ ι : Type*}
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
outcome. This is the formalization-only identity
`lem:sandwich-injective-postprocess` used to identify product outcomes in
`lem:ld-sandwich`; detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:930-946`. -/
theorem postprocess_effect_of_injective {α β ι : Type*}
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

/-- The squared effects of a POVM sum to at most the identity. This is the
formalization-only estimate `lem:sandwich-povm-square-sum` used in the
contractions underlying `lem:ld-sandwich`; detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:930-946`. -/
theorem measurement_sum_adjoint_mul_le_one {α ι : Type*}
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
the identity. This is the formalization-only estimate
`lem:sandwich-matched-tensor-sum` used in the joint-family comparison for
`lem:ld-sandwich`; detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:930-946`. -/
theorem matched_tensor_sum_le_one {α ιA ιB : Type*}
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
effect preserves square-summability. This is the formalization-only estimate
`lem:sandwich-projective-multiplier-sum` used for an outer palindromic factor in
`lem:ld-sandwich`; detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:930-946`. -/
theorem projective_mul_measurement_sum_adjoint_mul_le_one
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

/-- Tensoring two projectors gives a projector on the product space. This is
the formalization-only fact `lem:sandwich-tensor-projector` used when converting
distance back to consistency in `lem:ld-sandwich`; detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:930-946`. -/
theorem heteroKron_isProj {ιA ιB : Type*}
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
most the identity. This is the formalization-only estimate
`lem:sandwich-pair-fiber-sum` used for a joint-measurement marginal in
`lem:ld-sandwich`; detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:930-946`. -/
theorem measurement_pair_fiber_sum_adjoint_mul_le_one
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
postprocessing fiber. This is the formalization-only identity
`lem:sandwich-postprocess-effect-left` used in the joint-family comparison for
`lem:ld-sandwich`; detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:930-946`. -/
theorem postprocess_effect_mul_effect {α β ι : Type*}
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

/-- A projective joint effect selects its matching postprocessing fiber when
multiplied on the right. This is the formalization-only identity
`lem:sandwich-postprocess-effect-right` used in the joint-family comparison for
`lem:ld-sandwich`; detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:930-946`. -/
theorem effect_mul_postprocess_effect {α β ι : Type*}
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
the unique joint effect in their common fiber. This is the formalization-only
identity `lem:sandwich-joint-marginal-product` used in the palindromic insertion
for `lem:ld-sandwich`; detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:930-946`. -/
theorem postprocess_product_eq_effect {α β γ ι : Type*}
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
multipliers are square-summable on every fiber of the outcome map. This is the
formalization-only estimate `lem:sandwich-fiber-contraction` used in each
palindromic insertion for `lem:ld-sandwich`; detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:930-946`. -/
theorem opFamilyDistSq_mul_fiber_le {X α Γ ι : Type*}
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

end SandwichProduct

namespace SandwichInternal

@[deprecated SandwichProduct.avgOver_distribution_prod (since := "2026-09-05")]
alias avgOver_distribution_prod := SandwichProduct.avgOver_distribution_prod

@[deprecated SandwichProduct.diagonal_postprocess_stateQForm_eq_pair_sum
  (since := "2026-09-05")]
alias diagonal_postprocess_stateQForm_eq_pair_sum :=
  SandwichProduct.diagonal_postprocess_stateQForm_eq_pair_sum

@[deprecated SandwichProduct.consistencyDefect_placed_eq_avg_point
  (since := "2026-09-05")]
alias consistencyDefect_placed_eq_avg_point :=
  SandwichProduct.consistencyDefect_placed_eq_avg_point

@[deprecated SandwichProduct.avg_diagonal_postprocess_stateQForm_le
  (since := "2026-09-05")]
alias avg_diagonal_postprocess_stateQForm_le :=
  SandwichProduct.avg_diagonal_postprocess_stateQForm_le

@[deprecated SandwichProduct.point_codeword_defect_le_avg_evaluated_add
  (since := "2026-09-05")]
alias point_codeword_defect_le_avg_evaluated_add :=
  SandwichProduct.point_codeword_defect_le_avg_evaluated_add

@[deprecated SandwichProduct.consistencyDefect_codewords_le_evaluated_add
  (since := "2026-09-05")]
alias consistencyDefect_codewords_le_evaluated_add :=
  SandwichProduct.consistencyDefect_codewords_le_evaluated_add

@[deprecated SandwichProduct.consistencyDefect_prod_postprocess_le
  (since := "2026-09-05")]
alias consistencyDefect_prod_postprocess_le :=
  SandwichProduct.consistencyDefect_prod_postprocess_le

@[deprecated SandwichProduct.sqrt_opFamilyDistSq_triangle (since := "2026-09-05")]
alias sqrt_opFamilyDistSq_triangle := SandwichProduct.sqrt_opFamilyDistSq_triangle

@[deprecated SandwichProduct.postprocess_isProjective (since := "2026-09-05")]
alias postprocess_isProjective := SandwichProduct.postprocess_isProjective

@[deprecated SandwichProduct.postprocess_postprocess_effect (since := "2026-09-05")]
alias postprocess_postprocess_effect := SandwichProduct.postprocess_postprocess_effect

@[deprecated SandwichProduct.postprocess_effect_of_injective (since := "2026-09-05")]
alias postprocess_effect_of_injective := SandwichProduct.postprocess_effect_of_injective

@[deprecated SandwichProduct.measurement_sum_adjoint_mul_le_one
  (since := "2026-09-05")]
alias measurement_sum_adjoint_mul_le_one :=
  SandwichProduct.measurement_sum_adjoint_mul_le_one

@[deprecated SandwichProduct.matched_tensor_sum_le_one (since := "2026-09-05")]
alias matched_tensor_sum_le_one := SandwichProduct.matched_tensor_sum_le_one

@[deprecated SandwichProduct.projective_mul_measurement_sum_adjoint_mul_le_one
  (since := "2026-09-05")]
alias projective_mul_measurement_sum_adjoint_mul_le_one :=
  SandwichProduct.projective_mul_measurement_sum_adjoint_mul_le_one

@[deprecated SandwichProduct.heteroKron_isProj (since := "2026-09-05")]
alias heteroKron_isProj := SandwichProduct.heteroKron_isProj

@[deprecated SandwichProduct.measurement_pair_fiber_sum_adjoint_mul_le_one
  (since := "2026-09-05")]
alias measurement_pair_fiber_sum_adjoint_mul_le_one :=
  SandwichProduct.measurement_pair_fiber_sum_adjoint_mul_le_one

@[deprecated SandwichProduct.postprocess_effect_mul_effect (since := "2026-09-05")]
alias postprocess_effect_mul_effect := SandwichProduct.postprocess_effect_mul_effect

@[deprecated SandwichProduct.effect_mul_postprocess_effect (since := "2026-09-05")]
alias effect_mul_postprocess_effect := SandwichProduct.effect_mul_postprocess_effect

@[deprecated SandwichProduct.postprocess_product_eq_effect (since := "2026-09-05")]
alias postprocess_product_eq_effect := SandwichProduct.postprocess_product_eq_effect

@[deprecated SandwichProduct.opFamilyDistSq_mul_fiber_le (since := "2026-09-05")]
alias opFamilyDistSq_mul_fiber_le := SandwichProduct.opFamilyDistSq_mul_fiber_le

end SandwichInternal

end MIPStarRE.QPBT
