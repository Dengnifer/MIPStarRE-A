import MIPStarRE.QPBT.Games.DistanceTheorems.TensorSupport
import MIPStarRE.QPBT.Games.StrategyClasses

/-! # State-dependent distance calculus

This module records the consistency and state-dependent distance estimates used
throughout the quantum Pauli basis test. The statements retain explicit
constants that the paper absorbs into asymptotic notation.

## References

The source results are `fact:agreement` through
`lem:close-strategies-have-close-values` in
`blueprint/src/chapter/ch12_qpbt_games.tex:245-482`, with paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-461` and
`:531-540`. The observable conversion lemmas come from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:95-131`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

/-- Consistency bounds state-dependent distance, with the explicit factor
hidden in `fact:agreement`; blueprint `ch12_qpbt_games.tex:245-255`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-311`. -/
theorem opFamilyDistSq_le_two_mul_consistencyDefect {X α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B : X → Measurement α ι)
    (ψ : EuclideanSpace ℂ ι) :
    opFamilyDistSq μ (fun x a => (A x).effect a) (fun x a => (B x).effect a) ψ ≤
      2 * consistencyDefect μ (fun x a => (A x).effect a)
        (fun x a => (B x).effect a) ψ := by
  unfold opFamilyDistSq consistencyDefect avgOver
  simp_rw [consistency_term_eq_stateQForm]
  calc
    (∑ x ∈ μ.support, μ.weight x *
        ∑ a : α, ‖applyOperatorToState ((A x).effect a - (B x).effect a) ψ‖ ^ 2) ≤
      ∑ x ∈ μ.support, μ.weight x *
        (2 * ∑ a : α, ∑ b : α, if a = b then 0 else
          stateQForm ψ ((A x).effect a * (B x).effect b)) := by
      refine Finset.sum_le_sum ?_
      intro x _
      exact mul_le_mul_of_nonneg_left
        (point_distance_le_two_defect (A x) (B x) ψ) (μ.nonnegative x)
    _ = 2 * ∑ x ∈ μ.support, μ.weight x *
        (∑ a : α, ∑ b : α, if a = b then 0 else
          stateQForm ψ ((A x).effect a * (B x).effect b)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring

/-- For projective POVMs, state-dependent distance bounds consistency. This is
the second item of `fact:agreement`, blueprint `ch12_qpbt_games.tex:245-255`,
paper `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-311`. -/
theorem consistencyDefect_le_opFamilyDistSq_of_projective {X α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B : X → Measurement α ι)
    (ψ : EuclideanSpace ℂ ι)
    (hA : ∀ x, MIPStarRE.QPBT.Measurement.IsProjective (A x))
    (hB : ∀ x, MIPStarRE.QPBT.Measurement.IsProjective (B x)) :
    consistencyDefect μ (fun x a => (A x).effect a) (fun x a => (B x).effect a) ψ ≤
      opFamilyDistSq μ (fun x a => (A x).effect a) (fun x a => (B x).effect a) ψ := by
  have heq :
      opFamilyDistSq μ (fun x a => (A x).effect a)
          (fun x a => (B x).effect a) ψ =
        2 * consistencyDefect μ (fun x a => (A x).effect a)
          (fun x a => (B x).effect a) ψ := by
    unfold opFamilyDistSq consistencyDefect avgOver
    simp_rw [consistency_term_eq_stateQForm]
    calc
      (∑ x ∈ μ.support, μ.weight x *
          ∑ a : α,
            ‖applyOperatorToState ((A x).effect a - (B x).effect a) ψ‖ ^ 2) =
        ∑ x ∈ μ.support, μ.weight x *
          (2 * ∑ a : α, ∑ b : α, if a = b then 0 else
            stateQForm ψ ((A x).effect a * (B x).effect b)) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [point_distance_eq_two_defect_of_projective
          (A x) (B x) ψ (hA x) (hB x)]
      _ = 2 * ∑ x ∈ μ.support, μ.weight x *
          (∑ a : α, ∑ b : α, if a = b then 0 else
            stateQForm ψ ((A x).effect a * (B x).effect b)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
  have hnonneg := opFamilyDistSq_nonneg μ
    (fun x a => (A x).effect a) (fun x a => (B x).effect a) ψ
  nlinarith

/-- Projectivity of the left family gives the square-root consistency estimate
for a unit state under a probability distribution. This is the left-projective
branch of the third item of `fact:agreement`; blueprint
`ch12_qpbt_games.tex:245-255`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:306-309`.

**Scope restriction:** The cited item also permits the right family to be
projective. The source-facing disjunction is tracked by issue #33. -/
theorem consistencyDefect_le_sqrt_of_projective_left {X α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B : X → Measurement α ι)
    (ψ : EuclideanSpace ℂ ι)
    (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1)
    (hA : ∀ x, MIPStarRE.QPBT.Measurement.IsProjective (A x)) :
    consistencyDefect μ (fun x a => (A x).effect a) (fun x a => (B x).effect a) ψ ≤
      Real.sqrt (2 * opFamilyDistSq μ (fun x a => (A x).effect a)
        (fun x a => (B x).effect a) ψ) := by
  let f : X → ℝ := fun x =>
    ∑ a : α, ∑ b : α, if a = b then 0 else
      stateQForm ψ ((A x).effect a * (B x).effect b)
  let g : X → ℝ := fun x =>
    ∑ a : α, ‖applyOperatorToState
      ((A x).effect a - (B x).effect a) ψ‖ ^ 2
  have hf (x : X) : |f x| ≤ Real.sqrt (g x) :=
    abs_point_defect_le_sqrt_distance_of_projective_left
      (A x) (B x) ψ hψ (hA x)
  have hg (x : X) : 0 ≤ g x :=
    Finset.sum_nonneg fun a _ => sq_nonneg _
  have havg : |avgOver μ f| ≤ Real.sqrt (avgOver μ g) :=
    MIPStarRE.LDT.Preliminaries.avgOver_abs_le_sqrt_of_pointwise μ f g hf hg (by
      rw [hμ.weight_sum_eq_one])
  have hdefect : consistencyDefect μ (fun x a => (A x).effect a)
      (fun x a => (B x).effect a) ψ = avgOver μ f := by
    unfold consistencyDefect
    simp_rw [consistency_term_eq_stateQForm]
    rfl
  have hdistance : opFamilyDistSq μ (fun x a => (A x).effect a)
      (fun x a => (B x).effect a) ψ = avgOver μ g := rfl
  rw [hdefect, hdistance]
  have hgavg : 0 ≤ avgOver μ g := by
    unfold avgOver
    exact Finset.sum_nonneg fun x _ => mul_nonneg (μ.nonnegative x) (hg x)
  calc
    avgOver μ f ≤ |avgOver μ f| := le_abs_self _
    _ ≤ Real.sqrt (avgOver μ g) := havg
    _ ≤ Real.sqrt (2 * avgOver μ g) := by
      apply Real.sqrt_le_sqrt
      linarith

/-- Left multiplication by a square-summable operator family does not increase
state-dependent distance. This is `fact:add-a-proj`, blueprint
`ch12_qpbt_games.tex:260-265`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:313-344`. -/
theorem opFamilyDistSq_mul_left_le {X Y α β γ ι : Type*}
    [DecidableEq X] [Fintype α] [Fintype β] [Fintype γ]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution (X × Y)) (A B : X → (α × β) → Op ι)
    (C : Y → α → γ → Op ι) (ψ : EuclideanSpace ℂ ι) (δ : ℝ)
    (hC : ∀ y a, (1 - ∑ c : γ, (C y a c)ᴴ * C y a c).PosSemidef)
    (h : opFamilyDistSq (μ.map Prod.fst) A B ψ ≤ δ) :
    opFamilyDistSq μ
      (fun p (abc : (α × β) × γ) =>
        C p.2 abc.1.1 abc.2 * A p.1 (abc.1.1, abc.1.2))
      (fun p (abc : (α × β) × γ) =>
        C p.2 abc.1.1 abc.2 * B p.1 (abc.1.1, abc.1.2)) ψ ≤ δ := by
  have hC' (y : Y) (a : α) :
      ∑ c : γ, (C y a c)ᴴ * C y a c ≤ 1 :=
    Matrix.le_iff.mpr (hC y a)
  calc
    opFamilyDistSq μ
        (fun p (abc : (α × β) × γ) =>
          C p.2 abc.1.1 abc.2 * A p.1 (abc.1.1, abc.1.2))
        (fun p (abc : (α × β) × γ) =>
          C p.2 abc.1.1 abc.2 * B p.1 (abc.1.1, abc.1.2)) ψ
        ≤ opFamilyDistSq μ (fun p ab => A p.1 ab) (fun p ab => B p.1 ab) ψ := by
          unfold opFamilyDistSq
          apply avgOver_mono
          intro p
          rw [Fintype.sum_prod_type]
          apply Finset.sum_le_sum
          intro ab _
          simpa only [mul_sub] using
            sum_norm_mul_apply_le (fun c => C p.2 ab.1 c)
              (A p.1 ab - B p.1 ab) ψ (hC' p.2 ab.1)
    _ = opFamilyDistSq (μ.map Prod.fst) A B ψ := by
      unfold opFamilyDistSq
      exact (Distribution.avgOver_map μ Prod.fst
        (fun x => ∑ a : α × β,
          ‖applyOperatorToState (A x a - B x a) ψ‖ ^ 2)).symm
    _ ≤ δ := h

/-- Left multiplication by operators indexed by an arbitrary finite family of
functions preserves a state-dependent bound. This is `fact:add-a-proj2`,
blueprint `ch12_qpbt_games.tex:276-281`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:347-361`. -/
theorem opFamilyDistSq_mul_funIndexed_le {X α Γ ι : Type*}
    [Fintype α] [Fintype Γ]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B : X → Measurement α ι)
    (eval : Γ → X → α) (S : X → Γ → Op ι)
    (ψ : EuclideanSpace ℂ ι) (δ : ℝ)
    (hS : ∀ x, (1 - ∑ g : Γ, (S x g)ᴴ * S x g).PosSemidef)
    (h : opFamilyDistSq μ (fun x a => (A x).effect a)
      (fun x a => (B x).effect a) ψ ≤ δ) :
    opFamilyDistSq μ (fun x g => S x g * (A x).effect (eval g x))
      (fun x g => S x g * (B x).effect (eval g x)) ψ ≤ δ := by
  have hS' (x : X) : ∑ g : Γ, (S x g)ᴴ * S x g ≤ 1 :=
    Matrix.le_iff.mpr (hS x)
  calc
    opFamilyDistSq μ (fun x g => S x g * (A x).effect (eval g x))
        (fun x g => S x g * (B x).effect (eval g x)) ψ ≤
      opFamilyDistSq μ (fun x a => (A x).effect a)
        (fun x a => (B x).effect a) ψ := by
      unfold opFamilyDistSq
      apply avgOver_mono
      intro x
      simpa only [mul_sub] using
        sum_norm_mul_funIndexed_apply_le (fun g => eval g x) (S x)
          (fun a => (A x).effect a - (B x).effect a) ψ (hS' x)
    _ ≤ δ := h

/-- A projective sub-sum absorbs an approximating operator family. This is
`lem:cool-closeness-fact`, blueprint `ch12_qpbt_games.tex:294-302`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:364-380`. -/
theorem opDistSq_sum_sub_mul_le_of_projective {X α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype α]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A : X → Measurement α ι) (B : X → α → Op ι)
    (ψ : EuclideanSpace ℂ ι) (δ : ℝ)
    (hA : ∀ x, MIPStarRE.QPBT.Measurement.IsProjective (A x))
    (h : opFamilyDistSq μ (fun x a => (A x).effect a) B ψ ≤ δ)
    (s : Finset α) :
    opDistSq μ (fun x => ∑ a ∈ s, (A x).effect a)
      (fun x => ∑ a ∈ s, (A x).effect a * B x a) ψ ≤ δ := by
  classical
  apply le_trans ?_ h
  unfold opDistSq opFamilyDistSq avgOver
  simp only [Fintype.sum_unique]
  refine Finset.sum_le_sum fun x _ =>
    mul_le_mul_of_nonneg_left ?_ (μ.nonnegative x)
  let D : α → Op ι := fun a => (A x).effect a - B x a
  have horth : ∀ {a b : α}, a ≠ b →
      (A x).effect a * (A x).effect b = 0 := by
    intro a b hab
    exact projective_effect_mul_effect_eq_zero (A x) (hA x) hab
  have hsum :
      (∑ a ∈ s, (A x).effect a) -
          (∑ a ∈ s, (A x).effect a * B x a) =
        ∑ a ∈ s, (A x).effect a * D a := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    simp only [D, mul_sub]
    rw [(hA x a).isIdempotentElem.eq]
  rw [hsum]
  exact norm_finset_sum_projector_mul_sq_le
    (fun a => (A x).effect a) D (hA x) horth s ψ

/-- Explicit squared-distance triangle inequality. This is `fact:triangle`,
blueprint `ch12_qpbt_games.tex:316-321`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:383-387`. -/
theorem opFamilyDistSq_le_of_le_of_le {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B C : X → α → Op ι)
    (ψ : EuclideanSpace ℂ ι) (δ ε : ℝ)
    (hAB : opFamilyDistSq μ A B ψ ≤ δ)
    (hBC : opFamilyDistSq μ B C ψ ≤ ε) :
    opFamilyDistSq μ A C ψ ≤ 2 * δ + 2 * ε := by
  have hpoint : ∀ x a,
      ‖applyOperatorToState (A x a - C x a) ψ‖ ^ 2 ≤
        2 * ‖applyOperatorToState (A x a - B x a) ψ‖ ^ 2 +
          2 * ‖applyOperatorToState (B x a - C x a) ψ‖ ^ 2 := by
    intro x a
    have hdecomp : applyOperatorToState (A x a - C x a) ψ =
        applyOperatorToState (A x a - B x a) ψ +
          applyOperatorToState (B x a - C x a) ψ := by
      simp [applyOperatorToState]
    rw [hdecomp]
    let u := applyOperatorToState (A x a - B x a) ψ
    let v := applyOperatorToState (B x a - C x a) ψ
    calc
      ‖u + v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).2
          (norm_add_le u v)
      _ ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
        nlinarith [sq_nonneg (‖u‖ - ‖v‖)]
  unfold opFamilyDistSq at *
  calc
    avgOver μ (fun x => ∑ a, ‖applyOperatorToState (A x a - C x a) ψ‖ ^ 2)
        ≤ avgOver μ (fun x => ∑ a,
          (2 * ‖applyOperatorToState (A x a - B x a) ψ‖ ^ 2 +
            2 * ‖applyOperatorToState (B x a - C x a) ψ‖ ^ 2)) := by
          apply avgOver_mono
          intro x
          exact Finset.sum_le_sum fun a _ => hpoint x a
    _ = 2 * avgOver μ (fun x => ∑ a,
          ‖applyOperatorToState (A x a - B x a) ψ‖ ^ 2) +
        2 * avgOver μ (fun x => ∑ a,
          ‖applyOperatorToState (B x a - C x a) ψ‖ ^ 2) := by
          simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          rw [avgOver_add, avgOver_const_mul, avgOver_const_mul]
    _ ≤ 2 * δ + 2 * ε := add_le_add
      (mul_le_mul_of_nonneg_left hAB (by positivity))
      (mul_le_mul_of_nonneg_left hBC (by positivity))

/-- Triangle inequality for consistency on a unit state under a probability
distribution, with the square-root loss of `fact:triangle-for-simeq`; blueprint
`ch12_qpbt_games.tex:327-335`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:389-395`. -/
theorem consistencyDefect_trans_le {X α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B C D : X → Measurement α ι)
    (ψ : EuclideanSpace ℂ ι) (ε δ γ : ℝ)
    (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1)
    (hAB : consistencyDefect μ (fun x a => (A x).effect a)
      (fun x a => (B x).effect a) ψ ≤ ε)
    (hCB : consistencyDefect μ (fun x a => (C x).effect a)
      (fun x a => (B x).effect a) ψ ≤ δ)
    (hCD : consistencyDefect μ (fun x a => (C x).effect a)
      (fun x a => (D x).effect a) ψ ≤ γ) :
    consistencyDefect μ (fun x a => (A x).effect a)
      (fun x a => (D x).effect a) ψ ≤ ε + 2 * Real.sqrt (δ + γ) := by
  letI : Nonempty ι := by
    by_contra hι
    rw [not_nonempty_iff] at hι
    letI := hι
    have hzero : ψ = 0 := Subsingleton.elim _ _
    rw [hzero, norm_zero] at hψ
    norm_num at hψ
  have hCBdist : opFamilyDistSq μ (fun x a => (C x).effect a)
      (fun x a => (B x).effect a) ψ ≤ 2 * δ := by
    calc
      _ ≤ 2 * consistencyDefect μ (fun x a => (C x).effect a)
          (fun x a => (B x).effect a) ψ :=
        opFamilyDistSq_le_two_mul_consistencyDefect μ C B ψ
      _ ≤ 2 * δ := mul_le_mul_of_nonneg_left hCB (by norm_num)
  have hBCdist : opFamilyDistSq μ (fun x a => (B x).effect a)
      (fun x a => (C x).effect a) ψ ≤ 2 * δ := by
    rw [opFamilyDistSq_symm]
    exact hCBdist
  have hCDdist : opFamilyDistSq μ (fun x a => (C x).effect a)
      (fun x a => (D x).effect a) ψ ≤ 2 * γ := by
    calc
      _ ≤ 2 * consistencyDefect μ (fun x a => (C x).effect a)
          (fun x a => (D x).effect a) ψ :=
        opFamilyDistSq_le_two_mul_consistencyDefect μ C D ψ
      _ ≤ 2 * γ := mul_le_mul_of_nonneg_left hCD (by norm_num)
  have hBDdist : opFamilyDistSq μ (fun x a => (B x).effect a)
      (fun x a => (D x).effect a) ψ ≤ 4 * (δ + γ) := by
    have htri := opFamilyDistSq_le_of_le_of_le μ
      (fun x a => (B x).effect a) (fun x a => (C x).effect a)
      (fun x a => (D x).effect a) ψ (2 * δ) (2 * γ) hBCdist hCDdist
    linarith
  have hgap := overlap_gap_le_of_opFamilyDistSq μ A B D ψ hμ hψ
    (4 * (δ + γ)) hBDdist
  have hsqrt : Real.sqrt (4 * (δ + γ)) = 2 * Real.sqrt (δ + γ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  rw [consistencyDefect_eq_one_sub_overlap μ A B ψ hμ hψ] at hAB
  rw [consistencyDefect_eq_one_sub_overlap μ A D ψ hμ hψ]
  have hdiff :
      avgOver μ (fun x => ∑ a,
          stateQForm ψ ((A x).effect a * (B x).effect a)) -
        avgOver μ (fun x => ∑ a,
          stateQForm ψ ((A x).effect a * (D x).effect a)) ≤
        2 * Real.sqrt (δ + γ) := by
    calc
      _ ≤ |avgOver μ (fun x => ∑ a,
            stateQForm ψ ((A x).effect a * (B x).effect a)) -
          avgOver μ (fun x => ∑ a,
            stateQForm ψ ((A x).effect a * (D x).effect a))| := le_abs_self _
      _ ≤ Real.sqrt (4 * (δ + γ)) := hgap
      _ = 2 * Real.sqrt (δ + γ) := hsqrt
  linarith

/-- Coarse-graining measurements on opposite tensor factors cannot increase
inconsistency. This is `fact:data-processing`, blueprint
`ch12_qpbt_games.tex:341-349`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:397-401`. -/
theorem consistencyDefect_postprocess_le {X α β ιA ιB : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : Distribution X) (A : X → Measurement α ιA)
    (B : X → Measurement α ιB) (ψ : EuclideanSpace ℂ (ιA × ιB))
    (f : α → β) :
    consistencyDefect μ
        (fun x b => heteroKron (((A x).postprocess f).effect b) 1)
        (fun x b => heteroKron 1 (((B x).postprocess f).effect b)) ψ ≤
      consistencyDefect μ (fun x a => heteroKron ((A x).effect a) 1)
        (fun x a => heteroKron 1 ((B x).effect a)) ψ := by
  unfold consistencyDefect
  simp_rw [consistency_term_eq_stateQForm]
  apply avgOver_mono
  intro x
  rw [show (∑ b : β, ∑ c : β, if b = c then 0 else
      stateQForm ψ
        (heteroKron (((A x).postprocess f).effect b) 1 *
          heteroKron 1 (((B x).postprocess f).effect c))) =
      ‖ψ‖ ^ 2 - ∑ b : β, stateQForm ψ
        (heteroKron (((A x).postprocess f).effect b)
          (((B x).postprocess f).effect b)) by
    simpa [leftPlacedMeasurement, rightPlacedMeasurement,
      MIPStarRE.Quantum.Measurement.ofSumEqOne,
      placed_product_stateQForm_eq] using
      point_defect_eq
        (leftPlacedMeasurement ((A x).postprocess f))
        (rightPlacedMeasurement ((B x).postprocess f)) ψ]
  rw [show (∑ a : α, ∑ a' : α, if a = a' then 0 else
      stateQForm ψ
        (heteroKron ((A x).effect a) 1 * heteroKron 1 ((B x).effect a'))) =
      ‖ψ‖ ^ 2 - ∑ a : α,
        stateQForm ψ (heteroKron ((A x).effect a) ((B x).effect a)) by
    simpa [leftPlacedMeasurement, rightPlacedMeasurement,
      MIPStarRE.Quantum.Measurement.ofSumEqOne,
      placed_product_stateQForm_eq] using
      point_defect_eq (leftPlacedMeasurement (A x))
        (rightPlacedMeasurement (B x)) ψ]
  exact sub_le_sub_left (diagonal_postprocess_stateQForm_ge ψ (A x) (B x) f) _

private theorem opFamilyDistSq_mul_left_same_question_le {X α β γ ι : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B : X → (α × β) → Op ι)
    (C : X → α → γ → Op ι) (ψ : EuclideanSpace ℂ ι) (δ : ℝ)
    (hC : ∀ x a, (1 - ∑ c : γ, (C x a c)ᴴ * C x a c).PosSemidef)
    (h : opFamilyDistSq μ A B ψ ≤ δ) :
    opFamilyDistSq μ
      (fun x (abc : (α × β) × γ) =>
        C x abc.1.1 abc.2 * A x (abc.1.1, abc.1.2))
      (fun x (abc : (α × β) × γ) =>
        C x abc.1.1 abc.2 * B x (abc.1.1, abc.1.2)) ψ ≤ δ := by
  classical
  let μdiag : Distribution (X × X) := μ.map (fun x => (x, x))
  have hbase : opFamilyDistSq (μdiag.map Prod.fst) A B ψ ≤ δ := by
    simpa [μdiag, opFamilyDistSq, Distribution.avgOver_map] using h
  have hout := opFamilyDistSq_mul_left_le μdiag A B C ψ δ hC hbase
  simpa [μdiag, opFamilyDistSq, Distribution.avgOver_map] using hout

/-- Joint closeness to a projective refinement implies approximate
commutation. The bound has one universal constant, independent of the finite
alphabets, Hilbert space, distributions, operators, state, and error; blueprint
`ch12_qpbt_games.tex:356-369`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:410-461`. -/
theorem opDistSq_commutator_le :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧
      ∀ {X α β γ ιA ιB : Type*}
      [Fintype α] [DecidableEq α]
      [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
      [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
      (μ : Distribution X)
      (A : X → Measurement (α × β) ιA)
      (B : X → Measurement ((α × β) × γ) ιB)
      (D : X → Measurement (α × γ) ιA)
      (ψ : EuclideanSpace ℂ (ιA × ιB)) (δ : ℝ),
      (∀ x, MIPStarRE.QPBT.Measurement.IsProjective (B x)) →
      opFamilyDistSq μ
        (fun x ab => heteroKron ((A x).effect ab) 1)
        (fun x ab => heteroKron 1 (((B x).postprocess
          (fun abc => abc.1)).effect ab)) ψ ≤ δ →
      opFamilyDistSq μ
        (fun x ac => heteroKron ((D x).effect ac) 1)
        (fun x ac => heteroKron 1 (((B x).postprocess
          (fun abc => (abc.1.1, abc.2))).effect ac)) ψ ≤ δ →
      opFamilyDistSq μ
        (fun x (abc : (α × β) × γ) => heteroKron
          (((A x).effect (abc.1.1, abc.1.2)) * ((D x).effect (abc.1.1, abc.2)) -
            ((D x).effect (abc.1.1, abc.2)) * ((A x).effect (abc.1.1, abc.1.2))) 1)
        (fun _ _ => 0) ψ ≤ C₀ * δ := by
  refine ⟨16, by norm_num, ?_⟩
  intro X α β γ ιA ιB _ _ _ _ _ _ _ _ _ _ μ A B D ψ δ hB hAB hDB
  let AL : X → (α × β) → Op (ιA × ιB) :=
    fun x ab => leftTensor (ι₂ := ιB) ((A x).effect ab)
  let DL : X → (α × γ) → Op (ιA × ιB) :=
    fun x ac => leftTensor (ι₂ := ιB) ((D x).effect ac)
  let BAB : X → (α × β) → Op (ιA × ιB) :=
    fun x ab => rightTensor (ι₁ := ιA)
      (((B x).postprocess (fun abc => abc.1)).effect ab)
  let BAC : X → (α × γ) → Op (ιA × ιB) :=
    fun x ac => rightTensor (ι₁ := ιA)
      (((B x).postprocess (fun abc => (abc.1.1, abc.2))).effect ac)
  let BJ : X → ((α × β) × γ) → Op (ιA × ιB) :=
    fun x abc => rightTensor (ι₁ := ιA) ((B x).effect abc)
  let FAD : X → ((α × β) × γ) → Op (ιA × ιB) :=
    fun x abc => AL x abc.1 * DL x (abc.1.1, abc.2)
  let FDA : X → ((α × β) × γ) → Op (ιA × ιB) :=
    fun x abc => DL x (abc.1.1, abc.2) * AL x abc.1
  let FMidAD : X → ((α × β) × γ) → Op (ιA × ιB) :=
    fun x abc => AL x abc.1 * BAC x (abc.1.1, abc.2)
  let FMidDA : X → ((α × β) × γ) → Op (ιA × ιB) :=
    fun x abc => DL x (abc.1.1, abc.2) * BAB x abc.1
  have hAB' : opFamilyDistSq μ AL BAB ψ ≤ δ := by
    simpa [AL, BAB, heteroKron, leftTensor, rightTensor] using hAB
  have hDB' : opFamilyDistSq μ DL BAC ψ ≤ δ := by
    simpa [DL, BAC, heteroKron, leftTensor, rightTensor] using hDB
  have hAL : ∀ x a,
      (1 - ∑ b : β, (AL x (a, b))ᴴ * AL x (a, b)).PosSemidef := by
    intro x a
    exact left_fiber_contraction (A x) a
  have hDL : ∀ x a,
      (1 - ∑ c : γ, (DL x (a, c))ᴴ * DL x (a, c)).PosSemidef := by
    intro x a
    exact left_fiber_contraction (D x) a
  have hBAB : ∀ x a,
      (1 - ∑ b : β, (BAB x (a, b))ᴴ * BAB x (a, b)).PosSemidef := by
    intro x a
    exact right_fiber_contraction
      ((B x).postprocess (fun abc => abc.1)) a
  have hBAC : ∀ x a,
      (1 - ∑ c : γ, (BAC x (a, c))ᴴ * BAC x (a, c)).PosSemidef := by
    intro x a
    exact right_fiber_contraction
      ((B x).postprocess (fun abc => (abc.1.1, abc.2))) a
  have hAD_mid_raw := opFamilyDistSq_mul_left_same_question_le μ DL BAC
    (fun x a b => AL x (a, b)) ψ δ hAL hDB'
  have hAD_mid : opFamilyDistSq μ FAD FMidAD ψ ≤ δ := by
    rw [opFamilyDistSq_reindex μ (swapLast α β γ)] at hAD_mid_raw
    simpa [swapLast, FAD, FMidAD] using hAD_mid_raw
  have hmid_AD_joint_raw := opFamilyDistSq_mul_left_same_question_le μ AL BAB
    (fun x a c => BAC x (a, c)) ψ δ hBAC hAB'
  have hmid_AD_joint : opFamilyDistSq μ FMidAD BJ ψ ≤ δ := by
    have hcross (x : X) (abc : (α × β) × γ) :
        BAC x (abc.1.1, abc.2) * AL x abc.1 =
          AL x abc.1 * BAC x (abc.1.1, abc.2) :=
      (left_right_commute _ _).symm
    have hcollapse (x : X) (abc : (α × β) × γ) :
        BAC x (abc.1.1, abc.2) * BAB x abc.1 = BJ x abc := by
      change rightTensor (ι₁ := ιA)
            (((B x).postprocess (fun z => (z.1.1, z.2))).effect
              (abc.1.1, abc.2)) *
          rightTensor (ι₁ := ιA)
            (((B x).postprocess (fun z => z.1)).effect abc.1) =
        rightTensor (ι₁ := ιA) ((B x).effect abc)
      rw [rightTensor_mul_rightTensor]
      exact congrArg (rightTensor (ι₁ := ιA))
        (joint_marginal_product_rev (B x) (hB x)
          abc.1.1 abc.1.2 abc.2)
    simpa only [FMidAD, hcross, hcollapse] using hmid_AD_joint_raw
  have hAD_joint : opFamilyDistSq μ FAD BJ ψ ≤ 4 * δ := by
    have h := opFamilyDistSq_le_of_le_of_le μ FAD FMidAD BJ ψ δ δ
      hAD_mid hmid_AD_joint
    linarith
  have hDA_mid_raw := opFamilyDistSq_mul_left_same_question_le μ AL BAB
    (fun x a c => DL x (a, c)) ψ δ hDL hAB'
  have hDA_mid : opFamilyDistSq μ FDA FMidDA ψ ≤ δ := by
    simpa [FDA, FMidDA] using hDA_mid_raw
  have hmid_DA_joint_raw :
      opFamilyDistSq μ
        (fun x (acb : (α × γ) × β) => BAB x (acb.1.1, acb.2) * DL x acb.1)
        (fun x (acb : (α × γ) × β) => BAB x (acb.1.1, acb.2) * BAC x acb.1)
        ψ ≤ δ :=
    opFamilyDistSq_mul_left_same_question_le μ DL BAC
      (fun x a b => BAB x (a, b)) ψ δ hBAB hDB'
  have hmid_DA_joint : opFamilyDistSq μ FMidDA BJ ψ ≤ δ := by
    have hcross (x : X) (abc : (α × β) × γ) :
        BAB x abc.1 * DL x (abc.1.1, abc.2) =
          DL x (abc.1.1, abc.2) * BAB x abc.1 :=
      (left_right_commute _ _).symm
    have hcollapse (x : X) (abc : (α × β) × γ) :
        BAB x abc.1 * BAC x (abc.1.1, abc.2) = BJ x abc := by
      change rightTensor (ι₁ := ιA)
            (((B x).postprocess (fun z => z.1)).effect abc.1) *
          rightTensor (ι₁ := ιA)
            (((B x).postprocess (fun z => (z.1.1, z.2))).effect
              (abc.1.1, abc.2)) =
        rightTensor (ι₁ := ιA) ((B x).effect abc)
      rw [rightTensor_mul_rightTensor]
      exact congrArg (rightTensor (ι₁ := ιA))
        (joint_marginal_product (B x) (hB x)
          abc.1.1 abc.1.2 abc.2)
    have hreindexed : opFamilyDistSq μ
        (fun x (abc : (α × β) × γ) =>
          BAB x abc.1 * DL x (abc.1.1, abc.2))
        (fun x (abc : (α × β) × γ) =>
          BAB x abc.1 * BAC x (abc.1.1, abc.2)) ψ ≤ δ := by
      calc
        opFamilyDistSq μ
            (fun x (abc : (α × β) × γ) =>
              BAB x abc.1 * DL x (abc.1.1, abc.2))
            (fun x (abc : (α × β) × γ) =>
              BAB x abc.1 * BAC x (abc.1.1, abc.2)) ψ =
          opFamilyDistSq μ
            (fun x (acb : (α × γ) × β) =>
              BAB x (acb.1.1, acb.2) * DL x acb.1)
            (fun x (acb : (α × γ) × β) =>
              BAB x (acb.1.1, acb.2) * BAC x acb.1) ψ := by
            simpa only [swapLast_symm_apply] using
              (opFamilyDistSq_reindex μ (swapLast α β γ)
                (fun x (acb : (α × γ) × β) =>
                  BAB x (acb.1.1, acb.2) * DL x acb.1)
                (fun x (acb : (α × γ) × β) =>
                  BAB x (acb.1.1, acb.2) * BAC x acb.1) ψ).symm
        _ ≤ δ := hmid_DA_joint_raw
    calc
      opFamilyDistSq μ FMidDA BJ ψ = opFamilyDistSq μ
          (fun x (abc : (α × β) × γ) =>
            BAB x abc.1 * DL x (abc.1.1, abc.2))
          (fun x (abc : (α × β) × γ) =>
            BAB x abc.1 * BAC x (abc.1.1, abc.2)) ψ := by
        exact (opFamilyDistSq_congr μ _ _ FMidDA BJ ψ hcross hcollapse).symm
      _ ≤ δ := hreindexed
  have hDA_joint : opFamilyDistSq μ FDA BJ ψ ≤ 4 * δ := by
    have h := opFamilyDistSq_le_of_le_of_le μ FDA FMidDA BJ ψ δ δ
      hDA_mid hmid_DA_joint
    linarith
  have hjoint_DA : opFamilyDistSq μ BJ FDA ψ ≤ 4 * δ := by
    rw [← opFamilyDistSq_symm]
    exact hDA_joint
  have hcomm := opFamilyDistSq_le_of_le_of_le μ FAD BJ FDA ψ
    (4 * δ) (4 * δ) hAD_joint hjoint_DA
  have hraw : opFamilyDistSq μ FAD FDA ψ ≤ 16 * δ := by linarith
  calc
    opFamilyDistSq μ
        (fun x (abc : (α × β) × γ) => heteroKron
          (((A x).effect abc.1 * (D x).effect (abc.1.1, abc.2)) -
            (D x).effect (abc.1.1, abc.2) * (A x).effect abc.1) 1)
        (fun _ _ => 0) ψ = opFamilyDistSq μ FAD FDA ψ := by
      apply opFamilyDistSq_congr_sub
      intro x abc
      change heteroKron
          ((A x).effect abc.1 * (D x).effect (abc.1.1, abc.2) -
            (D x).effect (abc.1.1, abc.2) * (A x).effect abc.1) 1 - 0 =
        leftTensor (ι₂ := ιB) ((A x).effect abc.1) *
            leftTensor (ι₂ := ιB) ((D x).effect (abc.1.1, abc.2)) -
          leftTensor (ι₂ := ιB) ((D x).effect (abc.1.1, abc.2)) *
            leftTensor (ι₂ := ιB) ((A x).effect abc.1)
      rw [leftTensor_mul_leftTensor, leftTensor_mul_leftTensor, sub_zero]
      exact (leftTensor_sub _ _).symm
    _ ≤ 16 * δ := hraw

/-- Strategies on identified local spaces and the same transported state have
close values. The asymptotic constant is universal for the game. This is
`lem:close-strategies-have-close-values`, blueprint
`ch12_qpbt_games.tex:474-482`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:531-540`. -/
theorem abs_value_sub_le_of_areClose :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ (G : Game) (S S' : Strategy G) (δ : ℝ)
      (_hδ0 : 0 ≤ δ) (_hδ1 : δ ≤ 1) (hclose : AreCloseStrategies G S S' δ),
      reindexState (Equiv.prodCongr (Equiv.cast hclose.hA).symm
        (Equiv.cast hclose.hB).symm) S'.ψ = S.ψ →
      (S.IsProjective ∨ S'.IsProjective) →
      |S.value - S'.value| ≤ C₀ * Real.rpow δ (1 / 2 : ℝ) := by
  sorry

/-- Averaging contractions preserves state-dependent operator closeness.
This is `lem:avg-closeness`, blueprint
`blueprint/src/chapter/ch14_qpbt_observables.tex:299-319`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:100-113`.
The probability hypothesis is explicit because the proof uses Jensen's
inequality for the average. -/
theorem avg_closeness {X ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (hμ : μ.IsProbability) (A B : X → Op ι)
    (α : X → ℂ) (hα : ∀ x, ‖α x‖ ≤ 1) (ψ : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState
        (averageOperatorOverDistribution μ fun x =>
          α x • (A x - B x)) ψ‖ ^ 2 ≤
      opDistSq μ A B ψ := by
  let v : X → EuclideanSpace ℂ ι :=
    fun x => applyOperatorToState (A x - B x) ψ
  have happly :
      applyOperatorToState
          (averageOperatorOverDistribution μ fun x => α x • (A x - B x)) ψ =
        ∑ x ∈ μ.support, μ.weight x • (α x • v x) := by
    unfold averageOperatorOverDistribution applyOperatorToState
    rw [map_sum]
    simp only [LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro x _
    rw [← smul_assoc, map_smul]
    simp only [v, applyOperatorToState, Complex.real_smul, map_sub,
      LinearMap.smul_apply, LinearMap.sub_apply]
    rw [← smul_assoc, Complex.real_smul]
  have hnorm :
      ‖∑ x ∈ μ.support, μ.weight x • (α x • v x)‖ ≤
        ∑ x ∈ μ.support, μ.weight x * ‖v x‖ := by
    calc
      ‖∑ x ∈ μ.support, μ.weight x • (α x • v x)‖ ≤
          ∑ x ∈ μ.support, ‖μ.weight x • (α x • v x)‖ :=
        norm_sum_le μ.support _
      _ ≤ ∑ x ∈ μ.support, μ.weight x * ‖v x‖ := by
        apply Finset.sum_le_sum
        intro x _
        rw [norm_smul_of_nonneg (μ.nonnegative x), norm_smul]
        exact mul_le_mul_of_nonneg_left
          (by simpa only [one_mul] using
            mul_le_of_le_one_left (norm_nonneg (v x)) (hα x))
          (μ.nonnegative x)
  have hrhs_nonneg :
      0 ≤ ∑ x ∈ μ.support, μ.weight x * ‖v x‖ ^ 2 :=
    Finset.sum_nonneg fun x _ => mul_nonneg (μ.nonnegative x) (sq_nonneg _)
  have havg_norm :
      |avgOver μ (fun x => ‖v x‖)| ≤
        Real.sqrt (avgOver μ (fun x => ‖v x‖ ^ 2)) := by
    exact MIPStarRE.LDT.Preliminaries.avgOver_abs_le_sqrt_of_pointwise μ
      (fun x => ‖v x‖) (fun x => ‖v x‖ ^ 2)
      (fun x => by rw [abs_norm, Real.sqrt_sq_eq_abs, abs_norm])
      (fun x => sq_nonneg ‖v x‖) (by rw [hμ.weight_sum_eq_one])
  have hnorm_sqrt :
      ‖∑ x ∈ μ.support, μ.weight x • (α x • v x)‖ ≤
        Real.sqrt (∑ x ∈ μ.support, μ.weight x * ‖v x‖ ^ 2) := by
    calc
      ‖∑ x ∈ μ.support, μ.weight x • (α x • v x)‖ ≤
          ∑ x ∈ μ.support, μ.weight x * ‖v x‖ := hnorm
      _ ≤ |avgOver μ (fun x => ‖v x‖)| := le_abs_self _
      _ ≤ Real.sqrt (avgOver μ (fun x => ‖v x‖ ^ 2)) := havg_norm
  rw [happly]
  unfold opDistSq opFamilyDistSq avgOver
  simp only [Fintype.sum_unique]
  change ‖∑ x ∈ μ.support, μ.weight x • (α x • v x)‖ ^ 2 ≤
    ∑ x ∈ μ.support, μ.weight x * ‖v x‖ ^ 2
  calc
    ‖∑ x ∈ μ.support, μ.weight x • (α x • v x)‖ ^ 2 ≤
        (Real.sqrt (∑ x ∈ μ.support, μ.weight x * ‖v x‖ ^ 2)) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).2 hnorm_sqrt
    _ = ∑ x ∈ μ.support, μ.weight x * ‖v x‖ ^ 2 :=
      Real.sq_sqrt hrhs_nonneg

/-- Passing from answer-indexed effects to unit-modulus weighted observables
costs at most the answer-alphabet cardinality. This is `lem:povm-to-obs`,
blueprint `blueprint/src/chapter/ch14_qpbt_observables.tex:321-354`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:115-129`. -/
theorem povm_to_obs {X α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype α]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B : X → α → Op ι)
    (c : α → ℂ) (hc : ∀ a, ‖c a‖ = 1) (ψ : EuclideanSpace ℂ ι) :
    opDistSq μ (fun x => ∑ a, c a • A x a) (fun x => ∑ a, c a • B x a) ψ ≤
      Fintype.card α * opFamilyDistSq μ A B ψ := by
  have hpoint : ∀ x,
      ‖applyOperatorToState
          ((∑ a, c a • A x a) - ∑ a, c a • B x a) ψ‖ ^ 2 ≤
        (Fintype.card α : ℝ) *
          ∑ a, ‖applyOperatorToState (A x a - B x a) ψ‖ ^ 2 := by
    intro x
    have hrewrite :
        applyOperatorToState
            ((∑ a, c a • A x a) - ∑ a, c a • B x a) ψ =
          ∑ a, c a • applyOperatorToState (A x a - B x a) ψ := by
      simp [applyOperatorToState, ← Finset.sum_sub_distrib, ← smul_sub]
    rw [hrewrite]
    have hnorm :
        ‖∑ a, c a • applyOperatorToState (A x a - B x a) ψ‖ ≤
          ∑ a, ‖applyOperatorToState (A x a - B x a) ψ‖ := by
      calc
        ‖∑ a, c a • applyOperatorToState (A x a - B x a) ψ‖ ≤
            ∑ a, ‖c a • applyOperatorToState (A x a - B x a) ψ‖ :=
          norm_sum_le Finset.univ _
        _ = ∑ a, ‖applyOperatorToState (A x a - B x a) ψ‖ := by
          apply Finset.sum_congr rfl
          intro a _
          simp [norm_smul, hc a]
    calc
      ‖∑ a, c a • applyOperatorToState (A x a - B x a) ψ‖ ^ 2 ≤
          (∑ a, ‖applyOperatorToState (A x a - B x a) ψ‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)).2 hnorm
      _ ≤ (Fintype.card α : ℝ) *
          ∑ a, ‖applyOperatorToState (A x a - B x a) ψ‖ ^ 2 := by
        simpa using (sq_sum_le_card_mul_sum_sq
          (s := Finset.univ)
          (f := fun a : α => ‖applyOperatorToState (A x a - B x a) ψ‖))
  unfold opDistSq opFamilyDistSq
  simp only [Fintype.sum_unique]
  calc
    avgOver μ (fun x =>
        ‖applyOperatorToState
          ((∑ a, c a • A x a) - ∑ a, c a • B x a) ψ‖ ^ 2) ≤
      avgOver μ (fun x =>
        (Fintype.card α : ℝ) *
          ∑ a, ‖applyOperatorToState (A x a - B x a) ψ‖ ^ 2) :=
      avgOver_mono μ _ _ hpoint
    _ = (Fintype.card α : ℝ) * avgOver μ (fun x =>
        ∑ a, ‖applyOperatorToState (A x a - B x a) ψ‖ ^ 2) :=
      avgOver_const_mul _ _ _

/-- Orthonormalization of a consistent pair of POVMs. The resulting
Alice-side measurement is projective and remains close to the original one on
the unit bipartite state. This imported result is `lem:ortho`, blueprint
`blueprint/src/chapter/ch14_qpbt_observables.tex:356-383`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:131-153`;
the source cites KV11 and the self-contained proof [ML20]. -/
theorem exists_projective_close_of_consistent :
    ∃ η : ℝ → ℝ,
      (∃ C : ℝ, 1 ≤ C ∧ ∀ δ : ℝ, 0 ≤ δ →
        η δ ≤ C * Real.rpow δ (1 / 4 : ℝ)) ∧
      ∀ (ιA ιB α : Type) [Fintype ιA] [DecidableEq ιA]
        [Fintype ιB] [DecidableEq ιB] [Fintype α] [DecidableEq α]
        (ψ : EuclideanSpace ℂ (ιA × ιB)) (hψ : ‖ψ‖ = 1)
        (Q : Measurement α ιA)
        (R : Measurement α ιB) (δ : ℝ),
        0 ≤ δ ∧ δ ≤ 1 →
        consistencyDefect (uniformDistribution Unit)
          (fun _ a => heteroKron (Q.effect a) 1)
          (fun _ a => heteroKron 1 (R.effect a)) ψ ≤ δ →
        ∃ Pm : Measurement α ιA,
          MIPStarRE.QPBT.Measurement.IsProjective Pm ∧
          opFamilyDistSq (uniformDistribution Unit)
            (fun _ a => heteroKron (Pm.effect a) 1)
            (fun _ a => heteroKron (Q.effect a) 1) ψ ≤ η δ := by
  sorry

end MIPStarRE.QPBT
