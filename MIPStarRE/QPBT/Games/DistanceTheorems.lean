import MIPStarRE.QPBT.Games.Consistency
import MIPStarRE.QPBT.Games.StrategyClasses

/-! # State-dependent distance calculus

This module records the consistency and state-dependent distance estimates used
throughout the quantum Pauli basis test. The statements retain explicit
constants that the paper absorbs into asymptotic notation.

## References

The source results are `fact:agreement` through
`lem:close-strategies-have-close-values` in
`blueprint/src/chapter/ch12_qpbt_games.tex:245-482`, with paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-423` and
`:531-540`.
-/

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

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
  sorry

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
  sorry

/-- Projectivity on one side gives the square-root consistency estimate for a
unit state under a probability distribution. This is the third item of
`fact:agreement`; blueprint `ch12_qpbt_games.tex:245-255`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-311`. -/
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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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

end MIPStarRE.QPBT
