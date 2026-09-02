import MIPStarRE.LDT.Basic.Distribution

/-!
# Finite distribution combinators

This file supplies weighted mixtures, independent products, and normalized
restrictions for the explicit-support `Distribution` used throughout QPBT.

## References

These are formalization-only auxiliaries for the mixtures and independent
line samples in `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:882-1019`.
-/

open scoped BigOperators

namespace MIPStarRE.LDT.Distribution

/-- Mix a finite family of distributions using another distribution as the
law of the family index. -/
noncomputable def mixture {κ α : Type*} [DecidableEq α]
    (weights : Distribution κ) (component : κ → Distribution α) : Distribution α where
  support := weights.support.biUnion fun i => (component i).support
  weight := fun a =>
    ∑ i ∈ weights.support, weights.weight i * (component i).weight a
  nonnegative := fun a => Finset.sum_nonneg fun i _ =>
    mul_nonneg (weights.nonnegative i) ((component i).nonnegative a)
  outsideSupport := fun a ha => by
    apply Finset.sum_eq_zero
    intro i hi
    have hai : a ∉ (component i).support := by
      intro hai
      exact ha (Finset.mem_biUnion.mpr ⟨i, hi, hai⟩)
    rw [(component i).outsideSupport a hai, mul_zero]

/-- The mixture of probability distributions is a probability distribution.
This named formalization-only obligation provides the mass calculation used by
the line-point sampler. -/
theorem mixture_isProbability {κ α : Type*} [DecidableEq α]
    (weights : Distribution κ) (component : κ → Distribution α)
    (hw : weights.IsProbability)
    (hc : ∀ i ∈ weights.support, (component i).IsProbability) :
    (mixture weights component).IsProbability := by
  sorry

/-- The independent product of two finite-support distributions. -/
def prod {α β : Type*} [DecidableEq α] [DecidableEq β]
    (μ : Distribution α) (ν : Distribution β) : Distribution (α × β) where
  support := μ.support ×ˢ ν.support
  weight := fun ab => μ.weight ab.1 * ν.weight ab.2
  nonnegative := fun ab => mul_nonneg (μ.nonnegative ab.1) (ν.nonnegative ab.2)
  outsideSupport := fun ab hab => by
    by_cases ha : ab.1 ∈ μ.support
    · have hb : ab.2 ∉ ν.support := by
        intro hb
        exact hab (Finset.mem_product.mpr ⟨ha, hb⟩)
      rw [ν.outsideSupport ab.2 hb, mul_zero]
    · rw [μ.outsideSupport ab.1 ha, zero_mul]

/-- Independent products preserve total probability mass. -/
theorem prod_isProbability {α β : Type*} [DecidableEq α] [DecidableEq β]
    (μ : Distribution α) (ν : Distribution β)
    (hμ : μ.IsProbability) (hν : ν.IsProbability) :
    (prod μ ν).IsProbability := by
  sorry

/-- The mass of an event inside a finite-support distribution. -/
def restrictedWeight {α : Type*} [DecidableEq α]
    (μ : Distribution α) (p : α → Prop) [DecidablePred p] : ℝ :=
  ∑ a ∈ μ.support.filter p, μ.weight a

/-- Normalize a distribution on an event of positive mass.  The positive-mass
hypothesis is part of the domain, so the definition has no zero-mass fallback. -/
noncomputable def restrict {α : Type*} [DecidableEq α]
    (μ : Distribution α) (p : α → Prop) [DecidablePred p]
    (hpos : 0 < restrictedWeight μ p) : Distribution α where
  support := μ.support.filter p
  weight := fun a => if p a then μ.weight a / restrictedWeight μ p else 0
  nonnegative := fun a => by
    split_ifs
    · exact div_nonneg (μ.nonnegative a) hpos.le
    · exact le_rfl
  outsideSupport := fun a ha => by
    by_cases hpa : p a
    · have hsa : a ∉ μ.support := by
        intro hsa
        exact ha (Finset.mem_filter.mpr ⟨hsa, hpa⟩)
      rw [if_pos hpa, μ.outsideSupport a hsa, zero_div]
    · rw [if_neg hpa]

/-- A normalized restriction has total probability mass one. -/
theorem restrict_isProbability {α : Type*} [DecidableEq α]
    (μ : Distribution α) (p : α → Prop) [DecidablePred p]
    (hpos : 0 < restrictedWeight μ p) :
    (restrict μ p hpos).IsProbability := by
  sorry

end MIPStarRE.LDT.Distribution
