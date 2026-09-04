import MIPStarRE.LDT.Basic.Distribution

/-! # Operations on finite distributions

Products, convex mixtures, dependent binds, and normalized restrictions used by
the QPBT distributions. Their source uses occur in the line-point sampler,
typed conditionally linear distributions, sandwich products, and restricted
line distributions cited below.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

/-- The product of two finite distributions, a formalization-only auxiliary
used by blueprint `lem:ld-sandwich`; paper
`06_nonlocal_games_and_mipstar.tex:465-501`. -/
noncomputable def Distribution.prod {α β : Type*} [DecidableEq α] [DecidableEq β]
    (μ : Distribution α) (ν : Distribution β) : Distribution (α × β) where
  support := μ.support.product ν.support
  weight p := μ.weight p.1 * ν.weight p.2
  nonnegative p := mul_nonneg (μ.nonnegative p.1) (ν.nonnegative p.2)
  outsideSupport p hp := by
    by_cases hμ : p.1 ∈ μ.support
    · have hν : p.2 ∉ ν.support := by
        intro h
        exact hp (Finset.mem_product.mpr ⟨hμ, h⟩)
      simp [ν.outsideSupport p.2 hν]
    · simp [μ.outsideSupport p.1 hμ]

/-- The product of two probability distributions is a probability
distribution used by blueprint `lem:ld-sandwich`; paper
`06_nonlocal_games_and_mipstar.tex:465-501`. -/
theorem Distribution.prod_isProbability {α β : Type*}
    [DecidableEq α] [DecidableEq β] (μ : Distribution α) (ν : Distribution β)
    (hμ : μ.IsProbability) (hν : ν.IsProbability) :
    (Distribution.prod μ ν).IsProbability := by
  simp only [Distribution.IsProbability, Distribution.totalWeight,
    Distribution.prod]
  calc
    (∑ p ∈ μ.support.product ν.support, μ.weight p.1 * ν.weight p.2) =
        ∑ a ∈ μ.support, ∑ b ∈ ν.support, μ.weight a * ν.weight b := by
      exact Finset.sum_product' μ.support ν.support
        (fun a b => μ.weight a * ν.weight b)
    _ =
        ∑ a ∈ μ.support, μ.weight a * ∑ b ∈ ν.support, ν.weight b := by
      apply Finset.sum_congr rfl
      intro a _
      exact (Finset.mul_sum ν.support (fun b => ν.weight b) (μ.weight a)).symm
    _ = ∑ a ∈ μ.support, μ.weight a := by
      rw [hν.weight_sum_eq_one]
      simp
    _ = 1 := hμ.weight_sum_eq_one

/-- The convex mixture with a coefficient in `[0,1]`, as used for
the equal mixture in blueprint
`def:line-point-dist`, paper
`08_classical_and_quantum_low_degree_tests.tex:274-287`. -/
noncomputable def Distribution.mix {α : Type*} [DecidableEq α]
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (μ ν : Distribution α) : Distribution α where
  support := μ.support ∪ ν.support
  weight a := t * μ.weight a + (1 - t) * ν.weight a
  nonnegative a := by
    exact add_nonneg
      (mul_nonneg ht0 (μ.nonnegative a))
      (mul_nonneg (sub_nonneg.mpr ht1) (ν.nonnegative a))
  outsideSupport a ha := by
    have hμ : a ∉ μ.support := fun h => ha (Finset.mem_union_left _ h)
    have hν : a ∉ ν.support := fun h => ha (Finset.mem_union_right _ h)
    simp [μ.outsideSupport a hμ, ν.outsideSupport a hν]

/-- A convex mixture of probability distributions is a probability distribution;
blueprint `def:line-point-dist`, paper
`08_classical_and_quantum_low_degree_tests.tex:274-287`. -/
theorem Distribution.mix_isProbability {α : Type*} [DecidableEq α]
    (t : ℝ) (μ ν : Distribution α) (hμ : μ.IsProbability)
    (hν : ν.IsProbability) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (Distribution.mix t ht0 ht1 μ ν).IsProbability := by
  have hμ_union :
      ∑ a ∈ μ.support ∪ ν.support, μ.weight a = 1 := by
    apply hμ.weight_sum_eq_one_of_subset
    intro a ha
    exact Finset.mem_union_left ν.support ha
  have hν_union :
      ∑ a ∈ μ.support ∪ ν.support, ν.weight a = 1 := by
    apply hν.weight_sum_eq_one_of_subset
    intro a ha
    exact Finset.mem_union_right μ.support ha
  simp only [Distribution.IsProbability, Distribution.totalWeight,
    Distribution.mix]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    hμ_union, hν_union]
  ring

/-- The dependent bind of finite distributions used for typed question
distributions in blueprint `def:typed-cl-distributions`; paper
`07_types.tex:84-94`. -/
noncomputable def Distribution.bind {α β : Type*} [DecidableEq β]
    (μ : Distribution α) (ν : α → Distribution β) : Distribution β where
  support := μ.support.biUnion (fun a => (ν a).support)
  weight b := ∑ a ∈ μ.support, μ.weight a * (ν a).weight b
  nonnegative b := Finset.sum_nonneg fun a _ => mul_nonneg (μ.nonnegative a) ((ν a).nonnegative b)
  outsideSupport b hb := by
    apply Finset.sum_eq_zero
    intro a ha
    have hnot : b ∉ (ν a).support := by
      intro h
      exact hb (Finset.mem_biUnion.mpr ⟨a, ha, h⟩)
    simp [ν a |>.outsideSupport b hnot]

/-- A dependent bind of probability distributions is a probability distribution;
it supports blueprint `def:typed-cl-distributions`, paper `07_types.tex:84-94`. -/
theorem Distribution.bind_isProbability {α β : Type*} [DecidableEq β]
    (μ : Distribution α) (ν : α → Distribution β) (hμ : μ.IsProbability)
    (hν : ∀ a ∈ μ.support, (ν a).IsProbability) :
    (Distribution.bind μ ν).IsProbability := by
  classical
  have hν_union (a : α) (ha : a ∈ μ.support) :
      ∑ b ∈ μ.support.biUnion (fun a => (ν a).support), (ν a).weight b = 1 := by
    apply (hν a ha).weight_sum_eq_one_of_subset
    intro b hb
    exact Finset.mem_biUnion.mpr ⟨a, ha, hb⟩
  simp only [Distribution.IsProbability, Distribution.totalWeight,
    Distribution.bind]
  rw [Finset.sum_comm]
  calc
    (∑ a ∈ μ.support,
        ∑ b ∈ μ.support.biUnion (fun a => (ν a).support),
          μ.weight a * (ν a).weight b) =
        ∑ a ∈ μ.support,
          μ.weight a *
            ∑ b ∈ μ.support.biUnion (fun a => (ν a).support),
              (ν a).weight b := by
      apply Finset.sum_congr rfl
      intro a _
      exact (Finset.mul_sum _ (fun b => (ν a).weight b) (μ.weight a)).symm
    _ = ∑ a ∈ μ.support, μ.weight a := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hν_union a ha]
      simp
    _ = 1 := hμ.weight_sum_eq_one

/-- Restrict a distribution to a decidable positive-mass event and normalize it,
as in blueprint
`def:ith-restricted-line`, paper
`14_analysis_of_the_pauli_basis_test.tex:1038-1048`. -/
noncomputable def Distribution.restrict {α : Type*} [DecidableEq α]
    (μ : Distribution α) (p : α → Prop) [DecidablePred p]
    (hpos : 0 < ∑ a ∈ μ.support.filter p, μ.weight a) : Distribution α where
  support := μ.support.filter p
  weight a := if p a then μ.weight a / ∑ b ∈ μ.support.filter p, μ.weight b else 0
  nonnegative a := by
    split
    · exact div_nonneg (μ.nonnegative a) (le_of_lt hpos)
    · exact le_rfl
  outsideSupport a ha := by
    by_cases hp : p a
    · have hμ : a ∉ μ.support := fun h => ha (Finset.mem_filter.mpr ⟨h, hp⟩)
      simp [hp, μ.outsideSupport a hμ]
    · simp [hp]

/-- Restriction to a positive-mass event preserves total probability;
blueprint
`def:ith-restricted-line`, paper
`14_analysis_of_the_pauli_basis_test.tex:1038-1048`. -/
theorem Distribution.restrict_isProbability {α : Type*} [DecidableEq α]
    (μ : Distribution α) (p : α → Prop) [DecidablePred p]
    (hpos : 0 < ∑ a ∈ μ.support.filter p, μ.weight a) :
    (Distribution.restrict μ p hpos).IsProbability := by
  simp only [Distribution.IsProbability, Distribution.totalWeight,
    Distribution.restrict]
  calc
    (∑ a ∈ μ.support.filter p,
        if p a then μ.weight a / ∑ b ∈ μ.support.filter p, μ.weight b else 0) =
        ∑ a ∈ μ.support.filter p,
          μ.weight a / ∑ b ∈ μ.support.filter p, μ.weight b := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [if_pos (Finset.mem_filter.mp ha).2]
    _ = (∑ a ∈ μ.support.filter p, μ.weight a) /
        ∑ b ∈ μ.support.filter p, μ.weight b := by
      rw [Finset.sum_div]
    _ = 1 := div_self hpos.ne'

end MIPStarRE.QPBT
