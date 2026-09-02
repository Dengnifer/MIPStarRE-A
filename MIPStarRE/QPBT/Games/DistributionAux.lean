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
used by the sandwich construction; blueprint `ch12_qpbt_games.tex:398-425`,
paper `06_nonlocal_games_and_mipstar.tex:465-501`. -/
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
distribution; blueprint `ch12_qpbt_games.tex:398-425`, paper
`06_nonlocal_games_and_mipstar.tex:465-501`. -/
theorem Distribution.prod_isProbability {α β : Type*}
    [DecidableEq α] [DecidableEq β] (μ : Distribution α) (ν : Distribution β)
    (hμ : μ.IsProbability) (hν : ν.IsProbability) :
    (Distribution.prod μ ν).IsProbability := by
  sorry

/-- The convex mixture with a coefficient in `[0,1]`, as used for
the equal mixture in `def:line-point-dist`, blueprint
`ch13_qpbt_test.tex:85-95`, paper
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
`def:line-point-dist`, blueprint `ch13_qpbt_test.tex:85-95`, paper
`08_classical_and_quantum_low_degree_tests.tex:274-287`. -/
theorem Distribution.mix_isProbability {α : Type*} [DecidableEq α]
    (t : ℝ) (μ ν : Distribution α) (hμ : μ.IsProbability)
    (hν : ν.IsProbability) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (Distribution.mix t ht0 ht1 μ ν).IsProbability := by
  sorry

/-- The dependent bind of finite distributions used for typed question
distributions, blueprint `ch12_qpbt_games.tex:624-629`, paper
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
blueprint
`ch12_qpbt_games.tex:624-629`, paper `07_types.tex:84-94`. -/
theorem Distribution.bind_isProbability {α β : Type*} [DecidableEq β]
    (μ : Distribution α) (ν : α → Distribution β) (hμ : μ.IsProbability)
    (hν : ∀ a ∈ μ.support, (ν a).IsProbability) :
    (Distribution.bind μ ν).IsProbability := by
  sorry

/-- Restrict a distribution to a decidable positive-mass event and normalize it,
as in `def:ith-restricted-line`; blueprint
`ch15_qpbt_combining.tex:578-592`, paper
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
`def:ith-restricted-line`, blueprint
`ch15_qpbt_combining.tex:578-592`, paper
`14_analysis_of_the_pauli_basis_test.tex:1038-1048`. -/
theorem Distribution.restrict_isProbability {α : Type*} [DecidableEq α]
    (μ : Distribution α) (p : α → Prop) [DecidablePred p]
    (hpos : 0 < ∑ a ∈ μ.support.filter p, μ.weight a) :
    (Distribution.restrict μ p hpos).IsProbability := by
  sorry

end MIPStarRE.QPBT
