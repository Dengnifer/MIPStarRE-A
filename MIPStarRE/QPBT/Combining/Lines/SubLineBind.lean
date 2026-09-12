import MIPStarRE.QPBT.Combining.Lines.SubLinePrefix

/-!
# Rewriting rules for dependent mixtures of finite distributions

This module records the elementary rewriting rules for the dependent mixture
of finite distributions that the sampling procedure of the sub-line lemma
uses: a mixture indexed along a push-forward is the mixture indexed along the
original law, iterated mixtures associate, a mixture is unchanged when the
mixed family is changed only outside the index support, a mixture of a
constant family is that constant, a product with a fixed independent factor
distributes over a mixture, and an equal two-term mixture is the mixture
indexed by a uniform pair of labels.

## References

The rewriting rules support `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The mixture, product and equal-mixture operations are those of
blueprint `def:line-point-dist`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-! ## Reindexing a dependent mixture -/

/-- Mixing along a push-forward index is mixing along the original index.
Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem Distribution.bind_map_left {α β γ : Type*} [DecidableEq β]
    [DecidableEq γ] (μ : Distribution α) (f : α → β) (ν : β → Distribution γ) :
    Distribution.bind (μ.map f) ν =
      Distribution.bind μ (fun a => ν (f a)) := by
  classical
  refine Distribution.ext_of_support_of_weight ?_ ?_
  · change (μ.support.image f).biUnion (fun b => (ν b).support) =
      μ.support.biUnion (fun a => (ν (f a)).support)
    ext c
    simp only [Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨b, ⟨a, ha, rfl⟩, hc⟩
      exact ⟨a, ha, hc⟩
    · rintro ⟨a, ha, hc⟩
      exact ⟨f a, ⟨a, ha, rfl⟩, hc⟩
  · funext c
    change (∑ b ∈ μ.support.image f, (μ.map f).weight b * (ν b).weight c) =
      ∑ a ∈ μ.support, μ.weight a * (ν (f a)).weight c
    rw [← Finset.sum_fiberwise_of_maps_to
      (s := μ.support) (t := μ.support.image f) (g := f)
      (fun a ha => Finset.mem_image_of_mem f ha)
      (fun a => μ.weight a * (ν (f a)).weight c)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Distribution.map_weight, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [(Finset.mem_filter.mp ha).2]

/-- A dependent mixture depends on the mixed family only on the index
support.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem Distribution.bind_congr_support {α β : Type*} [DecidableEq β]
    (μ : Distribution α) (ν ν' : α → Distribution β)
    (h : ∀ a ∈ μ.support, ν a = ν' a) :
    Distribution.bind μ ν = Distribution.bind μ ν' := by
  refine Distribution.ext_of_support_of_weight ?_ ?_
  · change μ.support.biUnion (fun a => (ν a).support) =
      μ.support.biUnion (fun a => (ν' a).support)
    exact Finset.biUnion_congr rfl fun a ha => by rw [h a ha]
  · funext b
    exact Finset.sum_congr rfl fun a ha => by rw [h a ha]

/-- A dependent mixture of a constant family is that constant law.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem Distribution.bind_const {α β : Type*} [DecidableEq β]
    (μ : Distribution α) (hμ : μ.IsProbability) (ν : Distribution β) :
    Distribution.bind μ (fun _ => ν) = ν := by
  have hne : μ.support.Nonempty := by
    rw [← Finset.card_pos]
    by_contra hcard
    have hempty : μ.support = ∅ := by
      rw [← Finset.card_eq_zero]
      omega
    have h1 := hμ.weight_sum_eq_one
    rw [hempty] at h1
    simp at h1
  refine Distribution.ext_of_support_of_weight ?_ ?_
  · change μ.support.biUnion (fun _ => ν.support) = ν.support
    ext b
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨a, -, hb⟩
      exact hb
    · intro hb
      obtain ⟨a, ha⟩ := hne
      exact ⟨a, ha, hb⟩
  · funext b
    change (∑ a ∈ μ.support, μ.weight a * ν.weight b) = ν.weight b
    rw [← Finset.sum_mul, hμ.weight_sum_eq_one, one_mul]

/-! ## Associativity of dependent mixtures -/

/-- Iterated dependent mixtures associate.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem Distribution.bind_bind {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (μ : Distribution α) (ν : α → Distribution β) (ρ : β → Distribution γ) :
    Distribution.bind (Distribution.bind μ ν) ρ =
      Distribution.bind μ (fun a => Distribution.bind (ν a) ρ) := by
  classical
  refine Distribution.ext_of_support_of_weight ?_ ?_
  · change (μ.support.biUnion (fun a => (ν a).support)).biUnion
        (fun b => (ρ b).support) =
      μ.support.biUnion (fun a => (ν a).support.biUnion (fun b => (ρ b).support))
    ext c
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨b, ⟨a, ha, hb⟩, hc⟩
      exact ⟨a, ha, b, hb, hc⟩
    · rintro ⟨a, ha, b, hb, hc⟩
      exact ⟨b, ⟨a, ha, hb⟩, hc⟩
  · funext c
    change (∑ b ∈ μ.support.biUnion (fun a => (ν a).support),
        (∑ a ∈ μ.support, μ.weight a * (ν a).weight b) * (ρ b).weight c) =
      ∑ a ∈ μ.support, μ.weight a *
        ∑ b ∈ (ν a).support, (ν a).weight b * (ρ b).weight c
    rw [Finset.sum_congr rfl fun b _ =>
      Finset.sum_mul μ.support (fun a => μ.weight a * (ν a).weight b)
        ((ρ b).weight c), Finset.sum_comm]
    refine Finset.sum_congr rfl fun a ha => ?_
    have hsub : (ν a).support ⊆ μ.support.biUnion (fun a => (ν a).support) :=
      fun b hb => Finset.mem_biUnion.mpr ⟨a, ha, hb⟩
    have hzero : ∀ b ∈ μ.support.biUnion (fun a => (ν a).support),
        b ∉ (ν a).support →
        μ.weight a * ((ν a).weight b * (ρ b).weight c) = 0 := by
      intro b _ hbnot
      rw [(ν a).outsideSupport b hbnot, zero_mul, mul_zero]
    rw [Finset.mul_sum, Finset.sum_subset hsub hzero]
    exact Finset.sum_congr rfl fun b _ => mul_assoc _ _ _

/-! ## Products with an independent factor -/

/-- A product with a fixed independent second factor distributes over a
dependent mixture of the first factor.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem Distribution.prod_bind_left {α β γ : Type*} [DecidableEq β]
    [DecidableEq γ] (μ : Distribution α) (ν : α → Distribution β)
    (ρ : Distribution γ) :
    Distribution.prod (Distribution.bind μ ν) ρ =
      Distribution.bind μ (fun a => Distribution.prod (ν a) ρ) := by
  classical
  refine Distribution.ext_of_support_of_weight ?_ ?_
  · change (μ.support.biUnion (fun a => (ν a).support)) ×ˢ ρ.support =
      μ.support.biUnion (fun a => (ν a).support ×ˢ ρ.support)
    ext w
    simp only [Finset.mem_product, Finset.mem_biUnion]
    constructor
    · rintro ⟨⟨a, ha, hb⟩, hc⟩
      exact ⟨a, ha, hb, hc⟩
    · rintro ⟨a, ha, hb, hc⟩
      exact ⟨⟨a, ha, hb⟩, hc⟩
  · funext w
    change (∑ a ∈ μ.support, μ.weight a * (ν a).weight w.1) * ρ.weight w.2 =
      ∑ a ∈ μ.support, μ.weight a * ((ν a).weight w.1 * ρ.weight w.2)
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => mul_assoc _ _ _

/-! ## The equal two-term mixture as a uniform dependent mixture -/

/-- The equal mixture of two laws is the dependent mixture indexed by a
uniform pair of labels.  Blueprint `def:line-point-dist`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:274-287`.
-/
theorem Distribution.bind_uniform_fin_two {α : Type*} [DecidableEq α]
    (μ ν : Distribution α) :
    Distribution.bind (uniformDistribution (Fin 2)) ![μ, ν] =
      Distribution.mix (1 / 2) (by norm_num) (by norm_num) μ ν := by
  classical
  refine Distribution.ext_of_support_of_weight ?_ ?_
  · change (Finset.univ : Finset (Fin 2)).biUnion
        (fun i => (![μ, ν] i).support) = μ.support ∪ ν.support
    ext a
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr hi
    · rintro (h | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
  · funext a
    change (∑ i ∈ (Finset.univ : Finset (Fin 2)),
        (uniformDistribution (Fin 2)).weight i * (![μ, ν] i).weight a) =
      1 / 2 * μ.weight a + (1 - 1 / 2) * ν.weight a
    rw [Fin.sum_univ_two, uniformDistribution_weight_apply,
      uniformDistribution_weight_apply, Fintype.card_fin]
    norm_num

end

end MIPStarRE.QPBT
