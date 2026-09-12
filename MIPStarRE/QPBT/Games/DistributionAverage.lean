import MIPStarRE.LDT.Basic.DistributionAvg
import MIPStarRE.QPBT.Games.DistributionAux

/-!
# Averages of products and mixtures of finite distributions

Averages over products and dependent mixtures are iterated averages.
Convex mixtures act linearly on averages, and a nonnegative uniform mixture
bounds each of its components after scaling by the component's weight.

## References

These formalization-only identities support blueprint `lem:qld-sublines` and
`lem:restricted-line-mixture-bounds`, using the operations of
`Games/DistributionAux.lean`. The sampling argument is in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1038-1116`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-! ## Averages of the distribution operations -/

/-- Formalization-only auxiliary: an average against a dependent bind is the
iterated average.  Blueprint `lem:restricted-line-mixture-bounds`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1052-1058`. -/
theorem avgOver_bind {α β : Type*} [DecidableEq β]
    (μ : Distribution α) (ν : α → Distribution β) (f : β → ℝ) :
    avgOver (Distribution.bind μ ν) f =
      avgOver μ (fun a => avgOver (ν a) f) := by
  classical
  unfold avgOver
  have h1 : ∀ b : β, (∑ a ∈ μ.support, μ.weight a * (ν a).weight b) * f b =
      ∑ a ∈ μ.support, μ.weight a * ((ν a).weight b * f b) := by
    intro b
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by ring
  change (∑ b ∈ μ.support.biUnion (fun a => (ν a).support),
    (∑ a ∈ μ.support, μ.weight a * (ν a).weight b) * f b) = _
  rw [Finset.sum_congr rfl fun b _ => h1 b, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [← Finset.mul_sum]
  congr 1
  refine (Finset.sum_subset ?_ ?_).symm
  · intro b hb
    exact Finset.mem_biUnion.mpr ⟨a, ha, hb⟩
  · intro b _ hb
    rw [(ν a).outsideSupport b hb, zero_mul]

/-- Formalization-only auxiliary: an average against a convex mixture is the
convex combination of the two averages.  Blueprint
`lem:restricted-line-mixture-bounds`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1052-1058`. -/
theorem avgOver_mix {α : Type*} [DecidableEq α] (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (μ ν : Distribution α) (f : α → ℝ) :
    avgOver (Distribution.mix t ht0 ht1 μ ν) f =
      t * avgOver μ f + (1 - t) * avgOver ν f := by
  classical
  unfold avgOver
  have hsplit : (∑ a ∈ μ.support ∪ ν.support,
        (t * μ.weight a + (1 - t) * ν.weight a) * f a) =
      t * (∑ a ∈ μ.support ∪ ν.support, μ.weight a * f a) +
        (1 - t) * (∑ a ∈ μ.support ∪ ν.support, ν.weight a * f a) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  have hμ : (∑ a ∈ μ.support ∪ ν.support, μ.weight a * f a) =
      ∑ a ∈ μ.support, μ.weight a * f a := by
    refine (Finset.sum_subset Finset.subset_union_left ?_).symm
    intro a _ ha
    rw [μ.outsideSupport a ha, zero_mul]
  have hν : (∑ a ∈ μ.support ∪ ν.support, ν.weight a * f a) =
      ∑ a ∈ ν.support, ν.weight a * f a := by
    refine (Finset.sum_subset Finset.subset_union_right ?_).symm
    intro a _ ha
    rw [ν.outsideSupport a ha, zero_mul]
  change (∑ a ∈ μ.support ∪ ν.support,
    (t * μ.weight a + (1 - t) * ν.weight a) * f a) = _
  rw [hsplit, hμ, hν]

/-- Formalization-only auxiliary: an average against a product law is the
iterated average.  Blueprint `lem:restricted-line-mixture-bounds`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1056-1058`. -/
theorem avgOver_prod {α β : Type*} [DecidableEq α] [DecidableEq β]
    (μ : Distribution α) (ν : Distribution β) (f : α × β → ℝ) :
    avgOver (Distribution.prod μ ν) f =
      avgOver μ (fun a => avgOver ν (fun b => f (a, b))) := by
  classical
  unfold avgOver
  change (∑ p ∈ μ.support ×ˢ ν.support, μ.weight p.1 * ν.weight p.2 * f p) = _
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- Formalization-only auxiliary: one component of a uniform mixture carries at
most the whole nonnegative average, scaled by its mixture weight.  Blueprint
`lem:restricted-line-mixture-bounds`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1052-1056`. -/
theorem avgOver_bind_uniform_component_le {ι β : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι] [DecidableEq β]
    (ν : ι → Distribution β) (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) (i : ι) :
    1 / (Fintype.card ι : ℝ) * avgOver (ν i) f ≤
      avgOver (Distribution.bind (uniformDistribution ι) ν) f := by
  classical
  rw [avgOver_bind]
  have hterm : ∀ j ∈ (Finset.univ : Finset ι),
      0 ≤ (uniformDistribution ι).weight j * avgOver (ν j) f := fun j _ =>
    mul_nonneg ((uniformDistribution ι).nonnegative j) (avgOver_nonneg _ _ hf)
  have hsingle := Finset.single_le_sum
    (f := fun j => (uniformDistribution ι).weight j * avgOver (ν j) f)
    hterm (Finset.mem_univ i)
  rw [uniformDistribution_weight_apply] at hsingle
  exact hsingle

end

end MIPStarRE.QPBT
