import MIPStarRE.QPBT.Combining.Lines.SubLineProduct

/-!
# Reshuffling products of finitely supported laws

The sampling procedure of the sub-line lemma produces its six independent
generating blocks in one grouping, while the restricted line-point laws that
the projected marginals must match present the same six blocks in another
grouping.  This module records the rewriting rules that pass between two such
presentations: the support and the weight of a product, the fact that a
push-forward along a bijection is determined by the supports and weights it
compares, and the push-forward of the second factor of a product.

## References

The rewriting rules support `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The product operation is that of blueprint
`def:line-point-dist`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-! ## The support and the weight of a product -/

/-- The support of a product law is the product of the supports.  Blueprint
`def:line-point-dist`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:274-287`.
-/
theorem Distribution.prod_support {α β : Type*} [DecidableEq α]
    [DecidableEq β] (μ : Distribution α) (ν : Distribution β) :
    (Distribution.prod μ ν).support = μ.support ×ˢ ν.support := rfl

/-- The weight of a product law is the product of the weights.  Blueprint
`def:line-point-dist`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:274-287`.
-/
theorem Distribution.prod_weight {α β : Type*} [DecidableEq α]
    [DecidableEq β] (μ : Distribution α) (ν : Distribution β) (w : α × β) :
    (Distribution.prod μ ν).weight w = μ.weight w.1 * ν.weight w.2 := rfl

/-! ## Push-forward along a bijection -/

/-- A push-forward along a bijection is identified by the supports and the
weights it compares: if the map matches the two supports and carries each
weight to the corresponding weight, and if it has a two-sided inverse, the
push-forward is the target law.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem Distribution.map_bijective_eq {α β : Type*} [DecidableEq α]
    [DecidableEq β] (μ : Distribution α) (ν : Distribution β) (f : α → β)
    (g : β → α) (hgf : ∀ a, g (f a) = a) (hfg : ∀ b, f (g b) = b)
    (hs : ∀ a, a ∈ μ.support ↔ f a ∈ ν.support)
    (hw : ∀ a, μ.weight a = ν.weight (f a)) :
    μ.map f = ν := by
  classical
  refine Distribution.ext_of_support_of_weight ?_ ?_
  · rw [Distribution.map_support]
    ext b
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (hs a).mp ha
    · intro hb
      refine ⟨g b, (hs (g b)).mpr ?_, hfg b⟩
      rw [hfg b]
      exact hb
  · funext b
    rw [Distribution.map_weight]
    have hfilter : μ.support.filter (fun a => f a = b) =
        μ.support.filter (fun a => a = g b) := by
      ext a
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨ha, h⟩
        exact ⟨ha, by rw [← h, hgf]⟩
      · rintro ⟨ha, h⟩
        exact ⟨ha, by rw [h, hfg]⟩
    rw [hfilter, Finset.filter_eq' μ.support (g b)]
    by_cases hmem : g b ∈ μ.support
    · rw [if_pos hmem, Finset.sum_singleton, hw (g b), hfg]
    · rw [if_neg hmem, Finset.sum_empty]
      refine (ν.outsideSupport b ?_).symm
      intro hb
      exact hmem ((hs (g b)).mpr (by rw [hfg b]; exact hb))

/-! ## Push-forward of the second factor of a product -/

/-- Pushing the second factor of a product forward is pushing the product
forward along the map acting on that factor alone.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem Distribution.prod_map_right {α β γ : Type*} [DecidableEq α]
    [DecidableEq β] [DecidableEq γ] (μ : Distribution α) (ν : Distribution β)
    (g : β → γ) :
    Distribution.prod μ (ν.map g) =
      (Distribution.prod μ ν).map (fun w => (w.1, g w.2)) := by
  classical
  refine Distribution.ext_of_support_of_weight ?_ ?_
  · change μ.support ×ˢ (ν.support.image g) =
      (μ.support ×ˢ ν.support).image (fun w => (w.1, g w.2))
    ext w
    obtain ⟨x, c⟩ := w
    simp only [Finset.mem_product, Finset.mem_image, Prod.mk.injEq, Prod.exists]
    constructor
    · rintro ⟨hx, b, hb, rfl⟩
      exact ⟨x, b, ⟨hx, hb⟩, rfl, rfl⟩
    · rintro ⟨a, b, ⟨ha, hb⟩, rfl, rfl⟩
      exact ⟨ha, b, hb, rfl⟩
  · funext w
    obtain ⟨x, c⟩ := w
    have hfilter :
        (μ.support ×ˢ ν.support).filter (fun p => (p.1, g p.2) = (x, c)) =
          (μ.support.filter (fun a => a = x)) ×ˢ
            (ν.support.filter (fun b => g b = c)) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product, Prod.mk.injEq]
      tauto
    have hx : ∑ a ∈ μ.support.filter (fun a => a = x), μ.weight a =
        μ.weight x := by
      rw [Finset.filter_eq' μ.support x]
      by_cases hmem : x ∈ μ.support
      · rw [if_pos hmem, Finset.sum_singleton]
      · rw [if_neg hmem, Finset.sum_empty, μ.outsideSupport x hmem]
    change μ.weight x * (ν.map g).weight c =
      ∑ p ∈ (μ.support ×ˢ ν.support).filter (fun p => (p.1, g p.2) = (x, c)),
        μ.weight p.1 * ν.weight p.2
    rw [hfilter, Finset.sum_product,
      Finset.sum_congr rfl (fun a _ =>
        (Finset.mul_sum (ν.support.filter (fun b => g b = c))
          (fun b => ν.weight b) (μ.weight a)).symm),
      ← Finset.sum_mul, hx]
    rfl

end

end MIPStarRE.QPBT
