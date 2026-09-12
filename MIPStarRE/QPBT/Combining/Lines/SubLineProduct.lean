import MIPStarRE.QPBT.Combining.Lines.SubLineBind

/-!
# Products and push-forwards of finite distributions

The sampling procedure of the sub-line lemma presents one law both as an
independent product of its generating blocks and as a dependent mixture over
one of those blocks.  This module records the three rewriting rules that pass
between the two presentations: a push-forward of the first factor of a product
is a push-forward of the product, a product with a probability law in the
second factor has the first factor as its marginal, and a push-forward of a
product is the dependent mixture of the push-forwards of its second factor.

## References

The rewriting rules support `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The product and mixture operations are those of blueprint
`def:line-point-dist`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-! ## Nonemptiness of the support of a probability law -/

/-- A law of total mass one has a nonempty support.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem Distribution.support_nonempty_of_isProbability {α : Type*}
    {μ : Distribution α} (hμ : μ.IsProbability) : μ.support.Nonempty := by
  rw [← Finset.card_pos]
  by_contra hcard
  have hempty : μ.support = ∅ := by
    rw [← Finset.card_eq_zero]
    omega
  have h1 := hμ.weight_sum_eq_one
  rw [hempty] at h1
  simp at h1

/-! ## Push-forward of one factor of a product -/

/-- Pushing the first factor of a product forward is pushing the product
forward along the map acting on that factor alone.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem Distribution.prod_map_left {α β γ : Type*} [DecidableEq α]
    [DecidableEq β] [DecidableEq γ] (μ : Distribution α) (ν : Distribution β)
    (f : α → γ) :
    Distribution.prod (μ.map f) ν =
      (Distribution.prod μ ν).map (fun w => (f w.1, w.2)) := by
  classical
  refine Distribution.ext_of_support_of_weight ?_ ?_
  · change (μ.support.image f) ×ˢ ν.support =
      (μ.support ×ˢ ν.support).image (fun w => (f w.1, w.2))
    ext w
    obtain ⟨c, y⟩ := w
    simp only [Finset.mem_product, Finset.mem_image, Prod.mk.injEq, Prod.exists]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hy⟩
      exact ⟨a, y, ⟨ha, hy⟩, rfl, rfl⟩
    · rintro ⟨a, b, ⟨ha, hb⟩, rfl, rfl⟩
      exact ⟨⟨a, ha, rfl⟩, hb⟩
  · funext w
    obtain ⟨c, y⟩ := w
    have hfilter :
        (μ.support ×ˢ ν.support).filter (fun p => (f p.1, p.2) = (c, y)) =
          (μ.support.filter (fun a => f a = c)) ×ˢ
            (ν.support.filter (fun b => b = y)) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product, Prod.mk.injEq]
      tauto
    have hy : ∑ b ∈ ν.support.filter (fun b => b = y), ν.weight b =
        ν.weight y := by
      rw [Finset.filter_eq' ν.support y]
      by_cases hmem : y ∈ ν.support
      · rw [if_pos hmem, Finset.sum_singleton]
      · rw [if_neg hmem, Finset.sum_empty, ν.outsideSupport y hmem]
    change (μ.map f).weight c * ν.weight y =
      ∑ p ∈ (μ.support ×ˢ ν.support).filter (fun p => (f p.1, p.2) = (c, y)),
        μ.weight p.1 * ν.weight p.2
    rw [hfilter, Finset.sum_product,
      Finset.sum_congr rfl
        (fun a _ => (Finset.mul_sum (ν.support.filter (fun b => b = y))
          (fun b => ν.weight b) (μ.weight a)).symm),
      hy, ← Finset.sum_mul]
    rfl

/-! ## The first marginal of a product -/

/-- The first marginal of a product whose second factor is a probability law
is the first factor.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem Distribution.prod_map_fst {α β : Type*} [DecidableEq α] [DecidableEq β]
    (μ : Distribution α) (ν : Distribution β) (hν : ν.IsProbability) :
    (Distribution.prod μ ν).map Prod.fst = μ := by
  classical
  obtain ⟨b₀, hb₀⟩ := Distribution.support_nonempty_of_isProbability hν
  refine Distribution.ext_of_support_of_weight ?_ ?_
  · change (μ.support ×ˢ ν.support).image Prod.fst = μ.support
    ext a
    simp only [Finset.mem_image, Finset.mem_product, Prod.exists]
    constructor
    · rintro ⟨x, y, ⟨hx, -⟩, rfl⟩
      exact hx
    · intro ha
      exact ⟨a, b₀, ⟨ha, hb₀⟩, rfl⟩
  · funext a
    have hfilter : (μ.support ×ˢ ν.support).filter (fun p => p.1 = a) =
        (μ.support.filter (fun x => x = a)) ×ˢ ν.support := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product]
      tauto
    have ha : ∑ x ∈ μ.support.filter (fun x => x = a), μ.weight x =
        μ.weight a := by
      rw [Finset.filter_eq' μ.support a]
      by_cases hmem : a ∈ μ.support
      · rw [if_pos hmem, Finset.sum_singleton]
      · rw [if_neg hmem, Finset.sum_empty, μ.outsideSupport a hmem]
    change (∑ p ∈ (μ.support ×ˢ ν.support).filter (fun p => p.1 = a),
      μ.weight p.1 * ν.weight p.2) = μ.weight a
    rw [hfilter, Finset.sum_product,
      Finset.sum_congr rfl
        (fun x _ => (Finset.mul_sum ν.support (fun b => ν.weight b)
          (μ.weight x)).symm),
      hν.weight_sum_eq_one]
    simpa using ha

/-- Reading a function of the first factor of a product whose second factor is
a probability law is reading it on the first factor.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem Distribution.prod_map_of_fst {α β γ : Type*} [DecidableEq α]
    [DecidableEq β] [DecidableEq γ] (μ : Distribution α) (ν : Distribution β)
    (hν : ν.IsProbability) (h : α → γ) :
    (Distribution.prod μ ν).map (fun w => h w.1) = μ.map h := by
  rw [← Distribution.map_map (Distribution.prod μ ν) Prod.fst h,
    Distribution.prod_map_fst μ ν hν]

/-! ## A product as a dependent mixture -/

/-- A push-forward of a product is the dependent mixture, over the first
factor, of the push-forwards of the second factor.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem Distribution.prod_map_eq_bind {α β γ : Type*} [DecidableEq α]
    [DecidableEq β] [DecidableEq γ] (μ : Distribution α) (ν : Distribution β)
    (g : α × β → γ) :
    (Distribution.prod μ ν).map g =
      Distribution.bind μ (fun a => ν.map (fun b => g (a, b))) := by
  classical
  refine Distribution.ext_of_support_of_weight ?_ ?_
  · change (μ.support ×ˢ ν.support).image g =
      μ.support.biUnion (fun a => ν.support.image (fun b => g (a, b)))
    ext c
    simp only [Finset.mem_image, Finset.mem_biUnion, Finset.mem_product,
      Prod.exists]
    constructor
    · rintro ⟨a, b, ⟨ha, hb⟩, rfl⟩
      exact ⟨a, ha, b, hb, rfl⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, b, ⟨ha, hb⟩, rfl⟩
  · funext c
    change (∑ p ∈ (μ.support ×ˢ ν.support).filter (fun p => g p = c),
        μ.weight p.1 * ν.weight p.2) =
      ∑ a ∈ μ.support, μ.weight a *
        ∑ b ∈ ν.support.filter (fun b => g (a, b) = c), ν.weight b
    rw [Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases h : g (a, b) = c
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, mul_zero]

end

end MIPStarRE.QPBT
