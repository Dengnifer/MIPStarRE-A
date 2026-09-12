import MIPStarRE.QPBT.Games.DistributionAux

/-!
# Products and push-forwards of finite distributions

This module records the supports, weights, marginals, and push-forwards of
independent products, together with the product identity for uniform laws.

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


/-- Formalization-only auxiliary: the uniform law on a product of two finite
types is the product of the uniform laws.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem uniformDistribution_prod (α β : Type*) [Fintype α] [DecidableEq α]
    [Nonempty α] [Fintype β] [DecidableEq β] [Nonempty β] :
    uniformDistribution (α × β) =
      Distribution.prod (uniformDistribution α) (uniformDistribution β) := by
  classical
  have ha : (Fintype.card α : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := α)
  have hb : (Fintype.card β : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := β)
  refine Distribution.ext_of_support_of_weight ?_ ?_
  · show (Finset.univ : Finset (α × β)) =
      (Finset.univ : Finset α).product (Finset.univ : Finset β)
    ext p
    simp
  · funext p
    show (uniformDistribution (α × β)).weight p =
      (uniformDistribution α).weight p.1 * (uniformDistribution β).weight p.2
    rw [uniformDistribution_weight_apply, uniformDistribution_weight_apply,
      uniformDistribution_weight_apply, Fintype.card_prod]
    push_cast
    field_simp

end

end MIPStarRE.QPBT
