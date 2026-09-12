import MIPStarRE.LDT.Basic.PMFAverages
import MIPStarRE.QPBT.Games.DistributionAux

/-!
# Products, marginals, and restrictions of finite distributions

The finite-distribution push-forward calculus gives corresponding identities
for probability mass functions and for projections transported across finite
equivalences.  These forms are used by the directly indexed low-degree
line-point laws and by the correspondence between the seed-indexed and directly
indexed question distributions. Products can be expressed as dependent mixtures, and
conditioning on an event of one factor preserves the independence of the other.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:243-272`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

/-- Two finite probability distributions with the same support and the same
probability mass at every point are equal. -/
theorem distribution_eq_of_support_eq_of_toPMF_eq {alpha : Type*}
    (mu nu : Distribution alpha) (hmu : mu.IsProbability)
    (hnu : nu.IsProbability) (hsupport : mu.support = nu.support)
    (hpmf : mu.toPMF hmu = nu.toPMF hnu) : mu = nu := by
  have hweight : mu.weight = nu.weight := by
    funext a
    calc
      mu.weight a = (mu.toPMF hmu a).toReal :=
        (Distribution.toPMF_apply_toReal mu hmu a).symm
      _ = (nu.toPMF hnu a).toReal := by rw [hpmf]
      _ = nu.weight a := Distribution.toPMF_apply_toReal nu hnu a
  exact Distribution.ext_of_support_of_weight hsupport hweight

/-- Formalization-only lemma for the low-degree sampling laws: if an
equivalence identifies a nonempty finite set with the product of two nonempty
finite sets and a map agrees with the first projection, then the map sends the
uniform law to the uniform law on the first factor.  This is
`lem:uniform-first-marginal-after-equivalence` in blueprint chapter 13. -/
theorem uniformDistribution_map_fst_of_equiv
    {alpha beta gamma : Type*}
    [Fintype alpha] [DecidableEq alpha] [Nonempty alpha]
    [Fintype beta] [DecidableEq beta] [Nonempty beta]
    [Finite gamma] [Nonempty gamma]
    (e : alpha ≃ beta × gamma) (f : alpha → beta)
    (hf : ∀ a, f a = (e a).1) :
    (uniformDistribution alpha).map f = uniformDistribution beta := by
  classical
  letI : Fintype gamma := Fintype.ofFinite gamma
  calc
    (uniformDistribution alpha).map f =
        (uniformDistribution alpha).map (fun a => (e a).1) := by
      congr 1
      funext a
      exact hf a
    _ = ((uniformDistribution alpha).map e).map Prod.fst :=
      (Distribution.map_map _ _ _).symm
    _ = (uniformDistribution (beta × gamma)).map Prod.fst := by
      rw [uniformDistribution_map_equiv]
    _ = uniformDistribution beta := uniformDistribution_map_fst

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

/-! ## Uniform laws on products -/

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

/-- Formalization-only auxiliary: the mass of an event depending only on the
second factor is the same under a uniform product law and under the uniform
law of that factor.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem uniformDistribution_snd_event_mass {α β : Type*} [Fintype α]
    [DecidableEq α] [Nonempty α] [Fintype β] [DecidableEq β] [Nonempty β]
    (p : β → Prop) [DecidablePred p] :
    ∑ w ∈ (uniformDistribution (α × β)).support.filter (fun w => p w.2),
        (uniformDistribution (α × β)).weight w =
      ∑ b ∈ (uniformDistribution β).support.filter p,
        (uniformDistribution β).weight b := by
  classical
  rw [Distribution.sum_filter_weight_eq_avgOver,
    Distribution.sum_filter_weight_eq_avgOver,
    ← uniformDistribution_map_snd (α := α) (β := β), Distribution.avgOver_map]

/-! ## Conditioning one factor of a product -/

/-- Formalization-only auxiliary: normalized restriction depends on the
restricted law only through its support and weights.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem Distribution.restrict_congr {α : Type*} [DecidableEq α]
    {μ ν : Distribution α} (h : μ = ν) (p : α → Prop) [DecidablePred p]
    (hμ : 0 < ∑ a ∈ μ.support.filter p, μ.weight a)
    (hν : 0 < ∑ a ∈ ν.support.filter p, ν.weight a) :
    Distribution.restrict μ p hμ = Distribution.restrict ν p hν := by
  subst h
  rfl

/-- Restricting a product law to an event depending on the second factor alone
leaves the first factor unchanged and independent of the conditioned second
factor.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem Distribution.restrict_prod_snd {α β : Type*} [DecidableEq α]
    [DecidableEq β] (μ : Distribution α) (ν : Distribution β)
    (hμ : μ.IsProbability) (p : β → Prop) [DecidablePred p]
    (hpos : 0 < ∑ b ∈ ν.support.filter p, ν.weight b)
    (hpos' : 0 < ∑ w ∈ (Distribution.prod μ ν).support.filter
        (fun w => p w.2), (Distribution.prod μ ν).weight w) :
    Distribution.restrict (Distribution.prod μ ν) (fun w => p w.2) hpos' =
      Distribution.prod μ (Distribution.restrict ν p hpos) := by
  classical
  have hprodsupp : (Distribution.prod μ ν).support =
      μ.support ×ˢ ν.support := rfl
  have hsupp : (Distribution.prod μ ν).support.filter (fun w => p w.2) =
      μ.support ×ˢ (ν.support.filter p) := by
    rw [hprodsupp]
    ext w
    simp only [Finset.mem_filter, Finset.mem_product]
    tauto
  have hmass : (∑ w ∈ (Distribution.prod μ ν).support.filter
        (fun w => p w.2), (Distribution.prod μ ν).weight w) =
      ∑ b ∈ ν.support.filter p, ν.weight b := by
    rw [hsupp]
    have h1 : (∑ w ∈ μ.support ×ˢ (ν.support.filter p),
        (Distribution.prod μ ν).weight w) =
        ∑ a ∈ μ.support, ∑ b ∈ ν.support.filter p,
          μ.weight a * ν.weight b := by
      rw [Finset.sum_product]
      rfl
    rw [h1, Finset.sum_congr rfl fun a _ =>
        (Finset.mul_sum (ν.support.filter p) (fun b => ν.weight b)
          (μ.weight a)).symm,
      ← Finset.sum_mul, hμ.weight_sum_eq_one, one_mul]
  refine Distribution.ext_of_support_of_weight ?_ ?_
  · show (Distribution.prod μ ν).support.filter (fun w => p w.2) =
      μ.support ×ˢ (ν.support.filter p)
    exact hsupp
  · funext w
    show (if p w.2 then (Distribution.prod μ ν).weight w /
        ∑ c ∈ (Distribution.prod μ ν).support.filter (fun w => p w.2),
          (Distribution.prod μ ν).weight c else 0) =
      μ.weight w.1 * (if p w.2 then ν.weight w.2 /
        ∑ c ∈ ν.support.filter p, ν.weight c else 0)
    rw [hmass]
    by_cases h : p w.2
    · rw [if_pos h, if_pos h]
      show μ.weight w.1 * ν.weight w.2 / _ = _
      rw [mul_div_assoc]
    · rw [if_neg h, if_neg h, mul_zero]

/-- Conditioning a uniform product law on an event of its second factor leaves
the first factor uniform and independent.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem restrict_uniform_prod_snd {α β : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] [Fintype β] [DecidableEq β] [Nonempty β] (p : β → Prop)
    [DecidablePred p]
    (hpos : 0 < ∑ b ∈ (uniformDistribution β).support.filter p,
      (uniformDistribution β).weight b)
    (hpos' : 0 < ∑ w ∈ (uniformDistribution (α × β)).support.filter
        (fun w => p w.2), (uniformDistribution (α × β)).weight w) :
    Distribution.restrict (uniformDistribution (α × β)) (fun w => p w.2)
        hpos' =
      Distribution.prod (uniformDistribution α)
        (Distribution.restrict (uniformDistribution β) p hpos) := by
  classical
  have hpos'' : 0 < ∑ w ∈ (Distribution.prod (uniformDistribution α)
        (uniformDistribution β)).support.filter (fun w => p w.2),
      (Distribution.prod (uniformDistribution α)
        (uniformDistribution β)).weight w := by
    rw [← uniformDistribution_prod]
    exact hpos'
  rw [Distribution.restrict_congr (uniformDistribution_prod α β)
    (fun w => p w.2) hpos' hpos'']
  exact Distribution.restrict_prod_snd _ _
    (uniformDistribution_isProbability α) p hpos hpos''

/-! ## Conditioning the first factor of a product -/

/-- Restricting a product law to an event depending on the first factor alone
leaves the second factor unchanged and independent of the conditioned first
factor.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem Distribution.restrict_prod_fst {α β : Type*} [DecidableEq α]
    [DecidableEq β] (μ : Distribution α) (ν : Distribution β)
    (hν : ν.IsProbability) (p : α → Prop) [DecidablePred p]
    (hpos : 0 < ∑ a ∈ μ.support.filter p, μ.weight a)
    (hpos' : 0 < ∑ w ∈ (Distribution.prod μ ν).support.filter
        (fun w => p w.1), (Distribution.prod μ ν).weight w) :
    Distribution.restrict (Distribution.prod μ ν) (fun w => p w.1) hpos' =
      Distribution.prod (Distribution.restrict μ p hpos) ν := by
  classical
  have hsupp : (Distribution.prod μ ν).support.filter (fun w => p w.1) =
      (μ.support.filter p) ×ˢ ν.support := by
    change (μ.support ×ˢ ν.support).filter (fun w => p w.1) =
      (μ.support.filter p) ×ˢ ν.support
    ext w
    simp only [Finset.mem_filter, Finset.mem_product]
    tauto
  have hmass : (∑ w ∈ (Distribution.prod μ ν).support.filter
        (fun w => p w.1), (Distribution.prod μ ν).weight w) =
      ∑ a ∈ μ.support.filter p, μ.weight a := by
    rw [hsupp]
    have h1 : (∑ w ∈ (μ.support.filter p) ×ˢ ν.support,
        (Distribution.prod μ ν).weight w) =
        ∑ a ∈ μ.support.filter p, ∑ b ∈ ν.support,
          μ.weight a * ν.weight b := by
      rw [Finset.sum_product]
      rfl
    rw [h1, Finset.sum_congr rfl fun a _ =>
        (Finset.mul_sum ν.support (fun b => ν.weight b) (μ.weight a)).symm,
      hν.weight_sum_eq_one]
    simp
  refine Distribution.ext_of_support_of_weight ?_ ?_
  · change (Distribution.prod μ ν).support.filter (fun w => p w.1) =
      (μ.support.filter p) ×ˢ ν.support
    exact hsupp
  · funext w
    change (if p w.1 then (Distribution.prod μ ν).weight w /
        ∑ c ∈ (Distribution.prod μ ν).support.filter (fun w => p w.1),
          (Distribution.prod μ ν).weight c else 0) =
      (if p w.1 then μ.weight w.1 /
        ∑ c ∈ μ.support.filter p, μ.weight c else 0) * ν.weight w.2
    rw [hmass]
    by_cases h : p w.1
    · rw [if_pos h, if_pos h, div_mul_eq_mul_div]
      rfl
    · rw [if_neg h, if_neg h, zero_mul]

/-- Formalization-only auxiliary: the mass of an event depending only on the
first factor is the same under a uniform product law and under the uniform
law of that factor.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem uniformDistribution_fst_event_mass {α β : Type*} [Fintype α]
    [DecidableEq α] [Nonempty α] [Fintype β] [DecidableEq β] [Nonempty β]
    (p : α → Prop) [DecidablePred p] :
    ∑ w ∈ (uniformDistribution (α × β)).support.filter (fun w => p w.1),
        (uniformDistribution (α × β)).weight w =
      ∑ a ∈ (uniformDistribution α).support.filter p,
        (uniformDistribution α).weight a := by
  classical
  rw [Distribution.sum_filter_weight_eq_avgOver,
    Distribution.sum_filter_weight_eq_avgOver,
    ← uniformDistribution_map_fst (α := α) (β := β), Distribution.avgOver_map]

/-- Conditioning a uniform product law on an event of its first factor leaves
the second factor uniform and independent.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem restrict_uniform_prod_fst {α β : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] [Fintype β] [DecidableEq β] [Nonempty β] (p : α → Prop)
    [DecidablePred p]
    (hpos : 0 < ∑ a ∈ (uniformDistribution α).support.filter p,
      (uniformDistribution α).weight a)
    (hpos' : 0 < ∑ w ∈ (uniformDistribution (α × β)).support.filter
        (fun w => p w.1), (uniformDistribution (α × β)).weight w) :
    Distribution.restrict (uniformDistribution (α × β)) (fun w => p w.1)
        hpos' =
      Distribution.prod
        (Distribution.restrict (uniformDistribution α) p hpos)
        (uniformDistribution β) := by
  classical
  have hpos'' : 0 < ∑ w ∈ (Distribution.prod (uniformDistribution α)
        (uniformDistribution β)).support.filter (fun w => p w.1),
      (Distribution.prod (uniformDistribution α)
        (uniformDistribution β)).weight w := by
    rw [← uniformDistribution_prod]
    exact hpos'
  rw [Distribution.restrict_congr (uniformDistribution_prod α β)
    (fun w => p w.1) hpos' hpos'']
  exact Distribution.restrict_prod_fst _ _
    (uniformDistribution_isProbability β) p hpos hpos''

/-! ## Restriction of a push-forward -/

/-- Formalization-only auxiliary: restricting a push-forward distribution to a
decidable event is the push-forward of the restriction to the pre-image of
that event.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem Distribution.restrict_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (μ : Distribution α) (f : α → β) (p : β → Prop) [DecidablePred p]
    (q : α → Prop) [DecidablePred q] (hq : ∀ a, q a ↔ p (f a))
    (hpos : 0 < ∑ b ∈ (μ.map f).support.filter p, (μ.map f).weight b)
    (hpos' : 0 < ∑ a ∈ μ.support.filter q, μ.weight a) :
    Distribution.restrict (μ.map f) p hpos =
      (Distribution.restrict μ q hpos').map f := by
  classical
  have hfiber : ∀ b : β, p b →
      μ.support.filter (fun a => f a = b) =
        (μ.support.filter q).filter (fun a => f a = b) := by
    intro b hb
    ext a
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨ha, hab⟩
      exact ⟨⟨ha, (hq a).mpr (hab ▸ hb)⟩, hab⟩
    · rintro ⟨⟨ha, -⟩, hab⟩
      exact ⟨ha, hab⟩
  have himg : (μ.map f).support.filter p = (μ.support.filter q).image f := by
    ext b
    simp only [Distribution.map_support, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hpb⟩
      exact ⟨a, ⟨ha, (hq a).mpr hpb⟩, rfl⟩
    · rintro ⟨a, ⟨ha1, ha2⟩, rfl⟩
      exact ⟨⟨a, ha1, rfl⟩, (hq a).mp ha2⟩
  have hmass : (∑ b ∈ (μ.map f).support.filter p, (μ.map f).weight b) =
      ∑ a ∈ μ.support.filter q, μ.weight a := by
    rw [himg]
    rw [← Finset.sum_fiberwise_of_maps_to
      (s := μ.support.filter q) (t := (μ.support.filter q).image f)
      (g := f) (fun a ha => Finset.mem_image_of_mem f ha) μ.weight]
    refine Finset.sum_congr rfl fun b hb => ?_
    obtain ⟨a0, ha0, rfl⟩ := Finset.mem_image.mp hb
    rw [Distribution.map_weight,
      hfiber _ ((hq a0).mp (Finset.mem_filter.mp ha0).2)]
  refine Distribution.ext_of_support_of_weight ?_ ?_
  · exact himg
  · funext b
    show (if p b then (μ.map f).weight b /
        ∑ c ∈ (μ.map f).support.filter p, (μ.map f).weight c else 0) =
      ∑ a ∈ (μ.support.filter q).filter (fun a => f a = b),
        (if q a then μ.weight a / ∑ c ∈ μ.support.filter q, μ.weight c else 0)
    by_cases hb : p b
    · rw [if_pos hb, hmass, Distribution.map_weight, hfiber b hb,
        Finset.sum_div]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [if_pos (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2]
    · rw [if_neg hb]
      refine (Finset.sum_eq_zero fun a ha => ?_).symm
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
      exact absurd (ha2 ▸ (hq a).mp (Finset.mem_filter.mp ha1).2) hb

end MIPStarRE.QPBT
