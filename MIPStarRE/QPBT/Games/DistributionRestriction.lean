import MIPStarRE.QPBT.Games.DistributionProduct

/-!
# Conditioning finite distributions

Normalized restrictions commute with push-forwards. Conditioning an
independent product on an event of one factor preserves the other factor,
and uniform mixtures of equal-mass restrictions recover the original law.

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

/-- Formalization-only auxiliary: the mass of a decidable event is the average
of its indicator.  Blueprint `lem:restricted-line-mixture-bounds`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1049-1051`. -/
theorem Distribution.sum_filter_weight_eq_avgOver {α : Type*}
    (μ : Distribution α) (p : α → Prop) [DecidablePred p] :
    ∑ a ∈ μ.support.filter p, μ.weight a =
      avgOver μ (fun a => if p a then 1 else 0) := by
  unfold avgOver
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : p a <;> simp [h]

/-- Formalization-only auxiliary: a family of normalized restrictions along the
fibers of a classifying map recovers the original law when every fiber carries
the uniform mass `1 / |ι|`.  This is the mixture step of
blueprint `lem:restricted-line-mixture-bounds`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1049-1051`. -/
theorem Distribution.bind_uniform_restrict_eq {α ι : Type*} [DecidableEq α]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (μ : Distribution α) (p : ι → α → Prop) [∀ i, DecidablePred (p i)]
    (hpos : ∀ i, 0 < ∑ a ∈ μ.support.filter (p i), μ.weight a)
    (hmass : ∀ i, ∑ a ∈ μ.support.filter (p i), μ.weight a =
      1 / (Fintype.card ι : ℝ))
    (hunique : ∀ a, ∃! i, p i a) :
    Distribution.bind (uniformDistribution ι)
        (fun i => Distribution.restrict μ (p i) (hpos i)) = μ := by
  classical
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  refine Distribution.ext_of_support_of_weight ?_ ?_
  · change (Finset.univ : Finset ι).biUnion
      (fun i => μ.support.filter (p i)) = μ.support
    ext a
    constructor
    · intro ha
      obtain ⟨i, -, hai⟩ := Finset.mem_biUnion.mp ha
      exact (Finset.mem_filter.mp hai).1
    · intro ha
      obtain ⟨i, hi, -⟩ := hunique a
      exact Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_univ i, Finset.mem_filter.mpr ⟨ha, hi⟩⟩
  · funext a
    change (∑ i ∈ (Finset.univ : Finset ι), (uniformDistribution ι).weight i *
      (Distribution.restrict μ (p i) (hpos i)).weight a) = μ.weight a
    have hterm : ∀ i : ι, (uniformDistribution ι).weight i *
        (Distribution.restrict μ (p i) (hpos i)).weight a =
        if p i a then μ.weight a else 0 := by
      intro i
      rw [uniformDistribution_weight_apply]
      by_cases h : p i a
      · have hw : (Distribution.restrict μ (p i) (hpos i)).weight a =
            μ.weight a / (1 / (Fintype.card ι : ℝ)) := by
          simp only [Distribution.restrict, if_pos h, hmass i]
        rw [hw, if_pos h]
        field_simp
      · have hw : (Distribution.restrict μ (p i) (hpos i)).weight a = 0 := by
          simp only [Distribution.restrict, if_neg h]
        rw [hw, if_neg h, mul_zero]
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    obtain ⟨i₀, hi₀, huniq⟩ := hunique a
    rw [Finset.sum_eq_single i₀]
    · rw [if_pos hi₀]
    · intro i _ hne
      exact if_neg fun hi => hne (huniq i hi)
    · intro hmem
      exact absurd (Finset.mem_univ i₀) hmem

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

end

end MIPStarRE.QPBT
