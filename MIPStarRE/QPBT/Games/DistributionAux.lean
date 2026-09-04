import MIPStarRE.LDT.Basic.Distribution

/-! # Operations on finite distributions

Products, convex mixtures, dependent binds, and normalized restrictions used by
the QPBT distributions, together with the generic push-forward calculus for
finite and uniform distributions. Their source uses occur in the line-point
sampler, typed conditionally linear distributions, sandwich products, and
restricted line distributions cited below.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

/-- The product of two finite distributions, a formalization-only auxiliary
used by the sandwich construction; blueprint `ch12_qpbt_games.tex:427-454`,
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
distribution; blueprint `ch12_qpbt_games.tex:427-454`, paper
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
the equal mixture in `def:line-point-dist`, blueprint
`ch13_qpbt_test.tex:125-135`, paper
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
`def:line-point-dist`, blueprint `ch13_qpbt_test.tex:125-135`, paper
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
distributions, blueprint `ch12_qpbt_games.tex:1268-1272`, paper
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
`ch12_qpbt_games.tex:1268-1272`, paper `07_types.tex:84-94`. -/
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
as in `def:ith-restricted-line`; blueprint
`ch15_qpbt_combining.tex:600-618`, paper
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
`ch15_qpbt_combining.tex:600-618`, paper
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

/-! ### Push-forwards of finite and uniform distributions

The results of this section are not named in the paper.  They record the
elementary behaviour of push-forwards of finite distributions, and of uniform
distributions on finite types, that the line-point samplers of the low-degree
game and the identification of question distributions with typed conditionally
linear distributions rely on.
-/

/-- Two finite distributions coincide as soon as their supports and their
weight functions coincide.  Formalization-only extensionality principle for
`Distribution`. -/
theorem Distribution.ext_of_support_of_weight {α : Type*} {μ ν : Distribution α}
    (hsupport : μ.support = ν.support) (hweight : μ.weight = ν.weight) :
    μ = ν := by
  cases μ with
  | mk s w hn ho =>
    cases ν with
    | mk s' w' hn' ho' =>
      have hs : s = s' := hsupport
      have hw : w = w' := hweight
      subst hs
      subst hw
      rfl

/-- Successive push-forwards of a finite distribution compose.
Formalization-only auxiliary for `Distribution.map`. -/
theorem Distribution.map_map {α β γ : Type*}
    [DecidableEq β] [DecidableEq γ]
    (μ : Distribution α) (e : α → β) (f : β → γ) :
    (μ.map e).map f = μ.map fun a => f (e a) := by
  refine Distribution.ext_of_support_of_weight ?_ ?_
  · change (μ.support.image e).image f = μ.support.image fun a => f (e a)
    rw [Finset.image_image]
    rfl
  · funext c
    have hmaps : ∀ a ∈ μ.support.filter fun a => f (e a) = c,
        e a ∈ (μ.support.image e).filter fun b => f b = c := by
      intro a ha
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ ha1, ha2⟩
    have hkey := Finset.sum_fiberwise_of_maps_to hmaps μ.weight
    change (∑ b ∈ (μ.support.image e).filter fun b => f b = c,
        ∑ a ∈ μ.support.filter fun a => e a = b, μ.weight a) =
      ∑ a ∈ μ.support.filter fun a => f (e a) = c, μ.weight a
    rw [← hkey]
    refine Finset.sum_congr rfl fun b hb => ?_
    obtain ⟨-, hb2⟩ := Finset.mem_filter.mp hb
    congr 1
    ext a
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨ha1, rfl⟩
      exact ⟨⟨ha1, hb2⟩, rfl⟩
    · rintro ⟨⟨ha1, -⟩, hae⟩
      exact ⟨ha1, hae⟩

/-- Every point of a finite type carries the same uniform weight.
Formalization-only auxiliary for `uniformDistribution`. -/
theorem uniformDistribution_weight_apply (α : Type*)
    [Fintype α] [DecidableEq α] [Nonempty α] (a : α) :
    (uniformDistribution α).weight a = 1 / (Fintype.card α : Error) := by
  simp [uniformDistribution]

/-- A map whose fibers all have the same cardinality pushes the uniform
distribution forward to the uniform distribution.  Formalization-only
auxiliary for `uniformDistribution`. -/
theorem uniformDistribution_map_of_card_fiber {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (e : α → β) (c : ℕ)
    (hc : ∀ b : β, ((Finset.univ : Finset α).filter fun a => e a = b).card = c) :
    (uniformDistribution α).map e = uniformDistribution β := by
  have hcpos : 0 < c := by
    obtain ⟨a₀⟩ := (inferInstance : Nonempty α)
    have hmem : a₀ ∈ (Finset.univ : Finset α).filter fun a => e a = e a₀ :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    have hpos := Finset.card_pos.mpr ⟨a₀, hmem⟩
    rwa [hc] at hpos
  have hcard : Fintype.card α = Fintype.card β * c := by
    have h := Finset.card_eq_sum_card_fiberwise
      (f := e) (s := (Finset.univ : Finset α)) (t := (Finset.univ : Finset β))
      (fun a _ => Finset.mem_univ _)
    rw [Finset.card_univ] at h
    rw [h, Finset.sum_congr rfl fun b _ => hc b]
    simp [Finset.card_univ, mul_comm]
  refine Distribution.ext_of_support_of_weight ?_ ?_
  · change (Finset.univ : Finset α).image e = (Finset.univ : Finset β)
    ext b
    simp only [Finset.mem_image, Finset.mem_univ, iff_true, true_and]
    have hne : ((Finset.univ : Finset α).filter fun a => e a = b).Nonempty := by
      rw [← Finset.card_pos, hc]
      exact hcpos
    obtain ⟨a, ha⟩ := hne
    exact ⟨a, (Finset.mem_filter.mp ha).2⟩
  · funext b
    have hbeta : (Fintype.card β : Error) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero (α := β)
    have hc' : (c : Error) ≠ 0 := by exact_mod_cast hcpos.ne'
    change (∑ a ∈ (Finset.univ : Finset α).filter fun a => e a = b,
        (uniformDistribution α).weight a) = (uniformDistribution β).weight b
    rw [Finset.sum_congr rfl fun a _ => uniformDistribution_weight_apply α a,
      uniformDistribution_weight_apply, Finset.sum_const, hc, nsmul_eq_mul, hcard]
    push_cast
    field_simp

/-- Relabelling along a bijection preserves uniformity.  Formalization-only
auxiliary for `uniformDistribution`. -/
theorem uniformDistribution_map_equiv {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β] (E : α ≃ β) :
    (uniformDistribution α).map E = uniformDistribution β := by
  refine uniformDistribution_map_of_card_fiber _ 1 fun b => ?_
  have hfilter :
      ((Finset.univ : Finset α).filter fun a => E a = b) = {E.symm b} := by
    ext a
    simp [Equiv.apply_eq_iff_eq_symm_apply]
  rw [hfilter]
  simp

/-- The first marginal of the uniform distribution on a product is uniform.
Formalization-only auxiliary for `uniformDistribution`. -/
theorem uniformDistribution_map_fst {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β] :
    (uniformDistribution (α × β)).map Prod.fst = uniformDistribution α := by
  refine uniformDistribution_map_of_card_fiber _ (Fintype.card β) fun a => ?_
  have hfilter : ((Finset.univ : Finset (α × β)).filter fun p => p.1 = a)
      = ({a} : Finset α) ×ˢ (Finset.univ : Finset β) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_singleton, and_true]
  rw [hfilter, Finset.card_product]
  simp

/-- The second marginal of the uniform distribution on a product is uniform.
Formalization-only auxiliary for `uniformDistribution`. -/
theorem uniformDistribution_map_snd {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β] :
    (uniformDistribution (α × β)).map Prod.snd = uniformDistribution β := by
  refine uniformDistribution_map_of_card_fiber _ (Fintype.card α) fun b => ?_
  have hfilter : ((Finset.univ : Finset (α × β)).filter fun p => p.2 = b)
      = (Finset.univ : Finset α) ×ˢ ({b} : Finset β) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_singleton]
  rw [hfilter, Finset.card_product]
  simp

/-- Binding a uniform distribution to a family of uniformly seeded
push-forwards is the push-forward of the uniform distribution on the product.
Formalization-only auxiliary for `Distribution.bind`. -/
theorem bind_uniformDistribution_map {α β γ : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β] [DecidableEq γ]
    (g : α → β → γ) :
    Distribution.bind (uniformDistribution α)
        (fun a => (uniformDistribution β).map (g a)) =
      (uniformDistribution (α × β)).map fun p => g p.1 p.2 := by
  refine Distribution.ext_of_support_of_weight ?_ ?_
  · change (Finset.univ : Finset α).biUnion
        (fun a => (Finset.univ : Finset β).image (g a)) =
      (Finset.univ : Finset (α × β)).image fun p => g p.1 p.2
    ext c
    simp [Prod.exists]
  · funext c
    have hcount :
        ((Finset.univ : Finset (α × β)).filter fun p => g p.1 p.2 = c).card
          = ∑ a : α, ((Finset.univ : Finset β).filter fun b => g a b = c).card := by
      simp only [Finset.card_filter]
      rw [Fintype.sum_prod_type]
    have hinner : ∀ a : α,
        ((uniformDistribution β).map (g a)).weight c
          = (((Finset.univ : Finset β).filter fun b => g a b = c).card : Error) *
              (1 / (Fintype.card β : Error)) := by
      intro a
      change (∑ b ∈ (Finset.univ : Finset β).filter fun b => g a b = c,
          (uniformDistribution β).weight b) = _
      rw [Finset.sum_congr rfl fun b _ => uniformDistribution_weight_apply β b,
        Finset.sum_const, nsmul_eq_mul]
    have key : ∀ a : α, (uniformDistribution α).weight a *
        ((uniformDistribution β).map (g a)).weight c
        = (((Finset.univ : Finset β).filter fun b => g a b = c).card : Error) *
            (1 / ((Fintype.card α : Error) * (Fintype.card β : Error))) := by
      intro a
      rw [uniformDistribution_weight_apply, hinner a]
      ring
    change (∑ a ∈ (Finset.univ : Finset α), (uniformDistribution α).weight a *
        ((uniformDistribution β).map (g a)).weight c) =
      ∑ p ∈ (Finset.univ : Finset (α × β)).filter fun p => g p.1 p.2 = c,
        (uniformDistribution (α × β)).weight p
    rw [Finset.sum_congr rfl fun a _ => key a, ← Finset.sum_mul,
      Finset.sum_congr rfl fun p _ => uniformDistribution_weight_apply (α × β) p,
      Finset.sum_const, nsmul_eq_mul, hcount, Fintype.card_prod]
    push_cast
    ring

end MIPStarRE.QPBT
