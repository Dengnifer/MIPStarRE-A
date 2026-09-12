import MIPStarRE.LDT.Basic.DistributionAvg

/-! # Operations on finite distributions

Finite distributions support products, convex mixtures, dependent binds,
normalized restrictions, and push-forwards.  Uniform laws are preserved by
bijections and balanced maps, their product projections are uniform, and
dependent uniform sampling agrees with push-forward from a product.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

/-- The product of two finite distributions, a formalization-only auxiliary
used by the sandwich construction; blueprint `lem:ld-sandwich`,
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
distribution; blueprint `lem:ld-sandwich`, paper
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
distributions, blueprint `def:typed-cl-distributions`, paper
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
`def:typed-cl-distributions`, paper `07_types.tex:84-94`. -/
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

/-! ### Push-forwards of finite and uniform distributions

The results of this section are not named in the paper.  They record the
elementary behaviour of push-forwards of finite distributions, and of uniform
distributions on finite types, that the line-point samplers of the low-degree
game and the identification of question distributions with typed conditionally
linear distributions rely on.
-/

/-- Formalization-only lemma: two finite distributions coincide as soon as
their supports and weight functions coincide.  This is the support statement
`lem:distribution-ext-support` in blueprint chapter 13. -/
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

/-- Formalization-only lemma: successive push-forwards of a finite distribution
compose.  This is `lem:distribution-map-comp` in blueprint chapter 13. -/
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

/-- Formalization-only lemma: every point of a nonempty finite type carries the
reciprocal of the type's cardinality as its uniform weight.  This is
`lem:uniform-distribution-weight` in blueprint chapter 13. -/
theorem uniformDistribution_weight_apply (α : Type*)
    [Fintype α] [DecidableEq α] [Nonempty α] (a : α) :
    (uniformDistribution α).weight a = 1 / (Fintype.card α : Error) := by
  simp [uniformDistribution]

/-- Formalization-only lemma: a push-forward of a uniform law assigns to a point
the cardinality of its fibre divided by the cardinality of the source.  This is
`lem:uniform-map-fibre-weight` in blueprint chapter 13. -/
theorem uniformDistribution_map_weight {α γ : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α] [DecidableEq γ]
    (e : α → γ) (c : γ) :
    ((uniformDistribution α).map e).weight c =
      (((Finset.univ : Finset α).filter fun x => e x = c).card : Error) *
        (1 / (Fintype.card α : Error)) := by
  change (∑ x ∈ (Finset.univ : Finset α).filter (fun x => e x = c),
      (uniformDistribution α).weight x) = _
  rw [Finset.sum_congr rfl fun x _ => uniformDistribution_weight_apply α x,
    Finset.sum_const, nsmul_eq_mul]

/-- Formalization-only lemma: a map whose fibers all have the same cardinality
pushes the uniform distribution forward to the uniform distribution.  This is
`lem:uniform-map-equal-fibers` in blueprint chapter 13. -/
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

/-- Formalization-only lemma: relabelling along a bijection preserves
uniformity.  This is `lem:uniform-map-equivalence` in blueprint chapter 13. -/
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

/-- Formalization-only lemma: the first marginal of the uniform distribution on
a product is uniform.  This is `lem:uniform-product-first-marginal` in blueprint
chapter 13. -/
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

/-- Formalization-only lemma: the second marginal of the uniform distribution
on a product is uniform.  This is `lem:uniform-product-second-marginal` in
blueprint chapter 13. -/
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

/-- Formalization-only lemma: binding the uniform law on a finite subset to a
family of uniformly seeded push-forwards is the push-forward of the uniform law
on the product of an indexing type for that subset with the seed space.  This is
`lem:uniform-bind-on-finset-map` in blueprint chapter 13. -/
theorem bind_uniformOnFinset_map {α β γ σ : Type*} [DecidableEq α]
    [Fintype σ] [DecidableEq σ] [Nonempty σ]
    [Fintype β] [DecidableEq β] [Nonempty β] [DecidableEq γ]
    (s : Finset α) (f : σ → α) (hinj : Function.Injective f)
    (himage : (Finset.univ : Finset σ).image f = s) (g : α → β → γ) :
    Distribution.bind (Distribution.uniformOnFinset s)
        (fun a => (uniformDistribution β).map (g a)) =
      (uniformDistribution (σ × β)).map fun q => g (f q.1) q.2 := by
  have hmem : ∀ a, a ∈ s ↔ ∃ x : σ, f x = a := by
    intro a
    rw [← himage]
    simp
  have hcard : s.card = Fintype.card σ := by
    rw [← himage, Finset.card_image_of_injective _ hinj, Finset.card_univ]
  have hsum : ∀ h : α → Error, ∑ a ∈ s, h a = ∑ x : σ, h (f x) := by
    intro h
    rw [← himage, Finset.sum_image fun x _ y _ hxy => hinj hxy]
  refine Distribution.ext_of_support_of_weight ?_ ?_
  · change s.biUnion (fun a => (Finset.univ : Finset β).image (g a)) =
      (Finset.univ : Finset (σ × β)).image fun q => g (f q.1) q.2
    ext c
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and,
      Prod.exists]
    constructor
    · rintro ⟨a, ha, b, rfl⟩
      obtain ⟨xx, rfl⟩ := (hmem a).mp ha
      exact ⟨xx, b, rfl⟩
    · rintro ⟨xx, b, rfl⟩
      exact ⟨f xx, (hmem _).mpr ⟨xx, rfl⟩, b, rfl⟩
  · funext c
    have key : ∀ a ∈ s, (Distribution.uniformOnFinset s).weight a *
        ((uniformDistribution β).map (g a)).weight c =
        (((Finset.univ : Finset β).filter fun b => g a b = c).card : Error) *
          (1 / ((Fintype.card σ : Error) * (Fintype.card β : Error))) := by
      intro a ha
      rw [Distribution.uniformOnFinset_weight, if_pos ha,
        uniformDistribution_map_weight, hcard]
      ring
    have hcount :
        ((Finset.univ : Finset (σ × β)).filter fun q => g (f q.1) q.2 = c).card =
          ∑ x : σ, ((Finset.univ : Finset β).filter fun b => g (f x) b = c).card := by
      simp only [Finset.card_filter]
      rw [Fintype.sum_prod_type]
    change (∑ a ∈ s, (Distribution.uniformOnFinset s).weight a *
        ((uniformDistribution β).map (g a)).weight c) =
      ∑ q ∈ (Finset.univ : Finset (σ × β)).filter fun q => g (f q.1) q.2 = c,
        (uniformDistribution (σ × β)).weight q
    rw [Finset.sum_congr rfl key,
      hsum fun a => (((Finset.univ : Finset β).filter fun b => g a b = c).card : Error) *
        (1 / ((Fintype.card σ : Error) * (Fintype.card β : Error))),
      ← Finset.sum_mul,
      Finset.sum_congr rfl fun q _ => uniformDistribution_weight_apply (σ × β) q,
      Finset.sum_const, nsmul_eq_mul, hcount, Fintype.card_prod]
    push_cast
    ring

/-- Formalization-only lemma: binding a uniform distribution to a family of
uniformly seeded push-forwards is the push-forward of the uniform distribution
on the product.  This is `lem:uniform-bind-map` in blueprint chapter 13. -/
theorem bind_uniformDistribution_map {α β γ : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β] [DecidableEq γ]
    (g : α → β → γ) :
    Distribution.bind (uniformDistribution α)
        (fun a => (uniformDistribution β).map (g a)) =
      (uniformDistribution (α × β)).map fun p => g p.1 p.2 :=
  bind_uniformOnFinset_map (Finset.univ : Finset α) id Function.injective_id
    Finset.image_id g

/-! ## Elementary rewriting of finite distributions -/

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

/-- Formalization-only auxiliary: a push-forward commutes with a dependent
bind.  Blueprint `lem:restricted-line-mixture-bounds`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1049-1051`. -/
theorem Distribution.bind_map {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (μ : Distribution α) (ν : α → Distribution β) (f : β → γ) :
    (Distribution.bind μ ν).map f =
      Distribution.bind μ (fun a => (ν a).map f) := by
  classical
  refine Distribution.ext_of_support_of_weight ?_ ?_
  · change (μ.support.biUnion fun a => (ν a).support).image f =
      μ.support.biUnion fun a => (ν a).support.image f
    ext c
    constructor
    · intro hc
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨a, ha, hb'⟩ := Finset.mem_biUnion.mp hb
      exact Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image_of_mem f hb'⟩
    · intro hc
      obtain ⟨a, ha, hc'⟩ := Finset.mem_biUnion.mp hc
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hc'
      exact Finset.mem_image.mpr ⟨b, Finset.mem_biUnion.mpr ⟨a, ha, hb⟩, rfl⟩
  · funext c
    change (∑ b ∈ (μ.support.biUnion fun a => (ν a).support).filter
          (fun b => f b = c),
        ∑ a ∈ μ.support, μ.weight a * (ν a).weight b) =
      ∑ a ∈ μ.support, μ.weight a *
        ∑ b ∈ (ν a).support.filter (fun b => f b = c), (ν a).weight b
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.mul_sum]
    refine (Finset.sum_subset ?_ ?_).symm
    · intro b hb
      obtain ⟨hb1, hb2⟩ := Finset.mem_filter.mp hb
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_biUnion.mpr ⟨a, ha, hb1⟩, hb2⟩
    · intro b hb hbnot
      have hfb : f b = c := (Finset.mem_filter.mp hb).2
      have hnot : b ∉ (ν a).support := fun hmem =>
        hbnot (Finset.mem_filter.mpr ⟨hmem, hfb⟩)
      rw [(ν a).outsideSupport b hnot, mul_zero]

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

end MIPStarRE.QPBT
