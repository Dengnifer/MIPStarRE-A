import Mathlib
import Challenge.MIPStarRE.LDT.Basic.Distribution

/-! Challenge mirror of `MIPStarRE/QPBT/Games/DistributionAux.lean`.

One challenge module per contributing library module, importing the
mirrors of the library modules this one imports.  The partition is
what makes Lean generate the same auxiliary declarations, under the
same names, as the library does. -/

open scoped BigOperators MatrixOrder Matrix ComplexOrder
namespace MIPStarRE.QPBT

-- elaboration context of MIPStarRE/QPBT/Games/DistributionAux.lean
section
open MIPStarRE.LDT

-- source: MIPStarRE/QPBT/Games/DistributionAux.lean:98-112  (MIPStarRE.QPBT.Distribution.bind)
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

-- source: MIPStarRE/QPBT/Games/DistributionAux.lean:199-213  (MIPStarRE.QPBT.Distribution.ext_of_support_of_weight)
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

-- source: MIPStarRE/QPBT/Games/DistributionAux.lean:215-245  (MIPStarRE.QPBT.Distribution.map_map)
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

-- source: MIPStarRE/QPBT/Games/DistributionAux.lean:247-253  (MIPStarRE.QPBT.uniformDistribution_weight_apply)
/-- Formalization-only lemma: every point of a nonempty finite type carries the
reciprocal of the type's cardinality as its uniform weight.  This is
`lem:uniform-distribution-weight` in blueprint chapter 13. -/
theorem uniformDistribution_weight_apply (α : Type*)
    [Fintype α] [DecidableEq α] [Nonempty α] (a : α) :
    (uniformDistribution α).weight a = 1 / (Fintype.card α : Error) := by
  simp [uniformDistribution]

-- source: MIPStarRE/QPBT/Games/DistributionAux.lean:255-267  (MIPStarRE.QPBT.uniformDistribution_map_weight)
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

-- source: MIPStarRE/QPBT/Games/DistributionAux.lean:357-415  (MIPStarRE.QPBT.bind_uniformOnFinset_map)
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
end  -- module scope
end MIPStarRE.QPBT
