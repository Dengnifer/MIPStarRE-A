import MIPStarRE.QPBT.Combining.Defs

/-!
# Uniform coordinate-index mixtures of the line-point laws

This module proves that the axis-parallel and diagonal line-point laws are the
uniform mixtures of their coordinate-index restrictions.  The identity rests on
the exact seed decomposition of `chiIndex`: the retained scalar seed is uniform,
so each of its `m` coordinate-index fibers carries mass `1 / m`, and every
line conditioning map keeps that seed.

## References

The mixture assertion is the opening sentence of blueprint
`lem:restricted-line-mixture-bounds`, formalizing the unlabelled observation at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1049-1051`.
The restricted laws are blueprint `def:ith-restricted-line`, paper lines
1038--1048.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

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

/-! ## The uniform coordinate-index law of the retained seed -/

/-- The retained scalar seed of a uniformly sampled low-degree vector is
uniform.  This is a public copy of the private
`MIPStarRE.QPBT.map_uniformDistribution_seed` in
`MIPStarRE/QPBT/Test/LowDegreeGameTheorems.lean`, which belongs to another
module; the duplication is tracked by issue #204.  Formalization-only
auxiliary for blueprint `def:ith-restricted-line`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1038-1048`. -/
theorem uniformDistribution_map_ldSeed (L : LdParams) :
    (uniformDistribution (LdSpace L)).map (fun z : LdSpace L => z.seed) =
      uniformDistribution (ScalarQ L) := by
  classical
  haveI : Nonempty (ScalarQ L) := ⟨0⟩
  haveI : Nonempty ({j : LdIndex L // j ≠ (.inl (.inr ()) : LdIndex L)} →
    ScalarQ L) := ⟨fun _ => 0⟩
  have hfun : (fun z : LdSpace L => LdSpace.seed z) =
      fun z : LdSpace L =>
        (Equiv.funSplitAt (.inl (.inr ()) : LdIndex L) (ScalarQ L) z).1 := rfl
  rw [hfun, ← Distribution.map_map (uniformDistribution (LdSpace L))
      (Equiv.funSplitAt (.inl (.inr ()) : LdIndex L) (ScalarQ L)) Prod.fst,
    uniformDistribution_map_equiv, uniformDistribution_map_fst]

/-- The coordinate index of the retained seed of a uniformly sampled low-degree
vector is uniform.  Formalization-only auxiliary for blueprint
`def:ith-restricted-line`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1038-1048`. -/
theorem uniformDistribution_map_chiIndex_ldSeed (L : LdParams) :
    (uniformDistribution (LdSpace L)).map
        (fun z : LdSpace L => chiIndex L z.seed) =
      uniformDistribution (Fin L.m) := by
  classical
  haveI : Nonempty (ScalarQ L) := ⟨0⟩
  haveI : Nonempty (Fin L.m) :=
    Fin.pos_iff_nonempty.mp (lt_of_lt_of_le Nat.zero_lt_one L.hm)
  rw [← Distribution.map_map (uniformDistribution (LdSpace L))
      (fun z : LdSpace L => LdSpace.seed z) (chiIndex L),
    uniformDistribution_map_ldSeed, uniformDistribution_map_chiIndex]

/-! ## The mass of a coordinate-index event -/

/-- Every coordinate-index event of a line conditioning map that keeps the
shared scalar coordinate carries mass `1 / m`.  This is the equal-weight
statement behind blueprint `lem:restricted-line-mixture-bounds`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1049-1051`. -/
theorem clDistribution_seedEvent_mass (L : LdParams) (i : Fin L.m)
    (CL : LdSpace L → LdSpace L)
    (hseed : ∀ z : LdSpace L, (CL z).seed = z.seed) :
    ∑ sample ∈
        (clDistribution CL (ldPointCL L)).support.filter
          (restrictedLineSeedEvent L i),
      (clDistribution CL (ldPointCL L)).weight sample = 1 / (L.m : ℝ) := by
  classical
  haveI : Nonempty (Fin L.m) :=
    Fin.pos_iff_nonempty.mp (lt_of_lt_of_le Nat.zero_lt_one L.hm)
  rw [Distribution.sum_filter_weight_eq_avgOver]
  unfold clDistribution
  rw [Distribution.avgOver_map]
  have hpoint : ∀ z : LdSpace L,
      (if restrictedLineSeedEvent L i (CL z, ldPointCL L z) then (1 : ℝ)
        else 0) = if chiIndex L z.seed = i then 1 else 0 := by
    intro z
    by_cases h : chiIndex L z.seed = i
    · rw [if_pos h, if_pos]
      change chiIndex L (LdSpace.seed (CL z)) = i
      rw [hseed z]
      exact h
    · rw [if_neg h, if_neg]
      change ¬ chiIndex L (LdSpace.seed (CL z)) = i
      rw [hseed z]
      exact h
  rw [avgOver_congr _ _ _ hpoint,
    show (fun z : LdSpace L => if chiIndex L z.seed = i then (1 : ℝ) else 0) =
        fun z : LdSpace L => (fun j : Fin L.m => if j = i then (1 : ℝ) else 0)
          (chiIndex L z.seed) from rfl,
    ← Distribution.avgOver_map (uniformDistribution (LdSpace L))
      (fun z : LdSpace L => chiIndex L z.seed)
      (fun j : Fin L.m => if j = i then (1 : ℝ) else 0),
    uniformDistribution_map_chiIndex_ldSeed]
  unfold avgOver
  simp [uniformDistribution_weight_apply, mul_ite]

/-! ## The two source mixture identities -/

/-- The axis-parallel line-point law is the uniform mixture of its
coordinate-index restrictions.  This is the axis half of
blueprint `lem:restricted-line-mixture-bounds`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1049-1051`. -/
theorem aLinePointDist_eq_bind_restricted (L : LdParams) :
    aLinePointDist L =
      Distribution.bind (uniformDistribution (Fin L.m))
        (restrictedALineDist L) := by
  classical
  haveI : Nonempty (Fin L.m) :=
    Fin.pos_iff_nonempty.mp (lt_of_lt_of_le Nat.zero_lt_one L.hm)
  have hmix := Distribution.bind_uniform_restrict_eq
    (clDistribution (ldALineCL L) (ldPointCL L))
    (restrictedLineSeedEvent L) (restrictedALineSeedEvent_positive L)
    (fun i => by
      rw [clDistribution_seedEvent_mass L i (ldALineCL L) fun _ => rfl,
        Fintype.card_fin])
    (fun sample => ⟨chiIndex L (LdSpace.seed sample.1), rfl, fun i hi => hi.symm⟩)
  rw [aLinePointDist, ← hmix, Distribution.bind_map]
  rfl

/-- The diagonal line-point law is the uniform mixture of its coordinate-index
restrictions.  This is the diagonal half of
blueprint `lem:restricted-line-mixture-bounds`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1049-1051`. -/
theorem dLinePointDist_eq_bind_restricted (L : LdParams) :
    dLinePointDist L =
      Distribution.bind (uniformDistribution (Fin L.m))
        (restrictedDLineDist L) := by
  classical
  haveI : Nonempty (Fin L.m) :=
    Fin.pos_iff_nonempty.mp (lt_of_lt_of_le Nat.zero_lt_one L.hm)
  have hmix := Distribution.bind_uniform_restrict_eq
    (clDistribution (ldDLineCL L) (ldPointCL L))
    (restrictedLineSeedEvent L) (restrictedDLineSeedEvent_positive L)
    (fun i => by
      rw [clDistribution_seedEvent_mass L i (ldDLineCL L) fun _ => rfl,
        Fintype.card_fin])
    (fun sample => ⟨chiIndex L (LdSpace.seed sample.1), rfl, fun i hi => hi.symm⟩)
  rw [dLinePointDist, ← hmix, Distribution.bind_map]
  rfl

end

end MIPStarRE.QPBT
