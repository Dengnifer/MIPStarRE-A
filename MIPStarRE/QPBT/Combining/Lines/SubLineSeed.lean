import MIPStarRE.QPBT.Combining.Lines.SubLineBind

/-!
# The two independent blocks of a fresh diagonal direction pair

This module splits the fresh diagonal direction pair of the sub-line sampling
procedure into its two independent blocks.  The coordinate-index event
constrains only the scalar seed of the pair, so conditioning on it leaves the
direction block uniform and independent of the conditioned seed.  The
direction block of a fresh pair is therefore available as an unconstrained
uniform vector, which is what allows the sampling procedure to read it off the
corresponding block of the direction of the sampled extended line.

## References

The block decomposition supports `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The coordinate-index event is that of `def:ith-restricted-line`, blueprint
lines 1209--1228, paper lines 1038--1048.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

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

/-! ## The coordinate-index event on a scalar seed -/

/-- The coordinate-index event of `def:ith-restricted-line` read on a scalar
seed alone.  Blueprint `def:ith-restricted-line`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1038-1048`. -/
def ldSeedIndexEvent (L : LdParams) (i : Fin L.m) (s : ScalarQ L) : Prop :=
  chiIndex L s = i

/-- Decidability of the coordinate-index event on a scalar seed. -/
instance ldSeedIndexEvent_decidablePred (L : LdParams) (i : Fin L.m) :
    DecidablePred (ldSeedIndexEvent L i) := by
  intro s
  unfold ldSeedIndexEvent
  infer_instance

/-- Every coordinate-index event of a scalar seed has positive mass under the
uniform law.  Blueprint `def:ith-restricted-line`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1038-1048`. -/
theorem ldSeedIndexEvent_positive (L : LdParams) (i : Fin L.m) :
    0 < ∑ s ∈ (uniformDistribution (ScalarQ L)).support.filter
        (ldSeedIndexEvent L i),
      (uniformDistribution (ScalarQ L)).weight s := by
  classical
  refine Finset.sum_pos'
    (fun a _ => (uniformDistribution (ScalarQ L)).nonnegative a)
    ⟨seedOfIndexResidue L i ⟨0, L.seedFiberCard_pos⟩,
      Finset.mem_filter.mpr ⟨by simp, ?_⟩, ?_⟩
  · change chiIndex L (seedOfIndexResidue L i ⟨0, L.seedFiberCard_pos⟩) = i
    exact chiIndex_seedOfIndexResidue L i _
  · simp only [uniformDistribution, Distribution.uniformOnFinset_weight,
      Finset.mem_univ, if_true]
    positivity

/-! ## The blocks of a fresh diagonal direction pair -/

/-- A fresh diagonal direction pair at coordinate index `i` is a scalar seed
conditioned on the coordinate-index fiber of `i` together with an independent
uniform direction block.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem freshDiagonalPairDist_eq_prod (L : LdParams) (i : Fin L.m) :
    freshDiagonalPairDist L i =
      Distribution.prod
        (Distribution.restrict (uniformDistribution (ScalarQ L))
          (ldSeedIndexEvent L i) (ldSeedIndexEvent_positive L i))
        (uniformDistribution (Fin L.m → ScalarQ L)) := by
  classical
  unfold freshDiagonalPairDist
  exact restrict_uniform_prod_fst (ldSeedIndexEvent L i)
    (ldSeedIndexEvent_positive L i) (ldSeedDirEvent_positive L i)

/-- The direction block of a fresh diagonal direction pair is uniform.
Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem freshDiagonalPairDist_map_snd (L : LdParams) (i : Fin L.m) :
    (freshDiagonalPairDist L i).map Prod.snd =
      uniformDistribution (Fin L.m → ScalarQ L) := by
  classical
  rw [freshDiagonalPairDist_eq_prod]
  refine Distribution.ext_of_support_of_weight ?_ ?_
  · change (((uniformDistribution (ScalarQ L)).support.filter
        (ldSeedIndexEvent L i)) ×ˢ
        (Finset.univ : Finset (Fin L.m → ScalarQ L))).image Prod.snd =
      (Finset.univ : Finset (Fin L.m → ScalarQ L))
    ext v
    simp only [Finset.mem_image, Finset.mem_univ, iff_true, Prod.exists]
    exact ⟨seedOfIndexResidue L i ⟨0, L.seedFiberCard_pos⟩, v,
      Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨by simp, chiIndex_seedOfIndexResidue L i _⟩,
          Finset.mem_univ v⟩, rfl⟩
  · funext v
    have hprob := Distribution.restrict_isProbability
      (uniformDistribution (ScalarQ L)) (ldSeedIndexEvent L i)
      (ldSeedIndexEvent_positive L i)
    change (∑ w ∈ (((uniformDistribution (ScalarQ L)).support.filter
        (ldSeedIndexEvent L i)) ×ˢ
        (Finset.univ : Finset (Fin L.m → ScalarQ L))).filter
          (fun w => w.2 = v),
        (Distribution.restrict (uniformDistribution (ScalarQ L))
            (ldSeedIndexEvent L i) (ldSeedIndexEvent_positive L i)).weight w.1 *
          (uniformDistribution (Fin L.m → ScalarQ L)).weight w.2) =
      (uniformDistribution (Fin L.m → ScalarQ L)).weight v
    have hfilter : ((((uniformDistribution (ScalarQ L)).support.filter
        (ldSeedIndexEvent L i)) ×ˢ
        (Finset.univ : Finset (Fin L.m → ScalarQ L))).filter
          (fun w => w.2 = v)) =
        ((uniformDistribution (ScalarQ L)).support.filter
          (ldSeedIndexEvent L i)) ×ˢ ({v} : Finset (Fin L.m → ScalarQ L)) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
        Finset.mem_singleton]
      tauto
    rw [hfilter, Finset.sum_product]
    simp only [Finset.sum_singleton]
    have hsum : (∑ s ∈ (uniformDistribution (ScalarQ L)).support.filter
        (ldSeedIndexEvent L i),
        (Distribution.restrict (uniformDistribution (ScalarQ L))
          (ldSeedIndexEvent L i) (ldSeedIndexEvent_positive L i)).weight s)
        = 1 := hprob.weight_sum_eq_one
    rw [← Finset.sum_mul, hsum, one_mul]

end

end MIPStarRE.QPBT
