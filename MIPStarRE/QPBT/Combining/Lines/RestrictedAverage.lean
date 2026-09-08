import MIPStarRE.QPBT.Combining.Lines.RestrictedMixture
import MIPStarRE.QPBT.Combining.Witnesses

/-!
# Error inflation of restricted line-point averages

This module records how a nonnegative average over the line-point distribution
transfers to one restricted component.  The line-point law places weight
`1 / 2` on each of its two kinds and, inside each kind, weight `1 / m` on each
coordinate index, so every restricted component carries mixture weight
`1 / (2 m)` and a nonnegative average inflates by at most `2 m`.

## References

The estimates are items 1 and 2 of blueprint
`lem:restricted-line-mixture-bounds`, formalizing the unlabelled estimates at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1052-1058`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement

noncomputable section

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

/-! ## Inflation of a restricted line-point average -/

/-- Restricting a nonnegative line-point average to one kind and one coordinate
index inflates it by at most `2 m`.  This is the pointwise form of item 1 of
blueprint `lem:restricted-line-mixture-bounds`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1052-1056`. -/
theorem avgOver_restrictedLinePointDist_le {P : AdmissibleParams}
    (f : (LineDesc P.toLdParams × (Fin P.m → PauliScalar P)) → ℝ)
    (hf : ∀ sample, 0 ≤ f sample) (kind : LineKind) (i : Fin P.m) :
    avgOver (restrictedLinePointDist P kind i) f ≤
      2 * (P.m : ℝ) * avgOver (linePointDist P.toLdParams) f := by
  classical
  haveI : Nonempty (Fin P.m) :=
    Fin.pos_iff_nonempty.mp (lt_of_lt_of_le Nat.zero_lt_one P.one_le_m)
  have hm : (0 : ℝ) < (P.m : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one P.one_le_m
  have hAnonneg : 0 ≤ avgOver (aLinePointDist P.toLdParams) f :=
    avgOver_nonneg _ _ hf
  have hDnonneg : 0 ≤ avgOver (dLinePointDist P.toLdParams) f :=
    avgOver_nonneg _ _ hf
  have hmixture : avgOver (linePointDist P.toLdParams) f =
      1 / 2 * avgOver (aLinePointDist P.toLdParams) f +
        (1 - 1 / 2) * avgOver (dLinePointDist P.toLdParams) f :=
    avgOver_mix _ _ _ _ _ f
  -- Each kind is bounded by twice the full line-point average.
  have hsum : 2 * avgOver (linePointDist P.toLdParams) f =
      avgOver (aLinePointDist P.toLdParams) f +
        avgOver (dLinePointDist P.toLdParams) f := by
    rw [hmixture]
    ring
  have hAle : avgOver (aLinePointDist P.toLdParams) f ≤
      2 * avgOver (linePointDist P.toLdParams) f := by
    rw [hsum]
    exact le_add_of_nonneg_right hDnonneg
  have hDle : avgOver (dLinePointDist P.toLdParams) f ≤
      2 * avgOver (linePointDist P.toLdParams) f := by
    rw [hsum]
    exact le_add_of_nonneg_left hAnonneg
  -- The coordinate index contributes a further factor `m`.
  have hcomponent : ∀ (ν : Fin P.m → Distribution (LineDesc P.toLdParams ×
      (Fin P.m → PauliScalar P))) (μ : Distribution (LineDesc P.toLdParams ×
      (Fin P.m → PauliScalar P))),
      μ = Distribution.bind (uniformDistribution (Fin P.m)) ν →
      avgOver μ f ≤ 2 * avgOver (linePointDist P.toLdParams) f →
      avgOver (ν i) f ≤ 2 * (P.m : ℝ) * avgOver (linePointDist P.toLdParams) f := by
    intro ν μ hbind hle
    have hcomp := avgOver_bind_uniform_component_le ν f hf i
    rw [Fintype.card_fin, ← hbind] at hcomp
    have hstep : avgOver (ν i) f ≤ (P.m : ℝ) * avgOver μ f := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hm] at hcomp
      rw [mul_comm]
      exact hcomp
    calc avgOver (ν i) f ≤ (P.m : ℝ) * avgOver μ f := hstep
      _ ≤ (P.m : ℝ) * (2 * avgOver (linePointDist P.toLdParams) f) := by
          exact mul_le_mul_of_nonneg_left hle (le_of_lt hm)
      _ = 2 * (P.m : ℝ) * avgOver (linePointDist P.toLdParams) f := by ring
  cases kind with
  | axis =>
      exact hcomponent (restrictedALineDist P.toLdParams) _
        (aLinePointDist_eq_bind_restricted P.toLdParams) hAle
  | diagonal =>
      exact hcomponent (restrictedDLineDist P.toLdParams) _
        (dLinePointDist_eq_bind_restricted P.toLdParams) hDle

/-- Restricting a nonnegative average over two independent line-point samples
to one kind and coordinate index in each factor inflates it by at most
`4 m ^ 2`.  This is the pointwise form of item 2 of
blueprint `lem:restricted-line-mixture-bounds`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1056-1058`. -/
theorem avgOver_prod_restrictedLinePointDist_le {P : AdmissibleParams}
    (f : ((LineDesc P.toLdParams × (Fin P.m → PauliScalar P)) ×
      (LineDesc P.toLdParams × (Fin P.m → PauliScalar P))) → ℝ)
    (hf : ∀ sample, 0 ≤ f sample) (kindX kindZ : LineKind) (i j : Fin P.m) :
    avgOver (Distribution.prod (restrictedLinePointDist P kindX i)
        (restrictedLinePointDist P kindZ j)) f ≤
      4 * (P.m : ℝ) ^ 2 * avgOver (Distribution.prod
        (linePointDist P.toLdParams) (linePointDist P.toLdParams)) f := by
  classical
  have hfactor : (0 : ℝ) ≤ 2 * (P.m : ℝ) := by positivity
  rw [SandwichProduct.avgOver_distribution_prod,
    SandwichProduct.avgOver_distribution_prod]
  have hinner : ∀ s1 : LineDesc P.toLdParams × (Fin P.m → PauliScalar P),
      avgOver (restrictedLinePointDist P kindZ j) (fun s2 => f (s1, s2)) ≤
        2 * (P.m : ℝ) *
          avgOver (linePointDist P.toLdParams) (fun s2 => f (s1, s2)) :=
    fun s1 => avgOver_restrictedLinePointDist_le
      (fun s2 => f (s1, s2)) (fun s2 => hf (s1, s2)) kindZ j
  calc avgOver (restrictedLinePointDist P kindX i)
        (fun s1 => avgOver (restrictedLinePointDist P kindZ j)
          (fun s2 => f (s1, s2)))
      ≤ avgOver (restrictedLinePointDist P kindX i)
          (fun s1 => 2 * (P.m : ℝ) *
            avgOver (linePointDist P.toLdParams) (fun s2 => f (s1, s2))) :=
        avgOver_mono _ _ _ hinner
    _ = 2 * (P.m : ℝ) * avgOver (restrictedLinePointDist P kindX i)
          (fun s1 => avgOver (linePointDist P.toLdParams)
            (fun s2 => f (s1, s2))) := avgOver_const_mul _ _ _
    _ ≤ 2 * (P.m : ℝ) * (2 * (P.m : ℝ) *
          avgOver (linePointDist P.toLdParams)
            (fun s1 => avgOver (linePointDist P.toLdParams)
              (fun s2 => f (s1, s2)))) := by
        refine mul_le_mul_of_nonneg_left ?_ hfactor
        exact avgOver_restrictedLinePointDist_le
          (fun s1 => avgOver (linePointDist P.toLdParams)
            (fun s2 => f (s1, s2)))
          (fun s1 => avgOver_nonneg _ _ fun s2 => hf (s1, s2)) kindX i
    _ = 4 * (P.m : ℝ) ^ 2 * avgOver (linePointDist P.toLdParams)
          (fun s1 => avgOver (linePointDist P.toLdParams)
            (fun s2 => f (s1, s2))) := by ring

end

end MIPStarRE.QPBT
