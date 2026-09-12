import MIPStarRE.QPBT.Combining.Lines.RestrictedMixture
import MIPStarRE.QPBT.Combining.Witnesses
import MIPStarRE.QPBT.Games.DistributionAverage

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
  rw [avgOver_prod, avgOver_prod]
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
