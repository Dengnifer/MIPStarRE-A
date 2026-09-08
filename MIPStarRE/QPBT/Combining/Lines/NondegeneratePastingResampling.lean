import MIPStarRE.QPBT.Combining.Lines.MixedResampling
import MIPStarRE.QPBT.Combining.Lines.NondegeneratePastingDistribution

/-!
# Nondegenerate pasting parameter resampling

This module shows that resampling the point on the first, nondegenerate line
preserves the proof-only conditioned pasting question law.

## References

The resampling supports the Schwartz-Zippel step in `lem:qld-xz-lines`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-955`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

private theorem avgOver_restrict_eq {α : Type*} [DecidableEq α]
    (μ : Distribution α) (p : α → Prop) [DecidablePred p]
    (hpos : 0 < ∑ a ∈ μ.support.filter p, μ.weight a) (g : α → ℝ) :
    avgOver (Distribution.restrict μ p hpos) g =
      avgOver μ (fun a => if p a then g a else 0) /
        ∑ a ∈ μ.support.filter p, μ.weight a := by
  classical
  unfold avgOver Distribution.restrict
  change (∑ a ∈ μ.support.filter p,
      (if p a then μ.weight a / _ else 0) * g a) =
    (∑ a ∈ μ.support, μ.weight a * (if p a then g a else 0)) / _
  rw [Finset.sum_div, Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro a _
  by_cases hp : p a
  · simp [hp]
    ring
  · simp [hp]

/-- Uniformly resampling the point on the conditioned X line preserves every
scalar average under the nondegenerate pasting law. The line descriptor is
unchanged, so the nonzero-direction event is preserved exactly. -/
theorem avgOver_nondegenerateLinePastingDist_resample_parameter (L : LdParams)
    (value : (((LineDesc L × LineDesc L) ×
      (LineDesc L × (Fin L.m → ScalarQ L))) ×
        (LineDesc L × (Fin L.m → ScalarQ L))) → ℝ) :
    avgOver (nondegenerateLinePastingDist L) value =
      avgOver (nondegenerateLinePastingDist L) (fun sample =>
        avgOver (uniformDistribution (ScalarQ L)) (fun param =>
          value (sample.1, (sample.2.1,
            sample.2.1.base + param • sample.2.1.direction)))) := by
  classical
  unfold nondegenerateLinePastingDist
  simp only [Distribution.avgOver_map]
  rw [avgOver_restrict_eq, avgOver_restrict_eq]
  congr 1
  rw [avgOver_prod, avgOver_prod]
  calc
    avgOver (linePointDist L) (fun first => avgOver (linePointDist L) (fun second =>
        if first.1.direction ≠ 0 then
          value (((first.1, second.1), second), first) else 0)) =
      avgOver (linePointDist L) (fun first =>
        avgOver (uniformDistribution (ScalarQ L)) (fun param =>
          avgOver (linePointDist L) (fun second =>
            if first.1.direction ≠ 0 then
              value (((first.1, second.1), second),
                (first.1, first.1.base + param • first.1.direction)) else 0))) :=
      avgOver_linePointDist_resample_parameter L _
    _ = avgOver (linePointDist L) (fun first =>
        avgOver (linePointDist L) (fun second =>
          if first.1.direction ≠ 0 then
            avgOver (uniformDistribution (ScalarQ L)) (fun param =>
              value (((first.1, second.1), second),
                (first.1, first.1.base + param • first.1.direction))) else 0)) := by
      apply avgOver_congr
      intro first
      by_cases hdir : first.1.direction ≠ 0
      · simp only [if_pos hdir]
        rw [avgOver_comm]
      · simp [hdir, avgOver_const_of_isProbability _
          (uniformDistribution_isProbability _)]

end

end MIPStarRE.QPBT
