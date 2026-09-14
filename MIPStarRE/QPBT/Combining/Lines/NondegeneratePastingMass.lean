import MIPStarRE.QPBT.Combining.Lines.RestrictedAverage
import MIPStarRE.QPBT.Combining.Lines.ZeroDirectionMass

/-!
# Retained mass for nondegenerate-line pasting

This module defines the mass retained when the first line in the product
line-point law is restricted to nonzero direction and proves uniform lower and
upper bounds for that mass.

## References

The restriction is the proof-only conditioning used in `lem:qld-xz-lines`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-963`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-- Probability retained by the proof-only first-line nondegeneracy
restriction in the pasting argument for `lem:qld-xz-lines`. -/
def nondegenerateLinePastingMass (L : LdParams) : ℝ :=
  ∑ samples ∈
      (Distribution.prod (linePointDist L) (linePointDist L)).support.filter
        (fun samples => samples.1.1.direction ≠ 0),
    (Distribution.prod (linePointDist L) (linePointDist L)).weight samples

/-- The retained product-law mass lies between one half and one. -/
theorem nondegenerateLinePastingMass_bounds (L : LdParams) :
    1 / 2 ≤ nondegenerateLinePastingMass L ∧
      nondegenerateLinePastingMass L ≤ 1 := by
  classical
  let indicator := fun sample : LineDesc L × (Fin L.m → ScalarQ L) =>
    if sample.1.direction ≠ 0 then (1 : ℝ) else 0
  have hmass : nondegenerateLinePastingMass L =
      avgOver (linePointDist L) indicator := by
    unfold nondegenerateLinePastingMass
    rw [Distribution.sum_filter_weight_eq_avgOver,
      SandwichProduct.avgOver_distribution_prod]
    change avgOver (linePointDist L) (fun sample =>
      avgOver (linePointDist L) (fun _ => indicator sample)) = _
    simp_rw [avgOver_const_of_isProbability _ (linePointDist_isProbability L)]
  have haxis : avgOver (aLinePointDist L) indicator = 1 := by
    have hindicator : indicator = fun sample =>
        1 - if sample.1.direction = 0 then (1 : ℝ) else 0 := by
      funext sample
      by_cases hzero : sample.1.direction = 0 <;> simp [indicator, hzero]
    rw [hindicator, avgOver_sub,
      avgOver_const_of_isProbability _ (aLinePointDist_isProbability L),
      aLinePointDist_zero_direction_mass]
    norm_num
  have hdiag : 0 ≤ avgOver (dLinePointDist L) indicator :=
    avgOver_nonneg _ _ fun sample => by
      by_cases hzero : sample.1.direction = 0 <;> simp [indicator, hzero]
  have hlower : 1 / 2 ≤ avgOver (linePointDist L) indicator := by
    rw [linePointDist, avgOver_mix, haxis]
    norm_num
    linarith
  rw [hmass]
  refine ⟨hlower, ?_⟩
  calc
    avgOver (linePointDist L) indicator ≤
      avgOver (linePointDist L) (fun _ => 1) :=
      avgOver_mono _ _ _ fun sample => by
        by_cases hzero : sample.1.direction = 0 <;> simp [indicator, hzero]
    _ = 1 := avgOver_const_of_isProbability _ (linePointDist_isProbability L) 1

end

end MIPStarRE.QPBT
