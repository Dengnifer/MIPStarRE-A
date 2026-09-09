import MIPStarRE.QPBT.Combining.DirectLowDegree.ResampledCoefficientConsistency

/-!
# Extended direct coefficient-collision loss

This module compares the sum of the axis and diagonal coefficient-collision
losses at the extended directly indexed parameters with the original `m*d/q`
ratio.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:331-344`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1595-1603`
-/

namespace MIPStarRE.QPBT

/-- The axis loss `d/q` plus the diagonal loss `(2m+2)d/q` at the extended
direct parameters is at most five times the original loss `md/q`.

This is a Lean-only scalar auxiliary for combining the two coefficient-POVM
consistency estimates. It uses only admissibility of the original parameters. -/
theorem extendedDirectLd_coefficientCollisionLoss_le_five_mul
    (P : AdmissibleParams) :
    ((P.extendedDirectLd.d : ℝ) +
        (P.extendedDirectLd.m * P.extendedDirectLd.d : ℝ)) /
        (P.extendedDirectLd.q : ℝ) ≤
      5 * ((P.m * P.d : ℝ) / (P.q : ℝ)) := by
  have hm : (1 : ℝ) ≤ (P.m : ℝ) := by
    exact_mod_cast P.one_le_m
  have hqNat : 0 < P.q := by
    rcases P.hq with ⟨k, _, hk⟩
    rw [hk]
    exact Nat.pow_pos (by decide)
  have hq : (0 : ℝ) < (P.q : ℝ) := by
    exact_mod_cast hqNat
  change ((P.d : ℝ) + ((2 * P.m + 2 : ℕ) : ℝ) * (P.d : ℝ)) /
      (P.q : ℝ) ≤ 5 * ((P.m : ℝ) * (P.d : ℝ) / (P.q : ℝ))
  push_cast
  rw [show 5 * ((P.m : ℝ) * (P.d : ℝ) / (P.q : ℝ)) =
    (5 * ((P.m : ℝ) * (P.d : ℝ))) / (P.q : ℝ) by ring]
  apply (div_le_div_iff_of_pos_right hq).2
  nlinarith [show (0 : ℝ) ≤ (P.d : ℝ) by positivity]

end MIPStarRE.QPBT
