import MIPStarRE.QPBT.Combining.DirectLowDegree.GameValue

/-! # Probability bounds for the directly indexed low-degree game

This module records two elementary probability bounds needed when a caller caps an
assembled direct-game rejection estimate by one. The results are formalization-only
support: they do not bound any individual game branch or prove a passing-value theorem.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:178-186`
- Parent issue #119 and arithmetic issue #333
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

namespace Strategy

/-- Every tensor-product strategy has nonnegative value. -/
theorem value_nonneg {G : Game} (S : Strategy G) : 0 ≤ S.value := by
  unfold value
  apply avgOver_nonneg
  intro questions
  apply Finset.sum_nonneg
  intro answerA _
  apply Finset.sum_nonneg
  intro answerB _
  split
  · exact outcomeWeight_nonneg S questions.1 questions.2 answerA answerB
  · exact le_rfl

end Strategy

/-- The total rejection probability of a directly indexed low-degree strategy is at
most one. This is the probability cap used by scalar error envelopes; it gives no
quantitative branch estimate. -/
theorem directLdRejectionProbability_le_one
    (D : DirectLdParams) (S : Strategy (directLdGame D)) :
    directLdRejectionProbability D S ≤ 1 := by
  rw [directLdRejectionProbability_eq_one_sub_value]
  linarith [S.value_nonneg]

end MIPStarRE.QPBT
