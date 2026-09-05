import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.DiagonalRecursion

/-!
# Pass conversion for the directly indexed low-degree game

This module converts a value bound for a projective strategy of the directly
indexed low-degree game into the hypothesis of the low individual degree
theorem for each coordinate strategy `directCoordinateProjStrat`.

The LDT failure probability gives weight `1/3` to point agreement and
`1/6` to each of the four oriented line-versus-point checks.  The branch
comparisons of `Transport.BranchComparison` and `Transport.DiagonalRecursion`
bound the point and axis-line branches by the corresponding direct branch
rejections and each diagonal branch by twice its direct branch rejection.  The
factor-three rejection calculus of `GameValue` gives the line branches half the
weight of the point branch, so the factor two is absorbed: a direct strategy of
value at least `1 - ε` has coordinate strategies of LDT failure at most
`3 * ε`, which is exactly `PassesLowIndividualDegreeTest (3 * ε)`.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:214-458`
- `references/ldt-paper/test_definition.tex:130-151`
- Blueprint `def:ld-question-distribution`, `lem:ld-aline-level`,
  `lem:ld-dline-level`, `lem:ld-question-typed-cl`, `lem:alnf`, `lem:dlnf`,
  `def:ld-win-predicate`, `rem:ld-win-zero-direction`, and `def:ld-meas`
- `MIPStarRE/LDT/Test/StrategyFailures.lean:18-130`
- `MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean:300-311`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.Quantum

noncomputable section

/-! ## The failure comparison and the pass hypothesis -/

private theorem sum_ldType (f : LdType → ℝ) :
    ∑ t : LdType, f t = f .point + f .aline + f .dline := by
  change (Finset.univ : Finset LdType).sum f = _
  rw [show (Finset.univ : Finset LdType) = {.point, .aline, .dline} by decide]
  simp [add_assoc]

/-- The uniformly weighted rejection is one ninth of the sum over the nine
ordered type pairs. -/
private theorem directLdRejectionProbability_eq_sum (D : DirectLdParams)
    (S : Strategy (directLdGame D)) :
    directLdRejectionProbability D S =
      (∑ types : LdType × LdType, directLdBranchRejectionProbability D S types) / 9 := by
  unfold directLdRejectionProbability
  rw [avgOver_uniform_eq_inv_card_mul_sum, Fintype.card_prod,
    show Fintype.card LdType = 3 by decide, div_eq_inv_mul]
  norm_num

/-- Failure of the coordinate strategy compared with the LDT-weighted
rejection of the direct game.  The point and axis-line branches are dominated
termwise, while each diagonal branch is dominated up to the factor two of the
leading-index rereading; the surplus is the extra half weight of the diagonal
branches.  The bare inequality against `directLdLdtWeightedFailureProbability`
fails for index-sensitive strategies that answer the canonical question of
a direction badly and the non-canonical questions of the same geometric line
well, so the surplus term is not an artifact of the proof. -/
theorem directCoordinate_failure_le_weightedFailure
    (D : DirectLdParams) (S : Strategy (directLdGame D))
    (hS : S.IsProjective) (r : Fin D.k) :
    letI := D.toLDTFieldModel
    (directCoordinateProjStrat D S hS r).lowIndividualDegreeFailureProbability ≤
      directLdLdtWeightedFailureProbability D S +
        (directLdBranchRejectionProbability D S (.dline, .point) +
          directLdBranchRejectionProbability D S (.point, .dline)) / 6 := by
  letI := D.toLDTFieldModel
  rw [ProjStrat.lowIndividualDegreeFailureProbability_eq_role_averages]
  unfold ProjStrat.axisParallelRoleAverage ProjStrat.diagonalRoleAverage
    directLdLdtWeightedFailureProbability
  dsimp only
  have h1 := directCoordinate_axis_line_point_le D S hS r
  have h2 := directCoordinate_axis_point_line_le D S hS r
  have h3 := directCoordinate_point_agreement_le D S hS r
  have h4 := directCoordinate_diagonal_line_point_le D S hS r
  have h5 := directCoordinate_diagonal_point_line_le D S hS r
  linarith

/-- Failure of the coordinate strategy is at most three times the uniformly
weighted rejection of the direct game. -/
theorem directCoordinate_failure_le_three_mul_rejection
    (D : DirectLdParams) (S : Strategy (directLdGame D))
    (hS : S.IsProjective) (r : Fin D.k) :
    letI := D.toLDTFieldModel
    (directCoordinateProjStrat D S hS r).lowIndividualDegreeFailureProbability ≤
      3 * directLdRejectionProbability D S := by
  letI := D.toLDTFieldModel
  have h := directCoordinate_failure_le_weightedFailure D S hS r
  unfold directLdLdtWeightedFailureProbability at h
  dsimp only at h
  rw [directLdRejectionProbability_eq_sum, Fintype.sum_prod_type]
  simp only [sum_ldType]
  have hnonneg := directLdBranchRejectionProbability_nonneg D S
  have hpp := hnonneg (.point, .point)
  have hpa := hnonneg (.point, .aline)
  have hpd := hnonneg (.point, .dline)
  have hap := hnonneg (.aline, .point)
  have haa := hnonneg (.aline, .aline)
  have had := hnonneg (.aline, .dline)
  have hdp := hnonneg (.dline, .point)
  have hda := hnonneg (.dline, .aline)
  have hdd := hnonneg (.dline, .dline)
  linarith

/-- The error passed to the low individual degree theorem is nonnegative:
the direct value never exceeds one. -/
theorem directLd_error_nonneg_of_value (D : DirectLdParams)
    (S : Strategy (directLdGame D)) (ε : ℝ) (hwin : 1 - ε ≤ S.value) :
    0 ≤ ε := by
  have h0 : 0 ≤ directLdRejectionProbability D S :=
    avgOver_nonneg _ _ fun types => directLdBranchRejectionProbability_nonneg D S types
  rw [directLdRejectionProbability_eq_one_sub_value] at h0
  linarith

/-- The error `3 * ε` passed to the low individual degree theorem is
nonnegative. -/
theorem directCoordinate_three_mul_error_nonneg (D : DirectLdParams)
    (S : Strategy (directLdGame D)) (ε : ℝ) (hwin : 1 - ε ≤ S.value) :
    0 ≤ 3 * ε := by
  have := directLd_error_nonneg_of_value D S ε hwin
  linarith

/-- A direct strategy of value at least `1 - ε` has coordinate strategies of
low individual degree failure at most `3 * ε`. -/
theorem directCoordinate_failure_le_three_mul_error
    (D : DirectLdParams) (S : Strategy (directLdGame D))
    (hS : S.IsProjective) (r : Fin D.k) (ε : ℝ) (hwin : 1 - ε ≤ S.value) :
    letI := D.toLDTFieldModel
    (directCoordinateProjStrat D S hS r).lowIndividualDegreeFailureProbability ≤
      3 * ε := by
  letI := D.toLDTFieldModel
  have hrej : directLdRejectionProbability D S ≤ ε := by
    rw [directLdRejectionProbability_eq_one_sub_value]
    linarith
  calc
    (directCoordinateProjStrat D S hS r).lowIndividualDegreeFailureProbability ≤
        3 * directLdRejectionProbability D S :=
      directCoordinate_failure_le_three_mul_rejection D S hS r
    _ ≤ 3 * ε := by linarith

/-- The pass hypothesis of the low individual degree theorem for every
coordinate of a direct strategy of value at least `1 - ε`, with error
`3 * ε` and no further assumption. -/
theorem directCoordinate_passes
    (D : DirectLdParams) (S : Strategy (directLdGame D))
    (hS : S.IsProjective) (r : Fin D.k) (ε : ℝ) (hwin : 1 - ε ≤ S.value) :
    letI := D.toLDTFieldModel
    (directCoordinateProjStrat D S hS r).PassesLowIndividualDegreeTest (3 * ε) := by
  letI := D.toLDTFieldModel
  exact ⟨directCoordinate_failure_le_three_mul_error D S hS r ε hwin⟩

end

end MIPStarRE.QPBT
