import MIPStarRE.QPBT.Combining.DirectLowDegree.Game
import MIPStarRE.LDT.Basic.DistributionAvg

/-!
# Rejection probabilities for the directly indexed low-degree game

This module compares the rejection probability of the directly indexed game
with the branch weights used by the low individual degree test.
All declarations below are formalization-only support derived from the game
value; none is a paper-labelled result.

## References

The uniform distribution on the three ordered question types is specified in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:178-186`,
and its verifier is specified in the same file at lines 320-392.  The three
equal outer weights of the low individual degree test and its uniform role
choices are specified in `references/ldt-paper/test_definition.tex:10-67`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.Quantum

noncomputable section

private theorem directLdAccepted_add_rejected_eq_one
    (D : DirectLdParams) (S : Strategy (directLdGame D))
    (types : LdType × LdType) (sample : DirectLdSpace D) :
    (∑ a : (directLdGame D).AnswerA, ∑ b : (directLdGame D).AnswerB,
        if directLdWinPredicate D
            (types.1, directLdMap D types.1 sample)
            (types.2, directLdMap D types.2 sample) a b then
          outcomeWeight S
            (types.1, directLdMap D types.1 sample)
            (types.2, directLdMap D types.2 sample) a b
        else 0) +
      (∑ a : (directLdGame D).AnswerA, ∑ b : (directLdGame D).AnswerB,
        if directLdWinPredicate D
            (types.1, directLdMap D types.1 sample)
            (types.2, directLdMap D types.2 sample) a b then
          0
        else outcomeWeight S
          (types.1, directLdMap D types.1 sample)
          (types.2, directLdMap D types.2 sample) a b) = 1 := by
  calc
    _ = ∑ a : (directLdGame D).AnswerA, ∑ b : (directLdGame D).AnswerB,
        outcomeWeight S
          (types.1, directLdMap D types.1 sample)
          (types.2, directLdMap D types.2 sample) a b := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b _
      by_cases h : directLdWinPredicate D
          (types.1, directLdMap D types.1 sample)
          (types.2, directLdMap D types.2 sample) a b
      · simp [h]
      · simp [h]
    _ = 1 := outcomeWeight_sum_eq_one S
      (types.1, directLdMap D types.1 sample)
      (types.2, directLdMap D types.2 sample)

/-- Rejection probability conditioned on an ordered pair of low-degree
question types, averaged over the common direct sample. -/
noncomputable def directLdBranchRejectionProbability
    (D : DirectLdParams) (S : Strategy (directLdGame D))
    (types : LdType × LdType) : ℝ :=
  avgOver (uniformDistribution (DirectLdSpace D)) fun sample =>
    ∑ a : (directLdGame D).AnswerA, ∑ b : (directLdGame D).AnswerB,
      if directLdWinPredicate D
          (types.1, directLdMap D types.1 sample)
          (types.2, directLdMap D types.2 sample) a b then
        0
      else outcomeWeight S
        (types.1, directLdMap D types.1 sample)
        (types.2, directLdMap D types.2 sample) a b

/-- Total rejection probability of the directly indexed low-degree game,
averaged uniformly over its nine ordered type branches. -/
noncomputable def directLdRejectionProbability
    (D : DirectLdParams) (S : Strategy (directLdGame D)) : ℝ :=
  avgOver (uniformDistribution (LdType × LdType))
    (directLdBranchRejectionProbability D S)

/-- The branch failure probability with the weights used by the low
individual degree test. -/
noncomputable def directLdLdtWeightedFailureProbability
    (D : DirectLdParams) (S : Strategy (directLdGame D)) : ℝ :=
  let B := directLdBranchRejectionProbability D S
  ((B (.aline, .point) + B (.point, .aline)) / 2 +
      B (.point, .point) +
      (B (.dline, .point) + B (.point, .dline)) / 2) / 3

/-- Formalization-only expansion of a sum over the three low-degree question
types, in point, axis-line, and diagonal-line order.  This supports the uniform
branch calculation for the game in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:178-186`. -/
theorem sum_ldType (f : LdType → ℝ) :
    ∑ t : LdType, f t = f .point + f .aline + f .dline := by
  change (Finset.univ : Finset LdType).sum f = _
  rw [show (Finset.univ : Finset LdType) = {.point, .aline, .dline} by decide]
  simp [add_assoc]

private theorem avgOver_ldType_pair (f : LdType × LdType → ℝ) :
    avgOver (uniformDistribution (LdType × LdType)) f =
      (f (.point, .point) + f (.point, .aline) + f (.point, .dline) +
        (f (.aline, .point) + f (.aline, .aline) + f (.aline, .dline)) +
        (f (.dline, .point) + f (.dline, .aline) + f (.dline, .dline))) / 9 := by
  unfold avgOver uniformDistribution Distribution.uniformOnFinset
  simp only [Finset.mem_univ, if_true, Finset.card_univ, Fintype.card_prod]
  rw [show Fintype.card LdType = 3 by decide]
  rw [Fintype.sum_prod_type]
  simp_rw [sum_ldType]
  ring

/-- Every fixed-type rejection probability is nonnegative. -/
theorem directLdBranchRejectionProbability_nonneg
    (D : DirectLdParams) (S : Strategy (directLdGame D))
    (types : LdType × LdType) :
    0 ≤ directLdBranchRejectionProbability D S types := by
  apply avgOver_nonneg
  intro sample
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro b _
  by_cases h : directLdWinPredicate D
      (types.1, directLdMap D types.1 sample)
      (types.2, directLdMap D types.2 sample) a b
  · simp [h]
  · simpa [h] using outcomeWeight_nonneg S
      (types.1, directLdMap D types.1 sample)
      (types.2, directLdMap D types.2 sample) a b

/-- Total direct-game rejection is one minus the strategy value. -/
theorem directLdRejectionProbability_eq_one_sub_value
    (D : DirectLdParams) (S : Strategy (directLdGame D)) :
    directLdRejectionProbability D S = 1 - S.value := by
  let accepted : (LdType × LdType) → DirectLdSpace D → ℝ :=
    fun types sample =>
      ∑ a : (directLdGame D).AnswerA, ∑ b : (directLdGame D).AnswerB,
        if directLdWinPredicate D
            (types.1, directLdMap D types.1 sample)
            (types.2, directLdMap D types.2 sample) a b then
          outcomeWeight S
            (types.1, directLdMap D types.1 sample)
            (types.2, directLdMap D types.2 sample) a b
        else 0
  have hbranch (types : LdType × LdType) :
      directLdBranchRejectionProbability D S types =
        1 - avgOver (uniformDistribution (DirectLdSpace D)) (accepted types) := by
    rw [show directLdBranchRejectionProbability D S types =
        avgOver (uniformDistribution (DirectLdSpace D))
          (fun sample => 1 - accepted types sample) by
      apply avgOver_congr
      intro sample
      dsimp [accepted]
      linarith [directLdAccepted_add_rejected_eq_one D S types sample]]
    rw [avgOver_sub, avgOver_uniform_const]
  rw [show directLdRejectionProbability D S =
      avgOver (uniformDistribution (LdType × LdType))
        (fun types => 1 -
          avgOver (uniformDistribution (DirectLdSpace D)) (accepted types)) by
    unfold directLdRejectionProbability
    apply avgOver_congr
    exact hbranch]
  rw [avgOver_sub, avgOver_uniform_const]
  congr 1
  rw [Strategy.value]
  symm
  change avgOver (directLdQuestionDistribution D) _ = _
  rw [directLdQuestionDistribution, Distribution.avgOver_map]
  exact avgOver_uniform_prod (f := accepted)

/-- The low individual degree branch weighting is at most three times the
uniformly weighted direct-game rejection probability. -/
theorem directLdLdtWeightedFailureProbability_le_three_mul_rejection
    (D : DirectLdParams) (S : Strategy (directLdGame D)) :
    directLdLdtWeightedFailureProbability D S ≤
      3 * directLdRejectionProbability D S := by
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
  rw [directLdRejectionProbability, avgOver_ldType_pair]
  unfold directLdLdtWeightedFailureProbability
  dsimp only
  linarith

/-- A strategy with value at least `1 - ε` has LDT-weighted failure
probability at most `3 * ε`. -/
theorem directLdLdtWeightedFailureProbability_le_three_mul_error
    (D : DirectLdParams) (S : Strategy (directLdGame D))
    (ε : ℝ) (hwin : 1 - ε ≤ S.value) :
    directLdLdtWeightedFailureProbability D S ≤ 3 * ε := by
  have hrejection : directLdRejectionProbability D S ≤ ε := by
    rw [directLdRejectionProbability_eq_one_sub_value]
    linarith
  calc
    directLdLdtWeightedFailureProbability D S ≤
        3 * directLdRejectionProbability D S :=
      directLdLdtWeightedFailureProbability_le_three_mul_rejection D S
    _ ≤ 3 * ε := mul_le_mul_of_nonneg_left hrejection (by norm_num)

end

end MIPStarRE.QPBT
