import MIPStarRE.QPBT.Combining.ExtendedLineGame.LinePointRejection

/-!
# Same-line branch rejection for the extended direct game

The axis-axis and diagonal-diagonal verifier branches compare the complete
typed coefficient answers returned by the two line measurements. This module
identifies each branch rejection exactly with the corresponding coefficient-
answer consistency defect, averaged over the marginal law of the supplied
line. These are exact transport identities, not numerical passing bounds.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- Blueprint `lem:qld-4-7`.
- Issue #317.
-/

open scoped BigOperators MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace ExtendedLineGame

variable {P : AdmissibleParams} {epsilon deltaQ deltaL : Real}
variable {setting : ProjectiveSetting P epsilon}
variable {points : CombinedPointsWitness setting deltaQ}

/-- The consistency defect of the two axis-line coefficient answers on the
constructed two-player state. The question law is the axis-line marginal of
the supplied direct line-point distribution. -/
def axisCoefficientAnswerDefect
    (lines : ExtendedLinesWitness setting points deltaL) : Real :=
  consistencyDefect
    ((directALinePointDist P.extendedDirectLd).map Prod.fst)
    (fun line answer => heteroKron
      (((lines.Qline .alice line).postprocess (axisAnswer P)).effect answer) 1)
    (fun line answer => heteroKron 1
      (((lines.Qline .bob line).postprocess (axisAnswer P)).effect answer))
    (pairState setting)

/-- The consistency defect of the two diagonal-line coefficient answers on
the constructed two-player state. The question law is the diagonal-line
marginal of the supplied direct line-point distribution. -/
def diagonalCoefficientAnswerDefect
    (lines : ExtendedLinesWitness setting points deltaL) : Real :=
  consistencyDefect
    ((directDLinePointDist P.extendedDirectLd).map Prod.fst)
    (fun line answer => heteroKron
      (((lines.Qline .alice line).postprocess (diagonalAnswer P)).effect answer) 1)
    (fun line answer => heteroKron 1
      (((lines.Qline .bob line).postprocess (diagonalAnswer P)).effect answer))
    (pairState setting)

private theorem answer_mismatch_eq_consistency
    (D : DirectLdParams) {X : Type*} [Fintype X] [DecidableEq X]
    (mu : Distribution X) (S : Strategy (directLdGame D))
    (qA qB : X -> DirectLdQuestion D) :
    consistencyDefect mu
        (fun x answer => heteroKron ((S.A (qA x)).effect answer) 1)
        (fun x answer => heteroKron 1 ((S.B (qB x)).effect answer)) S.ψ =
      avgOver mu (fun x => outcomeEventWeight S (qA x) (qB x)
        (fun answerA answerB => answerA ≠ answerB)) := by
  unfold consistencyDefect outcomeEventWeight
  apply avgOver_congr
  intro x
  simp only [DistanceCalculus.consistency_term_eq_stateQForm]
  simp_rw [DistanceCalculus.placed_product_stateQForm_eq]
  apply Finset.sum_congr rfl
  intro answerA _
  apply Finset.sum_congr rfl
  intro answerB _
  by_cases heq : answerA = answerB
  · simp [heq]
  · simp [heq, outcomeWeight, DistanceCalculus.stateQForm]

private theorem sameLine_rejectedMass_eq_answer_mismatch
    (lines : ExtendedLinesWitness setting points deltaL)
    (kind : LdType) (hkind : kind = .aline ∨ kind = .dline)
    (sample : DirectLdSpace P.extendedDirectLd) :
    directRejectedMass P.extendedDirectLd (strategy lines)
        (kind, directLdMap P.extendedDirectLd kind sample)
        (kind, directLdMap P.extendedDirectLd kind sample) =
      outcomeEventWeight (strategy lines)
        (kind, directLdMap P.extendedDirectLd kind sample)
        (kind, directLdMap P.extendedDirectLd kind sample)
        (fun answerA answerB => answerA ≠ answerB) := by
  classical
  unfold directRejectedMass outcomeEventWeight
  apply Finset.sum_congr rfl
  intro answerA _
  apply Finset.sum_congr rfl
  intro answerB _
  by_cases heq : answerA = answerB
  · subst answerB
    by_cases hvalid : validDirectLdAnswer kind answerA = true
    · have hwin : directLdWinPredicate P.extendedDirectLd
          (kind, directLdMap P.extendedDirectLd kind sample)
          (kind, directLdMap P.extendedDirectLd kind sample)
          answerA answerA = true := by
        rcases hkind with rfl | rfl <;> cases answerA <;>
          simp_all [directLdWinPredicate, validDirectLdAnswer]
      simp [hwin]
    · have hvalidFalse : validDirectLdAnswer kind answerA = false :=
        Bool.eq_false_of_not_eq_true hvalid
      have hzero := outcomeWeight_eq_zero_of_invalid lines
        (kind, directLdMap P.extendedDirectLd kind sample)
        (kind, directLdMap P.extendedDirectLd kind sample)
        answerA answerA (Or.inl hvalidFalse)
      simp [hzero]
  · have hnotwin : directLdWinPredicate P.extendedDirectLd
        (kind, directLdMap P.extendedDirectLd kind sample)
        (kind, directLdMap P.extendedDirectLd kind sample)
        answerA answerB ≠ true := by
      intro hwin
      apply heq
      rcases hkind with rfl | rfl <;> cases answerA <;> cases answerB <;>
        simp_all [directLdWinPredicate, validDirectLdAnswer]
    have hwinFalse : directLdWinPredicate P.extendedDirectLd
        (kind, directLdMap P.extendedDirectLd kind sample)
        (kind, directLdMap P.extendedDirectLd kind sample)
        answerA answerB = false := Bool.eq_false_of_not_eq_true hnotwin
    simp only [hwinFalse, Bool.false_eq_true, if_false]
    split
    · rfl
    · rename_i hnot
      exact (hnot heq).elim

private theorem axis_answer_effect
    (lines : ExtendedLinesWitness setting points deltaL) (side : PlayerSide)
    (sample : DirectLdSpace P.extendedDirectLd)
    (answer : DirectLdAnswer P.extendedDirectLd) :
    (answerMeasurement lines side
      (.aline, directLdMap P.extendedDirectLd .aline sample)).effect answer =
      ((lines.Qline side (directALineDescOf P.extendedDirectLd sample)).postprocess
        (axisAnswer P)).effect answer := by
  unfold answerMeasurement
  rw [axis_description_canonical]

private theorem diagonal_answer_effect
    (lines : ExtendedLinesWitness setting points deltaL) (side : PlayerSide)
    (sample : DirectLdSpace P.extendedDirectLd)
    (answer : DirectLdAnswer P.extendedDirectLd) :
    (answerMeasurement lines side
      (.dline, directLdMap P.extendedDirectLd .dline sample)).effect answer =
      ((lines.Qline side (directDLineDescOf P.extendedDirectLd sample)).postprocess
        (diagonalAnswer P)).effect answer := by
  unfold answerMeasurement
  rw [diagonal_description_canonical]

/-- The axis-axis branch rejection is exactly the consistency defect of the
two typed axis coefficient answers over the axis-line marginal. -/
theorem aline_aline_rejection_eq_axisCoefficientAnswerDefect
    (lines : ExtendedLinesWitness setting points deltaL) :
    directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
        (.aline, .aline) = axisCoefficientAnswerDefect lines := by
  rw [directLdBranchRejectionProbability_eq_avgOver]
  calc
    avgOver (uniformDistribution (DirectLdSpace P.extendedDirectLd))
        (fun sample => directRejectedMass P.extendedDirectLd (strategy lines)
          (.aline, directLdMap P.extendedDirectLd .aline sample)
          (.aline, directLdMap P.extendedDirectLd .aline sample)) =
      avgOver (uniformDistribution (DirectLdSpace P.extendedDirectLd))
        (fun sample => outcomeEventWeight (strategy lines)
          (.aline, directLdMap P.extendedDirectLd .aline sample)
          (.aline, directLdMap P.extendedDirectLd .aline sample)
          (fun answerA answerB => answerA ≠ answerB)) := by
      apply avgOver_congr
      exact sameLine_rejectedMass_eq_answer_mismatch lines .aline (Or.inl rfl)
    _ = consistencyDefect (uniformDistribution (DirectLdSpace P.extendedDirectLd))
        (fun sample answer => heteroKron
          ((answerMeasurement lines .alice
            (.aline, directLdMap P.extendedDirectLd .aline sample)).effect answer) 1)
        (fun sample answer => heteroKron 1
          ((answerMeasurement lines .bob
            (.aline, directLdMap P.extendedDirectLd .aline sample)).effect answer))
        (pairState setting) :=
      (answer_mismatch_eq_consistency P.extendedDirectLd _ (strategy lines)
        (fun sample => (.aline, directLdMap P.extendedDirectLd .aline sample))
        (fun sample => (.aline, directLdMap P.extendedDirectLd .aline sample))).symm
    _ = axisCoefficientAnswerDefect lines := by
      unfold axisCoefficientAnswerDefect consistencyDefect
      rw [directALinePointDist, Distribution.map_map, Distribution.avgOver_map]
      apply avgOver_congr
      intro sample
      apply Finset.sum_congr rfl
      intro answerA _
      apply Finset.sum_congr rfl
      intro answerB _
      dsimp only
      rw [axis_answer_effect lines .alice sample answerA,
        axis_answer_effect lines .bob sample answerB]

/-- The diagonal-diagonal branch rejection is exactly the consistency defect
of the two typed diagonal coefficient answers over the diagonal-line marginal. -/
theorem dline_dline_rejection_eq_diagonalCoefficientAnswerDefect
    (lines : ExtendedLinesWitness setting points deltaL) :
    directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
        (.dline, .dline) = diagonalCoefficientAnswerDefect lines := by
  rw [directLdBranchRejectionProbability_eq_avgOver]
  calc
    avgOver (uniformDistribution (DirectLdSpace P.extendedDirectLd))
        (fun sample => directRejectedMass P.extendedDirectLd (strategy lines)
          (.dline, directLdMap P.extendedDirectLd .dline sample)
          (.dline, directLdMap P.extendedDirectLd .dline sample)) =
      avgOver (uniformDistribution (DirectLdSpace P.extendedDirectLd))
        (fun sample => outcomeEventWeight (strategy lines)
          (.dline, directLdMap P.extendedDirectLd .dline sample)
          (.dline, directLdMap P.extendedDirectLd .dline sample)
          (fun answerA answerB => answerA ≠ answerB)) := by
      apply avgOver_congr
      exact sameLine_rejectedMass_eq_answer_mismatch lines .dline (Or.inr rfl)
    _ = consistencyDefect (uniformDistribution (DirectLdSpace P.extendedDirectLd))
        (fun sample answer => heteroKron
          ((answerMeasurement lines .alice
            (.dline, directLdMap P.extendedDirectLd .dline sample)).effect answer) 1)
        (fun sample answer => heteroKron 1
          ((answerMeasurement lines .bob
            (.dline, directLdMap P.extendedDirectLd .dline sample)).effect answer))
        (pairState setting) :=
      (answer_mismatch_eq_consistency P.extendedDirectLd _ (strategy lines)
        (fun sample => (.dline, directLdMap P.extendedDirectLd .dline sample))
        (fun sample => (.dline, directLdMap P.extendedDirectLd .dline sample))).symm
    _ = diagonalCoefficientAnswerDefect lines := by
      unfold diagonalCoefficientAnswerDefect consistencyDefect
      rw [directDLinePointDist, Distribution.map_map, Distribution.avgOver_map]
      apply avgOver_congr
      intro sample
      apply Finset.sum_congr rfl
      intro answerA _
      apply Finset.sum_congr rfl
      intro answerB _
      dsimp only
      rw [diagonal_answer_effect lines .alice sample answerA,
        diagonal_answer_effect lines .bob sample answerB]

end ExtendedLineGame

end

end MIPStarRE.QPBT
