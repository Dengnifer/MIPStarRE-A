import MIPStarRE.QPBT.Combining.ExtendedLineGame.StateTransport

/-!
# Pair-state consistency transport

This module transports consistency defects on the two-player expanded state to
the corresponding opposite placements on the six-register expanded state.

## References

These formalization-only identities support the application of `lem:pasting`
in `lem:qld-xz-lines`, from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-963` and
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`.
-/

namespace MIPStarRE.QPBT

open scoped MatrixOrder ComplexOrder

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace ProjectiveSetting

/-- A consistency defect on the two-player expanded state equals the defect
of the same measurements placed on `AA'` and `BA''` in the six-register state. -/
theorem consistencyDefect_pairState_eq_AA'_BA''
    {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε)
    {Sample Outcome : Type*} [Fintype Sample] [DecidableEq Sample]
    [Fintype Outcome] [DecidableEq Outcome]
    (law : Distribution Sample)
    (first : Sample → Measurement Outcome (S.ExpandedLocalSpace .alice))
    (second : Sample → Measurement Outcome (S.ExpandedLocalSpace .bob)) :
    consistencyDefect law
        (fun sample answer => heteroKron ((first sample).effect answer) 1)
        (fun sample answer => heteroKron 1 ((second sample).effect answer))
        (ExtendedLineGame.pairState S) =
      consistencyDefect law
        (fun sample answer => S.place .AA' ((first sample).effect answer))
        (fun sample answer => S.place .BA'' ((second sample).effect answer))
        S.psiHat := by
  classical
  unfold consistencyDefect
  apply avgOver_congr
  intro sample
  apply Finset.sum_congr rfl
  intro firstAnswer _
  apply Finset.sum_congr rfl
  intro secondAnswer _
  by_cases hanswer : firstAnswer = secondAnswer
  · simp [hanswer]
  · simp only [if_neg hanswer]
    change DistanceCalculus.stateQForm (ExtendedLineGame.pairState S)
        (heteroKron ((first sample).effect firstAnswer) 1 *
          heteroKron 1 ((second sample).effect secondAnswer)) =
      DistanceCalculus.stateQForm S.psiHat
        (S.place .AA' ((first sample).effect firstAnswer) *
          S.place .BA'' ((second sample).effect secondAnswer))
    rw [heteroKron_mul, Matrix.mul_one, Matrix.one_mul]
    exact ExtendedLineGame.stateQForm_pairState_eq_AA'_BA'' S _ _
      (Matrix.nonneg_iff_posSemidef.mp ((first sample).pos firstAnswer)).isHermitian
      (Matrix.nonneg_iff_posSemidef.mp ((second sample).pos secondAnswer)).isHermitian

/-- A consistency defect on the two-player expanded state equals the defect
of the same measurements placed on `AB''` and `BB'` in the six-register state. -/
theorem consistencyDefect_pairState_eq_AB''_BB'
    {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε)
    {Sample Outcome : Type*} [Fintype Sample] [DecidableEq Sample]
    [Fintype Outcome] [DecidableEq Outcome]
    (law : Distribution Sample)
    (first : Sample → Measurement Outcome (S.ExpandedLocalSpace .alice))
    (second : Sample → Measurement Outcome (S.ExpandedLocalSpace .bob)) :
    consistencyDefect law
        (fun sample answer => heteroKron ((first sample).effect answer) 1)
        (fun sample answer => heteroKron 1 ((second sample).effect answer))
        (ExtendedLineGame.pairState S) =
      consistencyDefect law
        (fun sample answer => S.place .AB'' ((first sample).effect answer))
        (fun sample answer => S.place .BB' ((second sample).effect answer))
        S.psiHat := by
  classical
  unfold consistencyDefect
  apply avgOver_congr
  intro sample
  apply Finset.sum_congr rfl
  intro firstAnswer _
  apply Finset.sum_congr rfl
  intro secondAnswer _
  by_cases hanswer : firstAnswer = secondAnswer
  · simp [hanswer]
  · simp only [if_neg hanswer]
    change DistanceCalculus.stateQForm (ExtendedLineGame.pairState S)
        (heteroKron ((first sample).effect firstAnswer) 1 *
          heteroKron 1 ((second sample).effect secondAnswer)) =
      DistanceCalculus.stateQForm S.psiHat
        (S.place .AB'' ((first sample).effect firstAnswer) *
          S.place .BB' ((second sample).effect secondAnswer))
    rw [heteroKron_mul, Matrix.mul_one, Matrix.one_mul]
    exact ExtendedLineGame.stateQForm_pairState_eq_AB''_BB' S _ _
      (Matrix.nonneg_iff_posSemidef.mp ((first sample).pos firstAnswer)).isHermitian
      (Matrix.nonneg_iff_posSemidef.mp ((second sample).pos secondAnswer)).isHermitian

end ProjectiveSetting

end

end MIPStarRE.QPBT
