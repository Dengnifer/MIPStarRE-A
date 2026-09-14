import MIPStarRE.QPBT.Combining.ExtendedLineGame.EvaluatedLineComparison

/-!
# Failed completed line-evaluation mass

This module bounds the marginal Born mass of the `none` outcome of each
completed line read by the corresponding mixed line/point rejection branch.
Wrong-format point answers also read as `none`, so the proof first removes
those answer pairs using their zero Born weight and only then applies event
inclusion.

These statements concern completed `Option`-valued readouts. They do not
identify successful parameter evaluation or prove a coefficient-collision
bound.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:232-248`
- Blueprint `lem:qld-4-7`.
- Issue #332.
-/

open scoped BigOperators MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace ExtendedLineGame

variable {P : AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
variable {setting : ProjectiveSetting P epsilon}
variable {points : CombinedPointsWitness setting deltaQ}

/-- A direct point answer has completed read `none` exactly when its answer
tag is invalid for a point question. -/
private theorem pointGameRead_eq_none_iff_invalid
    (answer : DirectLdAnswer P.extendedDirectLd) :
    pointGameRead answer = none ↔
      validDirectLdAnswer (D := P.extendedDirectLd) .point answer = false := by
  cases answer <;> simp [pointGameRead, validDirectLdAnswer]

/-- After zero-weight invalid point answers are removed, Alice's line-`none`
event is the event that the line read is `none` and the point read is not. -/
private theorem alice_line_none_event_eq_point_some
    (lines : ExtendedLinesWitness setting points deltaL)
    (kind : LdType) (sample : DirectLdSpace P.extendedDirectLd)
    (readLine : DirectLdAnswer P.extendedDirectLd → Option (PauliScalar P)) :
    outcomeEventWeight (strategy lines)
        (kind, directLdMap P.extendedDirectLd kind sample)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (fun answerA _ => readLine answerA = none) =
      outcomeEventWeight (strategy lines)
        (kind, directLdMap P.extendedDirectLd kind sample)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (fun answerA answerB =>
          readLine answerA = none ∧ pointGameRead answerB ≠ none) := by
  classical
  unfold outcomeEventWeight
  apply Finset.sum_congr rfl
  intro answerA _
  apply Finset.sum_congr rfl
  intro answerB _
  by_cases hline : readLine answerA = none
  · by_cases hpoint : pointGameRead answerB = none
    · have hinvalid := (pointGameRead_eq_none_iff_invalid answerB).1 hpoint
      rw [outcomeWeight_eq_zero_of_invalid lines _ _ answerA answerB (Or.inr hinvalid)]
      simp [hline, hpoint]
    · simp [hline, hpoint]
  · simp [hline]

/-- After zero-weight invalid point answers are removed, Bob's line-`none`
event is the event that the point read is not `none` and the line read is. -/
private theorem bob_line_none_event_eq_point_some
    (lines : ExtendedLinesWitness setting points deltaL)
    (kind : LdType) (sample : DirectLdSpace P.extendedDirectLd)
    (readLine : DirectLdAnswer P.extendedDirectLd → Option (PauliScalar P)) :
    outcomeEventWeight (strategy lines)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (kind, directLdMap P.extendedDirectLd kind sample)
        (fun _ answerB => readLine answerB = none) =
      outcomeEventWeight (strategy lines)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (kind, directLdMap P.extendedDirectLd kind sample)
        (fun answerA answerB =>
          pointGameRead answerA ≠ none ∧ readLine answerB = none) := by
  classical
  unfold outcomeEventWeight
  apply Finset.sum_congr rfl
  intro answerA _
  apply Finset.sum_congr rfl
  intro answerB _
  by_cases hpoint : pointGameRead answerA = none
  · have hinvalid := (pointGameRead_eq_none_iff_invalid answerA).1 hpoint
    rw [outcomeWeight_eq_zero_of_invalid lines _ _ answerA answerB (Or.inl hinvalid)]
    simp [hpoint]
  · by_cases hline : readLine answerB = none
    · simp [hpoint, hline]
    · simp [hpoint, hline]

/-- Alice's marginal mass of failed completed axis-line evaluation under the
uniform common direct sample. -/
noncomputable def axisAliceNoneMass
    (lines : ExtendedLinesWitness setting points deltaL) : ℝ :=
  avgOver (uniformDistribution (DirectLdSpace P.extendedDirectLd)) fun sample =>
    aliceEventWeight (strategy lines)
      (.aline, directLdMap P.extendedDirectLd .aline sample)
      (fun answer => axisGameRead sample answer = none)

/-- Alice's marginal mass of failed completed diagonal-line evaluation under
the uniform common direct sample. -/
noncomputable def diagonalAliceNoneMass
    (lines : ExtendedLinesWitness setting points deltaL) : ℝ :=
  avgOver (uniformDistribution (DirectLdSpace P.extendedDirectLd)) fun sample =>
    aliceEventWeight (strategy lines)
      (.dline, directLdMap P.extendedDirectLd .dline sample)
      (fun answer => diagonalGameRead sample answer = none)

/-- Bob's marginal mass of failed completed axis-line evaluation under the
uniform common direct sample. -/
noncomputable def axisBobNoneMass
    (lines : ExtendedLinesWitness setting points deltaL) : ℝ :=
  avgOver (uniformDistribution (DirectLdSpace P.extendedDirectLd)) fun sample =>
    bobEventWeight (strategy lines)
      (.aline, directLdMap P.extendedDirectLd .aline sample)
      (fun answer => axisGameRead sample answer = none)

/-- Bob's marginal mass of failed completed diagonal-line evaluation under
the uniform common direct sample. -/
noncomputable def diagonalBobNoneMass
    (lines : ExtendedLinesWitness setting points deltaL) : ℝ :=
  avgOver (uniformDistribution (DirectLdSpace P.extendedDirectLd)) fun sample =>
    bobEventWeight (strategy lines)
      (.dline, directLdMap P.extendedDirectLd .dline sample)
      (fun answer => diagonalGameRead sample answer = none)

/-- At a fixed sample, Alice's failed completed axis evaluation is contained
in the axis-line/point rejection event after zero-mass invalid tags are removed. -/
private theorem axis_alice_none_mass_at_le_rejectedMass
    (lines : ExtendedLinesWitness setting points deltaL)
    (sample : DirectLdSpace P.extendedDirectLd) :
    aliceEventWeight (strategy lines)
        (.aline, directLdMap P.extendedDirectLd .aline sample)
        (fun answer => axisGameRead sample answer = none) ≤
      directRejectedMass P.extendedDirectLd (strategy lines)
        (.aline, directLdMap P.extendedDirectLd .aline sample)
        (.point, directLdMap P.extendedDirectLd .point sample) := by
  calc
    _ = outcomeEventWeight (strategy lines)
        (.aline, directLdMap P.extendedDirectLd .aline sample)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (fun answerA _ => axisGameRead sample answerA = none) :=
      (outcome_event_weight_left_eq _ _ _ _).symm
    _ = outcomeEventWeight (strategy lines)
        (.aline, directLdMap P.extendedDirectLd .aline sample)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (fun answerA answerB => axisGameRead sample answerA = none ∧
          pointGameRead answerB ≠ none) :=
      alice_line_none_event_eq_point_some lines .aline sample (axisGameRead sample)
    _ ≤ outcomeEventWeight (strategy lines)
        (.aline, directLdMap P.extendedDirectLd .aline sample)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (fun answerA answerB => axisGameRead sample answerA ≠ pointGameRead answerB) := by
      apply outcome_event_weight_mono
      intro answerA answerB hnone heq
      exact hnone.2 (heq.symm.trans hnone.1)
    _ = _ := (rejectedMass_eq_read_mismatch lines sample).symm

/-- At a fixed sample, Alice's failed completed diagonal evaluation is
contained in the diagonal-line/point rejection event after zero-mass invalid tags are removed. -/
private theorem diagonal_alice_none_mass_at_le_rejectedMass
    (lines : ExtendedLinesWitness setting points deltaL)
    (sample : DirectLdSpace P.extendedDirectLd) :
    aliceEventWeight (strategy lines)
        (.dline, directLdMap P.extendedDirectLd .dline sample)
        (fun answer => diagonalGameRead sample answer = none) ≤
      directRejectedMass P.extendedDirectLd (strategy lines)
        (.dline, directLdMap P.extendedDirectLd .dline sample)
        (.point, directLdMap P.extendedDirectLd .point sample) := by
  calc
    _ = outcomeEventWeight (strategy lines)
        (.dline, directLdMap P.extendedDirectLd .dline sample)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (fun answerA _ => diagonalGameRead sample answerA = none) :=
      (outcome_event_weight_left_eq _ _ _ _).symm
    _ = outcomeEventWeight (strategy lines)
        (.dline, directLdMap P.extendedDirectLd .dline sample)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (fun answerA answerB => diagonalGameRead sample answerA = none ∧
          pointGameRead answerB ≠ none) :=
      alice_line_none_event_eq_point_some lines .dline sample
        (diagonalGameRead sample)
    _ ≤ outcomeEventWeight (strategy lines)
        (.dline, directLdMap P.extendedDirectLd .dline sample)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (fun answerA answerB =>
          diagonalGameRead sample answerA ≠ pointGameRead answerB) := by
      apply outcome_event_weight_mono
      intro answerA answerB hnone heq
      exact hnone.2 (heq.symm.trans hnone.1)
    _ = _ := (diagonal_rejectedMass_eq_read_mismatch lines sample).symm

/-- At a fixed sample, Bob's failed completed axis evaluation is contained in
the point/axis-line rejection event after zero-mass invalid tags are removed. -/
private theorem axis_bob_none_mass_at_le_rejectedMass
    (lines : ExtendedLinesWitness setting points deltaL)
    (sample : DirectLdSpace P.extendedDirectLd) :
    bobEventWeight (strategy lines)
        (.aline, directLdMap P.extendedDirectLd .aline sample)
        (fun answer => axisGameRead sample answer = none) ≤
      directRejectedMass P.extendedDirectLd (strategy lines)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.aline, directLdMap P.extendedDirectLd .aline sample) := by
  calc
    _ = outcomeEventWeight (strategy lines)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.aline, directLdMap P.extendedDirectLd .aline sample)
        (fun _ answerB => axisGameRead sample answerB = none) :=
      (outcome_event_weight_right_eq _ _ _ _).symm
    _ = outcomeEventWeight (strategy lines)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.aline, directLdMap P.extendedDirectLd .aline sample)
        (fun answerA answerB => pointGameRead answerA ≠ none ∧
          axisGameRead sample answerB = none) :=
      bob_line_none_event_eq_point_some lines .aline sample (axisGameRead sample)
    _ ≤ outcomeEventWeight (strategy lines)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.aline, directLdMap P.extendedDirectLd .aline sample)
        (fun answerA answerB => pointGameRead answerA ≠ axisGameRead sample answerB) := by
      apply outcome_event_weight_mono
      intro answerA answerB hnone heq
      exact hnone.1 (heq.trans hnone.2)
    _ = _ := (point_axis_rejectedMass_eq_read_mismatch lines sample).symm

/-- At a fixed sample, Bob's failed completed diagonal evaluation is
contained in the point/diagonal-line rejection event after zero-mass invalid tags are removed. -/
private theorem diagonal_bob_none_mass_at_le_rejectedMass
    (lines : ExtendedLinesWitness setting points deltaL)
    (sample : DirectLdSpace P.extendedDirectLd) :
    bobEventWeight (strategy lines)
        (.dline, directLdMap P.extendedDirectLd .dline sample)
        (fun answer => diagonalGameRead sample answer = none) ≤
      directRejectedMass P.extendedDirectLd (strategy lines)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.dline, directLdMap P.extendedDirectLd .dline sample) := by
  calc
    _ = outcomeEventWeight (strategy lines)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.dline, directLdMap P.extendedDirectLd .dline sample)
        (fun _ answerB => diagonalGameRead sample answerB = none) :=
      (outcome_event_weight_right_eq _ _ _ _).symm
    _ = outcomeEventWeight (strategy lines)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.dline, directLdMap P.extendedDirectLd .dline sample)
        (fun answerA answerB => pointGameRead answerA ≠ none ∧
          diagonalGameRead sample answerB = none) :=
      bob_line_none_event_eq_point_some lines .dline sample
        (diagonalGameRead sample)
    _ ≤ outcomeEventWeight (strategy lines)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.dline, directLdMap P.extendedDirectLd .dline sample)
        (fun answerA answerB =>
          pointGameRead answerA ≠ diagonalGameRead sample answerB) := by
      apply outcome_event_weight_mono
      intro answerA answerB hnone heq
      exact hnone.1 (heq.trans hnone.2)
    _ = _ := (point_diagonal_rejectedMass_eq_read_mismatch lines sample).symm

/-- Alice's failed completed axis-evaluation mass is bounded by the
axis-line/point branch rejection probability. -/
theorem axis_alice_none_mass_le_rejection
    (lines : ExtendedLinesWitness setting points deltaL) :
    axisAliceNoneMass lines ≤
      directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
        (.aline, .point) := by
  unfold axisAliceNoneMass
  rw [directLdBranchRejectionProbability_eq_avgOver]
  apply avgOver_mono
  exact axis_alice_none_mass_at_le_rejectedMass lines

/-- Alice's failed completed diagonal-evaluation mass is bounded by the
diagonal-line/point branch rejection probability. -/
theorem diagonal_alice_none_mass_le_rejection
    (lines : ExtendedLinesWitness setting points deltaL) :
    diagonalAliceNoneMass lines ≤
      directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
        (.dline, .point) := by
  unfold diagonalAliceNoneMass
  rw [directLdBranchRejectionProbability_eq_avgOver]
  apply avgOver_mono
  exact diagonal_alice_none_mass_at_le_rejectedMass lines

/-- Bob's failed completed axis-evaluation mass is bounded by the
point/axis-line branch rejection probability. -/
theorem axis_bob_none_mass_le_rejection
    (lines : ExtendedLinesWitness setting points deltaL) :
    axisBobNoneMass lines ≤
      directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
        (.point, .aline) := by
  unfold axisBobNoneMass
  rw [directLdBranchRejectionProbability_eq_avgOver]
  apply avgOver_mono
  exact axis_bob_none_mass_at_le_rejectedMass lines

/-- Bob's failed completed diagonal-evaluation mass is bounded by the
point/diagonal-line branch rejection probability. -/
theorem diagonal_bob_none_mass_le_rejection
    (lines : ExtendedLinesWitness setting points deltaL) :
    diagonalBobNoneMass lines ≤
      directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
        (.point, .dline) := by
  unfold diagonalBobNoneMass
  rw [directLdBranchRejectionProbability_eq_avgOver]
  apply avgOver_mono
  exact diagonal_bob_none_mass_at_le_rejectedMass lines

end ExtendedLineGame

end

end MIPStarRE.QPBT
