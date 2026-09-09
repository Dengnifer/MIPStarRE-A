import MIPStarRE.QPBT.Combining.Points.Placement

/-!
# Pointwise consistency defect bound

This module records the unit upper bound for the pointwise consistency defect
of complete measurements placed on opposite expanded registers.

## References

This is a proof-only bound used when restoring discarded sampling mass in
`lem:qld-xz-lines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-963`.
-/

open scoped BigOperators MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-- The pointwise defect of complete measurements on opposite registers is at
most one: it equals one minus a nonnegative diagonal overlap. This proof-only
bound restores discarded mass graded by the ambient line-point distribution. -/
theorem consistencyDefect_integrand_le_one {P : AdmissibleParams} {ε : ℝ}
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (S : ProjectiveSetting P ε) (p1 p2 : Placement) (hopp : p1.IsOpposite p2)
    (first : Measurement Outcome (S.ExpandedLocalSpace p1.side))
    (second : Measurement Outcome (S.ExpandedLocalSpace p2.side)) :
    (∑ answer : Outcome, ∑ other : Outcome,
      if answer = other then 0 else DistanceCalculus.stateQForm S.psiHat
        (S.place p1 (first.effect answer) * S.place p2 (second.effect other))) ≤ 1 := by
  have h := DistanceCalculus.point_defect_eq
    (S.placedMeasurement p1 first) (S.placedMeasurement p2 second) S.psiHat
  simp only [ProjectiveSetting.placedMeasurement_effect, S.psiHat_norm, one_pow] at h
  rw [h]
  have hproduct (answer : Outcome) :
      0 ≤ S.place p1 (first.effect answer) * S.place p2 (second.effect answer) := by
    exact Commute.mul_nonneg
      (S.place_nonneg p1 (first.pos answer))
      (S.place_nonneg p2 (second.pos answer))
      (S.place_comm p1 p2 hopp _ _)
  have hdiag : 0 ≤ ∑ answer : Outcome, DistanceCalculus.stateQForm S.psiHat
      (S.place p1 (first.effect answer) * S.place p2 (second.effect answer)) :=
    Finset.sum_nonneg fun answer _ => DistanceCalculus.stateQForm_nonneg _
      (hproduct answer)
  linarith

end

end MIPStarRE.QPBT
