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
    have hfirst := first.pos answer
    have hsecond := second.pos answer
    have hone : 0 ≤ (1 : Op (PauliRegister P × PauliRegister P)) :=
      Matrix.PosSemidef.one.nonneg
    cases p1 <;> cases p2 <;> simp only [Placement.IsOpposite] at hopp
    · rw [ProjectiveSetting.place_AA'_eq, ProjectiveSetting.place_BA''_eq,
        ← WinImplications.reindexOp_mul, heteroKron_mul]
      simp only [mul_one, one_mul]
      exact ProjectiveSetting.reindexOp_nonneg _
        (MIPStarRE.Quantum.kronecker_nonneg hfirst
          (MIPStarRE.Quantum.kronecker_nonneg hsecond hone))
    · rw [ProjectiveSetting.place_BA''_eq, ProjectiveSetting.place_AA'_eq,
        ← WinImplications.reindexOp_mul, heteroKron_mul]
      simp only [mul_one, one_mul]
      exact ProjectiveSetting.reindexOp_nonneg _
        (MIPStarRE.Quantum.kronecker_nonneg hsecond
          (MIPStarRE.Quantum.kronecker_nonneg hfirst hone))
    · rw [ProjectiveSetting.place_BB'_eq, ProjectiveSetting.place_AB''_eq,
        ← WinImplications.reindexOp_mul, heteroKron_mul]
      simp only [mul_one, one_mul]
      exact ProjectiveSetting.reindexOp_nonneg _
        (MIPStarRE.Quantum.kronecker_nonneg hsecond
          (MIPStarRE.Quantum.kronecker_nonneg hfirst hone))
    · rw [ProjectiveSetting.place_AB''_eq, ProjectiveSetting.place_BB'_eq,
        ← WinImplications.reindexOp_mul, heteroKron_mul]
      simp only [mul_one, one_mul]
      exact ProjectiveSetting.reindexOp_nonneg _
        (MIPStarRE.Quantum.kronecker_nonneg hfirst
          (MIPStarRE.Quantum.kronecker_nonneg hsecond hone))
  have hdiag : 0 ≤ ∑ answer : Outcome, DistanceCalculus.stateQForm S.psiHat
      (S.place p1 (first.effect answer) * S.place p2 (second.effect answer)) :=
    Finset.sum_nonneg fun answer _ => DistanceCalculus.stateQForm_nonneg _
      (hproduct answer)
  linarith

end

end MIPStarRE.QPBT
