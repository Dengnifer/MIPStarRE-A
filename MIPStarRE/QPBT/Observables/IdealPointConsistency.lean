import MIPStarRE.QPBT.Observables.ExpandedDefs
import MIPStarRE.QPBT.Test.MagicSquareTheorems.PerfectStrategy.Observables

/-!
# Perfect consistency of ideal point measurements

The ideal point projectors on the two halves of one EPR state have zero joint
weight for distinct outcomes. This follows from the reality and orthogonality
of the characteristic-two Pauli basis projectors, with no strategy hypothesis.

The transpose identities are supplied by `pauliProj_transpose` in
`Algebra.Pauli` and `ProjectiveSetting.tauPointProj_transpose` in
`Observables.ExpandedDefs`. Orthogonality of the Pauli eigenspace projectors and
of the point fibers is likewise reused from `pauliProj_mul_pauliProj` and
`ProjectiveSetting.tauPointProj_mul_tauPointProj` in those two modules. The
latter module also supplies the actual measurement
`ProjectiveSetting.tauPointMeas`, whose effects are `tauPointProj`.

## References

- `references/qpbt-paper/04_preliminaries.tex:1101-1161`: Pauli eigenbases.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`,
  `eq:def-psihat`, `eq:qld-point-obs-def`, and the proof of `lem:qld-comm-cons`
  at line 489: perfect consistency of the ancillary point projectors.

These are auxiliary identities for the expanded-state construction, not the
approximate consistency theorem for the original strategy.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum

noncomputable section

namespace ProjectiveSetting

open MIPStarRE.LDT hiding Measurement
open DistanceCalculus

variable {P : AdmissibleParams}

/-- Distinct point fibers annihilate one another. This is the off-diagonal case
of the existing `tauPointProj_mul_tauPointProj` in `Observables.ExpandedDefs`. -/
theorem tauPointProj_mul_eq_zero_of_ne (W : PauliKind)
    (u : Fin P.m → PauliScalar P) {a b : PauliScalar P} (hab : a ≠ b) :
    tauPointProj W u a * tauPointProj W u b = 0 := by
  simp only [tauPointProj_mul_tauPointProj, if_neg hab]

/-- The ideal point projector has the same action on either half of one EPR
pair, as used in the proof of `lem:qld-comm-cons`, paper line 489. -/
theorem tauPointProj_epr_action (W : PauliKind)
    (u : Fin P.m → PauliScalar P) (a : PauliScalar P) :
    (heteroKron (tauPointProj W u a) 1).mulVec (eprState (PauliRegister P)) =
      (heteroKron 1 (tauPointProj W u a)).mulVec (eprState (PauliRegister P)) :=
  epr_action_eq_of_transpose _ (tauPointProj_transpose W u a)

/-- Two distinct ideal point outcomes annihilate the actual EPR vector.
Move the second effect to the first half and use orthogonality of point fibers. -/
theorem tauPointProj_epr_mulVec_eq_zero_of_ne (W : PauliKind)
    (u : Fin P.m → PauliScalar P) {a b : PauliScalar P} (hab : a ≠ b) :
    (heteroKron (tauPointProj W u a) (tauPointProj W u b)).mulVec
      (eprState (PauliRegister P)) = 0 := by
  have hprod : heteroKron (tauPointProj W u a) (tauPointProj W u b) =
      heteroKron (tauPointProj W u a) (1 : Op (PauliRegister P)) *
        heteroKron (1 : Op (PauliRegister P)) (tauPointProj W u b) := by
    rw [heteroKron_mul, mul_one, one_mul]
  rw [hprod, ← Matrix.mulVec_mulVec, ← tauPointProj_epr_action W u b,
    Matrix.mulVec_mulVec, heteroKron_mul, tauPointProj_mul_eq_zero_of_ne W u hab]
  simp [heteroKron]

/-- Every off-diagonal joint weight of the ideal point measurement on one EPR
pair is zero. The Pauli basis and the point are arbitrary. -/
theorem tauPointProj_epr_joint_eq_zero_of_ne (W : PauliKind)
    (u : Fin P.m → PauliScalar P) {a b : PauliScalar P} (hab : a ≠ b) :
    stateQForm (eprState (PauliRegister P))
      (heteroKron (tauPointProj W u a) (tauPointProj W u b)) = 0 := by
  unfold stateQForm applyOperatorToState
  change (inner ℂ (eprState (PauliRegister P))
    ((EuclideanSpace.equiv _ ℂ).symm
      ((heteroKron (tauPointProj W u a) (tauPointProj W u b)).mulVec
        (eprState (PauliRegister P))))).re = 0
  rw [tauPointProj_epr_mulVec_eq_zero_of_ne W u hab, map_zero, inner_zero_right]
  rfl

/-- Perfect ancillary consistency in the proof of `lem:qld-comm-cons`:
the off-diagonal joint mass is zero on the two halves of the same EPR state.
This auxiliary identity assumes no original strategy or consistency bound. -/
theorem tauPointProj_epr_offDiagonal_eq_zero (W : PauliKind)
    (u : Fin P.m → PauliScalar P) :
    (∑ a : PauliScalar P, ∑ b : PauliScalar P, if a = b then 0 else
      stateQForm (eprState (PauliRegister P))
        (heteroKron (tauPointProj W u a) (tauPointProj W u b))) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro b _
  split_ifs with hab
  · rfl
  · exact tauPointProj_epr_joint_eq_zero_of_ne W u hab

/-- Completeness and normalization of the actual EPR state put unit mass on
the diagonal of the ideal point joint measurement. No uniformity of its
individual outcomes is required. -/
theorem tauPointProj_epr_diagonal_eq_one (W : PauliKind)
    (u : Fin P.m → PauliScalar P) :
    (∑ a : PauliScalar P, stateQForm (eprState (PauliRegister P))
      (heteroKron (tauPointProj W u a) (tauPointProj W u a))) = 1 := by
  classical
  calc
    _ = ∑ a : PauliScalar P, ∑ b : PauliScalar P,
        stateQForm (eprState (PauliRegister P))
          (heteroKron (tauPointProj W u a) (tauPointProj W u b)) := by
      apply Finset.sum_congr rfl
      intro a _
      symm
      apply Finset.sum_eq_single a
      · intro b _ hba
        exact tauPointProj_epr_joint_eq_zero_of_ne W u hba.symm
      · simp
    _ = stateQForm (eprState (PauliRegister P))
        (heteroKron (∑ a, tauPointProj W u a) (∑ b, tauPointProj W u b)) := by
      simp only [heteroKron_finset_sum_left, heteroKron_finset_sum_right,
        stateQForm_finset_sum]
      exact Finset.sum_comm
    _ = 1 := by
      rw [sum_tauPointProj_eq_one, heteroKron_one_one, stateQForm_one,
        eprState_norm, one_pow]

/-- Averaging ideal point measurements over any question distribution preserves
their zero consistency defect on one EPR pair. This specializes the existing
`consistencyDefect` functional to the ancillary measurements in
`lem:qld-comm-cons`; it does not assume consistency of a strategy. -/
theorem tauPointProj_epr_consistencyDefect_eq_zero (W : PauliKind)
    (μ : Distribution (Fin P.m → PauliScalar P)) :
    consistencyDefect μ
      (fun u a => heteroKron (tauPointProj W u a) (1 : Op (PauliRegister P)))
      (fun u a => heteroKron (1 : Op (PauliRegister P)) (tauPointProj W u a))
      (eprState (PauliRegister P)) = 0 := by
  change avgOver μ (fun u => ∑ a : PauliScalar P, ∑ b : PauliScalar P,
    if a = b then 0 else stateQForm (eprState (PauliRegister P))
      (heteroKron (tauPointProj W u a) (1 : Op (PauliRegister P)) *
        heteroKron (1 : Op (PauliRegister P)) (tauPointProj W u b))) = 0
  simp_rw [heteroKron_mul, mul_one, one_mul, tauPointProj_epr_offDiagonal_eq_zero]
  simp [avgOver]

end ProjectiveSetting

end

end MIPStarRE.QPBT
