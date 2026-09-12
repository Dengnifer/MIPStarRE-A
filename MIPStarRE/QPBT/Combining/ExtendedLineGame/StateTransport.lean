import MIPStarRE.QPBT.Combining.ExtendedLineGame
import MIPStarRE.QPBT.Observables.ExpandedPlacement

/-!
# Correlations on the two-player expanded state

The six-register state of `eq:def-psihat` factors as the two-player state
`ExtendedLineGame.pairState` and an unused normalized EPR pair, for each of
the opposite register placements `AA'`--`BA''` and `AB''`--`BB'`. Therefore
arbitrary Hermitian operators on the expanded local spaces have the same
correlation in the two descriptions. An individual operator need not factor
between its strategy register and its Pauli register.

These are formalization-only auxiliary identities for the strategy construction
in the proof of `lem:qld-4-7`. They do not establish its passing value or the
existence of its input measurements. Parent issue #119 remains open.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:367-372`,
  equation `eq:def-psihat`.
- The same source, `lem:qld-4-7`, proof at lines 1279-1288.
- Blueprint `def:expanded-state`, `def:symmetric-equivalents`, and `lem:qld-4-7`.
- Issue #302.
-/

-- The six-register products require the same instance-search size as ExpandedPlacement.
set_option synthInstance.maxSize 400

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum
open ProjectiveSetting

noncomputable section

namespace ExtendedLineGame

variable {P : AdmissibleParams} {epsilon : Real}

/-- Regroup the six registers as `(AA', BA'')` and the unused pair `(B', B'')`.
This is the first opposite-placement partition of `eq:def-psihat`. -/
def aaBaRegrouping (setting : ProjectiveSetting P epsilon) :
    SixReg P setting.toStrategy.ιA setting.toStrategy.ιB ≃
      (setting.ExpandedLocalSpace .alice × setting.ExpandedLocalSpace .bob) ×
        (PauliRegister P × PauliRegister P) :=
  (aaBaBipartition P setting.toStrategy.ιA setting.toStrategy.ιB).trans
    (Equiv.prodAssoc _ _ _).symm

/-- Regroup the six registers as `(AB'', BB')` and the unused pair `(A', A'')`.
This is the second opposite-placement partition of `eq:def-psihat`. -/
def abBbRegrouping (setting : ProjectiveSetting P epsilon) :
    SixReg P setting.toStrategy.ιA setting.toStrategy.ιB ≃
      (setting.ExpandedLocalSpace .alice × setting.ExpandedLocalSpace .bob) ×
        (PauliRegister P × PauliRegister P) :=
  (abBbBipartition P setting.toStrategy.ιA setting.toStrategy.ιB).trans
    (Equiv.prodAssoc _ _ _).symm

/-- In the `AA'`--`BA''` grouping, the expanded state is `pairState` tensored
with the unused EPR pair. This is a coordinate consequence of `eq:def-psihat`,
not an assumption on the strategy or its measurement effects. -/
theorem reindexState_aaBaRegrouping_psiHat (setting : ProjectiveSetting P epsilon) :
    reindexState (aaBaRegrouping setting) setting.psiHat =
      vecTensor (pairState setting) (eprState (PauliRegister P)) := by
  ext p
  rfl

/-- The `AB''`--`BB'` grouping has the same two-player state because an EPR
pair is invariant under exchanging its registers. The other EPR pair is unused.
This is a coordinate consequence of `eq:def-psihat`. -/
theorem reindexState_abBbRegrouping_psiHat (setting : ProjectiveSetting P epsilon) :
    reindexState (abBbRegrouping setting) setting.psiHat =
      vecTensor (pairState setting) (eprState (PauliRegister P)) := by
  ext p
  have hswap := congrArg
    (fun v : EuclideanSpace Complex (PauliRegister P × PauliRegister P) =>
      v (p.1.1.2, p.1.2.2)) (reindexState_prodComm_eprState (PauliRegister P))
  change eprState (PauliRegister P) (p.1.2.2, p.1.1.2) =
    eprState (PauliRegister P) (p.1.1.2, p.1.2.2) at hswap
  change
    (setting.toStrategy.ψ (p.1.1.1, p.1.2.1) * eprState (PauliRegister P) p.2) *
        eprState (PauliRegister P) (p.1.2.2, p.1.1.2) =
      (setting.toStrategy.ψ (p.1.1.1, p.1.2.1) *
        eprState (PauliRegister P) (p.1.1.2, p.1.2.2)) *
          eprState (PauliRegister P) p.2
  rw [hswap]
  ring

/-- Arbitrary Hermitian expanded operators have the same correlation on
`pairState` as their `AA'`--`BA''` placements on `psiHat`. Hermiticity holds for
POVM effects; no factorization or consistency hypothesis is required. This
transports Born correlations in the first proof paragraph of `lem:qld-4-7`. -/
theorem stateQForm_pairState_eq_AA'_BA'' (setting : ProjectiveSetting P epsilon)
    (A : Op (setting.ExpandedLocalSpace .alice))
    (B : Op (setting.ExpandedLocalSpace .bob))
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    DistanceCalculus.stateQForm (pairState setting) (heteroKron A B) =
      DistanceCalculus.stateQForm setting.psiHat
        (setting.place .AA' A * setting.place .BA'' B) := by
  let I : Op (PauliRegister P × PauliRegister P) := 1
  have hop : reindexOp (aaBaRegrouping setting) (heteroKron (heteroKron A B) I) =
      setting.place .AA' A * setting.place .BA'' B := by
    change Op (setting.toStrategy.ιA × PauliRegister P) at A
    change Op (setting.toStrategy.ιB × PauliRegister P) at B
    change reindexOp (aaBaBipartition P setting.toStrategy.ιA setting.toStrategy.ιB)
      (reindexOp (Equiv.prodAssoc _ _ _).symm (heteroKron (heteroKron A B) I)) = _
    rw [show reindexOp (Equiv.prodAssoc _ _ _).symm
        (heteroKron (heteroKron A B) I) = heteroKron A (heteroKron B I) from
      Matrix.kronecker_assoc A B I]
    rw [show heteroKron A (heteroKron B I) =
        heteroKron A 1 * heteroKron 1 (heteroKron B I) by
      rw [heteroKron_mul, Matrix.mul_one, Matrix.one_mul]]
    exact (WinImplications.reindexOp_mul _ _ _).trans
      (congrArg₂ (fun X Y => X * Y)
        (reindexOp_aaBaBipartition_left setting A)
        (reindexOp_aaBaBipartition_right setting B))
  calc
    DistanceCalculus.stateQForm (pairState setting) (heteroKron A B) =
        DistanceCalculus.stateQForm
          (vecTensor (pairState setting) (eprState (PauliRegister P)))
          (heteroKron (heteroKron A B) I) := by
      rw [stateQForm_vecTensor_heteroKron _ _ _ _
        (heteroKron_isHermitian A B hA hB) Matrix.isHermitian_one]
      simp [stateQForm_one_eq_norm_sq, eprState_norm]
    _ = DistanceCalculus.stateQForm setting.psiHat
        (setting.place .AA' A * setting.place .BA'' B) := by
      rw [← reindexState_aaBaRegrouping_psiHat setting,
        WinImplications.stateQForm_reindexState, hop]

/-- Arbitrary Hermitian expanded operators have the same correlation on
`pairState` as their `AB''`--`BB'` placements on `psiHat`. This is the second
orientation of the Born-correlation transport for `lem:qld-4-7`; EPR symmetry
reverses the active ancillary registers without transposing either operator. -/
theorem stateQForm_pairState_eq_AB''_BB' (setting : ProjectiveSetting P epsilon)
    (A : Op (setting.ExpandedLocalSpace .alice))
    (B : Op (setting.ExpandedLocalSpace .bob))
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    DistanceCalculus.stateQForm (pairState setting) (heteroKron A B) =
      DistanceCalculus.stateQForm setting.psiHat
        (setting.place .AB'' A * setting.place .BB' B) := by
  let I : Op (PauliRegister P × PauliRegister P) := 1
  have hop : reindexOp (abBbRegrouping setting) (heteroKron (heteroKron A B) I) =
      setting.place .AB'' A * setting.place .BB' B := by
    change Op (setting.toStrategy.ιA × PauliRegister P) at A
    change Op (setting.toStrategy.ιB × PauliRegister P) at B
    change reindexOp (abBbBipartition P setting.toStrategy.ιA setting.toStrategy.ιB)
      (reindexOp (Equiv.prodAssoc _ _ _).symm (heteroKron (heteroKron A B) I)) = _
    rw [show reindexOp (Equiv.prodAssoc _ _ _).symm
        (heteroKron (heteroKron A B) I) = heteroKron A (heteroKron B I) from
      Matrix.kronecker_assoc A B I]
    rw [show heteroKron A (heteroKron B I) =
        heteroKron A 1 * heteroKron 1 (heteroKron B I) by
      rw [heteroKron_mul, Matrix.mul_one, Matrix.one_mul]]
    exact (WinImplications.reindexOp_mul _ _ _).trans
      (congrArg₂ (fun X Y => X * Y)
        (reindexOp_abBbBipartition_left setting A)
        (reindexOp_abBbBipartition_right setting B))
  calc
    DistanceCalculus.stateQForm (pairState setting) (heteroKron A B) =
        DistanceCalculus.stateQForm
          (vecTensor (pairState setting) (eprState (PauliRegister P)))
          (heteroKron (heteroKron A B) I) := by
      rw [stateQForm_vecTensor_heteroKron _ _ _ _
        (heteroKron_isHermitian A B hA hB) Matrix.isHermitian_one]
      simp [stateQForm_one_eq_norm_sq, eprState_norm]
    _ = DistanceCalculus.stateQForm setting.psiHat
        (setting.place .AB'' A * setting.place .BB' B) := by
      rw [← reindexState_abBbRegrouping_psiHat setting,
        WinImplications.stateQForm_reindexState, hop]

end ExtendedLineGame

end

end MIPStarRE.QPBT
