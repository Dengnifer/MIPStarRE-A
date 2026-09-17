import MIPStarRE.QPBT.Extraction.Consistency
import MIPStarRE.QPBT.Extraction.PointConsistencyPrime

/-!
# Measurements on extraction blocks

This module places a complete measurement from either player's three-register
extraction block on the full six-register space. It also records the transport
of original-player consistency through the two adjoined EPR states.

## References

These are finite-dimensional placement lemmas supporting blueprint
`lem:qld-construct-the-paulis` and `lem:qld-unitary`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Classical

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

namespace ProjectiveSetting

variable {P : AdmissibleParams} {epsilon : ℝ} (S : ProjectiveSetting P epsilon)

/-- Place a complete measurement on a player's full extraction block. -/
def blockMeasurement (side : PlayerSide) {α : Type*} [Fintype α]
    (A : Measurement α (ExtractionBlock P (S.LocalSpace side))) :
    Measurement α (SixReg P S.toStrategy.ιA S.toStrategy.ιB) := by
  refine Measurement.ofSumEqOne (fun a => S.placeSide side (A.effect a)) ?_ ?_
  · intro a
    cases side
    · exact reindexOp_nonneg _ (kronecker_nonneg (A.pos a) Matrix.PosSemidef.one.nonneg)
    · exact reindexOp_nonneg _ (kronecker_nonneg Matrix.PosSemidef.one.nonneg (A.pos a))
  · cases side
    · rw [← S.placeSide_alice_finset_sum, A.sum_eq_one]
      change reindexOp _ (heteroKron (1 : Op (ExtractionBlock P S.toStrategy.ιA))
        (1 : Op (ExtractionBlock P S.toStrategy.ιB))) = 1
      rw [heteroKron_one_one]
      ext row col
      simp [reindexOp, Matrix.one_apply]
    · rw [← S.placeSide_bob_finset_sum, A.sum_eq_one]
      change reindexOp _ (heteroKron (1 : Op (ExtractionBlock P S.toStrategy.ιA))
        (1 : Op (ExtractionBlock P S.toStrategy.ιB))) = 1
      rw [heteroKron_one_one]
      ext row col
      simp [reindexOp, Matrix.one_apply]

/-- The effects of a block measurement use the existing block placement. -/
@[simp] theorem blockMeasurement_effect (side : PlayerSide) {α : Type*} [Fintype α]
    (A : Measurement α (ExtractionBlock P (S.LocalSpace side))) (a : α) :
    (S.blockMeasurement side A).effect a = S.placeSide side (A.effect a) := by
  rfl

/-- Placing a projective measurement on an extraction block preserves projectivity. -/
theorem blockMeasurement_isProjective (side : PlayerSide) {α : Type*} [Fintype α]
    (A : Measurement α (ExtractionBlock P (S.LocalSpace side)))
    (hA : Measurement.IsProjective A) :
    Measurement.IsProjective (S.blockMeasurement side A) := by
  classical
  let e := sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB
  letI : DecidableEq (ExtractionRegisters P S.toStrategy.ιA S.toStrategy.ιB) :=
    instDecidableEqProd
  cases side
  · have h := reindexMeasurement_isProjective e (leftPlacedMeasurement A)
      (fun a => MakingMeasurementsProjective.isProj_kronecker (hA a)
        (IsStarProjection.one _))
    convert h using 1
    rfl
  · have h := reindexMeasurement_isProjective e (rightPlacedMeasurement A)
      (fun a => MakingMeasurementsProjective.isProj_kronecker
        (IsStarProjection.one _) (hA a))
    convert h using 1
    rfl

/-- Original-register quadratic forms are unchanged by adjoining the two EPR
pairs. -/
theorem stateQForm_placePlayers (A : Op S.toStrategy.ιA) (B : Op S.toStrategy.ιB)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    stateQForm S.psiHat (S.placePlayer .alice A * S.placePlayer .bob B) =
      stateQForm S.toStrategy.ψ (heteroKron A 1 * heteroKron 1 B) := by
  letI : DecidableEq (((S.toStrategy.ιA × S.toStrategy.ιB) ×
      (PauliRegister P × PauliRegister P)) × (PauliRegister P × PauliRegister P)) :=
    instDecidableEqProd
  have hAB := heteroKron_isHermitian A B hA hB
  rw [placed_product_stateQForm_eq]
  change stateQForm S.psiHat
    (S.place .AA' (heteroKron A 1) * S.place .BB' (heteroKron B 1)) = _
  rw [S.psiHat_eq_reindexState, WinImplications.stateQForm_reindexState,
    WinImplications.reindexOp_mul, S.reindexOp_sixRegShuffle_place_AA'_heteroKron,
    S.reindexOp_sixRegShuffle_place_BB'_heteroKron]
  simp only [heteroKron_mul, Matrix.one_mul, Matrix.mul_one, heteroKron_one_one]
  rw [stateQForm_vecTensor_heteroKron _ _ _ _
    (heteroKron_isHermitian _ _ hAB Matrix.isHermitian_one) Matrix.isHermitian_one,
    stateQForm_vecTensor_heteroKron _ _ _ _ hAB Matrix.isHermitian_one,
    stateQForm_one_eq_norm_sq, eprState_norm]
  ring

/-- Adjoining the two EPR pairs preserves the consistency defect between
families of original-register measurements. -/
theorem consistencyDefect_placePlayers {X α : Type*} [Fintype α] [DecidableEq α]
    [Fintype X] [DecidableEq X]
    (mu : Distribution X) (A : X → Measurement α S.toStrategy.ιA)
    (B : X → Measurement α S.toStrategy.ιB) :
    consistencyDefect mu (fun x a => S.placePlayer .alice ((A x).effect a))
        (fun x a => S.placePlayer .bob ((B x).effect a)) S.psiHat =
      consistencyDefect mu (fun x a => heteroKron ((A x).effect a) 1)
        (fun x a => heteroKron 1 ((B x).effect a)) S.toStrategy.ψ := by
  unfold consistencyDefect
  apply avgOver_congr
  intro x
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases hab : a = b
  · simp only [hab, if_true]
  · simp only [if_neg hab, consistency_term_eq_stateQForm]
    exact S.stateQForm_placePlayers _ _
      (Matrix.nonneg_iff_posSemidef.mp ((A x).pos a)).isHermitian
      (Matrix.nonneg_iff_posSemidef.mp ((B x).pos b)).isHermitian

end ProjectiveSetting

end

end MIPStarRE.QPBT
