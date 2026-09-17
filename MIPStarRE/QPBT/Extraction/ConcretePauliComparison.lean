import MIPStarRE.QPBT.Extraction.PauliTransport

/-!
# Pauli comparison for the concrete extraction maps

The ideal-state distance estimate is transported back to the six-register
operators occurring in the extraction witness, for both players.

## References

Blueprint `lem:qld-unitary`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1827-1858`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Classical

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum DistanceCalculus
open MIPStarRE.LDT hiding Measurement

noncomputable section

/-- Coordinate transport preserves the distance between two state vectors. -/
theorem norm_reindexState_sub_eq {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ≃ J) (psi phi : EuclideanSpace ℂ I) :
    ‖reindexState e psi - reindexState e phi‖ = ‖psi - phi‖ := by
  change ‖reindexState e (psi - phi)‖ = _
  exact reindexState_norm_eq e _

/-- The full Pauli comparison with the total measurement on the right block.
This follows from the left-block estimate by exchanging both auxiliary and
extracted registers; the EPR factor is invariant under this exchange. -/
theorem pauli_distance_on_ideal_right_le {P : AdmissibleParams} {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Measurement (PauliRegister P) (J × PauliRegister P)) (W : PauliKind)
    (aux : EuclideanSpace ℂ (I × J)) (haux : ‖aux‖ = 1)
    (theta : EuclideanSpace ℂ ((I × PauliRegister P) × (J × PauliRegister P)))
    (htheta : ‖theta‖ = 1) :
    let ideal := reindexState prodShuffle (vecTensor aux (eprState (PauliRegister P)))
    let B := rightPlacedMeasurement (ιA := I) (pauliRegisterMeas (params := P) W)
    (∑ h : PauliRegister P, ‖applyOperatorToState
      (heteroKron (1 : Op (I × PauliRegister P))
        (A.effect h - heteroKron (1 : Op J) (pauliProj W h))) ideal‖ ^ 2) ≤
      2 * (1 - avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun u =>
        ∑ a : PauliScalar P, stateQForm theta
          (heteroKron ((B.postprocess (fun h => evalPoly (encodingPoly h) u)).effect a)
            ((A.postprocess (fun h => evalPoly (encodingPoly h) u)).effect a)))) +
        2 * ((P.m * P.d : ℝ) / P.q) + 4 * ‖theta - ideal‖ := by
  let e := Equiv.prodComm (I × PauliRegister P) (J × PauliRegister P)
  let ideal := reindexState prodShuffle (vecTensor aux (eprState (PauliRegister P)))
  have hideal : reindexState prodShuffle
      (vecTensor (reindexState (Equiv.prodComm I J) aux) (eprState (PauliRegister P))) =
      reindexState e ideal := by
    ext p
    simp [reindexState, vecTensor, prodShuffle, eprState, e, ideal, eq_comm]
  have h := pauli_distance_on_ideal_le A W (reindexState (Equiv.prodComm I J) aux)
    (by rw [reindexState_norm_eq, haux]) (reindexState e theta)
    (by rw [reindexState_norm_eq, htheta])
  dsimp only at h ⊢
  rw [hideal, norm_reindexState_sub_eq] at h
  dsimp only [e] at h
  simp_rw [WinImplications.norm_applyOperatorToState_reindexState,
    WinImplications.stateQForm_reindexState, WinImplications.reindexOp_prodComm_heteroKron] at h
  exact h

namespace ProjectiveSetting

variable {P : AdmissibleParams} {epsilon deltaG : ℝ}
    (S : ProjectiveSetting P epsilon)

/-- The evaluated total-Pauli consistency defect against the opposite
pulled-apart measurement, with the tensor factors in Alice--Bob order. -/
def evaluatedPauliDefect (w : GlobalPairWitness S deltaG) (side : PlayerSide)
    (W : PauliKind) : ℝ :=
  match side with
  | .alice => consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
      (fun u a => S.placePlayer .alice ((S.pauliEvalMeas .alice W u).effect a))
      (fun u a => S.placeSide .bob (tildeM w .bob W (indicatorVec u) a)) S.psiHat
  | .bob => consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
      (fun u a => S.placeSide .alice (tildeM w .alice W (indicatorVec u) a))
      (fun u a => S.placePlayer .bob ((S.pauliEvalMeas .bob W u).effect a)) S.psiHat

/-- The ideal state in local extraction-block order. -/
theorem reindexState_idealExpState_blocks
    (aux : EuclideanSpace ℂ (ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB)) :
    reindexState (sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB)
      (S.idealExpState aux) = reindexState prodShuffle (vecTensor aux
        (eprState (PauliRegister P))) := by
  rfl

/-- Subtraction of block operators agrees with subtraction after placement. -/
theorem placeSide_sub (side : PlayerSide)
    (A B : Op (ExtractionBlock P (S.LocalSpace side))) :
    S.placeSide side (A - B) = S.placeSide side A - S.placeSide side B := by
  cases side
  · ext row col
    exact sub_mul _ _ _
  · ext row col
    exact mul_sub _ _ _

/-- The entire answer-summed distance in block coordinates is the distance
appearing in `ExtractionWitness.pauli_close`, for either player. -/
theorem extraction_pauli_dist_eq_sum (w : GlobalPairWitness S deltaG)
    (aux : EuclideanSpace ℂ (ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB))
    (side : PlayerSide) (W : PauliKind) :
    opFamilyDistSq (uniformDistribution Unit)
      (fun (_ : Unit) (h : PauliRegister P) =>
        conjBy (S.placeSide side (swapUnitary w side))
          (S.placePlayer side ((S.pauliMeas side W).effect h)))
      (fun (_ : Unit) (h : PauliRegister P) =>
        S.placeExtractedRegister side (pauliProj W h)) (S.idealExpState aux) =
      ∑ h : PauliRegister P, ‖applyOperatorToState
        (S.placeSide side (((S.swappedPauliMeas w side W).effect h) -
          heteroKron (1 : Op (S.ExpandedLocalSpace side)) (pauliProj W h)))
        (S.idealExpState aux)‖ ^ 2 := by
  simp_rw [S.placeSide_sub, S.placeSide_swappedPauliMeas, S.placeSide_extracted]
  exact avgOver_uniform_const _

set_option maxHeartbeats 800000 in
/-- For the concrete swaps, the full Pauli distance on the normalized ideal
state is bounded by the evaluated consistency defect and the two established
comparison losses. This instantiates `eq:qld-unitary-7`--`eq:qld-unitary-9`
with all six-register placements and both player orientations. -/
theorem extraction_pauli_dist_le (w : GlobalPairWitness S deltaG)
    (aux : EuclideanSpace ℂ (ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB))
    (haux : ‖aux‖ = 1) (side : PlayerSide) (W : PauliKind) :
    opFamilyDistSq (uniformDistribution Unit)
      (fun (_ : Unit) (h : PauliRegister P) =>
        conjBy (S.placeSide side (swapUnitary w side))
          (S.placePlayer side ((S.pauliMeas side W).effect h)))
      (fun (_ : Unit) (h : PauliRegister P) =>
        S.placeExtractedRegister side (pauliProj W h)) (S.idealExpState aux) ≤
      2 * S.evaluatedPauliDefect w side W + 2 * ((P.m * P.d : ℝ) / P.q) +
        4 * ‖S.applyBoth (swapUnitary w .alice) (swapUnitary w .bob) S.psiHat -
          S.idealExpState aux‖ := by
  let e := sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB
  let theta := S.applyBoth (swapUnitary w .alice) (swapUnitary w .bob) S.psiHat
  have htheta : ‖reindexState e theta‖ = 1 := by
    rw [reindexState_norm_eq]
    exact S.applyBoth_swap_norm w
  rw [S.extraction_pauli_dist_eq_sum]
  cases side
  · have h := pauli_distance_on_ideal_le (S.swappedPauliMeas w .alice W) W aux haux
      (reindexState e theta) htheta
    dsimp only at h
    erw [S.swapped_pauli_overlap_alice w W, sub_sub_cancel,
      ← S.reindexState_idealExpState_blocks aux, norm_reindexState_sub_eq] at h
    convert h using 1
    · apply Finset.sum_congr rfl
      intro label _
      congr 1
      exact (WinImplications.norm_applyOperatorToState_reindexState e _ _).symm
    · rfl
  · have h := pauli_distance_on_ideal_right_le (S.swappedPauliMeas w .bob W) W aux haux
      (reindexState e theta) htheta
    dsimp only at h
    erw [S.swapped_pauli_overlap_bob w W, sub_sub_cancel,
      ← S.reindexState_idealExpState_blocks aux, norm_reindexState_sub_eq] at h
    convert h using 1
    · apply Finset.sum_congr rfl
      intro label _
      congr 1
      exact (WinImplications.norm_applyOperatorToState_reindexState e _ _).symm
    · rfl

end ProjectiveSetting

end

end MIPStarRE.QPBT
