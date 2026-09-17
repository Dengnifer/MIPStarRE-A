import MIPStarRE.QPBT.Extraction.SwappedConsistency
import MIPStarRE.QPBT.Extraction.EvaluatedPauliConsistency
import MIPStarRE.QPBT.Extraction.PauliComparison

/-!
# Total Pauli measurements under the extraction swaps

The evaluated overlap on the swapped state is the original evaluated-Pauli
consistency overlap. Both player orientations retain their six-register
placements. These identities instantiate the ideal-state Pauli comparison.

## References

Blueprint `lem:qld-unitary`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1785-1858`,
especially `eq:qld-unitary-6` and `eq:qld-unitary-9`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Classical

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum DistanceCalculus
open MIPStarRE.LDT hiding Measurement

noncomputable section

/-- Simultaneous unitary conjugation preserves the quadratic form of a product. -/
theorem stateQForm_conjBy_mul_apply {I : Type*} [Fintype I] [DecidableEq I]
    (U A B : Op I) (hU : Uᴴ * U = 1) (psi : EuclideanSpace ℂ I) :
    stateQForm (applyOperatorToState U psi) (conjBy U A * conjBy U B) =
      stateQForm psi (A * B) := by
  rw [← stateQForm_conjTranspose_mul_mul]
  congr 1
  simp only [conjBy]
  calc
    _ = (Uᴴ * U) * A * (Uᴴ * U) * B * (Uᴴ * U) := by noncomm_ring
    _ = A * B := by rw [hU]; simp

namespace ProjectiveSetting

variable {P : AdmissibleParams} {epsilon deltaG : ℝ}
    (S : ProjectiveSetting P epsilon)

/-- The total Pauli POVM extended to the full local extraction block and
conjugated by the concrete swap. This is the measurement in `eq:qld-unitary-7`. -/
def swappedPauliMeas (w : GlobalPairWitness S deltaG) (side : PlayerSide)
    (W : PauliKind) : Measurement (PauliRegister P) (ExtractionBlock P (S.LocalSpace side)) :=
  Measurement.ofSumEqOne
    (fun h => conjBy (swapUnitary w side) (S.onPlayer side ((S.pauliMeas side W).effect h)))
    (fun h => by
      apply star_right_conjugate_nonneg
      exact kronecker_nonneg
        (kronecker_nonneg ((S.pauliMeas side W).pos h) Matrix.PosSemidef.one.nonneg)
        Matrix.PosSemidef.one.nonneg)
    (by
      simp only [conjBy, onPlayer, ← Finset.sum_mul, ← Matrix.mul_sum,
        ← heteroKron_finset_sum_left, (S.pauliMeas side W).sum_eq_one,
        heteroKron_one_one, Matrix.mul_one, swapUnitary_mul_conjTranspose])

/-- Coarse-graining commutes with extending and conjugating the Pauli POVM. -/
theorem swappedPauliMeas_eval_effect (w : GlobalPairWitness S deltaG)
    (side : PlayerSide) (W : PauliKind) (u : Fin P.m → PauliScalar P)
    (a : PauliScalar P) :
    ((S.swappedPauliMeas w side W).postprocess
      (fun h => evalPoly (encodingPoly h) u)).effect a =
      conjBy (swapUnitary w side) (S.onPlayer side ((S.pauliEvalMeas side W u).effect a)) := by
  simp only [swappedPauliMeas, Measurement.postprocess_effect, Measurement.ofSumEqOne,
    pauliEvalMeas, conjBy, onPlayer, ← Finset.sum_mul, ← Matrix.mul_sum,
    ← heteroKron_finset_sum_left]
  rfl

/-- Original-player placement agrees with extension to the whole local block. -/
theorem placeSide_onPlayer (side : PlayerSide) (A : Op (S.LocalSpace side)) :
    S.placeSide side (S.onPlayer side A) = S.placePlayer side A := by
  cases side
  · exact S.placeSide_alice_tensor_one _
  · exact S.placeSide_bob_tensor_one _

/-- The canonical last-register effect has the same block and crossed placements. -/
theorem placeSide_extracted (side : PlayerSide) (T : Op (PauliRegister P)) :
    S.placeSide side (heteroKron (1 : Op (S.ExpandedLocalSpace side)) T) =
      S.placeExtractedRegister side T := by
  cases side
  · ext row col
    change
      ((if (row.1.1, row.1.2.1) = (col.1.1, col.1.2.1) then (1 : ℂ) else 0) *
        T row.1.2.2 col.1.2.2) *
        (if ((row.2.1, row.2.2.1), row.2.2.2) =
          ((col.2.1, col.2.2.1), col.2.2.2) then 1 else 0) =
      (if row.1.1 = col.1.1 then 1 else 0) *
        (if row.1.2.1 = col.1.2.1 then 1 else 0) *
        ((if row.2.1 = col.2.1 then 1 else 0) * T row.1.2.2 col.1.2.2) *
        (if row.2.2.1 = col.2.2.1 then 1 else 0) *
        (if row.2.2.2 = col.2.2.2 then 1 else 0)
    simp only [Prod.mk.injEq, ite_and, ite_mul, mul_ite, one_mul, mul_one,
      zero_mul, mul_zero]
    split_ifs <;> rfl
  · ext row col
    change
      (if ((row.1.1, row.1.2.1), row.1.2.2) =
        ((col.1.1, col.1.2.1), col.1.2.2) then (1 : ℂ) else 0) *
        ((if (row.2.1, row.2.2.1) = (col.2.1, col.2.2.1) then 1 else 0) *
          T row.2.2.2 col.2.2.2) =
      ((if row.1.1 = col.1.1 then 1 else 0) * T row.2.2.2 col.2.2.2) *
        (if row.1.2.1 = col.1.2.1 then 1 else 0) *
        (if row.1.2.2 = col.1.2.2 then 1 else 0) *
        (if row.2.1 = col.2.1 then 1 else 0) *
        (if row.2.2.1 = col.2.2.1 then 1 else 0)
    simp only [Prod.mk.injEq, ite_and, ite_mul, mul_ite, one_mul, mul_one,
      zero_mul, mul_zero]
    split_ifs <;> rfl

/-- Block placement preserves conjugation. -/
theorem placeSide_conjBy (side : PlayerSide)
    (U A : Op (ExtractionBlock P (S.LocalSpace side))) :
    S.placeSide side (conjBy U A) = conjBy (S.placeSide side U) (S.placeSide side A) := by
  cases side <;>
    simp only [placeSide, conjBy, ← reindexOp_conjTranspose,
      ← WinImplications.reindexOp_mul, MagicSquareRigidity.heteroKron_conjTranspose,
      heteroKron_mul, Matrix.conjTranspose_one, Matrix.mul_one] <;> rfl

/-- Conjugated total-Pauli effects in block coordinates give exactly the
six-register operators required by the extraction witness. -/
theorem placeSide_swappedPauliMeas (w : GlobalPairWitness S deltaG)
    (side : PlayerSide) (W : PauliKind) (h : PauliRegister P) :
    S.placeSide side ((S.swappedPauliMeas w side W).effect h) =
      conjBy (S.placeSide side (swapUnitary w side))
        (S.placePlayer side ((S.pauliMeas side W).effect h)) := by
  exact (S.placeSide_conjBy side _ _).trans
    (congrArg (conjBy (S.placeSide side (swapUnitary w side))) (S.placeSide_onPlayer side _))

/-- The evaluated canonical block measurement is the swap-conjugated
pulled-apart measurement, by `eq:qld-unitary-6`. -/
theorem canonical_eval_eq_conj_tildeM (w : GlobalPairWitness S deltaG)
    (side : PlayerSide) (W : PauliKind) (u : Fin P.m → PauliScalar P)
    (a : PauliScalar P) :
    ((rightPlacedMeasurement (ιA := S.ExpandedLocalSpace side)
      (pauliRegisterMeas (params := P) W)).postprocess
      (fun h => evalPoly (encodingPoly h) u)).effect a =
      conjBy (swapUnitary w side) (tildeM w side W (indicatorVec u) a) := by
  rw [swapUnitary_conj_tildeM]
  simp only [Measurement.postprocess_effect, rightPlacedMeasurement,
    Measurement.ofSumEqOne, pauliRegisterMeas, bracketOp, ← heteroKron_finset_sum_right]
  rfl

/-- Multiplying the two block placements is their tensor product in block coordinates. -/
theorem reindexOp_heteroKron_eq_placeSides
    (A : Op (ExtractionBlock P S.toStrategy.ιA))
    (B : Op (ExtractionBlock P S.toStrategy.ιB)) :
    reindexOp (sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB)
      (heteroKron A B) = S.placeSide .alice A * S.placeSide .bob B := by
  simp only [placeSide, ← WinImplications.reindexOp_mul, heteroKron_mul,
    Matrix.mul_one, Matrix.one_mul]

/-- On the jointly swapped state, the overlap of conjugated block measurements
is one minus their original consistency defect. This is simultaneous unitary
invariance with the exact six-register reassociation. -/
theorem swapped_block_overlap_eq (w : GlobalPairWitness S deltaG)
    {X α : Type*} [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    (mu : Distribution X) (hmu : mu.IsProbability)
    (A : X → Measurement α (ExtractionBlock P S.toStrategy.ιA))
    (B : X → Measurement α (ExtractionBlock P S.toStrategy.ιB)) :
    avgOver mu (fun x => ∑ a, stateQForm
      (reindexState (sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB)
        (S.applyBoth (swapUnitary w .alice) (swapUnitary w .bob) S.psiHat))
      (heteroKron (conjBy (swapUnitary w .alice) ((A x).effect a))
        (conjBy (swapUnitary w .bob) ((B x).effect a)))) =
      1 - consistencyDefect mu
        (fun x a => S.placeSide .alice ((A x).effect a))
        (fun x a => S.placeSide .bob ((B x).effect a)) S.psiHat := by
  have h := consistencyDefect_eq_one_sub_overlap mu
    (fun x => S.blockMeasurement .alice (A x))
    (fun x => S.blockMeasurement .bob (B x)) S.psiHat hmu S.psiHat_norm
  simp only [blockMeasurement_effect] at h
  rw [h, sub_sub_cancel]
  apply avgOver_congr
  intro x
  apply Finset.sum_congr rfl
  intro a _
  rw [WinImplications.stateQForm_reindexState, S.reindexOp_heteroKron_eq_placeSides]
  erw [← S.conjBy_placeBoth_swap_placeSide w .alice,
    ← S.conjBy_placeBoth_swap_placeSide w .bob]
  exact stateQForm_conjBy_mul_apply _ _ _ (S.placeBoth_swap_left_unitary w) S.psiHat

set_option maxHeartbeats 800000 in
/-- Alice's evaluated swapped total-Pauli overlap with Bob's canonical
measurement is exactly one minus the evaluated-Pauli/tilde consistency defect. -/
theorem swapped_pauli_overlap_alice (w : GlobalPairWitness S deltaG) (W : PauliKind) :
    avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun u =>
      ∑ a : PauliScalar P, stateQForm
        (reindexState (sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB)
          (S.applyBoth (swapUnitary w .alice) (swapUnitary w .bob) S.psiHat))
        (heteroKron (((S.swappedPauliMeas w .alice W).postprocess
          (fun h => evalPoly (encodingPoly h) u)).effect a)
          (((rightPlacedMeasurement (ιA := S.ExpandedLocalSpace .bob)
            (pauliRegisterMeas (params := P) W)).postprocess
            (fun h => evalPoly (encodingPoly h) u)).effect a))) =
      1 - consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u a => S.placePlayer .alice ((S.pauliEvalMeas .alice W u).effect a))
        (fun u a => S.placeSide .bob (tildeM w .bob W (indicatorVec u) a)) S.psiHat := by
  simp only [S.swappedPauliMeas_eval_effect]
  simp_rw [S.canonical_eval_eq_conj_tildeM w .bob]
  have h := S.swapped_block_overlap_eq w _ (uniformDistribution_isProbability _)
    (fun u => leftPlacedMeasurement (leftPlacedMeasurement (S.pauliEvalMeas .alice W u)))
    (fun u => Measurement.ofSumEqOne (tildeM w .bob W (indicatorVec u))
      (fun a => (tildeM_isProj w .bob W (indicatorVec u) a).nonneg)
      (sum_tildeM_eq_one w .bob W (indicatorVec u)))
  have hplace (u : Fin P.m → PauliScalar P) (a : PauliScalar P) :=
    S.placeSide_onPlayer .alice ((S.pauliEvalMeas .alice W u).effect a)
  convert
    (h.trans (congrArg (fun f => 1 - consistencyDefect _ f _ S.psiHat)
      (funext fun u => funext fun a => hplace u a))) using 1 <;> rfl

set_option maxHeartbeats 800000 in
/-- Bob's evaluated swapped total-Pauli overlap with Alice's canonical
measurement satisfies the same exact transport, without strategy symmetry. -/
theorem swapped_pauli_overlap_bob (w : GlobalPairWitness S deltaG) (W : PauliKind) :
    avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun u =>
      ∑ a : PauliScalar P, stateQForm
        (reindexState (sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB)
          (S.applyBoth (swapUnitary w .alice) (swapUnitary w .bob) S.psiHat))
        (heteroKron (((rightPlacedMeasurement (ιA := S.ExpandedLocalSpace .alice)
            (pauliRegisterMeas (params := P) W)).postprocess
            (fun h => evalPoly (encodingPoly h) u)).effect a)
          (((S.swappedPauliMeas w .bob W).postprocess
            (fun h => evalPoly (encodingPoly h) u)).effect a))) =
      1 - consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u a => S.placeSide .alice (tildeM w .alice W (indicatorVec u) a))
        (fun u a => S.placePlayer .bob ((S.pauliEvalMeas .bob W u).effect a)) S.psiHat := by
  simp only [S.swappedPauliMeas_eval_effect]
  simp_rw [S.canonical_eval_eq_conj_tildeM w .alice]
  have h := S.swapped_block_overlap_eq w _ (uniformDistribution_isProbability _)
    (fun u => Measurement.ofSumEqOne (tildeM w .alice W (indicatorVec u))
      (fun a => (tildeM_isProj w .alice W (indicatorVec u) a).nonneg)
      (sum_tildeM_eq_one w .alice W (indicatorVec u)))
    (fun u => leftPlacedMeasurement (leftPlacedMeasurement (S.pauliEvalMeas .bob W u)))
  have hplace (u : Fin P.m → PauliScalar P) (a : PauliScalar P) :=
    S.placeSide_onPlayer .bob ((S.pauliEvalMeas .bob W u).effect a)
  convert
    (h.trans (congrArg (fun f => 1 - consistencyDefect _ _ f S.psiHat)
      (funext fun u => funext fun a => hplace u a))) using 1 <;> rfl

end ProjectiveSetting

end

end MIPStarRE.QPBT
