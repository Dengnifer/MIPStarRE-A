import MIPStarRE.QPBT.Extraction.SuppliedPointConsistency
import MIPStarRE.QPBT.Extraction.PullingDefect

/-!
# Evaluated total-Pauli consistency before extraction

The supplied-witness point estimates combine with point self-consistency and
the two orientations of the game's Pauli-basis check. All estimates act on the
original six-register state, before conjugation by the swaps.

## References

Blueprint `lem:qld-unitary`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1785-1810`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Classical

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum DistanceCalculus
open MIPStarRE.LDT hiding Measurement

noncomputable section

/-- Reversing complete measurement families preserves their real consistency
defect, even when the effects do not commute. -/
theorem consistencyDefect_measurement_symm {X α I : Type*}
    [Fintype X] [DecidableEq X]
    [Fintype α] [DecidableEq α] [Fintype I] [DecidableEq I]
    (mu : Distribution X) (A B : X → Measurement α I) (psi : EuclideanSpace ℂ I) :
    consistencyDefect mu (fun x a => (A x).effect a) (fun x a => (B x).effect a) psi =
      consistencyDefect mu (fun x a => (B x).effect a) (fun x a => (A x).effect a) psi := by
  unfold consistencyDefect
  apply avgOver_congr
  intro x
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  by_cases hab : a = b
  · simp [hab]
  · simp only [if_neg hab, if_neg (Ne.symm hab), consistency_term_eq_stateQForm]
    have hstar : ((A x).effect a * (B x).effect b)ᴴ =
        (B x).effect b * (A x).effect a := by
      simp only [Matrix.conjTranspose_mul, measurement_effect_hermitian]
    rw [← hstar]
    unfold stateQForm applyOperatorToState
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_right]
    exact inner_re_symm (𝕜 := ℂ) _ _

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

/-- Original-register quadratic forms are unchanged by adjoining the two EPR
pairs. This allows each evaluated Pauli check to be used on `psiHat`. -/
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

/-- The same invariance holds for the complete consistency defect of any two
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

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- Both evaluated total-Pauli measurements are consistent with the opposite
pulled-apart measurement at one universal construction scale. This proves the
two-player form of paper `eq:qld-unitary-5` from the actual game checks.

**Unfaithful:** The global witness is supplied, as in the recovered point
estimates. Its construction and the source-facing composition remain open
under issue #123 and `docs/paper-gaps/qpbt_extraction-transfer.tex`. -/
theorem evaluated_pauli_tilde_consistency_ofGlobalPairWitness :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (P : AdmissibleParams) (epsilon deltaG : ℝ),
      0 ≤ epsilon → epsilon ≤ 1 → 0 ≤ deltaG →
      ∀ (S : ProjectiveSetting P epsilon) (w : GlobalPairWitness S deltaG) (W : PauliKind),
      consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
          (fun u a => S.placePlayer .alice ((S.pauliEvalMeas .alice W u).effect a))
          (fun u a => S.placeSide .bob (tildeM w .bob W (indicatorVec u) a)) S.psiHat ≤
        deltaConstructPaulis C epsilon deltaG P.m P.d P.q ∧
      consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
          (fun u a => S.placeSide .alice (tildeM w .alice W (indicatorVec u) a))
          (fun u a => S.placePlayer .bob ((S.pauliEvalMeas .bob W u).effect a)) S.psiHat ≤
        deltaConstructPaulis C epsilon deltaG P.m P.d P.q := by
  obtain ⟨CA, hCA, hA⟩ := tildeM_consistent_pointMeas_ofGlobalPairWitness
  obtain ⟨CB, hCB, hB⟩ := tildeM_consistent_pointMeas'_ofGlobalPairWitness
  obtain ⟨CF, hCF, hF⟩ := win_pauli_basis_cons
  obtain ⟨CR, hCR, hR⟩ := WinImplications.win_pauli_basis_cons_interchanged_proof
  let E : ℝ := Fintype.card PauliEdge
  let K : ℝ := max CF CR
  let L : ℝ := max CA CB
  let C : ℝ := L + 2 * Real.sqrt (E + K)
  have hL : 1 ≤ L := hCA.trans (le_max_left _ _)
  have hC : 1 ≤ C := by dsimp [C]; linarith [Real.sqrt_nonneg (E + K)]
  refine ⟨C, hC, ?_⟩
  intro P epsilon deltaG he he1 hd S w W
  let mu := uniformDistribution (Fin P.m → PauliScalar P)
  let PA := fun u => S.placedMeasurement .AA' (leftPlacedMeasurement (S.pointMeas .alice W u))
  let PB := fun u => S.placedMeasurement .BB' (leftPlacedMeasurement (S.pointMeas .bob W u))
  let QA := fun u => S.placedMeasurement .AA'
    (leftPlacedMeasurement (S.pauliEvalMeas .alice W u))
  let QB := fun u => S.placedMeasurement .BB'
    (leftPlacedMeasurement (S.pauliEvalMeas .bob W u))
  let T := fun (side : PlayerSide) (u : Fin P.m → PauliScalar P) =>
    S.blockMeasurement side (Measurement.ofSumEqOne
      (tildeM w side W (indicatorVec u))
      (fun a => (tildeM_isProj w side W (indicatorVec u) a).nonneg)
      (sum_tildeM_eq_one w side W (indicatorVec u)))
  have hpoints : consistencyDefect mu (fun u a => (PA u).effect a)
      (fun u a => (PB u).effect a) S.psiHat ≤ E * epsilon := by
    change consistencyDefect mu (fun u a => S.placePlayer .alice _)
      (fun u a => S.placePlayer .bob _) S.psiHat ≤ _
    rw [S.consistencyDefect_placePlayers]
    exact point_self_consistency_le S W
  have hforward : consistencyDefect mu (fun u a => (PA u).effect a)
      (fun u a => (QB u).effect a) S.psiHat ≤ K * epsilon := by
    change consistencyDefect mu (fun u a => S.placePlayer .alice _)
      (fun u a => S.placePlayer .bob _) S.psiHat ≤ _
    rw [S.consistencyDefect_placePlayers]
    exact (hF P epsilon S he W).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) he)
  have hreverse : consistencyDefect mu (fun u a => (QA u).effect a)
      (fun u a => (PB u).effect a) S.psiHat ≤ K * epsilon := by
    change consistencyDefect mu (fun u a => S.placePlayer .alice _)
      (fun u a => S.placePlayer .bob _) S.psiHat ≤ _
    rw [S.consistencyDefect_placePlayers]
    exact (hR P epsilon S he W).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) he)
  have hleft : consistencyDefect mu (fun u a => (T .alice u).effect a)
      (fun u a => (PB u).effect a) S.psiHat ≤
        deltaConstructPaulis L epsilon deltaG P.m P.d P.q := by
    change consistencyDefect mu
      (fun u a => S.placeSide .alice (tildeM w .alice W (indicatorVec u) a))
      (fun u a => S.placePlayer .bob ((S.pointMeas .bob W u).effect a)) S.psiHat ≤ _
    have h := hB P epsilon deltaG he he1 hd S w W
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by
      positivity))
  have hright : consistencyDefect mu (fun u a => (PA u).effect a)
      (fun u a => (T .bob u).effect a) S.psiHat ≤
        deltaConstructPaulis L epsilon deltaG P.m P.d P.q := by
    change consistencyDefect mu
      (fun u a => S.placePlayer .alice ((S.pointMeas .alice W u).effect a))
      (fun u a => S.placeSide .bob (tildeM w .bob W (indicatorVec u) a)) S.psiHat ≤ _
    have h := hA P epsilon deltaG he he1 hd S w W
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by
      positivity))
  have hscalar : deltaConstructPaulis L epsilon deltaG P.m P.d P.q +
      2 * Real.sqrt (E * epsilon + K * epsilon) ≤
        deltaConstructPaulis C epsilon deltaG P.m P.d P.q := by
    have hEK : 0 ≤ E + K := add_nonneg (Nat.cast_nonneg _)
      ((by linarith : 0 ≤ CF).trans (le_max_left _ _))
    rw [← add_mul, Real.sqrt_mul hEK]
    change L * (deltaG + Real.sqrt epsilon + ((P.m * P.d : ℕ) : ℝ) / P.q) +
      2 * (Real.sqrt (E + K) * Real.sqrt epsilon) ≤
      (L + 2 * Real.sqrt (E + K)) *
        (deltaG + Real.sqrt epsilon + ((P.m * P.d : ℕ) : ℝ) / P.q)
    have hr : 0 ≤ ((P.m * P.d : ℕ) : ℝ) / P.q := by positivity
    nlinarith [Real.sqrt_nonneg (E + K)]
  constructor
  · change consistencyDefect mu (fun u a => (QA u).effect a)
      (fun u a => (T .bob u).effect a) S.psiHat ≤ _
    rw [consistencyDefect_measurement_symm]
    apply (consistencyDefect_trans_le mu (T .bob) PA PB QA S.psiHat _ _ _
      (uniformDistribution_isProbability _) S.psiHat_norm ?_ ?_ ?_).trans hscalar
    · rw [consistencyDefect_measurement_symm]; exact hright
    · rw [consistencyDefect_measurement_symm]; exact hpoints
    · rw [consistencyDefect_measurement_symm]; exact hreverse
  · exact (consistencyDefect_trans_le mu (T .alice) PB PA QB S.psiHat _ _ _
      (uniformDistribution_isProbability _) S.psiHat_norm hleft hpoints hforward).trans hscalar

end

end MIPStarRE.QPBT
