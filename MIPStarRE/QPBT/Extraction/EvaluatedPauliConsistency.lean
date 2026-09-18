import MIPStarRE.QPBT.Extraction.SuppliedPointConsistency
import MIPStarRE.QPBT.Extraction.BlockMeasurement
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
