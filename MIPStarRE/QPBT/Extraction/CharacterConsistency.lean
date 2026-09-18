import MIPStarRE.QPBT.Combining.Points.Commutation
import MIPStarRE.QPBT.Extraction.Observables

/-!
# Finite-character estimates for extracted observables

Parseval identifies the uniform average over field characters with the sum of
squared outcome norms. A fixed binary basis character instead admits a bound
by four times the consistency defect, using binary postprocessing.

## References

These are finite-dimensional auxiliary results for blueprint
`lem:qld-construct-the-paulis`, Item 2, and paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1542-1551`.
They do not assert the preceding pulled-apart measurement comparison
`eq:qld-pulling-cons`, whose extraction obligation is recorded under
issue #123 in `docs/paper-gaps/qpbt_extraction-transfer.tex`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus
open WinImplications

noncomputable section

/-- Parseval for the fixed field trace, with a uniform character average and
an unnormalized outcome sum. This specializes the orthogonality theorem used
for blueprint `lem:qld-4-10`; no measurement assumptions are needed. -/
theorem avg_norm_fixed_character_sum_sq {P : AdmissibleParams} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (v : PauliScalar P → E) :
    avgOver (uniformDistribution (PauliScalar P)) (fun r =>
      ‖∑ a, phaseSign (fixedBinTrace P.model (r * a)) • v a‖ ^ 2) =
      ∑ a, ‖v a‖ ^ 2 := by
  classical
  have horth (a b : PauliScalar P) :
      ∑ r : PauliScalar P,
        (starRingEnd ℂ) (phaseSign (fixedBinTrace P.model (r * a))) *
          phaseSign (fixedBinTrace P.model (r * b)) =
        if a = b then ((Fintype.card (PauliScalar P) : ℝ) : ℂ) else 0 := by
    simpa only [← Complex.star_def, star_phaseSign, Complex.ofReal_natCast] using
      sum_fixedCharacter_mul_fixedCharacter a b
  rw [avgOver_uniform_eq_inv_card_mul_sum,
    sum_norm_sum_smul_sq_of_orthogonal _ _ horth v, ← mul_assoc,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_mul]

/-- Multiplication by a chosen basis element only permutes the characters.
The basis coordinate is fixed, not averaged, in this normalized Parseval
identity supporting blueprint `lem:qld-construct-the-paulis`, Item 2. -/
theorem avg_norm_basis_character_sum_sq {P : AdmissibleParams} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (j : Fin P.model.basisDim) (v : PauliScalar P → E) :
    avgOver (uniformDistribution (PauliScalar P)) (fun r =>
      ‖∑ a, phaseSign (fixedBinTrace P.model (P.model.basis j * r * a)) • v a‖ ^ 2) =
      ∑ a, ‖v a‖ ^ 2 := by
  classical
  rw [avgOver_uniform_eq_inv_card_mul_sum]
  have hsum := Equiv.sum_comp
    (Equiv.mulLeft₀ (P.model.basis j) (P.model.basis.ne_zero j))
    (fun r => ‖∑ a, phaseSign (fixedBinTrace P.model (r * a)) • v a‖ ^ 2)
  change (∑ r, ‖∑ a,
    phaseSign (fixedBinTrace P.model (P.model.basis j * r * a)) • v a‖ ^ 2) = _ at hsum
  rw [hsum]
  exact (avgOver_uniform_eq_inv_card_mul_sum _).symm.trans
    (avg_norm_fixed_character_sum_sq v)

/-- Regroup a field-weighted observable by its binary trace label. This is the
postprocessing at paper `14_analysis_of_the_pauli_basis_test.tex:1547-1551`. -/
theorem sum_basis_character_effect_eq {P : AdmissibleParams} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (A : Measurement (PauliScalar P) ι)
    (j : Fin P.model.basisDim) :
    (∑ a, phaseSign (fixedBinTrace P.model (P.model.basis j * a)) • A.effect a) =
      ∑ b : ZMod 2, phaseSign b •
        (A.postprocess (fun a => fixedBinTrace P.model (P.model.basis j * a))).effect b := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := fun a : PauliScalar P => fixedBinTrace P.model (P.model.basis j * a))
    (t := (Finset.univ : Finset (ZMod 2))) (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro b _
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [(Finset.mem_filter.mp ha).2]

/-- A fixed basis character costs at most four times the field measurement
consistency defect. The question distribution and basis coordinate are retained
exactly. This proves the final conversion in blueprint
`lem:qld-construct-the-paulis`, without assuming a bound on that defect. -/
theorem basis_character_opDistSq_le_four_consistencyDefect
    {P : AdmissibleParams} {X ιA ιB : Type*}
    [Fintype X] [DecidableEq X]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : Distribution X) (A : X → Measurement (PauliScalar P) ιA)
    (B : X → Measurement (PauliScalar P) ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (j : Fin P.model.basisDim) :
    opDistSq μ
      (fun x => heteroKron
        (∑ a, phaseSign (fixedBinTrace P.model (P.model.basis j * a)) • (A x).effect a) 1)
      (fun x => heteroKron 1
        (∑ a, phaseSign (fixedBinTrace P.model (P.model.basis j * a)) • (B x).effect a)) ψ ≤
      4 * consistencyDefect μ (fun x a => heteroKron ((A x).effect a) 1)
        (fun x a => heteroKron 1 ((B x).effect a)) ψ := by
  classical
  let f := fun a : PauliScalar P => fixedBinTrace P.model (P.model.basis j * a)
  let A' := fun x => (A x).postprocess f
  let B' := fun x => (B x).postprocess f
  have hdef := consistencyDefect_postprocess_le μ A B ψ f
  have hfam := (opFamilyDistSq_le_two_mul_consistencyDefect μ
    (fun x => leftPlacedMeasurement (A' x))
    (fun x => rightPlacedMeasurement (B' x)) ψ).trans
      (mul_le_mul_of_nonneg_left hdef (by norm_num : (0 : ℝ) ≤ 2))
  have hobs := povm_to_obs_of_measurements μ
    (fun x => leftPlacedMeasurement (A' x))
    (fun x => rightPlacedMeasurement (B' x)) phaseSign norm_phaseSign ψ
  simp only [ZMod.card, Nat.cast_ofNat] at hobs
  have hbound := hobs.trans (mul_le_mul_of_nonneg_left hfam (by norm_num : (0 : ℝ) ≤ 2))
  simpa only [sum_basis_character_effect_eq, heteroKron_left_sum_smul,
    heteroKron_right_sum_smul, leftPlacedMeasurement, rightPlacedMeasurement,
    MIPStarRE.Quantum.Measurement.ofSumEqOne, ← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num]
    using hbound

/-- The final measurement-to-observable step of blueprint
`lem:qld-construct-the-paulis`, Item 2, on the original six-register state.
The measurement consistency defect is an explicit quantity, not an assumed
bound. Its construction-scale bound is the `eq:qld-pulling-cons`
extraction obligation recorded under issue #123 in
`docs/paper-gaps/qpbt_extraction-transfer.tex`; it is not supplied here. -/
theorem tildeObs_opDistSq_le_four_consistencyDefect
    {P : AdmissibleParams} {epsilon deltaG : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S deltaG)
    (W : PauliKind) (j : Fin P.model.basisDim) :
    opDistSq (uniformDistribution (PauliRegister P))
      (fun u => S.placeSide .alice (tildeObs w .alice W u j))
      (fun u => S.placeSide .bob (tildeObs w .bob W u j)) S.psiHat ≤
      4 * consistencyDefect (uniformDistribution (PauliRegister P))
        (fun u a => S.placeSide .alice (tildeM w .alice W u a))
        (fun u a => S.placeSide .bob (tildeM w .bob W u a)) S.psiHat := by
  classical
  let M (side : PlayerSide) (u : PauliRegister P) :
      Measurement (PauliScalar P) (ExtractionBlock P (S.LocalSpace side)) :=
    MIPStarRE.Quantum.Measurement.ofSumEqOne (tildeM w side W u)
      (fun a => (tildeM_isProj w side W u a).nonneg) (sum_tildeM_eq_one w side W u)
  let e := sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB
  have h := basis_character_opDistSq_le_four_consistencyDefect
    (uniformDistribution (PauliRegister P)) (M .alice) (M .bob)
    (reindexState e S.psiHat) j
  have hd : opDistSq (uniformDistribution (PauliRegister P))
      (fun u => heteroKron (tildeObs w .alice W u j) 1)
      (fun u => heteroKron 1 (tildeObs w .bob W u j)) (reindexState e S.psiHat) =
      opDistSq (uniformDistribution (PauliRegister P))
        (fun u => S.placeSide .alice (tildeObs w .alice W u j))
        (fun u => S.placeSide .bob (tildeObs w .bob W u j)) S.psiHat := by
    unfold opDistSq opFamilyDistSq
    simp only [Fintype.sum_unique]
    apply avgOver_congr
    intro u
    rw [norm_applyOperatorToState_reindexState, reindexOp_sub]
    rfl
  have hc : consistencyDefect (uniformDistribution (PauliRegister P))
      (fun u a => heteroKron (tildeM w .alice W u a) 1)
      (fun u a => heteroKron 1 (tildeM w .bob W u a)) (reindexState e S.psiHat) =
      consistencyDefect (uniformDistribution (PauliRegister P))
        (fun u a => S.placeSide .alice (tildeM w .alice W u a))
        (fun u a => S.placeSide .bob (tildeM w .bob W u a)) S.psiHat := by
    unfold consistencyDefect
    apply avgOver_congr
    intro u
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    by_cases hab : a = b
    · simp only [hab, if_true]
    · simp only [if_neg hab, consistency_term_eq_stateQForm]
      rw [stateQForm_reindexState, reindexOp_mul]
      rfl
  change opDistSq _ (fun u => heteroKron (tildeObs w .alice W u j) 1)
    (fun u => heteroKron 1 (tildeObs w .bob W u j)) _ ≤
      4 * consistencyDefect _ (fun u a => heteroKron (tildeM w .alice W u a) 1)
        (fun u a => heteroKron 1 (tildeM w .bob W u a)) _ at h
  rwa [hd, hc] at h

end

end MIPStarRE.QPBT
