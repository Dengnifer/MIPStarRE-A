import MIPStarRE.QPBT.Test.Soundness.StateTransfer

/-!
# Operator transfer from supplied extraction data

The complete swap-conjugated measurements intertwine with the local ancilla
isometries. The range-projection estimates then transfer both Pauli families
to the ideal state, with squared error at most four times the extraction error.

## References

Formalization support for the final argument at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1864-1875`.
This conditional construction uses supplied extraction data in a projective
setting; it does not prove blueprint `thm:pauli`. The omitted range projection
is documented in `docs/paper-gaps/qpbt_extraction-transfer.tex` (issue #529).
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum MagicSquareRigidity DistanceCalculus

noncomputable section

variable {P : AdmissibleParams} {epsilon deltaG delta : ℝ}
  {S : ProjectiveSetting P epsilon} {w : GlobalPairWitness S deltaG}

private theorem extracted_alice_eq (W : PauliKind) (h : PauliRegister P) :
    S.placeExtractedRegister .alice (pauliProj W h) =
      reindexOp (sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB)
        (pauliProjOnA'' P (ιA' := S.toStrategy.ιA × PauliRegister P)
          (ιB' := S.toStrategy.ιB × PauliRegister P) W h) := by
  ext i j
  change (1 : Op S.toStrategy.ιA) i.1.1 j.1.1 *
    (1 : Op (PauliRegister P)) i.1.2.1 j.1.2.1 *
    ((1 : Op S.toStrategy.ιB) i.2.1 j.2.1 * pauliProj W h i.1.2.2 j.1.2.2) *
    (1 : Op (PauliRegister P)) i.2.2.1 j.2.2.1 *
    (1 : Op (PauliRegister P)) i.2.2.2 j.2.2.2 = _
  simp [reindexOp, sixRegExtractionEquiv, pauliProjOnA'',
    Matrix.one_apply, Prod.ext_iff, ite_and, mul_ite, ite_mul]
  split_ifs <;> simp_all

private theorem extracted_bob_eq (W : PauliKind) (h : PauliRegister P) :
    S.placeExtractedRegister .bob (pauliProj W h) =
      reindexOp (sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB)
        (pauliProjOnB'' P (ιA' := S.toStrategy.ιA × PauliRegister P)
          (ιB' := S.toStrategy.ιB × PauliRegister P) W h) := by
  ext i j
  change ((1 : Op S.toStrategy.ιA) i.1.1 j.1.1 * pauliProj W h i.2.2.2 j.2.2.2) *
    (1 : Op (PauliRegister P)) i.1.2.1 j.1.2.1 *
    (1 : Op (PauliRegister P)) i.1.2.2 j.1.2.2 *
    (1 : Op S.toStrategy.ιB) i.2.1 j.2.1 *
    (1 : Op (PauliRegister P)) i.2.2.1 j.2.2.1 = _
  simp [reindexOp, sixRegExtractionEquiv, pauliProjOnB'',
    Matrix.one_apply, Prod.ext_iff, ite_and, mul_ite, ite_mul]
  split_ifs <;> simp_all

private theorem conjugated_alice_eq (_v : ExtractionWitness S w delta)
    (W : PauliKind) (h : PauliRegister P) :
    conjBy (S.placeSide .alice (swapUnitary w .alice))
        (S.placePlayer .alice ((S.pauliMeas .alice W).effect h)) =
      reindexOp (sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB)
        (heteroKron ((S.swappedPauliMeas w .alice W).effect h) 1) := by
  exact (S.placeSide_swappedPauliMeas w .alice W h).symm

private theorem conjugated_bob_eq (_v : ExtractionWitness S w delta)
    (W : PauliKind) (h : PauliRegister P) :
    conjBy (S.placeSide .bob (swapUnitary w .bob))
        (S.placePlayer .bob ((S.pauliMeas .bob W).effect h)) =
      reindexOp (sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB)
        (heteroKron 1 ((S.swappedPauliMeas w .bob W).effect h)) := by
  exact (S.placeSide_swappedPauliMeas w .bob W h).symm

private theorem full_pauli_distance_alice (v : ExtractionWitness S w delta)
    (W : PauliKind) :
    ∑ h : PauliRegister P, ‖applyOperatorToState
      (heteroKron ((S.swappedPauliMeas w .alice W).effect h) 1 -
        pauliProjOnA'' P W h) (idealState P v.toPauliSoundnessWitness.aux)‖ ^ 2 ≤ delta := by
  classical
  have hc := v.pauli_close .alice W
  rw [opFamilyDistSq_uniform_unit] at hc
  simp_rw [conjugated_alice_eq v, extracted_alice_eq,
    ← WinImplications.reindexOp_sub,
    ← WinImplications.norm_applyOperatorToState_reindexState] at hc
  rw [v.idealState_eq]
  exact hc

private theorem full_pauli_distance_bob (v : ExtractionWitness S w delta)
    (W : PauliKind) :
    ∑ h : PauliRegister P, ‖applyOperatorToState
      (heteroKron 1 ((S.swappedPauliMeas w .bob W).effect h) -
        pauliProjOnB'' P W h) (idealState P v.toPauliSoundnessWitness.aux)‖ ^ 2 ≤ delta := by
  classical
  have hc := v.pauli_close .bob W
  rw [opFamilyDistSq_uniform_unit] at hc
  simp_rw [conjugated_bob_eq v, extracted_bob_eq,
    ← WinImplications.reindexOp_sub,
    ← WinImplications.norm_applyOperatorToState_reindexState] at hc
  rw [v.idealState_eq]
  exact hc

/-- Alice's isometry-conjugated Pauli family has squared distance at most
`4 * delta` on the ideal state. Both the full-unitary comparison and the
squared state error are read from the supplied extraction witness. -/
theorem ExtractionWitness.pauli_distance_alice_le (v : ExtractionWitness S w delta)
    (W : PauliKind) :
    pauliOperatorDistanceA P S.toStrategy v.toPauliSoundnessWitness W ≤ 4 * delta := by
  have h := sum_norm_leftTensor_conjIsometry_sub_sq_le
    v.toPauliSoundnessWitness.φA v.toPauliSoundnessWitness.φB
    (S.pauliMeas .alice W).effect (S.swappedPauliMeas w .alice W)
    (pauliProjOnA'' P W)
    (fun h => unitaryAncillaIsometry_intertwines (eprState (PauliRegister P))
      (eprState_norm _) (swapUnitary w .alice) (v.swap_left_unitary .alice)
      ((S.pauliMeas .alice W).effect h))
    S.toStrategy.ψ (idealState P v.toPauliSoundnessWitness.aux)
  have hlift (M : Op S.toStrategy.ιA) :
      liftedAEffect S.toStrategy (ιB' := v.toPauliSoundnessWitness.ιB')
          v.toPauliSoundnessWitness.φA M =
        heteroKron (conjIsometry v.toPauliSoundnessWitness.φA M)
          (1 : Op (v.toPauliSoundnessWitness.ιB' × PauliRegister P)) := by
    ext i j
    simp [liftedAEffect, heteroKron, Matrix.kronecker, Matrix.one_apply]
  have hstate := v.state_close_ofExtractionWitness
  rw [norm_sub_rev] at hstate
  have hfull := full_pauli_distance_alice v W
  have hbound := h.trans ((add_le_add
    (mul_le_mul_of_nonneg_left hfull (by norm_num : (0 : ℝ) ≤ 2))
    (mul_le_mul_of_nonneg_left hstate (by norm_num : (0 : ℝ) ≤ 2))).trans_eq
      (show 2 * delta + 2 * delta = 4 * delta by ring))
  apply le_of_eq_of_le ?_ hbound
  unfold pauliOperatorDistanceA
  apply Finset.sum_congr rfl
  intro a _
  exact congrArg (fun O => ‖applyOperatorToState (O - pauliProjOnA'' P W a)
    (idealState P v.toPauliSoundnessWitness.aux)‖ ^ 2) (hlift _)

/-- Bob's isometry-conjugated Pauli family satisfies the same bound on the
same ideal state, without identifying the two original local spaces. -/
theorem ExtractionWitness.pauli_distance_bob_le (v : ExtractionWitness S w delta)
    (W : PauliKind) :
    pauliOperatorDistanceB P S.toStrategy v.toPauliSoundnessWitness W ≤ 4 * delta := by
  have h := sum_norm_rightTensor_conjIsometry_sub_sq_le
    v.toPauliSoundnessWitness.φA v.toPauliSoundnessWitness.φB
    (S.pauliMeas .bob W).effect (S.swappedPauliMeas w .bob W)
    (pauliProjOnB'' P W)
    (fun h => unitaryAncillaIsometry_intertwines (eprState (PauliRegister P))
      (eprState_norm _) (swapUnitary w .bob) (v.swap_left_unitary .bob)
      ((S.pauliMeas .bob W).effect h))
    S.toStrategy.ψ (idealState P v.toPauliSoundnessWitness.aux)
  have hlift (M : Op S.toStrategy.ιB) :
      liftedBEffect S.toStrategy (ιA' := v.toPauliSoundnessWitness.ιA')
          v.toPauliSoundnessWitness.φB M =
        heteroKron (1 : Op (v.toPauliSoundnessWitness.ιA' × PauliRegister P))
          (conjIsometry v.toPauliSoundnessWitness.φB M) := by
    ext i j
    simp [liftedBEffect, heteroKron, Matrix.kronecker, Matrix.one_apply]
  have hstate := v.state_close_ofExtractionWitness
  rw [norm_sub_rev] at hstate
  have hfull := full_pauli_distance_bob v W
  have hbound := h.trans ((add_le_add
    (mul_le_mul_of_nonneg_left hfull (by norm_num : (0 : ℝ) ≤ 2))
    (mul_le_mul_of_nonneg_left hstate (by norm_num : (0 : ℝ) ≤ 2))).trans_eq
      (show 2 * delta + 2 * delta = 4 * delta by ring))
  apply le_of_eq_of_le ?_ hbound
  unfold pauliOperatorDistanceB
  apply Finset.sum_congr rfl
  intro a _
  exact congrArg (fun O => ‖applyOperatorToState (O - pauliProjOnB'' P W a)
    (idealState P v.toPauliSoundnessWitness.aux)‖ ^ 2) (hlift _)

/-- Isometry transfer bounds for supplied extraction data in a projective
setting. The common bound is `max (sqrt delta) (4 * delta)`: the state norm
is unsquared and both operator distances sum squared norms over all outcomes.
This is blueprint `ex:pauli-supplied-extraction-support`, a conditional
support theorem for `thm:pauli`, not the source theorem.
Discharging the supplied-data premise requires the global-pair construction
and extraction; see `docs/paper-gaps/qpbt_extraction-transfer.tex`, issue #529. -/
theorem ExtractionWitness.isometry_transfer_bounds (v : ExtractionWitness S w delta) :
    ∃ t : PauliSoundnessWitness P S.toStrategy,
      ‖isometryTensor t.φA t.φB S.toStrategy.ψ - idealState P t.aux‖ ≤
        max (Real.sqrt delta) (4 * delta) ∧
      (∀ W : PauliKind, pauliOperatorDistanceA P S.toStrategy t W ≤
        max (Real.sqrt delta) (4 * delta)) ∧
      (∀ W : PauliKind, pauliOperatorDistanceB P S.toStrategy t W ≤
        max (Real.sqrt delta) (4 * delta)) := by
  refine ⟨v.toPauliSoundnessWitness, ?_, ?_, ?_⟩
  · exact (Real.le_sqrt_of_sq_le v.state_close_ofExtractionWitness).trans (le_max_left _ _)
  · intro W
    exact (v.pauli_distance_alice_le W).trans (le_max_right _ _)
  · intro W
    exact (v.pauli_distance_bob_le W).trans (le_max_right _ _)

/-- The actual transformed state lies in both local isometry ranges. These
identities impose no range condition on the ideal comparison state. -/
theorem ExtractionWitness.transformed_state_in_ranges (v : ExtractionWitness S w delta) :
    applyOperatorToState (heteroKron (conjIsometry v.toPauliSoundnessWitness.φA 1) 1)
        (isometryTensor v.toPauliSoundnessWitness.φA v.toPauliSoundnessWitness.φB
          S.toStrategy.ψ) =
      isometryTensor v.toPauliSoundnessWitness.φA v.toPauliSoundnessWitness.φB
        S.toStrategy.ψ ∧
    applyOperatorToState (heteroKron 1 (conjIsometry v.toPauliSoundnessWitness.φB 1))
        (isometryTensor v.toPauliSoundnessWitness.φA v.toPauliSoundnessWitness.φB
          S.toStrategy.ψ) =
      isometryTensor v.toPauliSoundnessWitness.φA v.toPauliSoundnessWitness.φB
        S.toStrategy.ψ := by
  constructor
  · rw [applyOperatorToState_leftTensor_conjIsometry, heteroKron_one_one,
      applyOperatorToState_one]
  · rw [applyOperatorToState_rightTensor_conjIsometry, heteroKron_one_one,
      applyOperatorToState_one]

private theorem four_mul_deltaQld_le {a b epsilon : ℝ}
    (ha : 1 ≤ a) (hepsilon : 0 ≤ epsilon) :
    4 * deltaQld a b epsilon P.m P.d P.q ≤ deltaQld (4 * a) b epsilon P.m P.d P.q := by
  have hmd : (1 : ℝ) ≤ ((P.m * P.d : ℕ) : ℝ) :=
    Nat.one_le_cast.mpr (Nat.mul_pos P.one_le_m P.hd)
  have hpow := Real.rpow_le_rpow_of_exponent_le hmd (show a ≤ 4 * a by linarith)
  unfold deltaQld
  calc
    4 * (a * Real.rpow ((P.m * P.d : ℕ) : ℝ) a *
        (Real.rpow epsilon b + Real.rpow (P.q : ℝ) (-b) +
          Real.rpow 2 (-(b * ((P.m * P.d : ℕ) : ℝ))))) =
      (4 * a) * Real.rpow ((P.m * P.d : ℕ) : ℝ) a *
        (Real.rpow epsilon b + Real.rpow (P.q : ℝ) (-b) +
          Real.rpow 2 (-(b * ((P.m * P.d : ℕ) : ℝ)))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (by linarith))
      (add_nonneg (add_nonneg (Real.rpow_nonneg hepsilon _)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (Real.rpow_nonneg (by norm_num) _))

/-- All three conditional soundness bounds have the source error form after
enlarging the universal prefactor and halving the extraction exponent. This
theorem assumes the actual extraction data in a projective setting; it does
not construct the global-pair witness or assert unrestricted soundness.
It supports blueprint `ex:pauli-supplied-extraction-error-support` and the
constant adjustment at paper
`14_analysis_of_the_pauli_basis_test.tex:1868-1876`. The remaining source
obligations are documented in `docs/paper-gaps/qpbt_extraction-transfer.tex`. -/
theorem pauli_soundness_deltaQld_ofExtractionWitness
    (C a b : ℝ) (hC : 1 ≤ C) (ha : 1 < a) (hb : 0 < b) (hb1 : b < 1) :
    ∃ a' b' : ℝ, 1 ≤ a' ∧ 0 < b' ∧ b' < 1 ∧
      ∀ (P : AdmissibleParams) (epsilon : ℝ), 0 ≤ epsilon → epsilon ≤ 1 →
        ∀ (S : ProjectiveSetting P epsilon)
          (w : GlobalPairWitness S (deltaQld a b epsilon P.m P.d P.q))
          (_v : ExtractionWitness S w
            (deltaExtract C (deltaConstructPaulis C epsilon
              (deltaQld a b epsilon P.m P.d P.q) P.m P.d P.q) P.m P.d P.q)),
          ∃ t : PauliSoundnessWitness P S.toStrategy,
            ‖isometryTensor t.φA t.φB S.toStrategy.ψ - idealState P t.aux‖ ≤
              deltaQld a' b' epsilon P.m P.d P.q ∧
            (∀ W : PauliKind, pauliOperatorDistanceA P S.toStrategy t W ≤
              deltaQld a' b' epsilon P.m P.d P.q) ∧
            (∀ W : PauliKind, pauliOperatorDistanceB P S.toStrategy t W ≤
              deltaQld a' b' epsilon P.m P.d P.q) := by
  obtain ⟨A, B, hA, hB, hB1, herror⟩ := deltaExtract_le_deltaQld C a b hC ha hb hb1
  refine ⟨4 * A, B / 2, by linarith, by positivity, by linarith, ?_⟩
  intro P epsilon hepsilon hepsilon1 S w v
  obtain ⟨t, ht, htA, htB⟩ := v.isometry_transfer_bounds
  have hmono := deltaQld_mono (P := P) hA (le_refl A) (show B / 2 ≤ B by linarith)
    (show 0 < B / 2 by positivity) hepsilon hepsilon1
  have hfour := four_mul_deltaQld_le (P := P) (b := B / 2) hA hepsilon
  have hnonneg : 0 ≤ deltaQld A (B / 2) epsilon P.m P.d P.q := by
    have hA0 := zero_le_one.trans hA
    simp only [deltaQld, Real.rpow_eq_pow]
    positivity
  have hcommon : max (Real.sqrt _) (4 * _) ≤
      deltaQld (4 * A) (B / 2) epsilon P.m P.d P.q := max_le
    (((Real.sqrt_le_sqrt (herror P epsilon hepsilon hepsilon1)).trans
      (sqrt_deltaQld_le hA hepsilon)).trans
        ((show deltaQld A (B / 2) epsilon P.m P.d P.q ≤
          4 * deltaQld A (B / 2) epsilon P.m P.d P.q by linarith).trans hfour))
    ((mul_le_mul_of_nonneg_left
      ((herror P epsilon hepsilon hepsilon1).trans hmono)
      (by norm_num : (0 : ℝ) ≤ 4)).trans hfour)
  exact ⟨t, ht.trans hcommon, fun W => (htA W).trans hcommon,
    fun W => (htB W).trans hcommon⟩

end

end MIPStarRE.QPBT
