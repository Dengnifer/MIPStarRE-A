import MIPStarRE.QPBT.Extraction.PointConsistency

/-!
# Point consistency with Alice's pulled-apart measurement

This module proves the register-interchanged overlap calculation for Item 1 of
blueprint `lem:qld-construct-the-paulis`. Polynomial evaluation is replaced by
decoded evaluation only on encoding outcomes; the remaining loss is bounded
by the mass of the non-encoding outcomes.

## References

* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1463-1492`.
* `docs/paper-gaps/qpbt_decoding-identity.tex` records the necessary restriction
  on the decoder identity.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

namespace ProjectiveSetting

variable {P : AdmissibleParams} {epsilon : ℝ}

/-- Placing a tensor with an identity on Alice's last register recovers `AA'`. -/
theorem placeSide_alice_tensor_one (S : ProjectiveSetting P epsilon)
    (B : Op (S.ExpandedLocalSpace .alice)) :
    S.placeSide .alice (heteroKron B (1 : Op (PauliRegister P))) = S.place .AA' B := by
  ext row col
  simp [placeSide, sixRegExtractionEquiv, reindexOp, heteroKron, Matrix.kronecker,
    place, Matrix.one_apply, Prod.ext_iff, ite_and, mul_ite]
  split_ifs <;> rfl

/-- The factors on `AA'A''` and `B` can be regrouped on `AA'` and `BA''`
without exchanging registers or assuming symmetry of the strategy. -/
theorem placeSide_alice_tensor_mul_placePlayer_bob (S : ProjectiveSetting P epsilon)
    (B : Op (S.ExpandedLocalSpace .alice)) (T : Op (PauliRegister P))
    (A : Op S.toStrategy.ιB) :
    S.placeSide .alice (heteroKron B T) * S.placePlayer .bob A =
      S.place .AA' B * S.place .BA'' (heteroKron A T) := by
  classical
  ext row col
  simp [placePlayer, placeSide, sixRegExtractionEquiv, reindexOp, heteroKron,
    Matrix.kronecker, place, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.one_apply, Prod.ext_iff, ite_and, mul_ite, ite_mul]
  split_ifs <;> ac_rfl

/-- Alice's extraction-block placement preserves finite sums. -/
theorem placeSide_alice_finset_sum (S : ProjectiveSetting P epsilon)
    {I : Type*} (s : Finset I) (B : I → Op (ExtractionBlock P S.toStrategy.ιA)) :
    S.placeSide .alice (∑ i ∈ s, B i) = ∑ i ∈ s, S.placeSide .alice (B i) := by
  classical
  change reindexOp (sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB)
    (heteroKron (∑ i ∈ s, B i) (1 : Op (ExtractionBlock P S.toStrategy.ιB))) = _
  rw [heteroKron_finset_sum_left]
  ext row col
  simp only [placeSide, reindexOp, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.sum_apply]

end ProjectiveSetting

/-- The Alice-pulled/Bob-point overlap is exactly the expanded-point overlap
at the decoded value. This is the register-interchanged version of the first
three lines of the calculation in paper lines 1483--1492. -/
theorem sum_tildeM_mul_pointMeas_eq_decoded_overlap
    {P : AdmissibleParams} {epsilon deltaG : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S deltaG) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) :
    (∑ a : PauliScalar P, S.placeSide .alice (tildeM w .alice W (indicatorVec u) a) *
      S.placePlayer .bob ((S.pointMeas .bob W u).effect a)) =
      ∑ g : Poly P, S.place .AA' ((w.marginalPoly .alice W).effect g) *
        S.place .BA'' ((S.pointMeasExp .bob W u).effect
          (dotProduct (decodeFq g) (indicatorVec u))) := by
  classical
  simp only [tildeM, S.placeSide_alice_finset_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  simp only [S.placeSide_alice_tensor_mul_placePlayer_bob]
  rw [← Finset.mul_sum, ← S.place_finset_sum,
    S.pointMeasExp_effect_eq_sum_sub .bob W u]
  rfl

/-- The Alice-pulled/Bob-point consistency defect is one minus the decoded
overlap. This uses completeness but no encoding restriction or mass estimate. -/
theorem tildeM_consistencyDefect_eq_one_sub_decoded_overlap'
    {P : AdmissibleParams} {epsilon deltaG : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S deltaG) (W : PauliKind) :
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
      (fun u a => S.placeSide .alice (tildeM w .alice W (indicatorVec u) a))
      (fun u a => S.placePlayer .bob ((S.pointMeas .bob W u).effect a)) S.psiHat =
      1 - avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun u =>
        ∑ g : Poly P, stateQForm S.psiHat
          (S.place .AA' ((w.marginalPoly .alice W).effect g) *
            S.place .BA'' ((S.pointMeasExp .bob W u).effect
              (dotProduct (decodeFq g) (indicatorVec u))))) := by
  classical
  let point := fun u : Fin P.m → PauliScalar P =>
    S.placedMeasurement .BB' (leftPlacedMeasurement (S.pointMeas .bob W u))
  let pulled : (Fin P.m → PauliScalar P) → Measurement (PauliScalar P)
      (SixReg P S.toStrategy.ιA S.toStrategy.ιB) := fun u =>
    Measurement.ofSumEqOne
      (fun a => S.placeSide .alice (tildeM w .alice W (indicatorVec u) a))
      (fun a => by
        apply ProjectiveSetting.reindexOp_nonneg
        exact kronecker_nonneg (tildeM_isProj w .alice W (indicatorVec u) a).nonneg
          Matrix.PosSemidef.one.nonneg)
      (by
        rw [← S.placeSide_alice_finset_sum, sum_tildeM_eq_one]
        change reindexOp (sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB)
          (heteroKron (1 : Op (ExtractionBlock P S.toStrategy.ιA))
            (1 : Op (ExtractionBlock P S.toStrategy.ιB))) = 1
        rw [heteroKron_one_one]
        ext row col
        simp [reindexOp, Matrix.one_apply])
  have h := consistencyDefect_eq_one_sub_overlap
    (uniformDistribution (Fin P.m → PauliScalar P)) pulled point S.psiHat
    (uniformDistribution_isProbability _) S.psiHat_norm
  change consistencyDefect _ _ _ S.psiHat = 1 - avgOver _ (fun u =>
    ∑ a : PauliScalar P, stateQForm S.psiHat
      (S.placeSide .alice (tildeM w .alice W (indicatorVec u) a) *
        S.placePlayer .bob ((S.pointMeas .bob W u).effect a))) at h
  refine h.trans ?_
  congr 1
  apply avgOver_congr
  intro u
  rw [← stateQForm_finset_sum, sum_tildeM_mul_pointMeas_eq_decoded_overlap,
    stateQForm_finset_sum]

open scoped Classical in
/-- On Alice's marginal, replacing polynomial evaluation by decoded evaluation
loses at most the non-encoding mass. This is the support-restricted version of
the fourth line of paper lines 1483--1492, with the players interchanged. -/
theorem marginal_eval_overlap_le_decoded_add_nonencoding'
    {P : AdmissibleParams} {epsilon deltaG : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S deltaG) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) :
    (∑ g : Poly P, stateQForm S.psiHat
      (S.place .AA' ((w.marginalPoly .alice W).effect g) *
        S.place .BA'' ((S.pointMeasExp .bob W u).effect (MvPolynomial.eval u g.1)))) ≤
      (∑ g : Poly P, stateQForm S.psiHat
        (S.place .AA' ((w.marginalPoly .alice W).effect g) *
          S.place .BA'' ((S.pointMeasExp .bob W u).effect
            (dotProduct (decodeFq g) (indicatorVec u))))) +
      ∑ g ∈ Finset.univ.filter (fun g : Poly P => ¬ IsEncoding g),
        stateQForm S.psiHat (S.place .AA' ((w.marginalPoly .alice W).effect g)) := by
  classical
  have hpos (g : Poly P) (a : PauliScalar P) :
      0 ≤ stateQForm S.psiHat
        (S.place .AA' ((w.marginalPoly .alice W).effect g) *
          S.place .BA'' ((S.pointMeasExp .bob W u).effect a)) :=
    stateQForm_nonneg _ (S.place_mul_place_nonneg .AA' .BA'' (by trivial)
      ((w.marginalPoly .alice W).pos g) ((S.pointMeasExp .bob W u).pos a))
  have hsum (g : Poly P) :
      (∑ a : PauliScalar P, stateQForm S.psiHat
        (S.place .AA' ((w.marginalPoly .alice W).effect g) *
          S.place .BA'' ((S.pointMeasExp .bob W u).effect a))) =
        stateQForm S.psiHat (S.place .AA' ((w.marginalPoly .alice W).effect g)) := by
    have hc : (∑ a : PauliScalar P,
        S.place .BA'' ((S.pointMeasExp .bob W u).effect a)) = 1 :=
      (S.placedMeasurement .BA'' (S.pointMeasExp .bob W u)).sum_eq_one
    rw [← stateQForm_finset_sum, ← Finset.mul_sum, hc, mul_one]
  rw [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro g _
  by_cases hg : IsEncoding g
  · simp only [hg, not_true_eq_false, if_false, add_zero]
    rw [decodeFq_dotProduct_indicatorVec hg u]
    rfl
  · simp only [hg, not_false_eq_true, if_true]
    have hle := Finset.single_le_sum (fun a _ => hpos g a)
      (Finset.mem_univ (MvPolynomial.eval u g.1))
    rw [hsum] at hle
    exact hle.trans (le_add_of_nonneg_left (hpos g _))

end

end MIPStarRE.QPBT
