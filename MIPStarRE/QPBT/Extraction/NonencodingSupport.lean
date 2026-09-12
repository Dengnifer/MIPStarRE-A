import MIPStarRE.QPBT.Extraction.EncodingSupport
import MIPStarRE.QPBT.Extraction.PolynomialCollision
import MIPStarRE.QPBT.Games.SupportMass
import MIPStarRE.QPBT.Games.DistanceTheorems.TensorConsistency
import MIPStarRE.QPBT.Combining.Lines.PairStateConsistencyTransport
import MIPStarRE.QPBT.Extraction.Observables

/-!
# Consistency with encoding-supported reference measurements

The Pauli-basis check remains a consistency estimate after adjoining the
perfectly correlated ideal point measurement. Schwartz-Zippel then controls
mass outside the encoding image by evaluated reference inconsistency.

## References

- Blueprint `eq:qld-nonencoding-mass` and `lem:qld-nonencoding-mass-bound`.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:197-264,383-418`.
- `docs/paper-gaps/qpbt_decoding-identity.tex`.
- The reference and comparison constructions reused here are from commits
  `55ae7487`, `36c07381`, `ff4c92d1`, `84c7ec43`, and `7f916eb8`.
- These are auxiliary estimates for a supplied witness, not its construction.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus ProjectiveSetting

noncomputable section

/-- For commuting families, reversing the order of the measurements preserves
the consistency defect. This is finite-sum algebra for opposite placements. -/
theorem consistencyDefect_comm_of_commute {X A I : Type*}
    [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A]
    [Fintype I] [DecidableEq I] (mu : Distribution X)
    (first second : X → A → Op I) (psi : EuclideanSpace ℂ I)
    (hcomm : ∀ x a b, first x a * second x b = second x b * first x a) :
    consistencyDefect mu first second psi = consistencyDefect mu second first psi := by
  unfold consistencyDefect
  apply avgOver_congr
  intro x
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  simp only [hcomm x a b, eq_comm]

open Classical in
/-- A polynomial measurement's mass outside the encoding image is at most
its evaluated inconsistency with an encoding-supported reference, plus `md/q`.
This is the Schwartz-Zippel step in blueprint `eq:qld-nonencoding-mass`.
The reference support is explicit because this auxiliary applies to any POVM;
the concrete reference above proves it without an additional strategy premise. -/
theorem mass_outside_encoding_le_evaluated_defect {P : AdmissibleParams}
    {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (meas : Measurement (Poly P) I) (reference : Measurement (Poly P) J)
    (psi : EuclideanSpace ℂ (I × J)) (hpsi : ‖psi‖ = 1)
    (hsupport : ∀ g, ¬ IsEncoding g → reference.effect g = 0) :
    (∑ g ∈ Finset.univ.filter (fun g : Poly P => ¬ IsEncoding g),
      stateQForm psi (heteroKron (meas.effect g) 1)) ≤
      consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u a => heteroKron ((meas.postprocess (fun g => evalPoly g u)).effect a) 1)
        (fun u a => heteroKron 1 ((reference.postprocess
          (fun g => evalPoly g u)).effect a)) psi + (P.m * P.d : ℝ) / P.q := by
  classical
  have hmass := mass_outside_support_le_point_defect meas reference psi
    (Finset.univ.filter IsEncoding) (by simpa using hsupport)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmass
  have hcollision := SandwichProduct.point_codeword_defect_le_avg_evaluated_add
    meas reference psi evalPoly ((P.m * P.d : ℝ) / P.q) hpsi
    (by positivity) poly_eval_collision_le
  refine hmass.trans (hcollision.trans_eq ?_)
  rw [SandwichProduct.consistencyDefect_placed_eq_avg_point]

namespace ProjectiveSetting

/-- The ideal point measurement has zero off-diagonal mass on its EPR pair.
This follows from the existing unit diagonal-overlap calculation. -/
private theorem tauPoint_offDiagonal_eq_zero {P : AdmissibleParams}
    (W : PauliKind) (u : Fin P.m → PauliScalar P) :
    (∑ a : PauliScalar P, ∑ b : PauliScalar P, if a = b then 0 else
      stateQForm (eprState (PauliRegister P))
        (heteroKron (tauPointProj W u a) (tauPointProj W u b))) = 0 := by
  have h := point_defect_eq (leftPlacedMeasurement (tauPointMeas W u))
    (rightPlacedMeasurement (tauPointMeas W u)) (eprState (PauliRegister P))
  simpa only [leftPlacedMeasurement, rightPlacedMeasurement, Measurement.ofSumEqOne,
    placed_product_stateQForm_eq, tauPointMeas, eprState_norm, one_pow,
    sum_tauPointProj_pair_stateQForm_eprState, sub_self] using h

/-- Adjoining the ideal point outcomes preserves the Pauli-basis check on the
two-player expanded state, in the point--Pauli orientation. -/
theorem point_encodingPauli_consistency_eq {P : AdmissibleParams} {epsilon : ℝ}
    (S : ProjectiveSetting P epsilon) (W : PauliKind) :
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u a => heteroKron ((S.pointMeasExp .alice W u).effect a) 1)
        (fun u a => heteroKron 1 (((S.encodingPauliMeas .bob W).postprocess
          (fun g => evalPoly g u)).effect a)) (ExtendedLineGame.pairState S) =
      consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u a => heteroKron ((S.pointMeas .alice W u).effect a) 1)
        (fun u a => heteroKron 1 ((S.pauliEvalMeas .bob W u).effect a))
        S.toStrategy.ψ := by
  have h := consistencyDefect_convolution_eq_of_perfect
    (uniformDistribution (Fin P.m → PauliScalar P))
    (S.pointMeas .alice W) (S.pauliEvalMeas .bob W)
    (tauPointMeas W) (tauPointMeas W) S.toStrategy.ψ
    (eprState (PauliRegister P)) (eprState_norm _)
    (tauPoint_offDiagonal_eq_zero W)
  simpa only [pointMeasExp, Measurement.ofSumEqOne, expPointOp_eq_convolution,
    encodingPauliMeas_eval_effect_eq_convolution, tauPointMeas,
    ExtendedLineGame.pairState] using h

/-- The same exact preservation holds in the Pauli--point orientation. -/
theorem encodingPauli_point_consistency_eq {P : AdmissibleParams} {epsilon : ℝ}
    (S : ProjectiveSetting P epsilon) (W : PauliKind) :
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u a => heteroKron (((S.encodingPauliMeas .alice W).postprocess
          (fun g => evalPoly g u)).effect a) 1)
        (fun u a => heteroKron 1 ((S.pointMeasExp .bob W u).effect a))
        (ExtendedLineGame.pairState S) =
      consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u a => heteroKron ((S.pauliEvalMeas .alice W u).effect a) 1)
        (fun u a => heteroKron 1 ((S.pointMeas .bob W u).effect a))
        S.toStrategy.ψ := by
  have h := consistencyDefect_convolution_eq_of_perfect
    (uniformDistribution (Fin P.m → PauliScalar P))
    (S.pauliEvalMeas .alice W) (S.pointMeas .bob W)
    (tauPointMeas W) (tauPointMeas W) S.toStrategy.ψ
    (eprState (PauliRegister P)) (eprState_norm _)
    (tauPoint_offDiagonal_eq_zero W)
  simpa only [pointMeasExp, Measurement.ofSumEqOne, expPointOp_eq_convolution,
    encodingPauliMeas_eval_effect_eq_convolution, tauPointMeas,
    ExtendedLineGame.pairState] using h

/-- Adjoining the same ideal point measurements also preserves point
self-consistency exactly. -/
theorem expanded_point_consistency_eq {P : AdmissibleParams} {epsilon : ℝ}
    (S : ProjectiveSetting P epsilon) (W : PauliKind) :
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u a => heteroKron ((S.pointMeasExp .alice W u).effect a) 1)
        (fun u a => heteroKron 1 ((S.pointMeasExp .bob W u).effect a))
        (ExtendedLineGame.pairState S) =
      consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u a => heteroKron ((S.pointMeas .alice W u).effect a) 1)
        (fun u a => heteroKron 1 ((S.pointMeas .bob W u).effect a))
        S.toStrategy.ψ := by
  have h := consistencyDefect_convolution_eq_of_perfect
    (uniformDistribution (Fin P.m → PauliScalar P))
    (S.pointMeas .alice W) (S.pointMeas .bob W)
    (tauPointMeas W) (tauPointMeas W) S.toStrategy.ψ
    (eprState (PauliRegister P)) (eprState_norm _)
    (tauPoint_offDiagonal_eq_zero W)
  simpa only [pointMeasExp, Measurement.ofSumEqOne, expPointOp_eq_convolution,
    tauPointMeas, ExtendedLineGame.pairState] using h

end ProjectiveSetting

open Classical in
/-- The right-hand marginal version of the support estimate, obtained by
interchanging the two tensor factors and using the same collision bound. -/
theorem right_mass_outside_encoding_le_evaluated_defect {P : AdmissibleParams}
    {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (reference : Measurement (Poly P) I) (meas : Measurement (Poly P) J)
    (psi : EuclideanSpace ℂ (I × J)) (hpsi : ‖psi‖ = 1)
    (hsupport : ∀ g, ¬ IsEncoding g → reference.effect g = 0) :
    (∑ g ∈ Finset.univ.filter (fun g : Poly P => ¬ IsEncoding g),
      stateQForm psi (heteroKron 1 (meas.effect g))) ≤
      consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u a => heteroKron ((reference.postprocess
          (fun g => evalPoly g u)).effect a) 1)
        (fun u a => heteroKron 1 ((meas.postprocess (fun g => evalPoly g u)).effect a))
        psi + (P.m * P.d : ℝ) / P.q := by
  have h := mass_outside_encoding_le_evaluated_defect meas reference
    (reindexState (Equiv.prodComm I J) psi)
    (by rw [reindexState_norm_eq, hpsi]) hsupport
  simpa only [WinImplications.stateQForm_reindexState,
    WinImplications.reindexOp_prodComm_heteroKron,
    WinImplications.consistencyDefect_swappedState] using h

/-- Both evaluated global marginals are consistent with the opposite
encoding-supported reference. The universal square-root coefficient comes
from the two Pauli-basis checks and point self-consistency; it does not assume
the non-encoding support estimate or the existence of a global witness. -/
theorem global_marginal_encoding_consistency :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (P : AdmissibleParams) (epsilon deltaG : ℝ),
      0 ≤ epsilon → ∀ (S : ProjectiveSetting P epsilon)
        (w : GlobalPairWitness S deltaG) (W : PauliKind),
      consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
          (fun u a => heteroKron (((w.marginalPoly .alice W).postprocess
            (fun g => evalPoly g u)).effect a) 1)
          (fun u a => heteroKron 1 (((S.encodingPauliMeas .bob W).postprocess
            (fun g => evalPoly g u)).effect a)) (ExtendedLineGame.pairState S) ≤
        deltaG + C * Real.sqrt epsilon ∧
      consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
          (fun u a => heteroKron (((S.encodingPauliMeas .alice W).postprocess
            (fun g => evalPoly g u)).effect a) 1)
          (fun u a => heteroKron 1 (((w.marginalPoly .bob W).postprocess
            (fun g => evalPoly g u)).effect a)) (ExtendedLineGame.pairState S) ≤
        deltaG + C * Real.sqrt epsilon := by
  obtain ⟨C1, hC1, hforward⟩ := win_pauli_basis_cons
  obtain ⟨C2, hC2, hreverse⟩ := WinImplications.win_pauli_basis_cons_interchanged_proof
  let E : ℝ := Fintype.card PauliEdge
  let K : ℝ := max C1 C2
  refine ⟨1 + 2 * Real.sqrt (E + K), by linarith [Real.sqrt_nonneg (E + K)], ?_⟩
  intro P epsilon deltaG hepsilon S w W
  let mu := uniformDistribution (Fin P.m → PauliScalar P)
  let psi := ExtendedLineGame.pairState S
  let pointA := fun u => leftPlacedMeasurement (ιB := S.ExpandedLocalSpace .bob)
    (S.pointMeasExp .alice W u)
  let pointB := fun u => rightPlacedMeasurement (ιA := S.ExpandedLocalSpace .alice)
    (S.pointMeasExp .bob W u)
  let refA := fun u => leftPlacedMeasurement (ιB := S.ExpandedLocalSpace .bob)
    ((S.encodingPauliMeas .alice W).postprocess (fun g => evalPoly g u))
  let refB := fun u => rightPlacedMeasurement (ιA := S.ExpandedLocalSpace .alice)
    ((S.encodingPauliMeas .bob W).postprocess (fun g => evalPoly g u))
  let margA := fun u => leftPlacedMeasurement (ιB := S.ExpandedLocalSpace .bob)
    ((w.marginalPoly .alice W).postprocess (fun g => evalPoly g u))
  let margB := fun u => rightPlacedMeasurement (ιA := S.ExpandedLocalSpace .alice)
    ((w.marginalPoly .bob W).postprocess (fun g => evalPoly g u))
  have hpost (side : PlayerSide) (u : Fin P.m → PauliScalar P) :
      (w.marginalPoly side W).postprocess (fun g => evalPoly g u) =
        (w.Smeas side).postprocess (evalAt W u) := by
    rw [GlobalPairWitness.marginalPoly, Measurement.postprocess_comp]
    cases W <;> rfl
  have hab : consistencyDefect mu (fun u a => (margA u).effect a)
      (fun u a => (pointB u).effect a) psi ≤ deltaG := by
    change consistencyDefect mu
      (fun u a => heteroKron (((w.marginalPoly .alice W).postprocess
        (fun g => evalPoly g u)).effect a) 1)
      (fun u a => heteroKron 1 ((S.pointMeasExp .bob W u).effect a)) psi ≤ deltaG
    rw [S.consistencyDefect_pairState_eq_AA'_BA'']
    simpa only [hpost] using w.point_consistent_alice W
  have hba : consistencyDefect mu (fun u a => (margB u).effect a)
      (fun u a => (pointA u).effect a) psi ≤ deltaG := by
    rw [consistencyDefect_comm_of_commute _ _ _ _ (by
      intro u a b
      exact (WinImplications.heteroKron_left_right_comm _ _).symm)]
    change consistencyDefect mu
      (fun u a => heteroKron ((S.pointMeasExp .alice W u).effect a) 1)
      (fun u a => heteroKron 1 (((w.marginalPoly .bob W).postprocess
        (fun g => evalPoly g u)).effect a)) psi ≤ deltaG
    rw [S.consistencyDefect_pairState_eq_AB''_BB',
      consistencyDefect_comm_of_commute _ _ _ _ (by
        intro u a b
        exact S.place_comm .AB'' .BB' trivial _ _)]
    simpa only [hpost] using w.point_consistent_bob W
  have hpoints : consistencyDefect mu (fun u a => (pointA u).effect a)
      (fun u a => (pointB u).effect a) psi ≤ E * epsilon := by
    change consistencyDefect mu
      (fun u a => heteroKron ((S.pointMeasExp .alice W u).effect a) 1)
      (fun u a => heteroKron 1 ((S.pointMeasExp .bob W u).effect a)) psi ≤ _
    rw [S.expanded_point_consistency_eq]
    exact point_self_consistency_le S W
  have hpoints' : consistencyDefect mu (fun u a => (pointB u).effect a)
      (fun u a => (pointA u).effect a) psi ≤ E * epsilon := by
    rw [consistencyDefect_comm_of_commute _ _ _ _ (by
      intro u a b
      exact (WinImplications.heteroKron_left_right_comm _ _).symm)]
    exact hpoints
  have hpb : consistencyDefect mu (fun u a => (pointA u).effect a)
      (fun u a => (refB u).effect a) psi ≤ K * epsilon := by
    change consistencyDefect mu
      (fun u a => heteroKron ((S.pointMeasExp .alice W u).effect a) 1)
      (fun u a => heteroKron 1 (((S.encodingPauliMeas .bob W).postprocess
        (fun g => evalPoly g u)).effect a)) psi ≤ _
    rw [S.point_encodingPauli_consistency_eq]
    exact (hforward P epsilon S hepsilon W).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hepsilon)
  have hpa : consistencyDefect mu (fun u a => (pointB u).effect a)
      (fun u a => (refA u).effect a) psi ≤ K * epsilon := by
    rw [consistencyDefect_comm_of_commute _ _ _ _ (by
      intro u a b
      exact (WinImplications.heteroKron_left_right_comm _ _).symm)]
    change consistencyDefect mu
      (fun u a => heteroKron (((S.encodingPauliMeas .alice W).postprocess
        (fun g => evalPoly g u)).effect a) 1)
      (fun u a => heteroKron 1 ((S.pointMeasExp .bob W u).effect a)) psi ≤ _
    rw [S.encodingPauli_point_consistency_eq]
    exact (hreverse P epsilon S hepsilon W).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hepsilon)
  have hscalar : deltaG + 2 * Real.sqrt (E * epsilon + K * epsilon) ≤
      deltaG + (1 + 2 * Real.sqrt (E + K)) * Real.sqrt epsilon := by
    have hEK : 0 ≤ E + K := add_nonneg (Nat.cast_nonneg _)
      (le_trans (by linarith : 0 ≤ C1) (le_max_left _ _))
    rw [← add_mul, Real.sqrt_mul hEK]
    nlinarith [Real.sqrt_nonneg epsilon]
  constructor
  · exact (consistencyDefect_trans_le mu margA pointB pointA refB psi
      deltaG (E * epsilon) (K * epsilon) (uniformDistribution_isProbability _)
      (ExtendedLineGame.pairState_norm S) hab hpoints hpb).trans hscalar
  · have h := (consistencyDefect_trans_le mu margB pointA pointB refA psi
      deltaG (E * epsilon) (K * epsilon) (uniformDistribution_isProbability _)
      (ExtendedLineGame.pairState_norm S) hba hpoints' hpa).trans hscalar
    rw [consistencyDefect_comm_of_commute _ _ _ _ (by
      intro u a b
      exact (WinImplications.heteroKron_left_right_comm _ _).symm)] at h
    exact h

/-- A marginal acting on `AA'` has the same mass in the extraction-block
notation and the two-player expanded state. The unused registers carry identities. -/
theorem stateQForm_placeSide_alice_tensor_one {P : AdmissibleParams} {epsilon : ℝ}
    (S : ProjectiveSetting P epsilon) (A : Op (S.ExpandedLocalSpace .alice))
    (hA : A.IsHermitian) :
    stateQForm S.psiHat (S.placeSide .alice (heteroKron A (1 : Op (PauliRegister P)))) =
      stateQForm (ExtendedLineGame.pairState S) (heteroKron A 1) := by
  have hplace : S.placeSide .alice (heteroKron A (1 : Op (PauliRegister P))) =
      S.place .AA' A := by
    ext row col
    simp only [placeSide, sixRegExtractionEquiv, reindexOp, place, heteroKron,
      Matrix.kronecker, Matrix.one_apply, mul_ite, ite_mul]
    split_ifs <;> simp_all
    rfl
  rw [hplace]
  have h := ExtendedLineGame.stateQForm_pairState_eq_AA'_BA'' S A 1 hA
    Matrix.isHermitian_one
  have hone : S.place .BA'' (1 : Op (S.ExpandedLocalSpace .bob)) = 1 := by
    convert S.place_one .BA'' using 1
    rfl
  rw [hone, Matrix.mul_one] at h
  exact h.symm

/-- The corresponding marginal-mass identity for `BB'`. The opposite placement
uses the second EPR pair, as in the witness's Bob consistency hypothesis. -/
theorem stateQForm_placeSide_bob_tensor_one {P : AdmissibleParams} {epsilon : ℝ}
    (S : ProjectiveSetting P epsilon) (B : Op (S.ExpandedLocalSpace .bob))
    (hB : B.IsHermitian) :
    stateQForm S.psiHat (S.placeSide .bob (heteroKron B (1 : Op (PauliRegister P)))) =
      stateQForm (ExtendedLineGame.pairState S) (heteroKron 1 B) := by
  have hplace : S.placeSide .bob (heteroKron B (1 : Op (PauliRegister P))) =
      S.place .BB' B := by
    ext row col
    simp only [placeSide, sixRegExtractionEquiv, reindexOp, place, heteroKron,
      Matrix.kronecker, Matrix.one_apply, mul_ite, ite_mul]
    split_ifs <;> simp_all
    rfl
  rw [hplace]
  have h := ExtendedLineGame.stateQForm_pairState_eq_AB''_BB' S 1 B
    Matrix.isHermitian_one hB
  have hone : S.place .AB'' (1 : Op (S.ExpandedLocalSpace .alice)) = 1 := by
    convert S.place_one .AB'' using 1
    rfl
  rw [hone, Matrix.one_mul] at h
  exact h.symm

end

end MIPStarRE.QPBT
