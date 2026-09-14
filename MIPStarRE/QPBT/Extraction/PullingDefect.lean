import MIPStarRE.QPBT.Extraction.Consistency
import MIPStarRE.QPBT.Extraction.PullingPointConsistency

/-!
# Evaluated consistency of the difference-polynomial measurements

The exact overlap identities identify the consistency with the opposite
player's point measurement with the consistency supplied by the global witness.

## References

- Blueprint `lem:qld-construct-the-paulis`, Item 2.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1495-1545`.
- Issue #520; the global witness is supplied, not constructed.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Classical

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

/-- Place a complete measurement on its three-register extraction block. -/
private def pullingPlacedMeasurement {P : AdmissibleParams} {epsilon : ℝ}
    (S : ProjectiveSetting P epsilon) (side : PlayerSide) {A : Type*} [Fintype A]
    (M : Measurement A (ExtractionBlock P (S.LocalSpace side))) :
    Measurement A (SixReg P S.toStrategy.ιA S.toStrategy.ιB) := by
  refine Measurement.ofSumEqOne (fun a => S.placeSide side (M.effect a)) ?_ ?_
  · intro a
    cases side
    · exact reindexOp_nonneg _ (kronecker_nonneg (M.pos a) Matrix.PosSemidef.one.nonneg)
    · exact reindexOp_nonneg _ (kronecker_nonneg Matrix.PosSemidef.one.nonneg (M.pos a))
  · cases side
    · rw [← S.placeSide_alice_finset_sum, M.sum_eq_one]
      change reindexOp _ (heteroKron (1 : Op (ExtractionBlock P S.toStrategy.ιA))
        (1 : Op (ExtractionBlock P S.toStrategy.ιB))) = 1
      rw [heteroKron_one_one]
      ext row col
      simp [reindexOp, Matrix.one_apply]
    · rw [← S.placeSide_bob_finset_sum, M.sum_eq_one]
      change reindexOp _ (heteroKron (1 : Op (ExtractionBlock P S.toStrategy.ιA))
        (1 : Op (ExtractionBlock P S.toStrategy.ιB))) = 1
      rw [heteroKron_one_one]
      ext row col
      simp [reindexOp, Matrix.one_apply]

private theorem pullingPlacedMeasurement_effect {P : AdmissibleParams} {epsilon : ℝ}
    (S : ProjectiveSetting P epsilon) (side : PlayerSide) {A : Type*} [Fintype A]
    (M : Measurement A (ExtractionBlock P (S.LocalSpace side))) (a : A) :
    (pullingPlacedMeasurement S side M).effect a = S.placeSide side (M.effect a) := by
  rfl

/-- Placing a projective measurement on an extraction block preserves projectivity. -/
private theorem pullingPlacedMeasurement_isProjective {P : AdmissibleParams} {epsilon : ℝ}
    (S : ProjectiveSetting P epsilon) (side : PlayerSide) {A : Type*} [Fintype A]
    (M : Measurement A (ExtractionBlock P (S.LocalSpace side)))
    (hM : Measurement.IsProjective M) :
    Measurement.IsProjective (pullingPlacedMeasurement S side M) := by
  classical
  let e := sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB
  letI : DecidableEq (ExtractionRegisters P S.toStrategy.ιA S.toStrategy.ιB) :=
    instDecidableEqProd
  cases side
  · have h := reindexMeasurement_isProjective e (leftPlacedMeasurement M)
      (fun a => MakingMeasurementsProjective.isProj_kronecker (hM a)
        (IsStarProjection.one _))
    convert h using 1
    rfl
  · have h := reindexMeasurement_isProjective e (rightPlacedMeasurement M)
      (fun a => MakingMeasurementsProjective.isProj_kronecker
        (IsStarProjection.one _) (hM a))
    convert h using 1
    rfl

/-- The Alice evaluation defect is bounded by the supplied global consistency
error, with no decoder correction or non-encoding mass term. -/
theorem pullingMeas_eval_point_consistent_alice {P : AdmissibleParams}
    {epsilon deltaG : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S deltaG) (W : PauliKind) :
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
      (fun u a => S.placeSide .alice
        (((pullingMeas w .alice W).postprocess (fun g => evalPoly g u)).effect a))
      (fun u a => S.placePlayer .bob ((S.pointMeas .bob W u).effect a)) S.psiHat ≤
        deltaG := by
  let mu := uniformDistribution (Fin P.m → PauliScalar P)
  let pulled := fun u => pullingPlacedMeasurement S .alice
    ((pullingMeas w .alice W).postprocess (fun g => evalPoly g u))
  let point := fun u => S.placedMeasurement .BB' (leftPlacedMeasurement (S.pointMeas .bob W u))
  let marginal := fun u => S.placedMeasurement .AA'
    ((w.marginalPoly .alice W).postprocess (fun g => evalPoly g u))
  let expanded := fun u => S.placedMeasurement .BA'' (S.pointMeasExp .bob W u)
  have hp := consistencyDefect_eq_one_sub_overlap mu pulled point S.psiHat
    (uniformDistribution_isProbability _) S.psiHat_norm
  have hm := consistencyDefect_eq_one_sub_overlap mu marginal expanded S.psiHat
    (uniformDistribution_isProbability _) S.psiHat_norm
  have heq : consistencyDefect mu (fun u a => (pulled u).effect a)
      (fun u a => (point u).effect a) S.psiHat =
      consistencyDefect mu (fun u a => (marginal u).effect a)
        (fun u a => (expanded u).effect a) S.psiHat := by
    rw [hp, hm]
    apply congrArg (1 - ·)
    apply avgOver_congr
    intro u
    simp only [pulled, point, marginal, expanded, pullingPlacedMeasurement_effect,
      ProjectiveSetting.placedMeasurement_effect]
    change (∑ a, stateQForm S.psiHat (S.placeSide .alice
      (((pullingMeas w .alice W).postprocess (fun g => evalPoly g u)).effect a) *
      S.placePlayer .bob ((S.pointMeas .bob W u).effect a))) = _
    rw [← stateQForm_finset_sum, sum_pullingMeas_eval_mul_pointMeas]
    rw [← stateQForm_finset_sum]
    exact congrArg (stateQForm S.psiHat)
      (sum_marginalPoly_eval_mul w .AA' W u
        (fun a => S.place .BA'' ((S.pointMeasExp .bob W u).effect a))).symm
  have hbound := marginalPoly_pointMeas_consistent_alice w W
  change consistencyDefect mu (fun u a => (marginal u).effect a)
    (fun u a => (expanded u).effect a) S.psiHat ≤ deltaG at hbound
  exact heq.le.trans hbound

/-- Bob's evaluation defect has the same bound, using the other consistency
field of the supplied witness and its `BB'`--`AB''` placements. -/
theorem pullingMeas_eval_point_consistent_bob {P : AdmissibleParams}
    {epsilon deltaG : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S deltaG) (W : PauliKind) :
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
      (fun u a => S.placePlayer .alice ((S.pointMeas .alice W u).effect a))
      (fun u a => S.placeSide .bob
        (((pullingMeas w .bob W).postprocess (fun g => evalPoly g u)).effect a)) S.psiHat ≤
        deltaG := by
  let mu := uniformDistribution (Fin P.m → PauliScalar P)
  let pulled := fun u => pullingPlacedMeasurement S .bob
    ((pullingMeas w .bob W).postprocess (fun g => evalPoly g u))
  let point := fun u => S.placedMeasurement .AA' (leftPlacedMeasurement (S.pointMeas .alice W u))
  let marginal := fun u => S.placedMeasurement .BB'
    ((w.marginalPoly .bob W).postprocess (fun g => evalPoly g u))
  let expanded := fun u => S.placedMeasurement .AB'' (S.pointMeasExp .alice W u)
  have hp := consistencyDefect_eq_one_sub_overlap mu point pulled S.psiHat
    (uniformDistribution_isProbability _) S.psiHat_norm
  have hm := consistencyDefect_eq_one_sub_overlap mu marginal expanded S.psiHat
    (uniformDistribution_isProbability _) S.psiHat_norm
  have heq : consistencyDefect mu (fun u a => (point u).effect a)
      (fun u a => (pulled u).effect a) S.psiHat =
      consistencyDefect mu (fun u a => (marginal u).effect a)
        (fun u a => (expanded u).effect a) S.psiHat := by
    rw [hp, hm]
    apply congrArg (1 - ·)
    apply avgOver_congr
    intro u
    simp only [pulled, point, marginal, expanded, pullingPlacedMeasurement_effect,
      ProjectiveSetting.placedMeasurement_effect]
    change (∑ a, stateQForm S.psiHat
      (S.placePlayer .alice ((S.pointMeas .alice W u).effect a) * S.placeSide .bob
        (((pullingMeas w .bob W).postprocess (fun g => evalPoly g u)).effect a))) = _
    rw [← stateQForm_finset_sum, sum_pointMeas_mul_pullingMeas_eval]
    rw [← stateQForm_finset_sum]
    exact congrArg (stateQForm S.psiHat)
      (sum_marginalPoly_eval_mul w .BB' W u
        (fun a => S.place .AB'' ((S.pointMeasExp .alice W u).effect a))).symm
  have hbound := marginalPoly_pointMeas_consistent_bob w W
  change consistencyDefect mu (fun u a => (marginal u).effect a)
    (fun u a => (expanded u).effect a) S.psiHat ≤ deltaG at hbound
  exact heq.le.trans hbound

/-- Tensoring the strategy state with the two normalized EPR states preserves
the point-measurement consistency defect. This is the six-register form of
the point self-consistency used at `eq:qld-pulling-3`. -/
theorem point_consistencyDefect_psiHat {P : AdmissibleParams} {epsilon : ℝ}
    (S : ProjectiveSetting P epsilon) (W : PauliKind) :
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u a => S.placePlayer .alice ((S.pointMeas .alice W u).effect a))
        (fun u a => S.placePlayer .bob ((S.pointMeas .bob W u).effect a)) S.psiHat =
      consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u a => heteroKron ((S.pointMeas .alice W u).effect a) 1)
        (fun u a => heteroKron 1 ((S.pointMeas .bob W u).effect a)) S.toStrategy.ψ := by
  classical
  have htransfer (A : Op S.toStrategy.ιA) (B : Op S.toStrategy.ιB)
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
    exact htransfer _ _
      (Matrix.nonneg_iff_posSemidef.mp ((S.pointMeas .alice W u).pos a)).isHermitian
      (Matrix.nonneg_iff_posSemidef.mp ((S.pointMeas .bob W u).pos b)).isHermitian

/-- The evaluated difference-polynomial measurements are self-consistent.
Agreement and two squared-distance triangle inequalities combine the two
opposite-player comparisons with the original point self-consistency.
The error is linear in the supplied witness error, as required before
the collision step `eq:qld-pulling-12`. -/
theorem pullingMeas_eval_consistencyDefect_le {P : AdmissibleParams}
    {epsilon deltaG : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S deltaG) (W : PauliKind) :
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u a => S.placeSide .alice
          (((pullingMeas w .alice W).postprocess (fun g => evalPoly g u)).effect a))
        (fun u a => S.placeSide .bob
          (((pullingMeas w .bob W).postprocess (fun g => evalPoly g u)).effect a))
        S.psiHat ≤ 12 * deltaG + 8 * (Fintype.card PauliEdge : ℝ) * epsilon := by
  let mu := uniformDistribution (Fin P.m → PauliScalar P)
  let A := fun u => pullingPlacedMeasurement S .alice
    ((pullingMeas w .alice W).postprocess (fun g => evalPoly g u))
  let B := fun u => pullingPlacedMeasurement S .bob
    ((pullingMeas w .bob W).postprocess (fun g => evalPoly g u))
  let PA := fun u => S.placedMeasurement .AA'
    (leftPlacedMeasurement (S.pointMeas .alice W u))
  let PB := fun u => S.placedMeasurement .BB'
    (leftPlacedMeasurement (S.pointMeas .bob W u))
  have hA := (opFamilyDistSq_le_two_mul_consistencyDefect mu A PB S.psiHat).trans
    (mul_le_mul_of_nonneg_left (pullingMeas_eval_point_consistent_alice w W)
      (by norm_num : (0 : ℝ) ≤ 2))
  have hB := (opFamilyDistSq_le_two_mul_consistencyDefect mu PA B S.psiHat).trans
    (mul_le_mul_of_nonneg_left (pullingMeas_eval_point_consistent_bob w W)
      (by norm_num : (0 : ℝ) ≤ 2))
  have hpoint : consistencyDefect mu (fun u a => (PA u).effect a)
      (fun u a => (PB u).effect a) S.psiHat ≤ (Fintype.card PauliEdge : ℝ) * epsilon := by
    change consistencyDefect mu
      (fun u a => S.placePlayer .alice ((S.pointMeas .alice W u).effect a))
      (fun u a => S.placePlayer .bob ((S.pointMeas .bob W u).effect a)) S.psiHat ≤ _
    rw [point_consistencyDefect_psiHat]
    exact point_self_consistency_le S W
  have hP := (opFamilyDistSq_le_two_mul_consistencyDefect mu PA PB S.psiHat).trans
    (mul_le_mul_of_nonneg_left hpoint (by norm_num : (0 : ℝ) ≤ 2))
  rw [opFamilyDistSq_symm] at hP
  have hAP := opFamilyDistSq_le_of_le_of_le mu _ _ _ S.psiHat _ _ hA hP
  have hAB := opFamilyDistSq_le_of_le_of_le mu _ _ _ S.psiHat _ _ hAP hB
  have hproj (side : PlayerSide) (u : Fin P.m → PauliScalar P) :
      Measurement.IsProjective (pullingPlacedMeasurement S side
        ((pullingMeas w side W).postprocess (fun g => evalPoly g u))) :=
    pullingPlacedMeasurement_isProjective S side _
      (SandwichProduct.postprocess_isProjective _ (pullingMeas_isProjective w side W) _)
  have hdef := consistencyDefect_le_opFamilyDistSq_of_projective mu A B S.psiHat
    (hproj .alice) (hproj .bob)
  exact hdef.trans (hAB.trans (by ring_nf; rfl))

end

end MIPStarRE.QPBT
