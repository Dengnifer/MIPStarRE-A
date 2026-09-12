import MIPStarRE.QPBT.Combining.Lines.Sampling
import MIPStarRE.QPBT.Combining.Points.MarginalContraction

/-!
# Point and line marginal comparisons

Projection contraction and the original line-point law give the two marginal
comparisons used by the X-Z-X line construction.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:882-963`,
blueprint `lem:qld-xz-lines`. The construction is recovered from commit
`6e8d67ef8ba22de69a0c166adcdf23ba6e7a33aa` for issue #512; the
source and completed-answer distinctions remain as documented in
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open scoped BigOperators Matrix MatrixOrder ComplexOrder

noncomputable section

set_option maxHeartbeats 800000 in
/-- The X marginal of any joint point witness is within squared distance
`4 * δQ` of the opposite X point measurement. This is
`eq:qld-qxz-close-to-point`, paper lines 917--932, with the supplied witness
error retained; the source later specializes to its constructed points. -/
theorem CombinedPointsWitness.marginal_X_distance_le
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
    opFamilyDistSq
      (uniformDistribution
        ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
      (fun xz a => ∑ b, S.place p1 ((points.Q p1.side xz.1 xz.2).effect (a, b)))
      (fun xz a => S.place p2 ((S.pointMeasExp p2.side .X xz.1).effect a))
      S.psiHat ≤ 4 * δQ := by
  classical
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (points.consistent_ZX p1 p2 hopp)
    (by norm_num : (0 : ℝ) ≤ 4))
  unfold opFamilyDistSq
  rw [← avgOver_const_mul]
  apply avgOver_mono
  intro xz
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  simpa only [ProjectiveSetting.placedMeasurement_effect, ProjectiveSetting.place_mul] using
    norm_marginal_sub_sq_le
    (fun b => S.place p1 ((points.Q p1.side xz.1 xz.2).effect (a, b)))
    (fun b => S.placedMeasurement_isProjective p1 _ (points.projective _ _ _) (a, b))
    (fun hbc => DistanceCalculus.projective_effect_mul_effect_eq_zero
      (S.placedMeasurement p1 (points.Q p1.side xz.1 xz.2))
      (S.placedMeasurement_isProjective p1 _ (points.projective _ _ _))
      (fun hpair => hbc (congrArg Prod.snd hpair)))
    (S.placedMeasurement p2 (S.pointMeasExp p2.side .Z xz.2))
    (S.placedMeasurement_isProjective p2 _ (S.pointMeasExp_isProjective _ _ _))
    (fun b => S.place_comm p1 p2 hopp _ _)
    (S.place p2 ((S.pointMeasExp p2.side .X xz.1).effect a)) S.psiHat

set_option maxHeartbeats 800000 in
/-- The Z marginal of any joint point witness is within squared distance
`4 * δQ` of the opposite Z point measurement. This is the symmetric
calculation `eq:qld-qxz-close-to-point-2`, paper lines 933--935. -/
theorem CombinedPointsWitness.marginal_Z_distance_le
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
    opFamilyDistSq
      (uniformDistribution
        ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
      (fun xz b => ∑ a, S.place p1 ((points.Q p1.side xz.1 xz.2).effect (a, b)))
      (fun xz b => S.place p2 ((S.pointMeasExp p2.side .Z xz.2).effect b))
      S.psiHat ≤ 4 * δQ := by
  classical
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (points.consistent_XZ p1 p2 hopp)
    (by norm_num : (0 : ℝ) ≤ 4))
  unfold opFamilyDistSq
  rw [← avgOver_const_mul]
  apply avgOver_mono
  intro xz
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b _
  simpa only [ProjectiveSetting.placedMeasurement_effect, ProjectiveSetting.place_mul] using
    norm_marginal_sub_sq_le
    (fun a => S.place p1 ((points.Q p1.side xz.1 xz.2).effect (a, b)))
    (fun a => S.placedMeasurement_isProjective p1 _ (points.projective _ _ _) (a, b))
    (fun hac => DistanceCalculus.projective_effect_mul_effect_eq_zero
      (S.placedMeasurement p1 (points.Q p1.side xz.1 xz.2))
      (S.placedMeasurement_isProjective p1 _ (points.projective _ _ _))
      (fun hpair => hac (congrArg Prod.fst hpair)))
    (S.placedMeasurement p2 (S.pointMeasExp p2.side .X xz.1))
    (S.placedMeasurement_isProjective p2 _ (S.pointMeasExp_isProjective _ _ _))
    (fun a => S.place_comm p1 p2 hopp _ _)
    (S.place p2 ((S.pointMeasExp p2.side .Z xz.2).effect b)) S.psiHat

/-- The point marginal of the line-point law is uniform. This is the
formalization-only averaging step in `eq:pasting-q1`, paper
`14_analysis_of_the_pauli_basis_test.tex:936-941`, using `lem:alnf` and `lem:dlnf`. -/
theorem avgOver_linePointDist_point (L : LdParams)
    (value : (Fin L.m → ScalarQ L) → ℝ) :
    avgOver (linePointDist L) (fun sample => value sample.2) =
      avgOver (uniformDistribution (Fin L.m → ScalarQ L)) value := by
  rw [linePointDist, avgOver_mix]
  rw [← Distribution.avgOver_map (aLinePointDist L) Prod.snd value,
    ← Distribution.avgOver_map (dLinePointDist L) Prod.snd value,
    (aLinePointDist_point_marginal_uniform L).1,
    (dLinePointDist_point_marginal_uniform L).1]
  ring

/-- Independent line-point samples have independent uniform point marginals.
This formalization-only identity transports the point estimates in
`eq:pasting-q1`, paper `14_analysis_of_the_pauli_basis_test.tex:936-941`. -/
theorem avgOver_prod_linePointDist_points (L : LdParams)
    (value : (Fin L.m → ScalarQ L) × (Fin L.m → ScalarQ L) → ℝ) :
    avgOver (Distribution.prod (linePointDist L) (linePointDist L))
      (fun sample => value (sample.1.2, sample.2.2)) =
      avgOver (uniformDistribution
        ((Fin L.m → ScalarQ L) × (Fin L.m → ScalarQ L))) value := by
  rw [uniformDistribution_prod, avgOver_prod, avgOver_prod]
  conv_lhs =>
    arg 2
    ext sample
    rw [avgOver_linePointDist_point L (fun point => value (sample.2, point))]
  exact avgOver_linePointDist_point L
    (fun point => avgOver (uniformDistribution _) (fun other => value (point, other)))

/-- The first postprocessed joint-point effect is its X marginal sum.
This is the definition preceding `eq:qld-qxz-close-to-point`, paper
`14_analysis_of_the_pauli_basis_test.tex:917-932`, not a witness assumption. -/
theorem CombinedPointsWitness.postprocess_fst_effect
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ) (side : PlayerSide)
    (x z : Fin P.m → PauliScalar P) (a : PauliScalar P) :
    ((points.Q side x z).postprocess Prod.fst).effect a =
      ∑ b, (points.Q side x z).effect (a, b) := by
  classical
  change (∑ pair ∈ Finset.univ.filter (fun pair => pair.1 = a),
    (points.Q side x z).effect pair) = _
  simp only [Finset.sum_filter, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp

/-- The second postprocessed joint-point effect is its Z marginal sum.
Source: `eq:qld-qxz-close-to-point-2`, paper
`14_analysis_of_the_pauli_basis_test.tex:933-935`. -/
theorem CombinedPointsWitness.postprocess_snd_effect
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ) (side : PlayerSide)
    (x z : Fin P.m → PauliScalar P) (b : PauliScalar P) :
    ((points.Q side x z).postprocess Prod.snd).effect b =
      ∑ a, (points.Q side x z).effect (a, b) := by
  classical
  change (∑ pair ∈ Finset.univ.filter (fun pair => pair.2 = b),
    (points.Q side x z).effect pair) = _
  simp [Finset.sum_filter, Fintype.sum_prod_type]

/-- X marginal distance on the product line-point law, retaining the supplied
point error. This is the first transport step of `eq:pasting-q1`, paper
`14_analysis_of_the_pauli_basis_test.tex:936-941`; no line comparison is assumed. -/
theorem CombinedPointsWitness.marginal_X_linePoint_distance_le
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
    opFamilyDistSq (Distribution.prod (linePointDist P.toLdParams)
      (linePointDist P.toLdParams))
      (fun sample a => S.place p1
        (((points.Q p1.side sample.1.2 sample.2.2).postprocess Prod.fst).effect a))
      (fun sample a => S.place p2 ((S.pointMeasExp p2.side .X sample.1.2).effect a))
      S.psiHat ≤ 4 * δQ := by
  classical
  simp_rw [points.postprocess_fst_effect, S.place_finset_sum]
  unfold opFamilyDistSq
  rw [avgOver_prod_linePointDist_points P.toLdParams (fun xz =>
    ∑ a, ‖applyOperatorToState
      ((∑ b, S.place p1 ((points.Q p1.side xz.1 xz.2).effect (a, b))) -
        S.place p2 ((S.pointMeasExp p2.side .X xz.1).effect a)) S.psiHat‖ ^ 2)]
  exact points.marginal_X_distance_le p1 p2 hopp

/-- Z marginal distance on the product line-point law, with the same error as
the uniform-point estimate. Source: `eq:pasting-q1`, paper
`14_analysis_of_the_pauli_basis_test.tex:936-941`. -/
theorem CombinedPointsWitness.marginal_Z_linePoint_distance_le
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
    opFamilyDistSq (Distribution.prod (linePointDist P.toLdParams)
      (linePointDist P.toLdParams))
      (fun sample b => S.place p1
        (((points.Q p1.side sample.1.2 sample.2.2).postprocess Prod.snd).effect b))
      (fun sample b => S.place p2 ((S.pointMeasExp p2.side .Z sample.2.2).effect b))
      S.psiHat ≤ 4 * δQ := by
  classical
  simp_rw [points.postprocess_snd_effect, S.place_finset_sum]
  unfold opFamilyDistSq
  rw [avgOver_prod_linePointDist_points P.toLdParams (fun xz =>
    ∑ b, ‖applyOperatorToState
      ((∑ a, S.place p1 ((points.Q p1.side xz.1 xz.2).effect (a, b))) -
        S.place p2 ((S.pointMeasExp p2.side .Z xz.2).effect b)) S.psiHat‖ ^ 2)]
  exact points.marginal_Z_distance_le p1 p2 hopp

/-- Completing both answer alphabets with a zero outcome preserves placed
squared distance. This formalization-only identity reconciles `eq:pasting-q1`
with the completed evaluation convention of `lem:qld-comm-line-cons`. -/
theorem ProjectiveSetting.opFamilyDistSq_postprocess_some
    {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε)
    {Sample Answer : Type*} [Fintype Answer] [DecidableEq Answer]
    (law : Distribution Sample) (p1 p2 : Placement)
    (first : Sample → MIPStarRE.Quantum.Measurement Answer (S.ExpandedLocalSpace p1.side))
    (second : Sample → MIPStarRE.Quantum.Measurement Answer (S.ExpandedLocalSpace p2.side)) :
    opFamilyDistSq law
      (fun sample answer => S.place p1 (((first sample).postprocess some).effect answer))
      (fun sample answer => S.place p2 (((second sample).postprocess some).effect answer))
      S.psiHat =
    opFamilyDistSq law (fun sample answer => S.place p1 ((first sample).effect answer))
      (fun sample answer => S.place p2 ((second sample).effect answer)) S.psiHat := by
  classical
  unfold opFamilyDistSq
  congr 1
  funext sample
  rw [Fintype.sum_option]
  simp [MIPStarRE.Quantum.Measurement.postprocess,
    MIPStarRE.Quantum.Submeasurement.postprocess, Finset.sum_filter,
    S.place_zero, applyOperatorToState]

/-- The completed X marginal has the same `4 * δQ` bound on line-point
samples. Source: the first comparison of `eq:pasting-q1`, paper
`14_analysis_of_the_pauli_basis_test.tex:936-941`, before inserting the line. -/
theorem CombinedPointsWitness.marginal_X_option_linePoint_distance_le
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
    opFamilyDistSq (Distribution.prod (linePointDist P.toLdParams)
      (linePointDist P.toLdParams))
      (fun sample answer => S.place p1
        ((((points.Q p1.side sample.1.2 sample.2.2).postprocess Prod.fst).postprocess
          some).effect answer))
      (fun sample answer => S.place p2
        ((S.pointMeasExpOption p2.side .X sample.1.2).effect answer))
      S.psiHat ≤ 4 * δQ := by
  unfold ProjectiveSetting.pointMeasExpOption
  erw [S.opFamilyDistSq_postprocess_some]
  exact points.marginal_X_linePoint_distance_le p1 p2 hopp

/-- The completed Z marginal has the same `4 * δQ` bound on line-point
samples. Source: the second comparison of `eq:pasting-q1`, paper
`14_analysis_of_the_pauli_basis_test.tex:936-941`, before inserting the line. -/
theorem CombinedPointsWitness.marginal_Z_option_linePoint_distance_le
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
    opFamilyDistSq (Distribution.prod (linePointDist P.toLdParams)
      (linePointDist P.toLdParams))
      (fun sample answer => S.place p1
        ((((points.Q p1.side sample.1.2 sample.2.2).postprocess Prod.snd).postprocess
          some).effect answer))
      (fun sample answer => S.place p2
        ((S.pointMeasExpOption p2.side .Z sample.2.2).effect answer))
      S.psiHat ≤ 4 * δQ := by
  unfold ProjectiveSetting.pointMeasExpOption
  erw [S.opFamilyDistSq_postprocess_some]
  exact points.marginal_Z_linePoint_distance_le p1 p2 hopp

/-- On either placement the evaluated line is close to the completed point
measurement. This formalization-only version of the intermediate comparison
in `eq:pasting-q1` retains the strategy error. It follows from
`lem:qld-comm-line-cons` item 3 and `lem:qld-comm-cons` item 1, rather than
identifying measurements on different placements. -/
theorem exists_expLine_point_same_placement_distance_le :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
        (p1 p2 : Placement), p1.IsOpposite p2 → ∀ W : PauliKind,
        opFamilyDistSq (linePointDist P.toLdParams)
          (fun sample answer => S.place p2
            ((S.lineEvalMeasExp p2.side W sample.1 sample.2).effect answer))
          (fun sample answer => S.place p2
            ((S.pointMeasExpOption p2.side W sample.2).effect answer))
          S.psiHat ≤ C * (ε + deltaLine ε) := by
  obtain ⟨Cp, hCp, hp⟩ := expPoint_self_cons
  obtain ⟨Cl, hCl, hl⟩ := expLine_point_cons'
  refine ⟨2 * (Cp + Cl), by linarith, ?_⟩
  intro P ε S p1 p2 hopp W
  classical
  have hreverse : p2.IsOpposite p1 := by
    cases p1 <;> cases p2 <;> simp_all [Placement.IsOpposite]
  have hpoint : opFamilyDistSq (linePointDist P.toLdParams)
      (fun sample answer => S.place p1
        ((S.pointMeasExpOption p1.side W sample.2).effect answer))
      (fun sample answer => S.place p2
        ((S.pointMeasExpOption p2.side W sample.2).effect answer)) S.psiHat ≤ Cp * ε := by
    unfold ProjectiveSetting.pointMeasExpOption
    erw [S.opFamilyDistSq_postprocess_some]
    unfold opFamilyDistSq
    rw [avgOver_linePointDist_point P.toLdParams (fun point =>
      ∑ answer, ‖applyOperatorToState
        (S.place p1 ((S.pointMeasExp p1.side W point).effect answer) -
          S.place p2 ((S.pointMeasExp p2.side W point).effect answer)) S.psiHat‖ ^ 2)]
    exact hp P ε S p1 p2 hopp W
  have htri := opFamilyDistSq_le_of_le_of_le _ _ _ _ S.psiHat _ _
    (hl P ε S p2 p1 hreverse W) hpoint
  refine htri.trans ?_
  have hε := S.eps_nonneg
  have hline : 0 ≤ deltaLine ε := Real.sqrt_nonneg ε
  nlinarith

/-- Both genuine line--point marginal comparisons needed for pasting, in
squared distance, follow from the supplied point witness and the expanded
line comparisons. The `8 * δQ` term is not absorbed into the strategy error.
Source: `eq:pasting-q1`, paper `14_analysis_of_the_pauli_basis_test.tex:936-941`. -/
theorem exists_combinedPoints_line_marginal_distance_le :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε δQ : ℝ) (S : ProjectiveSetting P ε)
        (points : CombinedPointsWitness S δQ)
        (p1 p2 : Placement), p1.IsOpposite p2 →
        opFamilyDistSq (Distribution.prod (linePointDist P.toLdParams)
          (linePointDist P.toLdParams))
          (fun sample answer => S.place p1
            ((((points.Q p1.side sample.1.2 sample.2.2).postprocess Prod.fst).postprocess
              some).effect answer))
          (fun sample answer => S.place p2
            ((S.lineEvalMeasExp p2.side .X sample.1.1 sample.1.2).effect answer))
          S.psiHat ≤ 8 * δQ + C * (ε + deltaLine ε) ∧
        opFamilyDistSq (Distribution.prod (linePointDist P.toLdParams)
          (linePointDist P.toLdParams))
          (fun sample answer => S.place p1
            ((((points.Q p1.side sample.1.2 sample.2.2).postprocess Prod.snd).postprocess
              some).effect answer))
          (fun sample answer => S.place p2
            ((S.lineEvalMeasExp p2.side .Z sample.2.1 sample.2.2).effect answer))
          S.psiHat ≤ 8 * δQ + C * (ε + deltaLine ε) := by
  obtain ⟨C, hC, hbound⟩ := exists_expLine_point_same_placement_distance_le
  refine ⟨2 * C, by linarith, ?_⟩
  intro P ε δQ S points p1 p2 hopp
  classical
  have hX : opFamilyDistSq (Distribution.prod (linePointDist P.toLdParams)
      (linePointDist P.toLdParams))
      (fun sample answer => S.place p2
        ((S.pointMeasExpOption p2.side .X sample.1.2).effect answer))
      (fun sample answer => S.place p2
        ((S.lineEvalMeasExp p2.side .X sample.1.1 sample.1.2).effect answer))
      S.psiHat ≤ C * (ε + deltaLine ε) := by
    rw [DistanceCalculus.opFamilyDistSq_symm]
    unfold opFamilyDistSq
    rw [avgOver_prod]
    simp_rw [avgOver_const_of_isProbability _ (linePointDist_isProbability P.toLdParams)]
    exact hbound P ε S p1 p2 hopp .X
  have hZ : opFamilyDistSq (Distribution.prod (linePointDist P.toLdParams)
      (linePointDist P.toLdParams))
      (fun sample answer => S.place p2
        ((S.pointMeasExpOption p2.side .Z sample.2.2).effect answer))
      (fun sample answer => S.place p2
        ((S.lineEvalMeasExp p2.side .Z sample.2.1 sample.2.2).effect answer))
      S.psiHat ≤ C * (ε + deltaLine ε) := by
    rw [DistanceCalculus.opFamilyDistSq_symm]
    unfold opFamilyDistSq
    rw [avgOver_prod]
    erw [avgOver_const_of_isProbability _ (linePointDist_isProbability P.toLdParams)
      (opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample answer => S.place p2
          ((S.lineEvalMeasExp p2.side .Z sample.1 sample.2).effect answer))
        (fun sample answer => S.place p2
          ((S.pointMeasExpOption p2.side .Z sample.2).effect answer)) S.psiHat)]
    exact hbound P ε S p1 p2 hopp .Z
  constructor
  · convert opFamilyDistSq_le_of_le_of_le _ _ _ _ S.psiHat _ _
      (points.marginal_X_option_linePoint_distance_le p1 p2 hopp) hX using 1
    ring
  · convert opFamilyDistSq_le_of_le_of_le _ _ _ _ S.psiHat _ _
      (points.marginal_Z_option_linePoint_distance_le p1 p2 hopp) hZ using 1
    ring

/-- Completing a joint answer and then taking its X marginal agrees with
completing the X marginal. This is a formalization-only postprocessing
identity for `eq:pasting-q1`; it is not an extra marginal hypothesis. -/
theorem CombinedPointsWitness.completed_fst_effect
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ) (side : PlayerSide)
    (x z : Fin P.m → PauliScalar P) (answer : Option (PauliScalar P)) :
    (((points.Q side x z).postprocess (fun pair => (some pair.1, some pair.2))).postprocess
      Prod.fst).effect answer =
      (((points.Q side x z).postprocess Prod.fst).postprocess some).effect answer := by
  classical
  exact congrArg (fun meas => meas.effect answer)
    ((MIPStarRE.Quantum.Measurement.postprocess_comp (points.Q side x z)
      (fun pair => (some pair.1, some pair.2)) Prod.fst).trans
      (MIPStarRE.Quantum.Measurement.postprocess_comp (points.Q side x z) Prod.fst some).symm)

/-- Completing a joint answer and then taking its Z marginal agrees with
completing the Z marginal. Source: `eq:pasting-q1`, with the existing
completed evaluation convention. -/
theorem CombinedPointsWitness.completed_snd_effect
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ) (side : PlayerSide)
    (x z : Fin P.m → PauliScalar P) (answer : Option (PauliScalar P)) :
    (((points.Q side x z).postprocess (fun pair => (some pair.1, some pair.2))).postprocess
      Prod.snd).effect answer =
      (((points.Q side x z).postprocess Prod.snd).postprocess some).effect answer := by
  classical
  exact congrArg (fun meas => meas.effect answer)
    ((MIPStarRE.Quantum.Measurement.postprocess_comp (points.Q side x z)
      (fun pair => (some pair.1, some pair.2)) Prod.snd).trans
      (MIPStarRE.Quantum.Measurement.postprocess_comp (points.Q side x z) Prod.snd some).symm)

/-- The two forward marginal hypotheses for pasting hold in the consistency
convention, with explicit dependence on both errors. Source: `eq:pasting-q1`,
paper `14_analysis_of_the_pauli_basis_test.tex:936-941`. Projectivity is
derived from the existing measurements and their postprocessings. -/
theorem exists_combinedPoints_line_marginal_defect_le :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε δQ : ℝ) (S : ProjectiveSetting P ε)
        (points : CombinedPointsWitness S δQ)
        (p1 p2 : Placement), p1.IsOpposite p2 →
        consistencyDefect (Distribution.prod (linePointDist P.toLdParams)
          (linePointDist P.toLdParams))
          (fun sample answer => S.place p1
            ((((points.Q p1.side sample.1.2 sample.2.2).postprocess
              (fun pair => (some pair.1, some pair.2))).postprocess Prod.fst).effect answer))
          (fun sample answer => S.place p2
            ((S.lineEvalMeasExp p2.side .X sample.1.1 sample.1.2).effect answer))
          S.psiHat ≤ 8 * δQ + C * (ε + deltaLine ε) ∧
        consistencyDefect (Distribution.prod (linePointDist P.toLdParams)
          (linePointDist P.toLdParams))
          (fun sample answer => S.place p1
            ((((points.Q p1.side sample.1.2 sample.2.2).postprocess
              (fun pair => (some pair.1, some pair.2))).postprocess Prod.snd).effect answer))
          (fun sample answer => S.place p2
            ((S.lineEvalMeasExp p2.side .Z sample.2.1 sample.2.2).effect answer))
          S.psiHat ≤ 8 * δQ + C * (ε + deltaLine ε) := by
  obtain ⟨C, hC, hbound⟩ := exists_combinedPoints_line_marginal_distance_le
  refine ⟨C, hC, ?_⟩
  intro P ε δQ S points p1 p2 hopp
  classical
  simp_rw [points.completed_fst_effect, points.completed_snd_effect]
  have hcompare (coordinate : PauliScalar P × PauliScalar P → PauliScalar P)
      (sampleLine : (LineDesc P.toLdParams × (Fin P.m → PauliScalar P)) ×
        (LineDesc P.toLdParams × (Fin P.m → PauliScalar P)) →
        LineDesc P.toLdParams × (Fin P.m → PauliScalar P)) (W : PauliKind) :=
    consistencyDefect_le_opFamilyDistSq_of_projective
      (Distribution.prod (linePointDist P.toLdParams) (linePointDist P.toLdParams))
      (fun sample => S.placedMeasurement p1
        (((points.Q p1.side sample.1.2 sample.2.2).postprocess coordinate).postprocess some))
      (fun sample => S.placedMeasurement p2
        (S.lineEvalMeasExp p2.side W (sampleLine sample).1 (sampleLine sample).2)) S.psiHat
      (fun sample => S.placedMeasurement_isProjective p1 _
        (SandwichProduct.postprocess_isProjective _
          (SandwichProduct.postprocess_isProjective _ (points.projective _ _ _) _) _))
      (fun sample => S.placedMeasurement_isProjective p2 _
        (SandwichProduct.postprocess_isProjective _ (S.lineMeasExp_isProjective _ _ _) _))
  exact ⟨(hcompare Prod.fst Prod.fst .X).trans (hbound P ε δQ S points p1 p2 hopp).1,
    (hcompare Prod.snd Prod.snd .Z).trans (hbound P ε δQ S points p1 p2 hopp).2⟩


end

end MIPStarRE.QPBT
