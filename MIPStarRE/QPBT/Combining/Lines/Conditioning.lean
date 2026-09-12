import MIPStarRE.QPBT.Combining.Lines.PointComparison
import MIPStarRE.QPBT.Combining.Lines.CombinedMeasurement
import MIPStarRE.QPBT.Combining.Lines.ConsistencyPositivity
import MIPStarRE.QPBT.Games.Sandwich

/-!
# Conditioning the line-pasting distribution

The proof conditions only on nonzero X directions. Conditional collision
bounds apply there, and the discarded probability is restored explicitly.

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

/-- Indicator averages express the positive-fiber collision predicate of
`lem:pasting`, paper `06_nonlocal_games_and_mipstar.tex:504-525`.
This formalization-only adapter is applied below with a proved fiber estimate. -/
theorem collision_bound_of_fiber_averages {X Y₁ Y₂ R₂ Γ₂ : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
    [Fintype Y₂] [DecidableEq Y₂] [Fintype R₂] [DecidableEq R₂]
    [Fintype Γ₂] (dist : Distribution ((X × Y₁) × Y₂))
    (eval₂ : Γ₂ → Y₂ → R₂) (eta : ℝ)
    (hbound : ∀ fixed : X × Y₁, ∀ first second : Γ₂, first ≠ second →
      avgOver dist (fun sample => if sample.1 = fixed then
        (if eval₂ first sample.2 = eval₂ second sample.2 then 1 else 0) else 0) ≤
      eta * avgOver dist (fun sample => if sample.1 = fixed then 1 else 0)) :
    HasConditionalCollisionBound dist eval₂ eta := by
  classical
  intro question point _ first second hne
  have havg (value : ((X × Y₁) × Y₂) → ℝ) :
      avgOver dist value = ∑ sample, dist.weight sample * value sample := by
    exact (dist.sum_univ_eq_sum_support _ (fun sample hout => by
      rw [dist.outsideSupport sample hout, zero_mul])).symm
  have hmass : (dist.map Prod.fst).weight (question, point) =
      avgOver dist (fun sample => if sample.1 = (question, point) then 1 else 0) := by
    rw [Distribution.map_weight, Distribution.sum_filter_weight_eq_avgOver]
  rw [hmass]
  have h := hbound (question, point) first second hne
  simpa [havg, Fintype.sum_prod_type, mul_ite] using h

/-- Independent Z sampling preserves the weighted collision estimate on nonzero
X directions. The weight may depend on the entire Z sample but only on the X
line, not its point. This is proof-only support for `lem:qld-xz-lines`, paper
`14_analysis_of_the_pauli_basis_test.tex:950-955`. No Z direction is discarded. -/
theorem prod_linePointDist_nondegenerate_weighted_collision_le {L : LdParams} {bound : ℕ}
    (weight : LineDesc L → (LineDesc L × (Fin L.m → ScalarQ L)) → ℝ)
    (hweight : ∀ line sample, 0 ≤ weight line sample)
    (first second : DegPoly L bound) (hne : first ≠ second) :
    avgOver (Distribution.prod (linePointDist L) (linePointDist L)) (fun samples =>
      if samples.1.1.direction ≠ 0 then weight samples.1.1 samples.2 *
        (if evalOpt samples.1.1 samples.1.2 first =
          evalOpt samples.1.1 samples.1.2 second then 1 else 0) else 0) ≤
    (bound : ℝ) / Fintype.card (ScalarQ L) *
      avgOver (Distribution.prod (linePointDist L) (linePointDist L)) (fun samples =>
        if samples.1.1.direction ≠ 0 then weight samples.1.1 samples.2 else 0) := by
  classical
  simp only [avgOver_prod]
  rw [avgOver_comm, avgOver_comm (linePointDist L) (linePointDist L)
    (fun firstSample secondSample =>
      if firstSample.1.direction ≠ 0 then weight firstSample.1 secondSample else 0)]
  rw [← avgOver_const_mul]
  apply avgOver_mono
  intro sample
  exact linePointDist_nondegenerate_weighted_collision_le
    (fun line => weight line sample) (fun line => hweight line sample) first second hne

/-- The event that the X direction is nonzero has positive mass under the
product line-point law. This formalization-only consequence of the retained-mass
bound permits conditioning in `lem:qld-xz-lines`, paper lines 950--963. -/
theorem prod_linePointDist_nondegenerate_mass_pos (L : LdParams) :
    0 < ∑ samples ∈ (Distribution.prod (linePointDist L) (linePointDist L)).support.filter
      (fun samples => samples.1.1.direction ≠ 0),
      (Distribution.prod (linePointDist L) (linePointDist L)).weight samples := by
  classical
  rw [Distribution.sum_filter_weight_eq_avgOver, avgOver_prod]
  change 0 < avgOver (linePointDist L) (fun sample => avgOver (linePointDist L)
    (fun _ => if sample.1.direction ≠ 0 then 1 else 0))
  simp_rw [avgOver_const_of_isProbability _ (linePointDist_isProbability L)]
  rw [← Distribution.sum_filter_weight_eq_avgOver]
  exact lt_of_lt_of_le (by norm_num) (linePointDist_nondegenerate_mass_ge L)

/-- Proof-only question law for one-sided pasting in `lem:qld-xz-lines`, paper
`14_analysis_of_the_pauli_basis_test.tex:950-963`. Condition the source product
law on nonzero X direction, and send `(sX,sZ)` to
`(((sX.line,sZ.line),sZ),sX)`. Thus `G1 = Z` and `G2 = X`; the evaluation
questions retain their line descriptors. This is not a modified game sampler.
See `docs/paper-gaps/qpbt_combined-lines-error-term.tex`, issue #118. -/
def nondegenerateLinePastingDist (L : LdParams) :
    Distribution (((LineDesc L × LineDesc L) ×
      (LineDesc L × (Fin L.m → ScalarQ L))) × (LineDesc L × (Fin L.m → ScalarQ L))) :=
  (Distribution.restrict (Distribution.prod (linePointDist L) (linePointDist L))
    (fun samples => samples.1.1.direction ≠ 0)
    (prod_linePointDist_nondegenerate_mass_pos L)).map
      (fun samples => (((samples.1.1, samples.2.1), samples.2), samples.1))

/-- The actual conditioned product question law satisfies the conditional
collision predicate with parameter `bound/q`. This discharges, rather than
assumes, the collision premise of `lem:pasting` used in `lem:qld-xz-lines`,
paper `14_analysis_of_the_pauli_basis_test.tex:950-955`. The restriction is
proof-only; the discarded probability remains in the restoration estimate. -/
theorem nondegenerateLinePastingDist_collision_bound (P : AdmissibleParams) (bound : ℕ) :
    HasConditionalCollisionBound (nondegenerateLinePastingDist P.toLdParams)
      (fun (poly : DegPoly P.toLdParams bound) sample => evalOpt sample.1 sample.2 poly)
      ((bound : ℝ) / Fintype.card (ScalarQ P.toLdParams)) := by
  classical
  let L := P.toLdParams
  apply collision_bound_of_fiber_averages
  intro fixed first second hne
  simp only [nondegenerateLinePastingDist, Distribution.avgOver_map]
  have hpos := prod_linePointDist_nondegenerate_mass_pos L
  apply (mul_le_mul_iff_right₀ hpos).mp
  rw [avgOver_restrict_mul_mass, mul_left_comm _ ((bound : ℝ) /
    Fintype.card (ScalarQ L)), avgOver_restrict_mul_mass]
  have h := prod_linePointDist_nondegenerate_weighted_collision_le
    (fun line sample => if ((line, sample.1), sample) = fixed then 1 else 0)
    (fun line sample => by split_ifs <;> norm_num) first second hne
  have hswap (condition other : Prop) [Decidable condition] [Decidable other] (value : ℝ) :
      (if condition then (if other then value else 0) else 0) =
        (if other then (if condition then value else 0) else 0) := by
    split_ifs <;> rfl
  simpa only [avgOver, Finset.sum_filter, mul_ite, mul_one, mul_zero,
    ite_mul, one_mul, zero_mul, hswap] using h

/-- Probability retained by the proof-only X-direction restriction for
`lem:qld-xz-lines`, paper `14_analysis_of_the_pauli_basis_test.tex:950-963`.
This coefficient is kept when restoring the source consistency defect. -/
def nondegenerateLinePastingMass (L : LdParams) : ℝ :=
  ∑ samples ∈ (Distribution.prod (linePointDist L) (linePointDist L)).support.filter
    (fun samples => samples.1.1.direction ≠ 0),
    (Distribution.prod (linePointDist L) (linePointDist L)).weight samples

/-- The proof-only pasting question law is normalized, as required by
`lem:pasting`, paper `06_nonlocal_games_and_mipstar.tex:504-525`. -/
theorem nondegenerateLinePastingDist_isProbability (L : LdParams) :
    (nondegenerateLinePastingDist L).IsProbability := by
  exact (Distribution.restrict_isProbability _ _
    (prod_linePointDist_nondegenerate_mass_pos L)).map _

/-- For arbitrary complete measurements on opposite placements, conditioning
and question relabeling inflate the defect by at most the inverse retained mass.
The needed nonnegativity follows from positivity on opposite registers, not a
new input. Proof-only support for `eq:pasting-q1`, paper lines 936--963. -/
theorem consistencyDefect_nondegenerateLinePastingDist_le {P : AdmissibleParams} {ε : ℝ}
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (S : ProjectiveSetting P ε) (p1 p2 : Placement) (hopp : p1.IsOpposite p2)
    (first : ((LineDesc P.toLdParams × (Fin P.m → PauliScalar P)) ×
      (LineDesc P.toLdParams × (Fin P.m → PauliScalar P))) →
      MIPStarRE.Quantum.Measurement Outcome (S.ExpandedLocalSpace p1.side))
    (second : ((LineDesc P.toLdParams × (Fin P.m → PauliScalar P)) ×
      (LineDesc P.toLdParams × (Fin P.m → PauliScalar P))) →
      MIPStarRE.Quantum.Measurement Outcome (S.ExpandedLocalSpace p2.side)) :
    consistencyDefect (nondegenerateLinePastingDist P.toLdParams)
      (fun question answer => S.place p1 ((first (question.2, question.1.2)).effect answer))
      (fun question answer => S.place p2 ((second (question.2, question.1.2)).effect answer))
      S.psiHat ≤
    consistencyDefect (Distribution.prod (linePointDist P.toLdParams)
      (linePointDist P.toLdParams))
      (fun sample answer => S.place p1 ((first sample).effect answer))
      (fun sample answer => S.place p2 ((second sample).effect answer)) S.psiHat /
      nondegenerateLinePastingMass P.toLdParams := by
  unfold consistencyDefect nondegenerateLinePastingDist
  rw [Distribution.avgOver_map]
  exact avgOver_restrict_le_div_mass _ _ _ _ (fun sample =>
    consistencyDefect_integrand_nonneg S p1 p2 hopp (first sample) (second sample))

/-- The supplied completed point marginals, with answers ordered Z then X,
satisfy both conditioned line comparisons with error
`(8 * δQ + C * (ε + deltaLine ε)) / r`. The line families depend only on the
common line-pair question. This proves the marginal inputs in the source order
for the X-outer sandwich, rather than assuming them or omitting the point error.
Source: `eq:pasting-q1`, paper `14_analysis_of_the_pauli_basis_test.tex:936-963`.
Tensor-register transport to the bipartite pasting theorem remains separate. -/
theorem exists_combinedPoints_conditioned_line_marginal_defect_le :
    ∃ constant : ℝ, 1 ≤ constant ∧
      ∀ (P : AdmissibleParams) (ε δQ : ℝ) (S : ProjectiveSetting P ε)
        (points : CombinedPointsWitness S δQ)
        (p1 p2 : Placement), p1.IsOpposite p2 →
        consistencyDefect (nondegenerateLinePastingDist P.toLdParams)
          (fun question answer => S.place p1
            ((((points.Q p1.side question.2.2 question.1.2.2).postprocess
              (fun pair => (some pair.2, some pair.1))).postprocess Prod.fst).effect answer))
          (fun question answer => S.place p2
            ((S.lineEvalMeasExp p2.side .Z question.1.1.2 question.1.2.2).effect answer))
          S.psiHat ≤ (8 * δQ + constant * (ε + deltaLine ε)) /
            nondegenerateLinePastingMass P.toLdParams ∧
        consistencyDefect (nondegenerateLinePastingDist P.toLdParams)
          (fun question answer => S.place p1
            ((((points.Q p1.side question.2.2 question.1.2.2).postprocess
              (fun pair => (some pair.2, some pair.1))).postprocess Prod.snd).effect answer))
          (fun question answer => S.place p2
            ((S.lineEvalMeasExp p2.side .X question.1.1.1 question.2.2).effect answer))
          S.psiHat ≤ (8 * δQ + constant * (ε + deltaLine ε)) /
            nondegenerateLinePastingMass P.toLdParams := by
  obtain ⟨constant, hconstant, hbound⟩ := exists_combinedPoints_line_marginal_defect_le
  refine ⟨constant, hconstant, ?_⟩
  intro P ε δQ S points p1 p2 hopp
  classical
  have hswap (side : PlayerSide) (pointX pointZ : Fin P.m → PauliScalar P)
      (answer : Option (PauliScalar P)) :
      (((points.Q side pointX pointZ).postprocess
        (fun pair => (some pair.2, some pair.1))).postprocess Prod.fst).effect answer =
        (((points.Q side pointX pointZ).postprocess
          (fun pair => (some pair.1, some pair.2))).postprocess Prod.snd).effect answer ∧
      (((points.Q side pointX pointZ).postprocess
        (fun pair => (some pair.2, some pair.1))).postprocess Prod.snd).effect answer =
        (((points.Q side pointX pointZ).postprocess
          (fun pair => (some pair.1, some pair.2))).postprocess Prod.fst).effect answer := by
    simp only [MIPStarRE.Quantum.Measurement.postprocess_comp, and_self]
  simp_rw [(hswap _ _ _ _).1, (hswap _ _ _ _).2]
  have hmass := (prod_linePointDist_nondegenerate_mass_pos P.toLdParams).le
  constructor
  · have h := (consistencyDefect_nondegenerateLinePastingDist_le S p1 p2 hopp
      (fun sample => ((points.Q p1.side sample.1.2 sample.2.2).postprocess
        (fun pair => (some pair.1, some pair.2))).postprocess Prod.snd)
      (fun sample => S.lineEvalMeasExp p2.side .Z sample.2.1 sample.2.2)).trans
      (div_le_div_of_nonneg_right (hbound P ε δQ S points p1 p2 hopp).2 hmass)
    unfold consistencyDefect nondegenerateLinePastingDist at h ⊢
    simp only [Distribution.avgOver_map] at h ⊢
    exact h
  · have h := (consistencyDefect_nondegenerateLinePastingDist_le S p1 p2 hopp
      (fun sample => ((points.Q p1.side sample.1.2 sample.2.2).postprocess
        (fun pair => (some pair.1, some pair.2))).postprocess Prod.fst)
      (fun sample => S.lineEvalMeasExp p2.side .X sample.1.1 sample.1.2)).trans
      (div_le_div_of_nonneg_right (hbound P ε δQ S points p1 p2 hopp).1 hmass)
    unfold consistencyDefect nondegenerateLinePastingDist at h ⊢
    simp only [Distribution.avgOver_map] at h ⊢
    exact h

/-- Restore the unconditioned consistency defect with its retained-mass factor
and additive cost at most `1/(2q)`. This holds for the supplied measurement
families on every directed opposite placement, without a defect hypothesis.
Proof-only support for `lem:qld-xz-lines`, paper lines 950--963. -/
theorem consistencyDefect_le_nondegenerateLinePastingDist_add_mass
    {P : AdmissibleParams} {ε : ℝ}
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (S : ProjectiveSetting P ε) (p1 p2 : Placement) (hopp : p1.IsOpposite p2)
    (first : ((LineDesc P.toLdParams × (Fin P.m → PauliScalar P)) ×
      (LineDesc P.toLdParams × (Fin P.m → PauliScalar P))) →
      MIPStarRE.Quantum.Measurement Outcome (S.ExpandedLocalSpace p1.side))
    (second : ((LineDesc P.toLdParams × (Fin P.m → PauliScalar P)) ×
      (LineDesc P.toLdParams × (Fin P.m → PauliScalar P))) →
      MIPStarRE.Quantum.Measurement Outcome (S.ExpandedLocalSpace p2.side)) :
    consistencyDefect (Distribution.prod (linePointDist P.toLdParams)
      (linePointDist P.toLdParams))
      (fun sample answer => S.place p1 ((first sample).effect answer))
      (fun sample answer => S.place p2 ((second sample).effect answer)) S.psiHat ≤
    nondegenerateLinePastingMass P.toLdParams *
      consistencyDefect (nondegenerateLinePastingDist P.toLdParams)
        (fun question answer => S.place p1 ((first (question.2, question.1.2)).effect answer))
        (fun question answer => S.place p2 ((second (question.2, question.1.2)).effect answer))
        S.psiHat + 1 / (2 * Fintype.card (ScalarQ P.toLdParams)) := by
  classical
  unfold consistencyDefect nondegenerateLinePastingDist nondegenerateLinePastingMass
  rw [Distribution.avgOver_map]
  let value := fun sample => ∑ answer : Outcome, ∑ other : Outcome,
      if answer = other then 0 else (inner ℂ S.psiHat
        ((EuclideanSpace.equiv (SixReg P S.toStrategy.ιA S.toStrategy.ιB) ℂ).symm
          ((S.place p1 ((first sample).effect answer) *
            S.place p2 ((second sample).effect other)).mulVec S.psiHat))).re
  have hunit : ∀ sample, value sample ≤ 1 := fun sample =>
    consistencyDefect_integrand_le_one S p1 p2 hopp (first sample) (second sample)
  have h := avgOver_le_restrict_add_discarded_mass _
    (fun samples => samples.1.1.direction ≠ 0)
    (prod_linePointDist_nondegenerate_mass_pos P.toLdParams) value hunit
  have hdiscard : (∑ sample ∈ (Distribution.prod (linePointDist P.toLdParams)
      (linePointDist P.toLdParams)).support.filter (fun sample => ¬ sample.1.1.direction ≠ 0),
      (Distribution.prod (linePointDist P.toLdParams)
        (linePointDist P.toLdParams)).weight sample) ≤
      1 / (2 * Fintype.card (ScalarQ P.toLdParams)) := by
    rw [Distribution.sum_filter_weight_eq_avgOver]
    simpa only [ne_eq, not_not] using prod_linePointDist_zero_X_direction_mass_le P.toLdParams
  have hfinal := h.trans (add_le_add_right hdiscard _)
  exact hfinal

/-- The actual X-outer line sandwich and the supplied completed points satisfy
the mass-restoration inequality on every directed opposite placement. This is
not the final consistency estimate: its right side still contains the
conditioned defect to be bounded by one-sided pasting. Source:
`lem:qld-xz-lines`, paper `14_analysis_of_the_pauli_basis_test.tex:942-963`;
remaining construction recorded in `docs/paper-gaps/qpbt_combined-lines-error-term.tex`. -/
theorem ProjectiveSetting.combinedLineMeasurement_consistency_le_conditioned
    {P : AdmissibleParams} {ε δQ : ℝ} (S : ProjectiveSetting P ε)
    (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
    consistencyDefect (Distribution.prod (linePointDist P.toLdParams)
      (linePointDist P.toLdParams))
      (fun sample answer => S.place p1
        (((points.Q p1.side sample.1.2 sample.2.2).postprocess
          (fun pair => (some pair.1, some pair.2))).effect answer))
      (fun sample answer => S.place p2
        (((S.combinedLineMeasurement p2.side sample.1.1 sample.2.1).postprocess
          (fun polys => (evalOpt sample.1.1 sample.1.2 polys.1,
            evalOpt sample.2.1 sample.2.2 polys.2))).effect answer)) S.psiHat ≤
    nondegenerateLinePastingMass P.toLdParams *
      consistencyDefect (nondegenerateLinePastingDist P.toLdParams)
        (fun question answer => S.place p1
          (((points.Q p1.side question.2.2 question.1.2.2).postprocess
            (fun pair => (some pair.1, some pair.2))).effect answer))
        (fun question answer => S.place p2
          (((S.combinedLineMeasurement p2.side question.2.1 question.1.2.1).postprocess
            (fun polys => (evalOpt question.2.1 question.2.2 polys.1,
              evalOpt question.1.2.1 question.1.2.2 polys.2))).effect answer)) S.psiHat +
      1 / (2 * Fintype.card (ScalarQ P.toLdParams)) := by
  exact consistencyDefect_le_nondegenerateLinePastingDist_add_mass S p1 p2 hopp
    (fun sample => (points.Q p1.side sample.1.2 sample.2.2).postprocess
      (fun pair => (some pair.1, some pair.2)))
    (fun sample => (S.combinedLineMeasurement p2.side sample.1.1 sample.2.1).postprocess
      (fun polys => (evalOpt sample.1.1 sample.1.2 polys.1,
        evalOpt sample.2.1 sample.2.2 polys.2)))

/-! ## Unequal-dimensional bipartite transport -/

open DistanceCalculus in

end

end MIPStarRE.QPBT
