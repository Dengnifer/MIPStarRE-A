import MIPStarRE.QPBT.Combining.Lines.DiagonalResampling
import MIPStarRE.QPBT.Combining.Lines.SubLineMixture
import MIPStarRE.QPBT.Combining.Points
import MIPStarRE.QPBT.Combining.Lines.PointwiseDefect
import MIPStarRE.QPBT.Games.RestrictedAverage

/-!
# Sampling for conditioned line pasting

The sampling identities retain the zero-direction mass when restoring the
original line-point law.

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

/-- On a nonzero direction, completed evaluation agrees with polynomial evaluation at
the unique affine parameter. This proof-only restriction is used in the collision
step of `lem:qld-xz-lines`, paper `14_analysis_of_the_pauli_basis_test.tex:950-955`. -/
theorem evalOpt_affine_parameter_of_direction_ne_zero {L : LdParams} {bound : ℕ} (line : LineDesc L)
    (hdir : line.direction ≠ 0) (poly : DegPoly L bound) (param : ScalarQ L) :
    evalOpt line (line.base + param • line.direction) poly =
      some (evalCoefficient poly param) := by
  apply (evalOpt_eq_some_iff _ _ _ _).mpr
  refine ⟨⟨param, rfl⟩, ?_⟩
  intro other heq
  have hsmul : param • line.direction = other • line.direction := add_left_cancel heq
  have hsub : (param - other) • line.direction = 0 := by
    rw [sub_smul, hsmul, sub_self]
  have hparam : param = other := sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_right hdir)
  rw [hparam]

/-- On a nondegenerate line, completed evaluations of distinct degree-bounded
polynomials collide with probability at most the degree bound divided by the field
size under a uniform affine parameter. This is a proof-only restriction of the
collision step at paper `14_analysis_of_the_pauli_basis_test.tex:950-955`. -/
theorem evalOpt_uniform_parameter_collision_le {L : LdParams} {bound : ℕ} (line : LineDesc L)
    (hdir : line.direction ≠ 0) (first second : DegPoly L bound)
    (hne : first ≠ second) :
    avgOver (uniformDistribution (ScalarQ L)) (fun param =>
      if evalOpt line (line.base + param • line.direction) first =
        evalOpt line (line.base + param • line.direction) second then 1 else 0) ≤
      (bound : ℝ) / Fintype.card (ScalarQ L) := by
  classical
  simp_rw [evalOpt_affine_parameter_of_direction_ne_zero line hdir, Option.some.injEq]
  have hcard := evalCoefficient_collision_card_le first second hne
  unfold avgOver
  simp only [uniformDistribution_support, uniformDistribution_weight_apply,
    mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) (by positivity)

/-- Multiplying a normalized restricted average by its retained mass gives the
unnormalized restricted sum. This formalization-only identity supports proof-only
conditioning in `lem:qld-xz-lines`, paper
`14_analysis_of_the_pauli_basis_test.tex:950-963`; it changes no game distribution. -/
theorem avgOver_restrict_mul_mass {Sample : Type*} [DecidableEq Sample]
    (dist : Distribution Sample) (good : Sample → Prop) [DecidablePred good]
    (hpos : 0 < ∑ sample ∈ dist.support.filter good, dist.weight sample)
    (value : Sample → ℝ) :
    (∑ sample ∈ dist.support.filter good, dist.weight sample) *
      avgOver (Distribution.restrict dist good hpos) value =
      ∑ sample ∈ dist.support.filter good, dist.weight sample * value sample := by
  unfold avgOver Distribution.restrict
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro sample hsample
  simp only [if_pos (Finset.mem_filter.mp hsample).2]
  field_simp

/-- An average of a function bounded above by one is at most the retained mass
times its conditional average, plus the discarded probability mass. This
formalization-only estimate restores the original distribution after proof-only
conditioning in `lem:qld-xz-lines`, paper
`14_analysis_of_the_pauli_basis_test.tex:950-963`. No discarded mass is omitted. -/
theorem avgOver_le_restrict_add_discarded_mass {Sample : Type*} [DecidableEq Sample]
    (dist : Distribution Sample) (good : Sample → Prop) [DecidablePred good]
    (hpos : 0 < ∑ sample ∈ dist.support.filter good, dist.weight sample)
    (defect : Sample → ℝ) (hunit : ∀ sample, defect sample ≤ 1) :
    avgOver dist defect ≤
      (∑ sample ∈ dist.support.filter good, dist.weight sample) *
        avgOver (Distribution.restrict dist good hpos) defect +
      ∑ sample ∈ dist.support.filter (fun sample => ¬ good sample), dist.weight sample := by
  classical
  rw [avgOver_restrict_mul_mass]
  unfold avgOver
  rw [← Finset.sum_filter_add_sum_filter_not dist.support good
    (fun sample => dist.weight sample * defect sample)]
  exact add_le_add_right (Finset.sum_le_sum fun sample _ =>
    mul_le_of_le_one_right (dist.nonnegative sample) (hunit sample)) _

/-- Under the unchanged diagonal line-point law, zero projected directions have
probability at most the inverse field size: the last raw direction coordinate must
vanish and is uniform. Source: `def:line-point-dist`, paper
`08_classical_and_quantum_low_degree_tests.tex:274-287`. This proof-only bound
supports the collision restriction in issue #118. -/
theorem dLinePointDist_zero_direction_mass_le (L : LdParams) :
    avgOver (dLinePointDist L) (fun sample =>
      if sample.1.direction = 0 then 1 else 0) ≤
      1 / Fintype.card (ScalarQ L) := by
  classical
  let last : Fin L.m := ⟨L.m - 1, by have := L.hm; omega⟩
  let coord : LdIndex L := .inr last
  have hmap : (uniformDistribution (LdSpace L)).map (fun raw => raw coord) =
      uniformDistribution (ScalarQ L) := by
    change (uniformDistribution (LdSpace L)).map
      (fun raw => (Equiv.funSplitAt coord (ScalarQ L) raw).1) = _
    rw [← Distribution.map_map, uniformDistribution_map_equiv,
      uniformDistribution_map_fst]
  have hzero : avgOver (uniformDistribution (LdSpace L))
      (fun raw => if raw coord = 0 then (1 : ℝ) else 0) =
      1 / Fintype.card (ScalarQ L) := by
    rw [← Distribution.avgOver_map (uniformDistribution (LdSpace L))
      (fun raw => raw coord) (fun value => if value = 0 then (1 : ℝ) else 0), hmap]
    simp [avgOver, uniformDistribution_weight_apply, mul_ite]
  unfold dLinePointDist clDistribution
  rw [Distribution.avgOver_map, Distribution.avgOver_map]
  refine le_trans (avgOver_mono _ _ _ ?_) hzero.le
  intro raw
  dsimp only
  rw [dLineDescOf_ldDLineCL]
  split_ifs with hdir hcoord hcoord
  · exact le_rfl
  · exfalso
    apply hcoord
    have hlast := congrFun hdir last
    change prefixProjection (chiIndex L (LdSpace.seed raw))
      (LdSpace.direction raw) last = 0 at hlast
    have hindex : ¬ last.val < (chiIndex L (LdSpace.seed raw)).val := by
      have := (chiIndex L (LdSpace.seed raw)).isLt
      dsimp [last]
      omega
    simpa [prefixProjection, hindex, LdSpace.direction, coord] using hlast
  · norm_num
  · exact le_rfl

/-- Axis-line sampling gives zero mass to zero directions, since a coordinate
direction is nonzero. This is a formalization-only consequence of
`def:line-point-dist`, paper `08_classical_and_quantum_low_degree_tests.tex:274-287`. -/
theorem aLinePointDist_zero_direction_mass (L : LdParams) :
    avgOver (aLinePointDist L) (fun sample =>
      if sample.1.direction = 0 then 1 else 0) = 0 := by
  classical
  unfold aLinePointDist
  rw [Distribution.avgOver_map]
  have hdir (raw : LdSpace L) : (aLineDescOf L raw).direction ≠ 0 := by
    intro hzero
    have hcoord := congrFun hzero (chiIndex L raw.seed)
    simp [aLineDescOf, LineDesc.direction, coordinateDirection] at hcoord
  simp [avgOver, hdir]

/-- The equal mixture of axis and diagonal line-point laws gives zero directions
mass at most `1 / (2q)`. This proof-only estimate preserves the source sampler of
`def:line-point-dist`, paper `08_classical_and_quantum_low_degree_tests.tex:274-287`,
including its degenerate fibers. -/
theorem linePointDist_zero_direction_mass_le (L : LdParams) :
    avgOver (linePointDist L) (fun sample =>
      if sample.1.direction = 0 then 1 else 0) ≤
      1 / (2 * Fintype.card (ScalarQ L)) := by
  rw [linePointDist, avgOver_mix, aLinePointDist_zero_direction_mass]
  have hdiag := dLinePointDist_zero_direction_mass_le L
  calc
    _ = (1 / 2 : ℝ) * avgOver (dLinePointDist L)
        (fun sample => if sample.1.direction = 0 then 1 else 0) := by ring
    _ ≤ (1 / 2 : ℝ) * (1 / Fintype.card (ScalarQ L)) :=
      mul_le_mul_of_nonneg_left hdiag (by norm_num)
    _ = _ := by rw [one_div_mul_one_div]

/-- A uniform point may be replaced by a uniform affine parameter on its
canonical line, while preserving the canonical representative jointly with the
point. This formalization-only identity, including zero directions, supports the
conditional sampling step at paper `14_analysis_of_the_pauli_basis_test.tex:955`. -/
theorem avgOver_lineRepMap_resample_parameter {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {dimension : ℕ} (direction : Fin dimension → K)
    (value : (Fin dimension → K) → (Fin dimension → K) → ℝ) :
    avgOver (uniformDistribution (Fin dimension → K))
      (fun point => value (lineRepMap direction point) point) =
    avgOver (uniformDistribution (Fin dimension → K)) (fun point =>
      avgOver (uniformDistribution K) (fun param =>
        value (lineRepMap direction point) (lineRepMap direction point + param • direction))) := by
  have hmap := uniformDistribution_map_lineRepMap_add_smul direction
  have havg := congrArg (fun dist => avgOver dist
    (fun point => value (lineRepMap direction point) point)) hmap
  rw [Distribution.avgOver_map, uniformDistribution_prod, avgOver_prod] at havg
  simpa only [lineRepMap_add_smul, lineRepMap_apply_self] using havg.symm

/-- Resampling a uniform parameter on the sampled axis line preserves the joint
line-point law. This formalization-only identity derives the conditional sampling
used at paper `14_analysis_of_the_pauli_basis_test.tex:955` from
`def:line-point-dist`, paper `08_classical_and_quantum_low_degree_tests.tex:274-287`. -/
theorem avgOver_aLinePointDist_resample_parameter (L : LdParams)
    (value : (LineDesc L × (Fin L.m → ScalarQ L)) → ℝ) :
    avgOver (aLinePointDist L) value =
    avgOver (aLinePointDist L) (fun sample => avgOver (uniformDistribution (ScalarQ L))
      (fun param => value (sample.1, sample.1.base + param • sample.1.direction))) := by
  classical
  unfold aLinePointDist clDistribution
  simp only [Distribution.avgOver_map, aLineDescOf_ldALineCL]
  have hblock := uniformDistribution_map_equiv (ldSpaceBlockEquiv L).symm
  rw [← hblock]
  simp only [Distribution.avgOver_map]
  rw [uniformDistribution_prod]
  simp only [avgOver_prod]
  rw [avgOver_comm, avgOver_comm (uniformDistribution (Fin L.m → ScalarQ L))]
  apply congrArg
  funext block
  have hresample := avgOver_lineRepMap_resample_parameter (coordinateDirection (chiIndex L block.1))
      (fun base point => value (LineDesc.axis
        (lineRepMap (coordinateDirection (chiIndex L block.1)) base) block.1
        (lineRepMap_apply_self _ _), point))
  simp only [lineRepMap_apply_self] at hresample
  exact hresample

/-- Uniform parameter resampling preserves the mixed line-point law exactly,
without excluding zero directions. This formalization-only identity justifies
conditioning on the line in the collision step of `lem:qld-xz-lines`, paper
`14_analysis_of_the_pauli_basis_test.tex:950-955`. -/
theorem avgOver_linePointDist_resample_parameter (L : LdParams)
    (value : (LineDesc L × (Fin L.m → ScalarQ L)) → ℝ) :
    avgOver (linePointDist L) value =
    avgOver (linePointDist L) (fun sample => avgOver (uniformDistribution (ScalarQ L))
      (fun param => value (sample.1, sample.1.base + param • sample.1.direction))) := by
  rw [linePointDist, avgOver_mix, avgOver_mix]
  rw [avgOver_aLinePointDist_resample_parameter L value,
    avgOver_dLinePointDist_resample_parameter L value]

/-- The collision bound remains valid with any nonnegative weight depending only
on the line, after restricting to nonzero directions. This proof-only estimate
is the conditional form of the root argument in `lem:qld-xz-lines`, paper
`14_analysis_of_the_pauli_basis_test.tex:950-955`; it is not the false
unrestricted collision claim on zero-direction coefficient presentations. -/
theorem linePointDist_nondegenerate_weighted_collision_le {L : LdParams} {bound : ℕ}
    (weight : LineDesc L → ℝ) (hweight : ∀ line, 0 ≤ weight line)
    (first second : DegPoly L bound) (hne : first ≠ second) :
    avgOver (linePointDist L) (fun sample =>
      if sample.1.direction ≠ 0 then weight sample.1 *
        (if evalOpt sample.1 sample.2 first = evalOpt sample.1 sample.2 second
          then 1 else 0) else 0) ≤
      (bound : ℝ) / Fintype.card (ScalarQ L) *
        avgOver (linePointDist L) (fun sample =>
          if sample.1.direction ≠ 0 then weight sample.1 else 0) := by
  classical
  rw [avgOver_linePointDist_resample_parameter]
  rw [← avgOver_const_mul]
  apply avgOver_mono
  intro sample
  by_cases hdir : sample.1.direction ≠ 0
  · simp only [if_pos hdir]
    rw [avgOver_const_mul]
    exact (mul_le_mul_of_nonneg_left
      (evalOpt_uniform_parameter_collision_le sample.1 hdir first second hne)
      (hweight sample.1)).trans_eq
      (mul_comm _ _)
  · simp [hdir, avgOver]

/-- Nondegenerate line fibers have total mass at least three quarters in the
unchanged line-point law. This follows from the zero-direction mass bound and
the fact that a field has at least two elements. This proof-only positivity bound
supports conditioning at paper `14_analysis_of_the_pauli_basis_test.tex:950-963`. -/
theorem linePointDist_nondegenerate_mass_ge (L : LdParams) :
    (3 / 4 : ℝ) ≤ ∑ sample ∈ (linePointDist L).support.filter
      (fun sample => sample.1.direction ≠ 0), (linePointDist L).weight sample := by
  classical
  have hsplit : (∑ sample ∈ (linePointDist L).support.filter
        (fun sample => sample.1.direction ≠ 0), (linePointDist L).weight sample) +
      avgOver (linePointDist L) (fun sample => if sample.1.direction = 0 then 1 else 0) = 1 := by
    simp only [avgOver, mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
    rw [add_comm, Finset.sum_filter_add_sum_filter_not]
    exact (linePointDist_isProbability L).weight_sum_eq_one
  have hmass := linePointDist_zero_direction_mass_le L
  have hcard : (2 : ℝ) ≤ Fintype.card (ScalarQ L) := by
    exact_mod_cast Fintype.one_lt_card (α := ScalarQ L)
  have hquarter : 1 / (2 * (Fintype.card (ScalarQ L) : ℝ)) ≤ 1 / 4 := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  linarith

/-- For two independent line-point samples, excluding only zero X directions
costs at most `1 / (2q)`. Only X requires the collision estimate when the
X-outer sandwich is instantiated with `G2 = X`. This is a proof-only bound for
paper `14_analysis_of_the_pauli_basis_test.tex:943-963`. -/
theorem prod_linePointDist_zero_X_direction_mass_le (L : LdParams) :
    avgOver (Distribution.prod (linePointDist L) (linePointDist L))
      (fun samples => if samples.1.1.direction = 0 then 1 else 0) ≤
      1 / (2 * Fintype.card (ScalarQ L)) := by
  rw [avgOver_prod]
  change avgOver (linePointDist L) (fun sample => avgOver (linePointDist L)
    (fun _ => if sample.1.direction = 0 then 1 else 0)) ≤ _
  simp_rw [avgOver_const_of_isProbability _ (linePointDist_isProbability L)]
  exact linePointDist_zero_direction_mass_le L


end

end MIPStarRE.QPBT
