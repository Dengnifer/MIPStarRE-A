import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Questions

/-!
# Affine resampling of directly indexed lines

This module identifies the joint directly indexed line-point laws with the
equivalent sampling procedure that first draws their line marginal and then a
uniform affine parameter.  The argument retains zero diagonal directions: it
uses only translations of finite affine spaces and never cancels a direction.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:243-287`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1116`
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-- Translate the point coordinate of a direct sample along a direction that
depends only on its stored index and direction coordinates. -/
private def directLdSpacePointTranslateEquiv (D : DirectLdParams)
    (directionOf : Fin D.m → (Fin D.m → DirectScalarQ D) →
      (Fin D.m → DirectScalarQ D))
    (t : DirectScalarQ D) : DirectLdSpace D ≃ DirectLdSpace D where
  toFun sample :=
    ⟨sample.point + t • directionOf sample.index sample.direction,
      sample.index, sample.direction⟩
  invFun sample :=
    ⟨sample.point + (-t) • directionOf sample.index sample.direction,
      sample.index, sample.direction⟩
  left_inv sample := by
    cases sample with
    | mk point index direction =>
        simp [add_assoc]
  right_inv sample := by
    cases sample with
    | mk point index direction =>
        simp [add_assoc]

@[simp] private theorem directLdSpacePointTranslateEquiv_apply
    (D : DirectLdParams)
    (directionOf : Fin D.m → (Fin D.m → DirectScalarQ D) →
      (Fin D.m → DirectScalarQ D))
    (t : DirectScalarQ D) (sample : DirectLdSpace D) :
    directLdSpacePointTranslateEquiv D directionOf t sample =
      ⟨sample.point + t • directionOf sample.index sample.direction,
        sample.index, sample.direction⟩ := rfl

@[simp] private theorem directLdSpacePointTranslateEquiv_symm_apply
    (D : DirectLdParams)
    (directionOf : Fin D.m → (Fin D.m → DirectScalarQ D) →
      (Fin D.m → DirectScalarQ D))
    (t : DirectScalarQ D) (sample : DirectLdSpace D) :
    (directLdSpacePointTranslateEquiv D directionOf t).symm sample =
      ⟨sample.point + (-t) • directionOf sample.index sample.direction,
        sample.index, sample.direction⟩ := rfl

/-- Uniformly resampling a canonical affine line by a scalar parameter
recovers its original joint line-point sample. -/
private theorem avgOver_directLinePoint_resample
    (D : DirectLdParams)
    (directionOf : Fin D.m → (Fin D.m → DirectScalarQ D) →
      (Fin D.m → DirectScalarQ D))
    (lineOf : DirectLdSpace D → DirectLineDesc D)
    (hbase : ∀ sample,
      (lineOf sample).base =
        lineRepMap (directionOf sample.index sample.direction) sample.point)
    (hdirection : ∀ sample,
      (lineOf sample).direction = directionOf sample.index sample.direction)
    (hline : ∀ sample t,
      lineOf (directLdSpacePointTranslateEquiv D directionOf t sample) =
        lineOf sample)
    (F : (DirectLineDesc D × (Fin D.m → DirectScalarQ D)) → Error) :
    avgOver (uniformDistribution (DirectLdSpace D)) (fun sample =>
        avgOver (uniformDistribution (DirectScalarQ D)) (fun t =>
          F (lineOf sample,
            (lineOf sample).base + t • (lineOf sample).direction))) =
      avgOver (uniformDistribution (DirectLdSpace D)) (fun sample =>
        F (lineOf sample, sample.point)) := by
  have hparameter : ∀ sample,
      avgOver (uniformDistribution (DirectScalarQ D)) (fun t =>
          F (lineOf sample,
            (lineOf sample).base + t • (lineOf sample).direction)) =
        avgOver (uniformDistribution (DirectScalarQ D)) (fun t =>
          F (lineOf sample,
            sample.point +
              t • directionOf sample.index sample.direction)) := by
    intro sample
    let direction := directionOf sample.index sample.direction
    let r := directLineRepParameter direction sample.point
    calc
      avgOver (uniformDistribution (DirectScalarQ D)) (fun t =>
          F (lineOf sample,
            (lineOf sample).base + t • (lineOf sample).direction)) =
          avgOver (uniformDistribution (DirectScalarQ D)) (fun t =>
            F (lineOf sample,
              (lineOf sample).base +
                ((Equiv.addRight (-r)).symm t) •
                  (lineOf sample).direction)) :=
        avgOver_uniform_equiv (Equiv.addRight (-r)) _
      _ = avgOver (uniformDistribution (DirectScalarQ D)) (fun t =>
          F (lineOf sample,
            sample.point +
              t • directionOf sample.index sample.direction)) := by
        apply avgOver_congr
        intro t
        congr 2
        rw [hdirection, hbase]
        have hadd : (Equiv.addRight (-r)).symm t = t + r := by
          simp
        rw [hadd]
        change lineRepMap direction sample.point + (t + r) • direction =
          sample.point + t • direction
        rw [add_comm t r, add_smul, ← add_assoc,
          ← directLineRepParameter_spec direction sample.point]
  have hsample : ∀ t : DirectScalarQ D,
      avgOver (uniformDistribution (DirectLdSpace D)) (fun sample =>
          F (lineOf sample,
            sample.point +
              t • directionOf sample.index sample.direction)) =
        avgOver (uniformDistribution (DirectLdSpace D)) (fun sample =>
          F (lineOf sample, sample.point)) := by
    intro t
    calc
      avgOver (uniformDistribution (DirectLdSpace D)) (fun sample =>
          F (lineOf sample,
            sample.point +
              t • directionOf sample.index sample.direction)) =
          avgOver (uniformDistribution (DirectLdSpace D)) (fun sample =>
            F (lineOf ((directLdSpacePointTranslateEquiv D directionOf t).symm sample),
              ((directLdSpacePointTranslateEquiv D directionOf t).symm sample).point +
                t • directionOf
                  ((directLdSpacePointTranslateEquiv D directionOf t).symm sample).index
                  ((directLdSpacePointTranslateEquiv D directionOf t).symm sample).direction)) :=
        avgOver_uniform_equiv (directLdSpacePointTranslateEquiv D directionOf t) _
      _ = avgOver (uniformDistribution (DirectLdSpace D)) (fun sample =>
          F (lineOf sample, sample.point)) := by
        apply avgOver_congr
        intro sample
        congr 2
        · change lineOf (directLdSpacePointTranslateEquiv D directionOf (-t) sample) =
            lineOf sample
          exact hline sample (-t)
        · rw [directLdSpacePointTranslateEquiv_symm_apply]
          simp [add_assoc]
  calc
    avgOver (uniformDistribution (DirectLdSpace D)) (fun sample =>
        avgOver (uniformDistribution (DirectScalarQ D)) (fun t =>
          F (lineOf sample,
            (lineOf sample).base + t • (lineOf sample).direction))) =
        avgOver (uniformDistribution (DirectLdSpace D)) (fun sample =>
          avgOver (uniformDistribution (DirectScalarQ D)) (fun t =>
            F (lineOf sample,
              sample.point +
                t • directionOf sample.index sample.direction))) := by
      apply avgOver_congr
      exact hparameter
    _ = avgOver (uniformDistribution (DirectScalarQ D)) (fun t =>
        avgOver (uniformDistribution (DirectLdSpace D)) (fun sample =>
          F (lineOf sample,
            sample.point +
              t • directionOf sample.index sample.direction))) :=
      avgOver_uniform_comm _
    _ = avgOver (uniformDistribution (DirectScalarQ D)) (fun _ =>
        avgOver (uniformDistribution (DirectLdSpace D)) (fun sample =>
          F (lineOf sample, sample.point))) := by
      apply avgOver_congr
      exact hsample
    _ = avgOver (uniformDistribution (DirectLdSpace D)) (fun sample =>
        F (lineOf sample, sample.point)) := avgOver_uniform_const _

/-- Sampling an axis line with its marginal and then a uniform affine
parameter reproduces the original joint axis-line/point distribution. -/
theorem avgOver_directALinePointDist_resample
    (D : DirectLdParams)
    (F : (DirectLineDesc D × (Fin D.m → DirectScalarQ D)) → Error) :
    avgOver ((directALinePointDist D).map Prod.fst) (fun line =>
        avgOver (uniformDistribution (DirectScalarQ D)) (fun t =>
          F (line, line.base + t • line.direction))) =
      avgOver (directALinePointDist D) F := by
  simp only [directALinePointDist, Distribution.avgOver_map]
  apply avgOver_directLinePoint_resample D
      (fun (index : Fin D.m) (_ : Fin D.m → DirectScalarQ D) =>
        coordinateDirection index)
      (directALineDescOf D)
  · intro sample
    rfl
  · intro sample
    rfl
  · intro sample t
    rw [directLdSpacePointTranslateEquiv_apply]
    simp only [directALineDescOf]
    simp [lineRepMap_add_smul]

/-- Sampling a prefix-diagonal line with its marginal and then a uniform
affine parameter reproduces the original joint diagonal-line/point
distribution, including samples with zero direction. -/
theorem avgOver_directDLinePointDist_resample
    (D : DirectLdParams)
    (F : (DirectLineDesc D × (Fin D.m → DirectScalarQ D)) → Error) :
    avgOver ((directDLinePointDist D).map Prod.fst) (fun line =>
        avgOver (uniformDistribution (DirectScalarQ D)) (fun t =>
          F (line, line.base + t • line.direction))) =
      avgOver (directDLinePointDist D) F := by
  simp only [directDLinePointDist, Distribution.avgOver_map]
  apply avgOver_directLinePoint_resample D
      (fun (index : Fin D.m) (direction : Fin D.m → DirectScalarQ D) =>
        directPrefixProjection index direction)
      (directDLineDescOf D)
  · intro sample
    rfl
  · intro sample
    rfl
  · intro sample t
    rw [directLdSpacePointTranslateEquiv_apply]
    simp only [directDLineDescOf]
    simp [lineRepMap_add_smul]

end

end MIPStarRE.QPBT
