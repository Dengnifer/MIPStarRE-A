import MIPStarRE.QPBT.Combining.DirectLowDegree.CoefficientConsistency
import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.LineResampling

/-!
# Resampled consistency of direct coefficient measurements

This module reexpresses the consistency defect of uniformly evaluated direct
coefficient measurements over the original joint line-point distributions.
For a zero direction, the sampled point does not determine the affine
parameter, so the joint integrand retains the full uniform parameter average.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:243-344`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1116`
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum
open DistanceCalculus

noncomputable section

/-- The pointwise consistency defect of two direct coefficient measurements
after evaluating both coefficient vectors at the parameter `t`. -/
noncomputable def directCoefficientEvaluationDefect
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (D : DirectLdParams) (degree : ℕ)
    (A : DirectLineDesc D → Measurement (DirectDegPoly D degree) ιA)
    (B : DirectLineDesc D → Measurement (DirectDegPoly D degree) ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB))
    (line : DirectLineDesc D) (t : DirectScalarQ D) : Error :=
  ∑ a : DirectScalarQ D, ∑ b : DirectScalarQ D, if a = b then 0 else
    stateQForm ψ
      (heteroKron
        (((A line).postprocess
          (fun coefficients => evalCoefficient coefficients t)).effect a)
        (((B line).postprocess
          (fun coefficients => evalCoefficient coefficients t)).effect b))

/-- The evaluated coefficient defect as a function of a joint direct
line-point sample. For a zero direction the point is independent of the
uniform affine parameter, so this definition retains that entire average
rather than selecting a distinguished parameter. -/
noncomputable def directJointCoefficientEvaluationDefect
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (D : DirectLdParams) (degree : ℕ)
    (A : DirectLineDesc D → Measurement (DirectDegPoly D degree) ιA)
    (B : DirectLineDesc D → Measurement (DirectDegPoly D degree) ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB))
    (sample : DirectLineDesc D × (Fin D.m → DirectScalarQ D)) : Error :=
  if sample.1.direction = 0 then
    avgOver (uniformDistribution (DirectScalarQ D))
      (fun t => directCoefficientEvaluationDefect D degree A B ψ sample.1 t)
  else
    directCoefficientEvaluationDefect D degree A B ψ sample.1
      (directLineRepParameter sample.1.direction sample.2)

private theorem directLineRepParameter_base_add_smul
    (D : DirectLdParams) (line : DirectLineDesc D)
    (hdir : line.direction ≠ 0) (t : DirectScalarQ D) :
    directLineRepParameter line.direction
        (line.base + t • line.direction) = t := by
  apply directLineRepParameter_eq_of_nonzero hdir
  rw [lineRepMap_add_smul, line.base_fixed]

private theorem avgOver_directJointCoefficientEvaluationDefect_affine
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (D : DirectLdParams) (degree : ℕ)
    (A : DirectLineDesc D → Measurement (DirectDegPoly D degree) ιA)
    (B : DirectLineDesc D → Measurement (DirectDegPoly D degree) ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (line : DirectLineDesc D) :
    avgOver (uniformDistribution (DirectScalarQ D))
        (fun t => directCoefficientEvaluationDefect D degree A B ψ line t) =
      avgOver (uniformDistribution (DirectScalarQ D)) (fun t =>
        directJointCoefficientEvaluationDefect D degree A B ψ
          (line, line.base + t • line.direction)) := by
  by_cases hdir : line.direction = 0
  · simp [directJointCoefficientEvaluationDefect, hdir, avgOver_uniform_const]
  · apply avgOver_congr
    intro t
    simp [directJointCoefficientEvaluationDefect, hdir,
      directLineRepParameter_base_add_smul D line hdir t]

/-- Uniform parameter evaluation over the axis-line marginal is exactly the
joint axis-line/point expectation of the corresponding coefficient defect. -/
theorem avgOver_directALinePointDist_coefficientEvaluation
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (D : DirectLdParams) (degree : ℕ)
    (A : DirectLineDesc D → Measurement (DirectDegPoly D degree) ιA)
    (B : DirectLineDesc D → Measurement (DirectDegPoly D degree) ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    avgOver ((directALinePointDist D).map Prod.fst) (fun line =>
        avgOver (uniformDistribution (DirectScalarQ D))
          (fun t => directCoefficientEvaluationDefect D degree A B ψ line t)) =
      avgOver (directALinePointDist D)
        (directJointCoefficientEvaluationDefect D degree A B ψ) := by
  calc
    _ = avgOver ((directALinePointDist D).map Prod.fst) (fun line =>
        avgOver (uniformDistribution (DirectScalarQ D)) (fun t =>
          directJointCoefficientEvaluationDefect D degree A B ψ
            (line, line.base + t • line.direction))) := by
      apply avgOver_congr
      exact avgOver_directJointCoefficientEvaluationDefect_affine D degree A B ψ
    _ = _ := avgOver_directALinePointDist_resample D
      (directJointCoefficientEvaluationDefect D degree A B ψ)

/-- Uniform parameter evaluation over the diagonal-line marginal is exactly
the joint diagonal-line/point expectation of the corresponding coefficient
defect, including zero-direction samples. -/
theorem avgOver_directDLinePointDist_coefficientEvaluation
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (D : DirectLdParams) (degree : ℕ)
    (A : DirectLineDesc D → Measurement (DirectDegPoly D degree) ιA)
    (B : DirectLineDesc D → Measurement (DirectDegPoly D degree) ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    avgOver ((directDLinePointDist D).map Prod.fst) (fun line =>
        avgOver (uniformDistribution (DirectScalarQ D))
          (fun t => directCoefficientEvaluationDefect D degree A B ψ line t)) =
      avgOver (directDLinePointDist D)
        (directJointCoefficientEvaluationDefect D degree A B ψ) := by
  calc
    _ = avgOver ((directDLinePointDist D).map Prod.fst) (fun line =>
        avgOver (uniformDistribution (DirectScalarQ D)) (fun t =>
          directJointCoefficientEvaluationDefect D degree A B ψ
            (line, line.base + t • line.direction))) := by
      apply avgOver_congr
      exact avgOver_directJointCoefficientEvaluationDefect_affine D degree A B ψ
    _ = _ := avgOver_directDLinePointDist_resample D
      (directJointCoefficientEvaluationDefect D degree A B ψ)

/-- The product-law consistency defect of evaluated direct coefficient POVMs
over axis lines is the corresponding original joint line-point expectation. -/
theorem consistencyDefect_directALine_coefficients_evaluated_eq_joint
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (D : DirectLdParams) (degree : ℕ)
    (A : DirectLineDesc D → Measurement (DirectDegPoly D degree) ιA)
    (B : DirectLineDesc D → Measurement (DirectDegPoly D degree) ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    consistencyDefect
        (Distribution.prod ((directALinePointDist D).map Prod.fst)
          (uniformDistribution (DirectScalarQ D)))
        (fun lt value => heteroKron
          (((A lt.1).postprocess
            (fun coefficients => evalCoefficient coefficients lt.2)).effect value) 1)
        (fun lt value => heteroKron 1
          (((B lt.1).postprocess
            (fun coefficients => evalCoefficient coefficients lt.2)).effect value)) ψ =
      avgOver (directALinePointDist D)
        (directJointCoefficientEvaluationDefect D degree A B ψ) := by
  rw [SandwichProduct.consistencyDefect_placed_eq_avg_point,
    SandwichProduct.avgOver_distribution_prod]
  exact avgOver_directALinePointDist_coefficientEvaluation D degree A B ψ

/-- The product-law consistency defect of evaluated direct coefficient POVMs
over diagonal lines is the corresponding original joint line-point
expectation, including zero-direction samples. -/
theorem consistencyDefect_directDLine_coefficients_evaluated_eq_joint
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (D : DirectLdParams) (degree : ℕ)
    (A : DirectLineDesc D → Measurement (DirectDegPoly D degree) ιA)
    (B : DirectLineDesc D → Measurement (DirectDegPoly D degree) ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    consistencyDefect
        (Distribution.prod ((directDLinePointDist D).map Prod.fst)
          (uniformDistribution (DirectScalarQ D)))
        (fun lt value => heteroKron
          (((A lt.1).postprocess
            (fun coefficients => evalCoefficient coefficients lt.2)).effect value) 1)
        (fun lt value => heteroKron 1
          (((B lt.1).postprocess
            (fun coefficients => evalCoefficient coefficients lt.2)).effect value)) ψ =
      avgOver (directDLinePointDist D)
        (directJointCoefficientEvaluationDefect D degree A B ψ) := by
  rw [SandwichProduct.consistencyDefect_placed_eq_avg_point,
    SandwichProduct.avgOver_distribution_prod]
  exact avgOver_directDLinePointDist_coefficientEvaluation D degree A B ψ

/-- Coefficient consistency over the axis-line marginal is bounded by its
original joint line-point evaluation defect plus `degree / q`. -/
theorem consistencyDefect_directALine_coefficients_le_joint_add
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (D : DirectLdParams) (degree : ℕ)
    (A : DirectLineDesc D → Measurement (DirectDegPoly D degree) ιA)
    (B : DirectLineDesc D → Measurement (DirectDegPoly D degree) ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (hψ : ‖ψ‖ = 1) :
    consistencyDefect ((directALinePointDist D).map Prod.fst)
        (fun line coefficients => heteroKron ((A line).effect coefficients) 1)
        (fun line coefficients => heteroKron 1 ((B line).effect coefficients)) ψ ≤
      avgOver (directALinePointDist D)
          (directJointCoefficientEvaluationDefect D degree A B ψ) +
        (degree : ℝ) / (D.q : ℝ) := by
  have h := consistencyDefect_directCoefficients_le_evaluated_add
    D degree ((directALinePointDist D).map Prod.fst) A B ψ
    ((directALinePointDist_isProbability D).map Prod.fst) hψ
  rw [consistencyDefect_directALine_coefficients_evaluated_eq_joint
    D degree A B ψ] at h
  exact h

/-- Coefficient consistency over the diagonal-line marginal is bounded by its
original joint line-point evaluation defect plus `degree / q`, with no
nonzero-direction restriction. -/
theorem consistencyDefect_directDLine_coefficients_le_joint_add
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (D : DirectLdParams) (degree : ℕ)
    (A : DirectLineDesc D → Measurement (DirectDegPoly D degree) ιA)
    (B : DirectLineDesc D → Measurement (DirectDegPoly D degree) ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (hψ : ‖ψ‖ = 1) :
    consistencyDefect ((directDLinePointDist D).map Prod.fst)
        (fun line coefficients => heteroKron ((A line).effect coefficients) 1)
        (fun line coefficients => heteroKron 1 ((B line).effect coefficients)) ψ ≤
      avgOver (directDLinePointDist D)
          (directJointCoefficientEvaluationDefect D degree A B ψ) +
        (degree : ℝ) / (D.q : ℝ) := by
  have h := consistencyDefect_directCoefficients_le_evaluated_add
    D degree ((directDLinePointDist D).map Prod.fst) A B ψ
    ((directDLinePointDist_isProbability D).map Prod.fst) hψ
  rw [consistencyDefect_directDLine_coefficients_evaluated_eq_joint
    D degree A B ψ] at h
  exact h

end

end MIPStarRE.QPBT
