import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Simultaneous
import MIPStarRE.QPBT.Games.Sandwich.Support

/-!
# Polynomial consistency from point comparisons

Two polynomial POVMs consistent with opposite point measurements are consistent
with each other. The proof compares their evaluations through the point
measurements, then uses Schwartz--Zippel to recover the polynomial labels.
Projectivity is not required, so the estimate applies after ground compression.

## References

* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1278-1288`,
  the polynomial self-consistency needed before the ordered correlations in
  `lem:qld-4-7`.
* `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` and issue #513.
* `audits/2026-09-12_issue-513_composition-compatibility.md`, obligation 2.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

/-- Distinct tuples disagree in one component. Schwartz--Zippel for that
component bounds collision of the whole tuple, without a factor depending on
the number of components. This uses polynomial representatives, not functions
identified by their evaluations. -/
theorem direct_poly_tuple_collision_le (D : DirectLdParams)
    (g h : DirectPolyTuple D) (hne : g ≠ h) :
    avgOver (uniformDistribution (Fin D.m → DirectScalarQ D))
      (fun u => if evalDirectPolyTupleAt u g = evalDirectPolyTupleAt u h
        then (1 : ℝ) else 0) ≤ (D.m * D.d : ℝ) / D.q := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, g j ≠ h j := Function.ne_iff.mp hne
  refine (avgOver_mono _ _ _ fun u => ?_).trans
    (directPolynomialAgreement_avg_le_mdq D (g j) (h j) hj)
  by_cases heq : evalDirectPolyTupleAt u g = evalDirectPolyTupleAt u h
  · have hj := congrFun heq j
    simp only [evalDirectPolyTupleAt] at hj
    simp [heq, hj]
  · simp only [heq, if_false]
    split_ifs <;> norm_num

/-- Cross-player polynomial consistency follows from the two soundness
point comparisons and point self-consistency. The asymmetric bound retains
both point-comparison errors. It holds for complete POVMs on heterogeneous
spaces and requires neither projectivity nor an assumed polynomial defect.

This is an operator estimate for the first paragraph of `lem:qld-4-7`,
paper lines 1278--1288; it is not a construction of its global pair witness.
The distinction between this operator estimate and the source's global-pair
construction is recorded in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`. -/
theorem direct_polynomial_consistency_le_point_bounds
    (D : DirectLdParams) {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : DirectPolyMeasTuple D I) (B : DirectPolyMeasTuple D J)
    (QA : (Fin D.m → DirectScalarQ D) → Measurement (Fin D.k → DirectScalarQ D) I)
    (QB : (Fin D.m → DirectScalarQ D) → Measurement (Fin D.k → DirectScalarQ D) J)
    (ψ : EuclideanSpace ℂ (I × J)) (hψ : ‖ψ‖ = 1) (ηA ηB δQ : ℝ)
    (hA : consistencyDefect (uniformDistribution (Fin D.m → DirectScalarQ D))
      (fun u a => heteroKron ((A.postprocess (evalDirectPolyTupleAt u)).effect a) 1)
      (fun u a => heteroKron 1 ((QB u).effect a)) ψ ≤ ηA)
    (hB : consistencyDefect (uniformDistribution (Fin D.m → DirectScalarQ D))
      (fun u a => heteroKron ((QA u).effect a) 1)
      (fun u a => heteroKron 1 ((B.postprocess (evalDirectPolyTupleAt u)).effect a)) ψ ≤ ηB)
    (hQ : consistencyDefect (uniformDistribution (Fin D.m → DirectScalarQ D))
      (fun u a => heteroKron ((QA u).effect a) 1)
      (fun u a => heteroKron 1 ((QB u).effect a)) ψ ≤ δQ) :
    consistencyDefect (uniformDistribution Unit)
      (fun _ g => heteroKron (A.effect g) 1)
      (fun _ g => heteroKron 1 (B.effect g)) ψ ≤
        ηA + 2 * Real.sqrt (δQ + ηB) + (D.m * D.d : ℝ) / D.q := by
  have heval := consistencyDefect_trans_le
    (uniformDistribution (Fin D.m → DirectScalarQ D))
    (fun u => leftPlacedMeasurement (A.postprocess (evalDirectPolyTupleAt u)))
    (fun u => rightPlacedMeasurement (QB u))
    (fun u => leftPlacedMeasurement (QA u))
    (fun u => rightPlacedMeasurement (B.postprocess (evalDirectPolyTupleAt u)))
    ψ ηA δQ ηB (uniformDistribution_isProbability _) hψ hA hQ hB
  have hcollision := SandwichProduct.point_codeword_defect_le_avg_evaluated_add
    A B ψ (fun g u => evalDirectPolyTupleAt u g) ((D.m * D.d : ℝ) / D.q)
    hψ (by positivity) (direct_poly_tuple_collision_le D)
  simp only [leftPlacedMeasurement, rightPlacedMeasurement, Measurement.ofSumEqOne,
    consistencyDefect, consistency_term_eq_stateQForm,
    placed_product_stateQForm_eq] at heval ⊢
  rw [avgOver_uniform_const]
  exact hcollision.trans (add_le_add heval le_rfl)

end

end MIPStarRE.QPBT
