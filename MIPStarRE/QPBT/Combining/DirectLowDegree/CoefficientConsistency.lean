import MIPStarRE.QPBT.Combining.DirectLowDegree.CoefficientCollision
import MIPStarRE.QPBT.Games.Sandwich.Support

/-!
# Consistency of direct coefficient measurements

This module lifts consistency of uniformly evaluated coefficient-vector POVMs
to consistency of their full coefficient outcomes.  The loss is the direct
univariate collision bound `degree / q`.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:331-344`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1595-1603`
- Blueprint `lem:sandwich-codeword-defect`
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-- The consistency defect of two coefficient-vector POVM families is at most
their consistency defect after evaluation at an independent uniform parameter,
plus `degree / q`.

This is a formalization-only specialization of
`SandwichProduct.consistencyDefect_codewords_le_evaluated_add`.  It applies to
arbitrary POVMs and retains all degrees, including `degree ≥ q`. -/
theorem consistencyDefect_directCoefficients_le_evaluated_add
    {X ιA ιB : Type*}
    [Fintype X] [DecidableEq X]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (D : DirectLdParams) (degree : ℕ) (μ : Distribution X)
    (A : X → Measurement (DirectDegPoly D degree) ιA)
    (B : X → Measurement (DirectDegPoly D degree) ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB))
    (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1) :
    consistencyDefect μ
        (fun x coefficients => heteroKron ((A x).effect coefficients) 1)
        (fun x coefficients => heteroKron 1 ((B x).effect coefficients)) ψ ≤
      consistencyDefect
        (Distribution.prod μ (uniformDistribution (DirectScalarQ D)))
        (fun xt value => heteroKron
          (((A xt.1).postprocess
            (fun coefficients => evalCoefficient coefficients xt.2)).effect value) 1)
        (fun xt value => heteroKron 1
          (((B xt.1).postprocess
            (fun coefficients => evalCoefficient coefficients xt.2)).effect value)) ψ +
        (degree : ℝ) / (D.q : ℝ) := by
  apply SandwichProduct.consistencyDefect_codewords_le_evaluated_add
      μ A B ψ (fun coefficients t => evalCoefficient coefficients t)
      ((degree : ℝ) / (D.q : ℝ)) hμ hψ
  · positivity
  · intro a b hne
    exact directCoefficientCollision_avg_le D degree a b hne

end

end MIPStarRE.QPBT
