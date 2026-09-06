import MIPStarRE.LDT.Basic.DistributionAvg
import MIPStarRE.QPBT.Algebra.Decoding

/-!
# Real polynomial collision bounds

The existing Schwartz–Zippel estimate for bounded polynomial representatives
is expressed as a nonnegative rational cardinality ratio. This module converts
it to the real uniform average used by the sandwich support comparison and
specializes it to the polynomial outcomes of the Pauli basis test.

## References

* `references/qpbt-paper/04_preliminaries.tex`, `lem:schwartz-zippel`.
* Blueprint `lem:schwartz-zippel-individual` and the collision calculation
  preceding `eq:qld-nonencoding-mass` in `sec:separating`.
* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1483-1492`,
  the consistency calculation in `lem:qld-construct-the-paulis` whose decoder
  substitution requires the blueprint's nonencoding-mass estimate.
* `docs/paper-gaps/qpbt_decoding-identity.tex`, for that substitution's scope.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.LDT.Preliminaries

/-- Two distinct individual-degree-`d` polynomial representatives agree on at
most an `m * d / |K|` fraction of field points, expressed as a real uniform
average. This is the scalar collision estimate used before blueprint
`eq:qld-nonencoding-mass`, not the nonencoding-mass estimate itself.

The field is finite and hence nonempty. No positive dimension, positive degree,
or degree bound relative to the field size is required; representatives are
not identified merely because their evaluations agree. -/
theorem polyFunc_eval_collision_le {m d : ℕ} {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] (first second : polyFunc m K d) (hne : first ≠ second) :
    avgOver (uniformDistribution (Fin m → K))
      (fun point => if MvPolynomial.eval point first.1 = MvPolynomial.eval point second.1
        then (1 : ℝ) else 0) ≤ (m * d : ℝ) / Fintype.card K := by
  have havg :
      avgOver (uniformDistribution (Fin m → K))
        (fun point => if MvPolynomial.eval point first.1 = MvPolynomial.eval point second.1
          then (1 : ℝ) else 0) =
        (polynomialAgreementProbability m K first.1 second.1 : ℝ) := by
    rw [avgOver_uniform_eq_inv_card_mul_sum, ← Finset.sum_filter]
    simp [polynomialAgreementProbability, div_eq_mul_inv, mul_comm]
  rw [havg]
  have hbound := schwartzZippel_individualDegree first second hne
  have hreal : (polynomialAgreementProbability m K first.1 second.1 : ℝ) ≤
      ((((m * d : ℕ) : ℚ≥0) / Fintype.card K) : ℝ) := by
    exact_mod_cast hbound
  simpa using hreal

/-- The collision hypothesis for the sandwich support comparison on QPBT
polynomial outcomes, with the field cardinality written as `P.q`.

This specializes `polyFunc_eval_collision_le` to the fixed field model and
`evalPoly`; it adds no assumptions to the admissible parameter domain of
blueprint `eq:qld-nonencoding-mass`. -/
theorem poly_eval_collision_le {P : AdmissibleParams}
    (first second : Poly P) (hne : first ≠ second) :
    avgOver (uniformDistribution (Fin P.m → PauliScalar P))
      (fun point => if evalPoly first point = evalPoly second point then (1 : ℝ) else 0) ≤
        (P.m * P.d : ℝ) / P.q := by
  have hcard : Fintype.card (PauliScalar P) = P.q :=
    @FieldModel.card P.q P.model.toFieldModel
  unfold evalPoly
  conv_rhs => rw [← hcard]
  exact polyFunc_eval_collision_le first second hne

end MIPStarRE.QPBT
