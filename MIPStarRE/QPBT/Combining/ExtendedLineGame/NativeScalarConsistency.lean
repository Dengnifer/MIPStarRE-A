import MIPStarRE.QPBT.Combining.ExtendedLineGame.NativePointConsistency

/-!
# Native scalar polynomial consistency

This module extracts the unique polynomial coordinate from supplied-witness
direct soundness.  The resulting ordinary polynomial POVMs remain on the
original expanded player spaces, and their point-consistency bounds are stated
against the supplied scalar point measurements.

This is a Lean-only consequence supporting the first paragraph of paper
`lem:qld-4-7`.  It does not construct the supplied witnesses, make the
polynomial measurements projective, or complete that source lemma.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1277-1289`
- Blueprint `lem:qld-4-7`
- Issue #364
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.Quantum

noncomputable section

namespace ExtendedLineGame

/-- Supplied point and extended-line witnesses determine ordinary polynomial
POVMs on the original expanded player spaces.  Their evaluations are
consistent with the supplied scalar point measurements, and the two polynomial
POVMs retain the direct-soundness self-consistency bound.

The error supplied to `deltaLd` is unchanged from
`exists_direct_polynomial_measurements_of_supplied_witnesses`.  This is
Lean-only support for the first paragraph of paper `lem:qld-4-7`; it does not
assert projectivity or the later polynomial-shape conclusion. -/
theorem exists_native_scalar_polynomial_measurements_of_supplied_witnesses :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b ≤ 1 ∧
      ∀ {P : AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
        {setting : ProjectiveSetting P epsilon}
        (points : CombinedPointsWitness setting deltaQ)
        (_lines : ExtendedLinesWitness setting points deltaL),
          ∃ GA : PolyMeas P.extendedDirectLd.m
              (DirectScalarQ P.extendedDirectLd) P.extendedDirectLd.d
              (setting.ExpandedLocalSpace .alice),
            ∃ GB : PolyMeas P.extendedDirectLd.m
                (DirectScalarQ P.extendedDirectLd) P.extendedDirectLd.d
                (setting.ExpandedLocalSpace .bob),
              consistencyDefect
                  (uniformDistribution (Fin P.extendedDirectLd.m →
                    DirectScalarQ P.extendedDirectLd))
                  (fun u outcome =>
                    heteroKron
                      ((points.extendedQ .alice
                        (projX (directPointToPauli P u))
                        (projZ (directPointToPauli P u))
                        (directPointToPauli P u (alphaVar P.m))
                        (directPointToPauli P u (betaVar P.m))).effect outcome) 1)
                  (fun u outcome =>
                    heteroKron 1
                      ((GB.postprocess (fun g =>
                        extendedDirectScalarEquiv P
                          (MvPolynomial.eval u g.1))).effect outcome))
                  (pairState setting) ≤
                deltaLd a b
                  (3 * (Real.sqrt (deltaQ + deltaL) +
                    ((P.m * P.d : ℝ) / (P.q : ℝ))))
                  P.extendedDirectLd.q P.extendedDirectLd.m
                  P.extendedDirectLd.d P.extendedDirectLd.k ∧
              consistencyDefect
                  (uniformDistribution (Fin P.extendedDirectLd.m →
                    DirectScalarQ P.extendedDirectLd))
                  (fun u outcome =>
                    heteroKron
                      ((GA.postprocess (fun g =>
                        extendedDirectScalarEquiv P
                          (MvPolynomial.eval u g.1))).effect outcome) 1)
                  (fun u outcome =>
                    heteroKron 1
                      ((points.extendedQ .bob
                        (projX (directPointToPauli P u))
                        (projZ (directPointToPauli P u))
                        (directPointToPauli P u (alphaVar P.m))
                        (directPointToPauli P u (betaVar P.m))).effect outcome))
                  (pairState setting) ≤
                deltaLd a b
                  (3 * (Real.sqrt (deltaQ + deltaL) +
                    ((P.m * P.d : ℝ) / (P.q : ℝ))))
                  P.extendedDirectLd.q P.extendedDirectLd.m
                  P.extendedDirectLd.d P.extendedDirectLd.k ∧
              consistencyDefect (uniformDistribution Unit)
                  (fun _ g => heteroKron (GA.effect g) 1)
                  (fun _ g => heteroKron 1 (GB.effect g))
                  (pairState setting) ≤
                deltaLd a b
                  (3 * (Real.sqrt (deltaQ + deltaL) +
                    ((P.m * P.d : ℝ) / (P.q : ℝ))))
                  P.extendedDirectLd.q P.extendedDirectLd.m
                  P.extendedDirectLd.d P.extendedDirectLd.k := by
  obtain ⟨a, b, ha, hb, hb1, hsound⟩ :=
    exists_direct_polynomial_measurements_of_supplied_witnesses
  refine ⟨a, b, ha, hb, hb1, ?_⟩
  intro P epsilon deltaQ deltaL setting points lines
  obtain ⟨GATuple, GBTuple, hAlice, hBob, hPolynomial⟩ := hsound points lines
  let r : Fin P.extendedDirectLd.k := ⟨0, by change 0 < 1; decide⟩
  let GA := directPolyMeasTupleMarginal P.extendedDirectLd GATuple r
  let GB := directPolyMeasTupleMarginal P.extendedDirectLd GBTuple r
  refine ⟨GA, GB, ?_, ?_, ?_⟩
  · let pointA := fun u =>
      (answerMeasurement lines .alice
        (directLdPointQuestionOf P.extendedDirectLd u)).postprocess
          (directLdPointValuesOrZero P.extendedDirectLd)
    let polynomialB := fun u => GBTuple.postprocess (evalDirectPolyTupleAt u)
    have hprocess := consistencyDefect_postprocess_le
      (uniformDistribution (Fin P.extendedDirectLd.m →
        DirectScalarQ P.extendedDirectLd)) pointA polynomialB
      (pairState setting)
      (fun values => extendedDirectScalarEquiv P (values r))
    have hEvalB : ∀ u,
        (polynomialB u).postprocess
            (fun values => extendedDirectScalarEquiv P (values r)) =
          GB.postprocess (fun g =>
            extendedDirectScalarEquiv P (MvPolynomial.eval u g.1)) := by
      intro u
      calc
        (polynomialB u).postprocess
            (fun values => extendedDirectScalarEquiv P (values r)) =
            ((polynomialB u).postprocess (fun values => values r)).postprocess
              (extendedDirectScalarEquiv P) := by
                symm
                exact Measurement.postprocess_comp _ _ _
        _ = ((directPolyMeasTupleMarginal P.extendedDirectLd GBTuple r).postprocess
              (fun g => MvPolynomial.eval u g.1)).postprocess
                (extendedDirectScalarEquiv P) := by
              rw [directPolyMeasTuple_evaluation_marginal]
        _ = GB.postprocess (fun g =>
              extendedDirectScalarEquiv P (MvPolynomial.eval u g.1)) := by
              unfold GB
              rw [Measurement.postprocess_comp]
    refine (consistencyDefect_congr _ _ _ _ _ (pairState setting) ?_ ?_).trans_le
      (hprocess.trans hAlice)
    · intro u outcome
      unfold pointA
      rw [point_values_measurement_eq_suppliedQ]
      rfl
    · intro u outcome
      rw [hEvalB u]
  · let polynomialA := fun u => GATuple.postprocess (evalDirectPolyTupleAt u)
    let pointB := fun u =>
      (answerMeasurement lines .bob
        (directLdPointQuestionOf P.extendedDirectLd u)).postprocess
          (directLdPointValuesOrZero P.extendedDirectLd)
    have hprocess := consistencyDefect_postprocess_le
      (uniformDistribution (Fin P.extendedDirectLd.m →
        DirectScalarQ P.extendedDirectLd)) polynomialA pointB
      (pairState setting)
      (fun values => extendedDirectScalarEquiv P (values r))
    have hEvalA : ∀ u,
        (polynomialA u).postprocess
            (fun values => extendedDirectScalarEquiv P (values r)) =
          GA.postprocess (fun g =>
            extendedDirectScalarEquiv P (MvPolynomial.eval u g.1)) := by
      intro u
      calc
        (polynomialA u).postprocess
            (fun values => extendedDirectScalarEquiv P (values r)) =
            ((polynomialA u).postprocess (fun values => values r)).postprocess
              (extendedDirectScalarEquiv P) := by
                symm
                exact Measurement.postprocess_comp _ _ _
        _ = ((directPolyMeasTupleMarginal P.extendedDirectLd GATuple r).postprocess
              (fun g => MvPolynomial.eval u g.1)).postprocess
                (extendedDirectScalarEquiv P) := by
              rw [directPolyMeasTuple_evaluation_marginal]
        _ = GA.postprocess (fun g =>
              extendedDirectScalarEquiv P (MvPolynomial.eval u g.1)) := by
              unfold GA
              rw [Measurement.postprocess_comp]
    refine (consistencyDefect_congr _ _ _ _ _ (pairState setting) ?_ ?_).trans_le
      (hprocess.trans hBob)
    · intro u outcome
      rw [hEvalA u]
    · intro u outcome
      unfold pointB
      rw [point_values_measurement_eq_suppliedQ]
      rfl
  · simpa [GA, GB, directPolyMeasTupleMarginal] using
      (consistencyDefect_postprocess_le (uniformDistribution Unit)
        (fun _ => GATuple) (fun _ => GBTuple) (pairState setting)
        (fun tuple => tuple r)).trans hPolynomial

end ExtendedLineGame

end

end MIPStarRE.QPBT
