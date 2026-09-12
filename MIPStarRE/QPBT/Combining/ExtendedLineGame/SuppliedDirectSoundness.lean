import MIPStarRE.QPBT.Combining.DirectLowDegree.AnyStrategySoundness
import MIPStarRE.QPBT.Combining.ExtendedLineGame.PassingValue

/-!
# Direct low-degree soundness for supplied extended-line witnesses

This module applies arbitrary-strategy directly indexed low-degree soundness to
the strategy determined by supplied point and extended-line witnesses.  The
resulting polynomial-tuple POVMs remain on the two original expanded local
spaces, and all three consistency defects retain the same `deltaLd` bound.

This is a formalization-only consequence of supplied witnesses.  It neither
constructs those witnesses nor asserts projectivity of the returned POVMs or a
global paired measurement.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1277-1289`
- Blueprint `lem:qld-4-7`
- Issue #360
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.Quantum

noncomputable section

namespace ExtendedLineGame

/-- Supplied point and extended-line witnesses determine polynomial-tuple POVMs
on the original expanded player spaces with the three direct low-degree
consistency bounds.

The error supplied to `deltaLd` is
`3 * (sqrt (deltaQ + deltaL) + m * d / q)`.  Positivity of its second summand
follows from admissibility, so no additional game-passing hypothesis is needed.
This is Lean-only support for the first paragraph of the proof of paper
`lem:qld-4-7`; it does not complete that source lemma. -/
theorem exists_direct_polynomial_measurements_of_supplied_witnesses :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b ≤ 1 ∧
      ∀ {P : AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
        {setting : ProjectiveSetting P epsilon}
        (points : CombinedPointsWitness setting deltaQ)
        (lines : ExtendedLinesWitness setting points deltaL),
          ∃ GA : DirectPolyMeasTuple P.extendedDirectLd
              (setting.ExpandedLocalSpace .alice),
            ∃ GB : DirectPolyMeasTuple P.extendedDirectLd
                (setting.ExpandedLocalSpace .bob),
              consistencyDefect
                  (uniformDistribution (Fin P.extendedDirectLd.m →
                    DirectScalarQ P.extendedDirectLd))
                  (fun u outcome =>
                    heteroKron
                      (((answerMeasurement lines .alice
                        (directLdPointQuestionOf P.extendedDirectLd u)).postprocess
                          (directLdPointValuesOrZero P.extendedDirectLd)).effect outcome) 1)
                  (fun u outcome =>
                    heteroKron 1
                      ((GB.postprocess (evalDirectPolyTupleAt u)).effect outcome))
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
                      ((GA.postprocess (evalDirectPolyTupleAt u)).effect outcome) 1)
                  (fun u outcome =>
                    heteroKron 1
                      (((answerMeasurement lines .bob
                        (directLdPointQuestionOf P.extendedDirectLd u)).postprocess
                          (directLdPointValuesOrZero P.extendedDirectLd)).effect outcome))
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
    exists_direct_ld_soundness_of_k_eq_one_any_strategy
  refine ⟨a, b, ha, hb, hb1, ?_⟩
  intro P epsilon deltaQ deltaL setting points lines
  have hm : 0 < (P.m : ℝ) := by
    exact_mod_cast P.one_le_m
  have hd : 0 < (P.d : ℝ) := by
    exact_mod_cast P.hd
  have hq : 0 < (P.q : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) P.hq.two_le)
  have hratio : 0 < (P.m * P.d : ℝ) / (P.q : ℝ) := by
    exact div_pos (mul_pos hm hd) hq
  have herror : 0 <
      3 * (Real.sqrt (deltaQ + deltaL) +
        ((P.m * P.d : ℝ) / (P.q : ℝ))) := by
    simpa only [directPassingErrorEnvelope] using
      directPassingErrorEnvelope_pos (deltaQ + deltaL)
        ((P.m * P.d : ℝ) / (P.q : ℝ)) hratio
  have hvalue :
      1 - 3 * (Real.sqrt (deltaQ + deltaL) +
          ((P.m * P.d : ℝ) / (P.q : ℝ))) ≤
        (strategy lines).value := by
    simpa only [directPassingErrorEnvelope] using
      strategy_value_ge_directPassingErrorEnvelope lines
  obtain ⟨GA, GB, hGA, hGB, hpair⟩ :=
    hsound P.extendedDirectLd
      (3 * (Real.sqrt (deltaQ + deltaL) +
        ((P.m * P.d : ℝ) / (P.q : ℝ)))) rfl herror (strategy lines) hvalue
  dsimp only [strategy] at hGA hGB hpair
  refine ⟨GA, GB, ?_, ?_, ?_⟩
  · exact hGA
  · exact hGB
  · exact hpair

end ExtendedLineGame

end

end MIPStarRE.QPBT
