import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Combining.RecoveryTransport
import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Simultaneous

/-!
# Simultaneous polynomial measurements for a general simultaneity parameter

`prop:ld-simultaneous-general-k` produces, from a projective strategy for the
directly indexed low-degree game at parameters `(q, m, d, k)` succeeding with
probability at least `1 - ε`, a pair of polynomial-tuple measurements
satisfying the three consistency relations of `lem:ld-soundness`.

The reduction applies the case `k = 1` once, to the combined strategy of
`def:ld-combined-strategy` at the combined parameters `(q, m + k, d, 1)`: by
`lem:ld-combined-value` that strategy succeeds with probability at least
`1 - 10 ε`, so the case `k = 1` produces measurements with outcomes in the
polynomials of `m + k` variables, satisfying the three relations with the error
of `thm:main-formal` at the combined parameters, and
`lem:ld-combining-recovery` post-processes them by the recovery map of
`def:ld-combining-map`, at the cost of `(m + k) d / q` in the two point
relations.

The error obtained here is the error of `lem:ld-soundness` for the combined
game plus `(m + k) d / q`, which is the form displayed in the source; its
absorption into `deltaLd` at the original parameters, with the universal
constants `a = 10^23` and `b = 1/80000`, is
`exists_directCombinedTransportConstants`, and the absorbed form of the
conclusion is `exists_direct_ld_soundness`.

## Main statements

* `exists_directSimultaneousPolynomialMeasurements_combinedError` —
  `prop:ld-simultaneous-general-k` with the error displayed in the parameters
  of the combined game.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1409-1503`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:682-715`
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.Quantum
open DistanceCalculus

noncomputable section

set_option maxHeartbeats 1600000 in
/-- `prop:ld-simultaneous-general-k`, with the error displayed as the error of
`lem:ld-soundness` for the combined game at the combined parameters plus the
recovery loss `(m + k) d / q`.

The combined strategy of `def:ld-combined-strategy` succeeds with probability
at least `1 - 10 ε` at the combined parameters, whose simultaneity parameter is
`1`; the case `k = 1` of `lem:ld-soundness` produces measurements with outcomes
in the polynomials of `m + k` variables, and
`lem:ld-combining-recovery` post-processes them by the recovery map. -/
theorem exists_directSimultaneousPolynomialMeasurements_combinedError
    (D : DirectLdParams) (S : Strategy (directLdGame D)) (hS : S.IsProjective)
    (ε : Error) (hwin : 1 - ε ≤ S.value) :
    ∃ GA : DirectPolyMeasTuple D S.ιA,
      ∃ GB : DirectPolyMeasTuple D S.ιB,
        consistencyDefect
            (uniformDistribution (Fin D.m → DirectScalarQ D))
            (fun u outcome => heteroKron
              (((S.A (directLdPointQuestionOf D u)).postprocess
                (directLdPointValuesOrZero D)).effect outcome) 1)
            (fun u outcome => heteroKron 1
              ((GB.postprocess (evalDirectPolyTupleAt u)).effect outcome))
            S.ψ ≤
          Test.mainFormalError D.combined.toLDTParameters
              (directLdAuxParameter D.combined) (3 * (10 * ε)) +
            ((D.combined.m * D.d : ℕ) : ℝ) / D.q ∧
        consistencyDefect
            (uniformDistribution (Fin D.m → DirectScalarQ D))
            (fun u outcome => heteroKron
              ((GA.postprocess (evalDirectPolyTupleAt u)).effect outcome) 1)
            (fun u outcome => heteroKron 1
              (((S.B (directLdPointQuestionOf D u)).postprocess
                (directLdPointValuesOrZero D)).effect outcome))
            S.ψ ≤
          Test.mainFormalError D.combined.toLDTParameters
              (directLdAuxParameter D.combined) (3 * (10 * ε)) +
            ((D.combined.m * D.d : ℕ) : ℝ) / D.q ∧
        consistencyDefect (uniformDistribution Unit)
            (fun _ g => heteroKron (GA.effect g) 1)
            (fun _ g => heteroKron 1 (GB.effect g)) S.ψ ≤
          Test.mainFormalError D.combined.toLDTParameters
            (directLdAuxParameter D.combined) (3 * (10 * ε)) := by
  obtain ⟨GA, GB, h1, h2, h3⟩ :=
    exists_directSimultaneousPolynomialMeasurements_of_k_eq_one D.combined rfl
      (directCombinedStrategy D S) (directCombinedStrategy_isProjective D S hS)
      (10 * ε) (directCombinedStrategy_value_ge D S ε hwin)
  refine ⟨GA.postprocess (directTupleOfCombinedTuple D),
    GB.postprocess (directTupleOfCombinedTuple D), ?_, ?_, ?_⟩
  · exact le_trans (directCombinedRecovery_relation_one D S GB)
      (add_le_add h1 le_rfl)
  · exact le_trans (directCombinedRecovery_relation_two D S GA)
      (add_le_add h2 le_rfl)
  · exact le_trans (directCombinedRecovery_relation_three D S GA GB) h3

end

end MIPStarRE.QPBT
