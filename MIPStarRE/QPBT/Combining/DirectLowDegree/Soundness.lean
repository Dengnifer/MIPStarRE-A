import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Combining.Error
import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Combining.SimultaneousGeneral

/-!
# Soundness for the directly indexed low-degree game

This module proves the quantum soundness statement for the directly indexed
low-degree game, in the form used by the Chapter 15 combining argument: the
polynomial-tuple measurements of `prop:ld-simultaneous-general-k` satisfy the
three consistency relations of `lem:ld-soundness` with the error function
`deltaLd` at the parameters `(q, m, d, k)` of the game.

In the regime `0 < ε ≤ 1` the error carried by
`prop:ld-simultaneous-general-k` — the error of `thm:main-formal` at the
combined parameters of `def:ld-combining-parameters` together with the recovery
loss `(m + k) d / q` — is absorbed into `deltaLd` at the universal constants
`a = 10^23` and `b = 1/80000` by
`exists_directCombinedTransportConstants`.  In the regime `1 ≤ ε` the error
function is at least one, while every bipartite consistency defect on a unit
state is at most one, so the conclusion carries no information there.

## Main statements

* `exists_direct_ld_soundness` — quantum soundness of the directly indexed
  low-degree game, with the error function `deltaLd`.

## References

The obligation supports the Chapter 15 combining argument at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1288`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.Quantum

noncomputable section

/-- Quantum soundness of the directly indexed low-degree game.
This is the repaired import form proposed in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`, needed by the Chapter 15
combining argument at paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1288`.

This is a formalization auxiliary assertion, not the source-labelled
`lem:ld-soundness`; the game-correspondence and auxiliary-parameter bounds
catalogued in the cited gap note are established, not hidden as hypotheses.
The measurements are those of `prop:ld-simultaneous-general-k`, and the
universal constants exhibited are `a = 10^23` and `b = 1/80000`: for
`0 < ε ≤ 1` the error of that proposition is absorbed into `deltaLd` by
`exists_directCombinedTransportConstants`, and for `1 ≤ ε` the error function
is at least one while every bipartite consistency defect on a unit state is at
most one. -/
theorem exists_direct_ld_soundness :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b ≤ 1 ∧
      ∀ (D : DirectLdParams) (ε : ℝ), 0 < ε →
        ∀ S : Strategy (directLdGame D), S.IsProjective → 1 - ε ≤ S.value →
          ∃ GA : DirectPolyMeasTuple D S.ιA,
            ∃ GB : DirectPolyMeasTuple D S.ιB,
              consistencyDefect
                  (uniformDistribution (Fin D.m → DirectScalarQ D))
                  (fun u outcome =>
                    heteroKron
                      (((S.A (directLdPointQuestionOf D u)).postprocess
                        (directLdPointValuesOrZero D)).effect outcome) 1)
                  (fun u outcome =>
                    heteroKron 1
                      ((GB.postprocess (evalDirectPolyTupleAt u)).effect outcome))
                  S.ψ ≤ deltaLd a b ε D.q D.m D.d D.k ∧
              consistencyDefect
                  (uniformDistribution (Fin D.m → DirectScalarQ D))
                  (fun u outcome =>
                    heteroKron
                      ((GA.postprocess (evalDirectPolyTupleAt u)).effect outcome) 1)
                  (fun u outcome =>
                    heteroKron 1
                      (((S.B (directLdPointQuestionOf D u)).postprocess
                        (directLdPointValuesOrZero D)).effect outcome))
                  S.ψ ≤ deltaLd a b ε D.q D.m D.d D.k ∧
              consistencyDefect (uniformDistribution Unit)
                  (fun _ g => heteroKron (GA.effect g) 1)
                  (fun _ g => heteroKron 1 (GB.effect g))
                  S.ψ ≤ deltaLd a b ε D.q D.m D.d D.k := by
  obtain ⟨a, b, ha, hb0, hb1, habs⟩ := exists_directCombinedTransportConstants
  refine ⟨a, b, ha, hb0, hb1, ?_⟩
  intro D ε hε S hS hwin
  obtain ⟨GA, GB, h1, h2, h3⟩ :=
    exists_directSimultaneousPolynomialMeasurements_combinedError D S hS ε hwin
  refine ⟨GA, GB, ?_, ?_, ?_⟩
  all_goals by_cases hε1 : ε ≤ 1
  · exact le_trans h1 (habs D ε hε hε1)
  · exact le_trans
      (consistencyDefect_heteroKron_le_one _ (uniformDistribution_isProbability _) _ _
        S.ψ S.ψ_norm)
      (one_le_deltaLd_of_one_le_error ha hb0.le (not_le.mp hε1).le D.hm D.hd D.hk)
  · exact le_trans h2 (habs D ε hε hε1)
  · exact le_trans
      (consistencyDefect_heteroKron_le_one _ (uniformDistribution_isProbability _) _ _
        S.ψ S.ψ_norm)
      (one_le_deltaLd_of_one_le_error ha hb0.le (not_le.mp hε1).le D.hm D.hd D.hk)
  · refine le_trans h3 (le_trans ?_ (habs D ε hε hε1))
    have hloss : (0 : ℝ) ≤ ((D.combined.m * D.d : ℕ) : ℝ) / (D.q : ℝ) := by positivity
    linarith
  · exact le_trans
      (consistencyDefect_heteroKron_le_one _ (uniformDistribution_isProbability _) _ _
        S.ψ S.ψ_norm)
      (one_le_deltaLd_of_one_le_error ha hb0.le (not_le.mp hε1).le D.hm D.hd D.hk)

end

end MIPStarRE.QPBT
