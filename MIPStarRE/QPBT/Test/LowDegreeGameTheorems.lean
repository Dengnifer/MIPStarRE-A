import MIPStarRE.QPBT.Combining.DirectLowDegree.Soundness
import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.PointAgreement
import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.SeedError
import MIPStarRE.QPBT.Games.Sandwich.Support

/-!
# Quantum soundness of the seed-indexed low-degree game

The general simultaneity reduction for the directly indexed game is transported
through the correlated seed dilation. Point consistency survives compression
exactly; global polynomial consistency is recovered by point agreement and
Schwartz--Zippel, with the square-root loss absorbed into `deltaLd`.

## References

* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `references/neexp-paper/05_quantum_preliminaries.tex:1409-1503`
* Blueprint `lem:ld-soundness`
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.Quantum

noncomputable section

/-- Distinct polynomial tuples collide only where one of their distinct
coordinates collides. This formalization auxiliary for `lem:ld-soundness`
therefore has the same Schwartz--Zippel bound for every simultaneity parameter. -/
theorem polyTupleAgreement_avg_le_mdq (L : LdParams)
    (g g' : PolyTuple L) (hne : g ≠ g') :
    avgOver (uniformDistribution (Fin L.m → ScalarQ L))
        (fun u => if evalPolyTupleAt u g = evalPolyTupleAt u g' then
          (1 : ℝ) else 0) ≤
      ((L.m : ℝ) * (L.d : ℝ)) / (L.q : ℝ) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  refine le_trans (avgOver_mono _ _ _ fun u => ?_)
    (directPolynomialAgreement_avg_le_mdq L.toDirectLdParams (g i) (g' i) hi)
  split_ifs with h h'
  · exact le_rfl
  · exact False.elim (h' (congrFun h i))
  · norm_num
  · exact le_rfl

set_option maxHeartbeats 1000000 in
/-- Quantum soundness of the simultaneous classical low individual degree
test (blueprint `lem:ld-soundness`; paper theorem and proof
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`).

The first two consistency bounds compare the point-answer postprocessing of the
strategy with evaluations of the polynomial measurements. Answers of the wrong
form are folded into the zero tuple so that the point family remains a POVM.

The printed tensor-code reduction still requires proofs of its claimed game
correspondence and auxiliary parameter bound. These two facts are detailed in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` and
`rem:ld-soundness-provider`, and are tracked by issue #16.

The proof here instead uses the established direct low individual degree
reduction and transports it through the correlated seed dilation. It works for
every `L.k`: simultaneity comes from the single-polynomial case by the combining
reduction of Theorem 4.43 in the NEEXP paper, not coordinatewise; the
coordinatewise route planned for the formalization is refuted in
`docs/paper-gaps/qpbt_ld-simultaneous-sandwich.tex`. The combining reduction
is proved for the directly indexed game in
`MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/Combining/SimultaneousGeneral.lean`;
the two mixed relations survive seed compression exactly. Global consistency
is recovered from point agreement and the tuple Schwartz--Zippel bound, rather
than double compression. The resulting square-root loss is absorbed by replacing
the direct constants `(a, b)` with `(10 * a, b / 2)`. This discharges the
seed-indexed extension tracked by issues #210 and #527, without using either
open assertion of the printed tensor-code proof. -/
theorem exists_ld_soundness :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b ≤ 1 ∧
      ∀ (L : LdParams) (ε : ℝ), 0 < ε →
        ∀ S : Strategy (ldGame L), S.IsProjective → 1 - ε ≤ S.value →
          ∃ GA : PolyMeasTuple L S.ιA, ∃ GB : PolyMeasTuple L S.ιB,
            consistencyDefect (uniformDistribution (Fin L.m → ScalarQ L))
                (fun u outcome =>
                  heteroKron
                    (((S.A (ldPointQuestionOf L u)).postprocess
                      (ldPointValuesOrZero L)).effect outcome) 1)
                (fun u outcome =>
                  heteroKron 1
                    ((GB.postprocess (evalPolyTupleAt u)).effect outcome))
                S.ψ ≤ deltaLd a b ε L.q L.m L.d L.k ∧
            consistencyDefect (uniformDistribution (Fin L.m → ScalarQ L))
                (fun u outcome =>
                  heteroKron
                    ((GA.postprocess (evalPolyTupleAt u)).effect outcome) 1)
                (fun u outcome =>
                  heteroKron 1
                    (((S.B (ldPointQuestionOf L u)).postprocess
                      (ldPointValuesOrZero L)).effect outcome))
                S.ψ ≤ deltaLd a b ε L.q L.m L.d L.k ∧
            consistencyDefect (uniformDistribution Unit)
                (fun _ g => heteroKron (GA.effect g) 1)
                (fun _ g => heteroKron 1 (GB.effect g))
                S.ψ ≤ deltaLd a b ε L.q L.m L.d L.k := by
  classical
  obtain ⟨a, b, ha, hb, hb1, hs⟩ := exists_direct_ld_soundness
  refine ⟨10 * a, b / 2, by linarith, by positivity, by linarith, ?_⟩
  intro L ε hε S hS hwin
  let D := L.toDirectLdParams
  let E := deltaLd a b ε L.q L.m L.d L.k
  let F := deltaLd (10 * a) (b / 2) ε L.q L.m L.d L.k
  obtain ⟨GA₀, GB₀, h1, h2, _⟩ := hs D ε hε (ldStrategyToDirect L S)
    (ldStrategyToDirect_isProjective L S hS)
    (by simpa only [ldStrategyToDirect_value_eq] using hwin)
  let GA : PolyMeasTuple L S.ιA := seedFiberCompressPolyMeasTuple L GA₀
  let GB : PolyMeasTuple L S.ιB := seedFiberCompressPolyMeasTuple L GB₀
  have c1 : consistencyDefect (uniformDistribution (Fin L.m → ScalarQ L))
      (fun u outcome => heteroKron
        (((S.A (ldPointQuestionOf L u)).postprocess
          (ldPointValuesOrZero L)).effect outcome) 1)
      (fun u outcome => heteroKron 1
        ((GB.postprocess (evalPolyTupleAt u)).effect outcome)) S.ψ ≤ E := by
    rw [show GB = seedFiberCompressPolyMeasTuple L GB₀ from rfl,
      ← ldStrategyToDirect_pointPolynomial_compression L S GB₀]
    exact h1
  have c2 : consistencyDefect (uniformDistribution (Fin L.m → ScalarQ L))
      (fun u outcome => heteroKron
        ((GA.postprocess (evalPolyTupleAt u)).effect outcome) 1)
      (fun u outcome => heteroKron 1
        (((S.B (ldPointQuestionOf L u)).postprocess
          (ldPointValuesOrZero L)).effect outcome)) S.ψ ≤ E := by
    rw [show GA = seedFiberCompressPolyMeasTuple L GA₀ from rfl,
      ← ldStrategyToDirect_polynomialPoint_compression L S GA₀]
    exact h2
  have c3 := ldPointPair_consistencyDefect_le L S hS ε hwin
  have ctrans : consistencyDefect (uniformDistribution (Fin L.m → ScalarQ L))
      (fun u outcome => heteroKron
        ((GA.postprocess (evalPolyTupleAt u)).effect outcome) 1)
      (fun u outcome => heteroKron 1
        ((GB.postprocess (evalPolyTupleAt u)).effect outcome)) S.ψ ≤
      E + 2 * Real.sqrt (9 * ε + E) :=
    consistencyDefect_trans_le (uniformDistribution (Fin L.m → ScalarQ L))
      (fun u => DistanceCalculus.leftPlacedMeasurement
        (GA.postprocess (evalPolyTupleAt u)))
      (fun u => DistanceCalculus.rightPlacedMeasurement
        ((S.B (ldPointQuestionOf L u)).postprocess (ldPointValuesOrZero L)))
      (fun u => DistanceCalculus.leftPlacedMeasurement
        ((S.A (ldPointQuestionOf L u)).postprocess (ldPointValuesOrZero L)))
      (fun u => DistanceCalculus.rightPlacedMeasurement
        (GB.postprocess (evalPolyTupleAt u)))
      S.ψ E (9 * ε) E (uniformDistribution_isProbability _) S.ψ_norm c2 c3 c1
  have ccode : consistencyDefect (uniformDistribution Unit)
      (fun _ g => heteroKron (GA.effect g) 1)
      (fun _ g => heteroKron 1 (GB.effect g)) S.ψ ≤
      E + 2 * Real.sqrt (9 * ε + E) + (L.m : ℝ) * L.d / L.q := by
    have hstep := SandwichProduct.consistencyDefect_codewords_le_evaluated_add
      (uniformDistribution Unit) (fun _ : Unit => GA) (fun _ : Unit => GB) S.ψ
      (fun g u => evalPolyTupleAt u g) ((L.m : ℝ) * L.d / L.q)
      (uniformDistribution_isProbability _) S.ψ_norm (by positivity)
      (fun g g' hne => polyTupleAgreement_avg_le_mdq L g g' hne)
    have hprod : ∀ (A B : Unit × (Fin L.m → ScalarQ L) →
        (Fin L.k → ScalarQ L) → Op (S.ιA × S.ιB)),
        consistencyDefect
          (Distribution.prod (uniformDistribution Unit)
            (uniformDistribution (Fin L.m → ScalarQ L))) A B S.ψ =
        consistencyDefect (uniformDistribution (Fin L.m → ScalarQ L))
          (fun u => A ((), u)) (fun u => B ((), u)) S.ψ := by
      intro A B
      unfold consistencyDefect
      rw [SandwichProduct.avgOver_distribution_prod,
        avgOver_uniform_eq_inv_card_mul_sum]
      simp
    rw [hprod] at hstep
    exact hstep.trans (by linarith)
  have hsqrt : 10 * Real.sqrt E ≤ F := ten_sqrt_deltaLd_le D ha hε.le
  have hEnn : 0 ≤ E := by dsimp [E, deltaLd]; positivity
  have hbound {X α : Type} [Fintype X] [DecidableEq X] [Nonempty X]
      [Fintype α] [DecidableEq α]
      (A : X → MIPStarRE.Quantum.Measurement α S.ιA)
      (B : X → MIPStarRE.Quantum.Measurement α S.ιB)
      (hc : consistencyDefect (uniformDistribution X)
        (fun x o => heteroKron ((A x).effect o) 1)
        (fun x o => heteroKron 1 ((B x).effect o)) S.ψ ≤
        E + 2 * Real.sqrt (9 * ε + E) + (L.m : ℝ) * L.d / L.q) :
      consistencyDefect (uniformDistribution X)
        (fun x o => heteroKron ((A x).effect o) 1)
        (fun x o => heteroKron 1 ((B x).effect o)) S.ψ ≤ F := by
    have hone := consistencyDefect_heteroKron_le_one
      (uniformDistribution X) (uniformDistribution_isProbability _) A B S.ψ S.ψ_norm
    by_cases hε1 : ε ≤ 1
    · by_cases hE1 : E ≤ 1
      · obtain ⟨he, hm⟩ := error_and_collision_le_deltaLd D ha hb1 hε hε1
        change ε ≤ E at he
        change (L.m : ℝ) * L.d / L.q ≤ E at hm
        have hEs : E ≤ Real.sqrt E := le_sqrt_of_le_of_le_one le_rfl hE1
        have hroot : Real.sqrt (9 * ε + E) ≤ 4 * Real.sqrt E := by
          apply (Real.sqrt_le_iff).mpr
          refine ⟨by positivity, ?_⟩
          nlinarith [Real.sq_sqrt hEnn]
        exact hc.trans (by linarith)
      · have hEs : 1 ≤ Real.sqrt E := by
          simpa using Real.sqrt_le_sqrt (not_le.mp hE1).le
        exact hone.trans (by linarith)
    · exact hone.trans (one_le_deltaLd_of_one_le_error (by linarith) (by positivity)
        (not_le.mp hε1).le L.hm L.hd L.hk)
  have hrem : 0 ≤ 2 * Real.sqrt (9 * ε + E) + (L.m : ℝ) * L.d / L.q := by
    positivity
  refine ⟨GA, GB, ?_, ?_, ?_⟩
  · apply hbound
      (fun u => (S.A (ldPointQuestionOf L u)).postprocess (ldPointValuesOrZero L))
      (fun u => GB.postprocess (evalPolyTupleAt u))
    exact c1.trans (by linarith)
  · apply hbound (fun u => GA.postprocess (evalPolyTupleAt u))
      (fun u => (S.B (ldPointQuestionOf L u)).postprocess (ldPointValuesOrZero L))
    exact c2.trans (by linarith)
  · exact hbound (fun _ : Unit => GA) (fun _ : Unit => GB) ccode

end

end MIPStarRE.QPBT
