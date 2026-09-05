import MIPStarRE.QPBT.Combining.DirectLowDegree.Soundness
import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.PointAgreement
import MIPStarRE.QPBT.Games.Sandwich.Support

/-!
# Seed-indexed low-degree soundness for one simultaneous coordinate

This module transports the polynomial-tuple conclusions of the directly
indexed low-degree game back to the seed-indexed game `ldGame` of
`def:ld-game`, for simultaneity parameter `1`.

## The route

A seed-indexed strategy is dilated to a direct strategy by the correlated
seed-residue register of `Transport.SeedFiber`; the dilation preserves the
value exactly, so the low individual degree theorem applies to it and produces
polynomial-tuple measurements on the extended Hilbert spaces.  Compressing the
residue register returns polynomial measurements on the original Hilbert spaces.

Compression is exact for the two point-versus-polynomial relations, because
the point measurement on the opposite side is a block-diagonal amplification
that leaves the correlated register untouched
(`ldStrategyToDirect_pointPolynomial_compression`).  It is *not* exact for the
global polynomial relation, where both measurements act on the correlated
register: on a maximally entangled residue pair the two compressed
measurements can be far apart while the uncompressed ones agree exactly.  The
global relation is therefore recovered on the original Hilbert spaces instead of
transported: the two compressed polynomial measurements are consistent with
the point measurement of the opposite player, the point-agreement branch of
the game (`ldPointPair_consistencyDefect_le`) links the two point
measurements, the triangle inequality `consistencyDefect_trans_le` chains the
three relations into agreement of the two evaluated polynomial measurements,
and the Schwartz--Zippel estimate `consistencyDefect_codewords_le_evaluated_add`
lifts agreement of evaluations at a uniformly random point to agreement of
the polynomials themselves.

## References

* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `references/ldt-paper/test_definition.tex:180-202`
* `blueprint/src/chapter/ch13_qpbt_test.tex:139-215`
* `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
* `docs/paper-gaps/qpbt_ld-simultaneous-sandwich.tex`
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.Quantum

noncomputable section

/-! ## Auxiliary reductions -/

/-- A consistency defect over a one-point question law paired with a uniform
law is the defect over the uniform law alone. -/
private theorem consistencyDefect_prod_unit
    {Y Outcome iota : Type*} [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype Outcome] [DecidableEq Outcome]
    [Fintype iota] [DecidableEq iota]
    (A B : Unit × Y → Outcome → Op iota) (psi : EuclideanSpace ℂ iota) :
    consistencyDefect
        (Distribution.prod (uniformDistribution Unit) (uniformDistribution Y))
        A B psi =
      consistencyDefect (uniformDistribution Y)
        (fun y => A ((), y)) (fun y => B ((), y)) psi := by
  unfold consistencyDefect
  rw [SandwichProduct.avgOver_distribution_prod,
    avgOver_uniform_eq_inv_card_mul_sum]
  simp

/-- Two distinct one-coordinate polynomial tuples agree at a uniformly random
point with probability at most `m d / q`.  This is the tuple form of the
Schwartz--Zippel estimate `directPolynomialAgreement_avg_le_mdq` at
simultaneity parameter `1`. -/
private theorem polyTupleAgreement_avg_le_mdq (L : LdParams) (hk : L.k = 1)
    (g g' : PolyTuple L) (hne : g ≠ g') :
    avgOver (uniformDistribution (Fin L.m → ScalarQ L))
        (fun u => if evalPolyTupleAt u g = evalPolyTupleAt u g' then
          (1 : ℝ) else 0) ≤
      ((L.m : ℝ) * (L.d : ℝ)) / (L.q : ℝ) := by
  haveI hU : Unique (Fin L.k) :=
    { default := ⟨0, by omega⟩
      uniq := fun i => Fin.ext (by have := i.isLt; omega) }
  have hne' : g default ≠ g' default := by
    intro h
    refine hne (funext fun i => ?_)
    rw [Unique.eq_default i]
    exact h
  have hbase := directPolynomialAgreement_avg_le_mdq L.toDirectLdParams
    (g default) (g' default) hne'
  refine le_trans (le_of_eq (avgOver_congr _ _ _ ?_)) hbase
  intro u
  refine if_congr ?_ rfl rfl
  constructor
  · intro h
    exact congrFun h default
  · intro h
    funext i
    rw [Unique.eq_default i]
    exact h

/-! ## The seed-indexed soundness theorem for one coordinate -/

set_option maxHeartbeats 1000000 in
/-- Quantum soundness of the simultaneous classical low individual degree
test (`lem:ld-soundness`) for simultaneity parameter `1`: the conclusions of
`exists_ld_soundness`, with universal constants of the same shape, under the
hypothesis `L.k = 1`.

For arbitrary `L.k` the source proof extends the case `L.k = 1` by the
combining reduction of Theorem 4.43 in
`references/neexp-paper/05_quantum_preliminaries.tex:1409-1503`, which is not
formalized here; the coordinatewise alternative planned for the formalization
is refuted in `docs/paper-gaps/qpbt_ld-simultaneous-sandwich.tex`.  Blueprint
`ch13_qpbt_test.tex:139-215`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`. -/
theorem exists_ld_soundness_of_k_eq_one :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b ≤ 1 ∧
      ∀ (L : LdParams) (ε : ℝ), L.k = 1 → 0 < ε →
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
  obtain ⟨a, b, ha, hb, hb1, habs⟩ :=
    exists_directLdTransportConstants 10 (by norm_num)
  refine ⟨a, b, ha, hb, hb1, ?_⟩
  intro L ε hk hε S hS hwin
  haveI : Nonempty (Fin L.m → ScalarQ L) :=
    Nonempty.map (directPointEquiv L.toDirectLdParams).symm
      (directLdtPointNonempty L.toDirectLdParams)
  set E : ℝ :=
    Test.mainFormalError L.toDirectLdParams.toLDTParameters
      (directLdAuxParameter L.toDirectLdParams) (3 * ε) with hE
  have hEnn : (0 : ℝ) ≤ E := by
    rw [hE, Test.mainFormalError_eq_envelope]
    exact mul_nonneg (by positivity)
      (Test.mainFormalEnvelope_nonneg _ _ _ (by linarith))
  have hS'proj : (ldStrategyToDirect L S).IsProjective :=
    ldStrategyToDirect_isProjective L S hS
  have hS'win : 1 - ε ≤ (ldStrategyToDirect L S).value := by
    rw [ldStrategyToDirect_value_eq]
    exact hwin
  obtain ⟨GA₀, GB₀, h1, h2, h3⟩ :=
    exists_directSimultaneousPolynomialMeasurements_of_k_eq_one
      L.toDirectLdParams hk (ldStrategyToDirect L S) hS'proj ε hS'win
  set GA : PolyMeasTuple L S.ιA := seedFiberCompressPolyMeasTuple L GA₀ with hGA
  set GB : PolyMeasTuple L S.ιB := seedFiberCompressPolyMeasTuple L GB₀ with hGB
  -- The two compressed point-versus-polynomial relations.
  have c1 : consistencyDefect (uniformDistribution (Fin L.m → ScalarQ L))
      (fun u outcome =>
        heteroKron
          (((S.A (ldPointQuestionOf L u)).postprocess
            (ldPointValuesOrZero L)).effect outcome) 1)
      (fun u outcome =>
        heteroKron 1 ((GB.postprocess (evalPolyTupleAt u)).effect outcome))
      S.ψ ≤ E := by
    rw [hGB, ← ldStrategyToDirect_pointPolynomial_compression L S GB₀]
    exact h1
  have c2 : consistencyDefect (uniformDistribution (Fin L.m → ScalarQ L))
      (fun u outcome =>
        heteroKron ((GA.postprocess (evalPolyTupleAt u)).effect outcome) 1)
      (fun u outcome =>
        heteroKron 1
          (((S.B (ldPointQuestionOf L u)).postprocess
            (ldPointValuesOrZero L)).effect outcome))
      S.ψ ≤ E := by
    rw [hGA, ← ldStrategyToDirect_polynomialPoint_compression L S GA₀]
    exact h2
  -- The point-agreement branch of the game.
  have c3 := ldPointPair_consistencyDefect_le L S hS ε hwin
  -- Chaining the three relations.
  have ctrans : consistencyDefect (uniformDistribution (Fin L.m → ScalarQ L))
      (fun u outcome =>
        heteroKron ((GA.postprocess (evalPolyTupleAt u)).effect outcome) 1)
      (fun u outcome =>
        heteroKron 1 ((GB.postprocess (evalPolyTupleAt u)).effect outcome))
      S.ψ ≤ E + 2 * Real.sqrt (9 * ε + E) :=
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
  -- Lifting agreement of evaluations to agreement of polynomials.
  have hmdq : (0 : ℝ) ≤ ((L.m : ℝ) * (L.d : ℝ)) / (L.q : ℝ) := by positivity
  have ccode : consistencyDefect (uniformDistribution Unit)
      (fun _ g => heteroKron (GA.effect g) 1)
      (fun _ g => heteroKron 1 (GB.effect g)) S.ψ ≤
      E + 2 * Real.sqrt (9 * ε + E) + ((L.m : ℝ) * (L.d : ℝ)) / (L.q : ℝ) := by
    have hstep := SandwichProduct.consistencyDefect_codewords_le_evaluated_add
      (uniformDistribution Unit) (fun _ : Unit => GA) (fun _ : Unit => GB) S.ψ
      (fun g u => evalPolyTupleAt u g) (((L.m : ℝ) * (L.d : ℝ)) / (L.q : ℝ))
      (uniformDistribution_isProbability _) S.ψ_norm hmdq
      (fun g g' hne => polyTupleAgreement_avg_le_mdq L hk g g' hne)
    rw [consistencyDefect_prod_unit] at hstep
    exact le_trans hstep (by linarith)
  -- Absorbing the transport error into `deltaLd`.
  have hmdq_eq : ((L.toDirectLdParams.m : ℝ) * (L.toDirectLdParams.d : ℝ)) /
      (L.toDirectLdParams.q : ℝ) = ((L.m : ℝ) * (L.d : ℝ)) / (L.q : ℝ) := rfl
  have hmature : ∀ _ : ε ≤ 1,
      ∀ _ : E + ((L.m : ℝ) * (L.d : ℝ)) / (L.q : ℝ) + ε ≤ 1,
      E ≤ Real.sqrt (E + ((L.m : ℝ) * (L.d : ℝ)) / (L.q : ℝ) + ε) := by
    intro _ hT
    exact le_sqrt_of_le_of_le_one (by linarith) hT
  refine ⟨GA, GB, ?_, ?_, ?_⟩
  · refine consistencyDefect_le_deltaLd_of_transportBound ha hb (by norm_num)
      habs L.toDirectLdParams ε hε
      (uniformDistribution (Fin L.m → ScalarQ L))
      (uniformDistribution_isProbability _)
      (fun u => (S.A (ldPointQuestionOf L u)).postprocess (ldPointValuesOrZero L))
      (fun u => GB.postprocess (evalPolyTupleAt u)) S.ψ S.ψ_norm ?_
    intro hε1 hT
    rw [← hE, hmdq_eq] at hT ⊢
    have hsq := hmature hε1 hT
    have hnn : (0 : ℝ) ≤
        Real.sqrt (E + ((L.m : ℝ) * (L.d : ℝ)) / (L.q : ℝ) + ε) := Real.sqrt_nonneg _
    linarith
  · refine consistencyDefect_le_deltaLd_of_transportBound ha hb (by norm_num)
      habs L.toDirectLdParams ε hε
      (uniformDistribution (Fin L.m → ScalarQ L))
      (uniformDistribution_isProbability _)
      (fun u => GA.postprocess (evalPolyTupleAt u))
      (fun u => (S.B (ldPointQuestionOf L u)).postprocess (ldPointValuesOrZero L))
      S.ψ S.ψ_norm ?_
    intro hε1 hT
    rw [← hE, hmdq_eq] at hT ⊢
    have hsq := hmature hε1 hT
    have hnn : (0 : ℝ) ≤
        Real.sqrt (E + ((L.m : ℝ) * (L.d : ℝ)) / (L.q : ℝ) + ε) := Real.sqrt_nonneg _
    linarith
  · refine consistencyDefect_le_deltaLd_of_transportBound ha hb (by norm_num)
      habs L.toDirectLdParams ε hε
      (uniformDistribution Unit) (uniformDistribution_isProbability _)
      (fun _ => GA) (fun _ => GB) S.ψ S.ψ_norm ?_
    intro hε1 hT
    rw [← hE, hmdq_eq] at hT ⊢
    have hsqE := hmature hε1 hT
    have hsqmd : ((L.m : ℝ) * (L.d : ℝ)) / (L.q : ℝ) ≤
        Real.sqrt (E + ((L.m : ℝ) * (L.d : ℝ)) / (L.q : ℝ) + ε) :=
      le_sqrt_of_le_of_le_one (by linarith) hT
    have hten : 9 * ε + E ≤
        10 * (E + ((L.m : ℝ) * (L.d : ℝ)) / (L.q : ℝ) + ε) := by linarith
    have hroot : Real.sqrt (9 * ε + E) ≤
        4 * Real.sqrt (E + ((L.m : ℝ) * (L.d : ℝ)) / (L.q : ℝ) + ε) := by
      have hmono : Real.sqrt (9 * ε + E) ≤
          Real.sqrt (10 * (E + ((L.m : ℝ) * (L.d : ℝ)) / (L.q : ℝ) + ε)) :=
        Real.sqrt_le_sqrt hten
      have hsplit : Real.sqrt (10 * (E + ((L.m : ℝ) * (L.d : ℝ)) / (L.q : ℝ) + ε)) =
          Real.sqrt 10 * Real.sqrt (E + ((L.m : ℝ) * (L.d : ℝ)) / (L.q : ℝ) + ε) :=
        Real.sqrt_mul (by norm_num) _
      have hten4 : Real.sqrt (10 : ℝ) ≤ 4 := by
        have h16 : Real.sqrt (16 : ℝ) = 4 := by
          rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
        calc Real.sqrt (10 : ℝ) ≤ Real.sqrt (16 : ℝ) :=
              Real.sqrt_le_sqrt (by norm_num)
          _ = 4 := h16
      have hnn : (0 : ℝ) ≤
          Real.sqrt (E + ((L.m : ℝ) * (L.d : ℝ)) / (L.q : ℝ) + ε) := Real.sqrt_nonneg _
      calc Real.sqrt (9 * ε + E) ≤
            Real.sqrt 10 * Real.sqrt (E + ((L.m : ℝ) * (L.d : ℝ)) / (L.q : ℝ) + ε) := by
              rw [← hsplit]; exact hmono
        _ ≤ 4 * Real.sqrt (E + ((L.m : ℝ) * (L.d : ℝ)) / (L.q : ℝ) + ε) :=
            mul_le_mul_of_nonneg_right hten4 hnn
    linarith [ccode]

end

end MIPStarRE.QPBT
