import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Simultaneous

/-!
# Soundness for the directly indexed low-degree game

This module isolates the quantum soundness obligation for the directly indexed
low-degree game and proves the specialization to simultaneity parameter `1`,
which is the case that the Chapter 15 combining argument instantiates.

## Main results

* `exists_direct_ld_soundness` is the obligation for arbitrary simultaneity
  parameter.  Its proof is open: the coordinatewise route is refuted in
  `docs/paper-gaps/qpbt_ld-simultaneous-sandwich.tex`, and the source's own
  route is the combining reduction of the NEEXP paper, a separate packet.
* `exists_direct_ld_soundness_of_k_eq_one` proves the same three consistency
  conclusions, with universal constants of the same shape, for `D.k = 1`.

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

/-- Quantum soundness obligation for the directly indexed low-degree game.
This is the repaired import form proposed in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`, needed by the Chapter 15
combining argument at paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1288`.

This is a formalization auxiliary assertion, not the source-labelled
`lem:ld-soundness`.  Its proof must establish the game-correspondence and
auxiliary-parameter bounds catalogued in the cited gap note; neither is hidden
as a hypothesis here.

The remaining obligation for arbitrary `D.k` is the construction of
simultaneous polynomial measurements.  The coordinatewise route through the
palindromic sandwich of `lem:ld-sandwich` is refuted for `D.k ≥ 2` by the
explicit example of `docs/paper-gaps/qpbt_ld-simultaneous-sandwich.tex`; the
source obtains general `k` from one application of the `k = 1` theorem in
dimension `m + k` by the combining reduction of Theorem 4.43 in
`references/neexp-paper/05_quantum_preliminaries.tex:1409-1503`, which is the
separate packet tracked by issue #210.  For `D.k = 1` the present conclusions
are proved in `exists_direct_ld_soundness_of_k_eq_one` below. -/
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
  sorry

/-! ## Absorbing the mature error into the error function of `lem:ld-soundness`

The specialization below combines three inputs: the polynomial-tuple
conclusions for `D.k = 1`, whose error is the mature error
`mainFormalError` of `thm:main-formal` at the auxiliary sampling parameter;
the absorption `exists_directLdTransportConstants` of that error into
`deltaLd`, applied with the trivial constant `C₀ = 1` because for `k = 1` the
tuple measurements are the coordinate measurements themselves and no sandwich
is formed; and the coarse bound `consistencyDefect_heteroKron_le_one`, which
closes the regime `1 ≤ ε` where `deltaLd` is at least one. -/

/-- Formalization-only absorption step: a bipartite consistency defect on a
unit state bounded by the mature error of `thm:main-formal` at the auxiliary
sampling parameter is bounded by `deltaLd` at the transport constants.

In the regime `0 < ε ≤ 1` the defect is at most the minimum of the mature
error and one, hence at most the square root of the transport argument, which
`exists_directLdTransportConstants` absorbs at `C₀ = 1`; in the regime `1 < ε`
the defect is at most one and `deltaLd` is at least one.  Blueprint
`ch13_qpbt_test.tex:139-167`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`. -/
private theorem consistencyDefect_le_deltaLd_of_mainFormalError
    {a b : ℝ} (ha : 1 ≤ a) (hb : 0 < b)
    (habs : ∀ (D : DirectLdParams) (ε : ℝ), 0 < ε → ε ≤ 1 →
      1 * (D.k : ℝ) *
          Real.sqrt
            (Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) +
              ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) + ε) ≤
        deltaLd a b ε D.q D.m D.d D.k)
    (D : DirectLdParams) (ε : ℝ) (hε : 0 < ε)
    {X α ιA ιB : Type*} [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : Distribution X) (hμ : μ.IsProbability)
    (A : X → Quantum.Measurement α ιA) (B : X → Quantum.Measurement α ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (hψ : ‖ψ‖ = 1)
    (hbound : consistencyDefect μ (fun x c => heteroKron ((A x).effect c) 1)
        (fun x c => heteroKron 1 ((B x).effect c)) ψ ≤
      Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε)) :
    consistencyDefect μ (fun x c => heteroKron ((A x).effect c) 1)
        (fun x c => heteroKron 1 ((B x).effect c)) ψ ≤
      deltaLd a b ε D.q D.m D.d D.k := by
  have hle1 : consistencyDefect μ (fun x c => heteroKron ((A x).effect c) 1)
      (fun x c => heteroKron 1 ((B x).effect c)) ψ ≤ 1 :=
    consistencyDefect_heteroKron_le_one μ hμ A B ψ hψ
  rcases le_or_gt ε 1 with hε1 | hε1
  · have hE : 0 ≤
        Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) := by
      rw [Test.mainFormalError_eq_envelope]
      exact mul_nonneg (by positivity)
        (Test.mainFormalEnvelope_nonneg _ _ _ (by linarith))
    have hmd : (0 : ℝ) ≤ ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) := by positivity
    have hT : 0 ≤
        Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) +
          ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) + ε := by linarith
    have hsqrt : consistencyDefect μ (fun x c => heteroKron ((A x).effect c) 1)
        (fun x c => heteroKron 1 ((B x).effect c)) ψ ≤
        Real.sqrt
          (Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) +
            ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) + ε) := by
      rcases le_or_gt
          (Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε))
          1 with hEle | hEgt
      · have hsq :
            Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) ^ 2 ≤
              Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) +
                ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) + ε := by nlinarith
        have hstep :
            Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) ≤
              Real.sqrt
                (Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) +
                  ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) + ε) := by
          calc Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε)
              = Real.sqrt
                  (Test.mainFormalError D.toLDTParameters
                    (directLdAuxParameter D) (3 * ε) ^ 2) := (Real.sqrt_sq hE).symm
            _ ≤ _ := Real.sqrt_le_sqrt hsq
        linarith
      · have hone : (1 : ℝ) ≤
            Real.sqrt
              (Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) +
                ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) + ε) := by
          calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
            _ ≤ _ := Real.sqrt_le_sqrt (by linarith)
        linarith
    have hk : (1 : ℝ) ≤ (D.k : ℝ) := by exact_mod_cast D.hk
    have hsqrtnn : (0 : ℝ) ≤
        Real.sqrt
          (Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) +
            ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) + ε) := Real.sqrt_nonneg _
    calc consistencyDefect μ (fun x c => heteroKron ((A x).effect c) 1)
          (fun x c => heteroKron 1 ((B x).effect c)) ψ
        ≤ Real.sqrt
            (Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) +
              ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) + ε) := hsqrt
      _ ≤ 1 * (D.k : ℝ) *
            Real.sqrt
              (Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) +
                ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) + ε) := by nlinarith
      _ ≤ deltaLd a b ε D.q D.m D.d D.k := habs D ε hε hε1
  · have hone : (1 : ℝ) ≤ deltaLd a b ε D.q D.m D.d D.k :=
      one_le_deltaLd_of_one_le_error ha hb.le hε1.le D.hm D.hd D.hk
    linarith

/-- Quantum soundness of the directly indexed low-degree game for simultaneity
parameter `1`: the conclusions of `exists_direct_ld_soundness`, with universal
constants of the same shape, under the hypothesis `D.k = 1`.

The proof reads the coordinate conclusions of the low individual degree
theorem as one-coordinate tuples
(`exists_directSimultaneousPolynomialMeasurements_of_k_eq_one`) and absorbs
the resulting mature error into `deltaLd` by
`exists_directLdTransportConstants` at the constant `C₀ = 1`, no sandwich
being formed when there is one coordinate.  This is the case instantiated by
the Chapter 15 combining argument at paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1288`;
`docs/paper-gaps/qpbt_ld-simultaneous-sandwich.tex` records why arbitrary
`D.k` needs the combining reduction instead.  Blueprint
`ch13_qpbt_test.tex:139-167`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`. -/
theorem exists_direct_ld_soundness_of_k_eq_one :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b ≤ 1 ∧
      ∀ (D : DirectLdParams) (ε : ℝ), D.k = 1 → 0 < ε →
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
  obtain ⟨a, b, ha, hb, hb1, habs⟩ := exists_directLdTransportConstants 1 le_rfl
  refine ⟨a, b, ha, hb, hb1, ?_⟩
  intro D ε hk hε S hS hwin
  obtain ⟨GA, GB, h1, h2, h3⟩ :=
    exists_directSimultaneousPolynomialMeasurements_of_k_eq_one D hk S hS ε hwin
  refine ⟨GA, GB, ?_, ?_, ?_⟩
  · exact consistencyDefect_le_deltaLd_of_mainFormalError ha hb habs D ε hε
      (uniformDistribution (Fin D.m → DirectScalarQ D))
      (uniformDistribution_isProbability _)
      (fun u => (S.A (directLdPointQuestionOf D u)).postprocess
        (directLdPointValuesOrZero D))
      (fun u => GB.postprocess (evalDirectPolyTupleAt u)) S.ψ S.ψ_norm h1
  · exact consistencyDefect_le_deltaLd_of_mainFormalError ha hb habs D ε hε
      (uniformDistribution (Fin D.m → DirectScalarQ D))
      (uniformDistribution_isProbability _)
      (fun u => GA.postprocess (evalDirectPolyTupleAt u))
      (fun u => (S.B (directLdPointQuestionOf D u)).postprocess
        (directLdPointValuesOrZero D)) S.ψ S.ψ_norm h2
  · exact consistencyDefect_le_deltaLd_of_mainFormalError ha hb habs D ε hε
      (uniformDistribution Unit) (uniformDistribution_isProbability _)
      (fun _ => GA) (fun _ => GB) S.ψ S.ψ_norm h3

end

end MIPStarRE.QPBT
