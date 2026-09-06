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
* `exists_direct_ld_soundness_of_k_eq_one` retains the one-coordinate proof
  used by the seed-indexed soundness transport.

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
This is the established directly indexed auxiliary form described in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`, needed by the Chapter 15
combining argument at paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1288`.

This is a formalization auxiliary assertion, not the source-labelled
`lem:ld-soundness`.  Its proof invokes `MIPStarRE.LDT.Test.mainFormal` and
verifies that theorem's sampling condition `400 M d <= N` at combined dimension
`M = m + k`, using `N = 2560000 M^3 d`.  It does not invoke the tensor-code
theorem used in the source proof of `lem:ld-soundness`.  At seed-indexed
dimension `m`, that route chooses `K = m^3 d` but requires
`K >= 12 m (d + 1)`.  The direct proof therefore discharges neither that bound
nor the claimed game correspondence; both remain open for the printed source route.
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

/-! ## Absorbing the error bound from the low individual degree theorem

The specializations below combine three inputs: polynomial-tuple conclusions
whose error is built from `mainFormalError`, the error bound of
`thm:main-formal` at the auxiliary sampling parameter; the absorption
`exists_directLdTransportConstants` of that error into `deltaLd`; and the
coarse bound `consistencyDefect_heteroKron_le_one`, which closes both the
regime `1 ≤ ε` and the regime where the transport argument exceeds one, in
each of which `deltaLd` is already at least one. -/

/-- Formalization-only scalar step: a quantity dominated by an argument that
is itself at most one is dominated by the square root of that argument.

Support for the transport of `lem:ld-soundness`, blueprint
`ch13_qpbt_test.tex:139-167`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`. -/
theorem le_sqrt_of_le_of_le_one {x T : ℝ} (hxT : x ≤ T) (hT : T ≤ 1) :
    x ≤ Real.sqrt T := by
  rcases le_or_gt x 0 with hx | hx
  · exact le_trans hx (Real.sqrt_nonneg T)
  · have hx2 : x ^ 2 ≤ T := by nlinarith
    calc x = Real.sqrt (x ^ 2) := (Real.sqrt_sq hx.le).symm
      _ ≤ Real.sqrt T := Real.sqrt_le_sqrt hx2

/-- Formalization-only absorption step for the low-degree soundness
transport.  A bipartite consistency defect on a unit state that is at most
`C₀` times the square root of the transport argument

  `mainFormalError (2560000 m³ d) (3 ε) + m d / q + ε`

whenever both `ε` and that argument are at most one is bounded by `deltaLd`
at the constants supplied by `exists_directLdTransportConstants C₀`.

Outside that regime the conclusion is vacuous quantitatively: the defect is
at most one by `consistencyDefect_heteroKron_le_one`, while `deltaLd` is at
least one, either by `one_le_deltaLd_of_one_le_error` when `1 < ε` or because
the square root of an argument exceeding one is itself at least one.
Blueprint `ch13_qpbt_test.tex:139-167`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`. -/
theorem consistencyDefect_le_deltaLd_of_transportBound
    {a b C₀ : ℝ} (ha : 1 ≤ a) (hb : 0 < b) (hC₀ : 1 ≤ C₀)
    (habs : ∀ (D : DirectLdParams) (ε : ℝ), 0 < ε → ε ≤ 1 →
      C₀ * (D.k : ℝ) *
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
    (hbound : ε ≤ 1 →
      Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) +
            ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) + ε ≤ 1 →
        consistencyDefect μ (fun x c => heteroKron ((A x).effect c) 1)
            (fun x c => heteroKron 1 ((B x).effect c)) ψ ≤
          C₀ *
            Real.sqrt
              (Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) +
                ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) + ε)) :
    consistencyDefect μ (fun x c => heteroKron ((A x).effect c) 1)
        (fun x c => heteroKron 1 ((B x).effect c)) ψ ≤
      deltaLd a b ε D.q D.m D.d D.k := by
  have hle1 : consistencyDefect μ (fun x c => heteroKron ((A x).effect c) 1)
      (fun x c => heteroKron 1 ((B x).effect c)) ψ ≤ 1 :=
    consistencyDefect_heteroKron_le_one μ hμ A B ψ hψ
  rcases le_or_gt ε 1 with hε1 | hε1
  · have hk : (1 : ℝ) ≤ (D.k : ℝ) := by exact_mod_cast D.hk
    have hsqrtnn : (0 : ℝ) ≤
        Real.sqrt
          (Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) +
            ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) + ε) := Real.sqrt_nonneg _
    have hstep : consistencyDefect μ (fun x c => heteroKron ((A x).effect c) 1)
        (fun x c => heteroKron 1 ((B x).effect c)) ψ ≤
        C₀ *
          Real.sqrt
            (Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) +
              ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) + ε) := by
      rcases le_or_gt
          (Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) +
            ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) + ε) 1 with hT1 | hT1
      · exact hbound hε1 hT1
      · have hone : (1 : ℝ) ≤
            Real.sqrt
              (Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) +
                ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) + ε) := by
          calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
            _ ≤ _ := Real.sqrt_le_sqrt hT1.le
        nlinarith [mul_nonneg (sub_nonneg.mpr hC₀) (sub_nonneg.mpr hone)]
    calc consistencyDefect μ (fun x c => heteroKron ((A x).effect c) 1)
          (fun x c => heteroKron 1 ((B x).effect c)) ψ
        ≤ C₀ *
            Real.sqrt
              (Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) +
                ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) + ε) := hstep
      _ ≤ C₀ * (D.k : ℝ) *
            Real.sqrt
              (Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) +
                ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) + ε) :=
          mul_le_mul_of_nonneg_right
            (le_mul_of_one_le_right (by linarith) hk) hsqrtnn
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
the resulting error bound into `deltaLd` by
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
  have hmd : (0 : ℝ) ≤ ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) := by positivity
  have hmature : ∀ hT :
      Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) +
          ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) + ε ≤ 1,
      Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) ≤
        Real.sqrt
          (Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) +
            ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) + ε) := by
    intro hT
    exact le_sqrt_of_le_of_le_one (by linarith) hT
  refine ⟨GA, GB, ?_, ?_, ?_⟩
  · refine consistencyDefect_le_deltaLd_of_transportBound ha hb le_rfl habs D ε hε
      (uniformDistribution (Fin D.m → DirectScalarQ D))
      (uniformDistribution_isProbability _)
      (fun u => (S.A (directLdPointQuestionOf D u)).postprocess
        (directLdPointValuesOrZero D))
      (fun u => GB.postprocess (evalDirectPolyTupleAt u)) S.ψ S.ψ_norm ?_
    intro _ hT
    rw [one_mul]
    exact le_trans h1 (hmature hT)
  · refine consistencyDefect_le_deltaLd_of_transportBound ha hb le_rfl habs D ε hε
      (uniformDistribution (Fin D.m → DirectScalarQ D))
      (uniformDistribution_isProbability _)
      (fun u => GA.postprocess (evalDirectPolyTupleAt u))
      (fun u => (S.B (directLdPointQuestionOf D u)).postprocess
        (directLdPointValuesOrZero D)) S.ψ S.ψ_norm ?_
    intro _ hT
    rw [one_mul]
    exact le_trans h2 (hmature hT)
  · refine consistencyDefect_le_deltaLd_of_transportBound ha hb le_rfl habs D ε hε
      (uniformDistribution Unit) (uniformDistribution_isProbability _)
      (fun _ => GA) (fun _ => GB) S.ψ S.ψ_norm ?_
    intro _ hT
    rw [one_mul]
    exact le_trans h3 (hmature hT)

end

end MIPStarRE.QPBT
