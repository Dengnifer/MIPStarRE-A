import MIPStarRE.QPBT.Games.Consistency
import MIPStarRE.QPBT.Games.StrategyClasses
import MIPStarRE.QPBT.Games.TypedCondLinear
import MIPStarRE.QPBT.Observables.LineDefs

/-!
# Low-degree game interfaces

This file defines the finite polynomial-measurement index and states the
low-degree soundness theorem used by the QPBT combining argument. Polynomial
outcomes are bounded multivariate polynomials.

## References

The source-facing declarations are `def:ld-meas` and `lem:ld-soundness` in
`blueprint/src/chapter/ch13_qpbt_test.tex:63-160`. Their paper origin is
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:243-287,392-480`.
The dimension-divisibility hypothesis is documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.Quantum

noncomputable section

/-- The positive dimension in `LdParams` supplies the finite coordinate type
used by the uniform axis and prefix-index marginals. -/
instance (L : LdParams) : Nonempty (Fin L.m) :=
  ⟨⟨0, lt_of_lt_of_le Nat.zero_lt_one L.hm⟩⟩

/-- `lem:alnf`: the point and axis-index marginals of the axis line-point
distribution are uniform. Blueprint `ch13_qpbt_test.tex:63-68`, paper
`08_classical_and_quantum_low_degree_tests.tex:243-257`. -/
theorem aLinePointDist_point_marginal_uniform (L : LdParams) :
    (aLinePointDist L).map Prod.snd =
        uniformDistribution (Fin L.m → ScalarQ L) ∧
      (aLinePointDist L).map (fun sample => chiIndex L sample.1.seed) =
        uniformDistribution (Fin L.m) := by
  sorry

/-- The incidence conclusion of `lem:alnf`, blueprint
`ch13_qpbt_test.tex:63-68`, paper
`08_classical_and_quantum_low_degree_tests.tex:243-257`. -/
theorem aLinePointDist_mem_line (L : LdParams) :
    ∀ sample ∈ (aLinePointDist L).support, sample.2 ∈ sample.1.pointSet := by
  sorry

/-- `lem:dlnf`: the point and prefix-index marginals of the diagonal
line-point distribution are uniform. Blueprint `ch13_qpbt_test.tex:74-79`,
paper `08_classical_and_quantum_low_degree_tests.tex:261-272`. -/
theorem dLinePointDist_point_marginal_uniform (L : LdParams) :
    (dLinePointDist L).map Prod.snd =
        uniformDistribution (Fin L.m → ScalarQ L) ∧
      (dLinePointDist L).map (fun sample => chiIndex L sample.1.seed) =
        uniformDistribution (Fin L.m) := by
  sorry

/-- The incidence conclusion of `lem:dlnf`, blueprint
`ch13_qpbt_test.tex:74-79`, paper
`08_classical_and_quantum_low_degree_tests.tex:261-272`. -/
theorem dLinePointDist_mem_line (L : LdParams) :
    ∀ sample ∈ (dLinePointDist L).support, sample.2 ∈ sample.1.pointSet := by
  sorry

/-- The diagonal direction in every sampled description has the prefix-zero
property of `lem:dlnf`, blueprint `ch13_qpbt_test.tex:74-79`, paper
`08_classical_and_quantum_low_degree_tests.tex:261-272`. -/
theorem dLinePointDist_prefix_zero (L : LdParams) :
    ∀ sample ∈ (dLinePointDist L).support,
      ∀ j : Fin L.m, j.val < (chiIndex L sample.1.seed).val →
        sample.1.direction j = 0 := by
  sorry

/-- The low-degree question sampler is the typed conditionally linear
distribution on the complete type graph. This identifies the sampler with
`def:typed-cl-distributions`; blueprint
`ch12_qpbt_games.tex:624-629`, paper
`references/qpbt-paper/07_types.tex:84-94`. -/
theorem ldQuestionDistribution_eq_typedCL (L : LdParams) :
    ldQuestionDistribution L =
      typedCLDistribution (Finset.univ : Finset (Sym2 LdType)) (by simp)
        (ldCL L) (ldCL L) := by
  sorry

/-- Bounded multivariate polynomials form a finite set over a finite coefficient
semiring. This is the finite outcome set required by `def:ld-meas`,
blueprint `ch13_qpbt_test.tex:124-129`, paper
`08_classical_and_quantum_low_degree_tests.tex:394-408`. -/
noncomputable instance polyFuncFintype (m : ℕ) (K : Type*)
    [CommSemiring K] [Fintype K] (d : ℕ) : Fintype ↥(polyFunc m K d) := by
  letI : Finite ↥(polyFunc m K d) := Module.finite_of_finite K
  exact Fintype.ofFinite _

/-- A bounded multivariate polynomial outcome over an arbitrary finite
coefficient semiring. -/
noncomputable abbrev PolyIndex (m : ℕ) (K : Type*) [CommSemiring K]
    [Fintype K] (d : ℕ) := ↥(polyFunc m K d)

/-- A POVM indexed by one bounded multivariate polynomial. -/
noncomputable abbrev PolyMeas (m : ℕ) (K : Type*) [CommSemiring K]
    [Fintype K] [DecidableEq K] (d : ℕ) (ι : Type*)
    [Fintype ι] [DecidableEq ι] := Measurement (PolyIndex m K d) ι

/-- The dependent family in `def:ld-meas`: component `i` may
have its own coefficient field, number of variables, and degree bound.
Blueprint `ch13_qpbt_test.tex:124-129`, paper
`08_classical_and_quantum_low_degree_tests.tex:394-408`. -/
noncomputable abbrev PolyMeasFamily (k : ℕ) (K : Fin k → Type*)
    [∀ i, CommSemiring (K i)] [∀ i, Fintype (K i)]
    [∀ i, DecidableEq (K i)] (m d : Fin k → ℕ) (ι : Type*)
    [Fintype ι] [DecidableEq ι] :=
  Measurement ((i : Fin k) → PolyIndex (m i) (K i) (d i)) ι

/-- A simultaneous tuple of `L.k` bounded polynomial representatives. -/
noncomputable abbrev PolyTuple (L : LdParams) :=
  Fin L.k → PolyIndex L.m (ScalarQ L) L.d

/-- The constant-family specialization used by `lem:ld-soundness`. -/
noncomputable abbrev PolyMeasTuple (L : LdParams) (ι : Type*)
    [Fintype ι] [DecidableEq ι] :=
  PolyMeasFamily L.k (fun _ => ScalarQ L) (fun _ => L.m) (fun _ => L.d) ι

/-- Evaluate every component of a polynomial tuple at a point. -/
def evalPolyTupleAt {L : LdParams} (u : Fin L.m → ScalarQ L)
    (g : PolyTuple L) : Fin L.k → ScalarQ L :=
  fun j => MvPolynomial.eval u (g j).1

/-- Embed a geometric point into the ambient coefficient space used by a
point question. -/
def pointSpaceOf (L : LdParams) (u : Fin L.m → ScalarQ L) : LdSpace L :=
  fun i => match i with
  | .inl (.inl j) => u j
  | .inl (.inr _) => 0
  | .inr _ => 0

/-- The typed low-degree point question associated with `u`. -/
def ldPointQuestionOf (L : LdParams) (u : Fin L.m → ScalarQ L) : LdQuestion L :=
  (.point, pointSpaceOf L u)

/-- Read the point component of a low-degree answer, sending answers of the
wrong form to the fixed zero tuple. This total relabeling turns the strategy's
answer measurement into the point POVM used by `lem:ld-soundness`. -/
def ldPointValuesOrZero (L : LdParams) : LdAnswer L → Fin L.k → ScalarQ L
  | .pointVals values => values
  | .alinePolys _ => 0
  | .dlinePolys _ => 0

/-- The quantitative error function in `lem:ld-soundness`.  Its argument order
is `(a, b, ε, q, m, d, k)`. -/
noncomputable def deltaLd (a b ε : ℝ) (q m d k : ℕ) : ℝ :=
  a * Real.rpow (((d * m * k : ℕ) : ℝ)) a *
    (Real.rpow ε b + Real.rpow (q : ℝ) (-b) +
      Real.rpow 2 (-(b * ((m * d : ℕ) : ℝ))))

/-- Quantum soundness of the simultaneous classical low individual degree
test (`lem:ld-soundness`, blueprint lines 135--160; paper theorem and proof
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`).

The first two consistency bounds compare the point-answer postprocessing of the
strategy with evaluations of the polynomial measurements. Answers of the wrong
form are folded into the zero tuple so that the point family remains a POVM.

The source reduction still requires proofs of the claimed game correspondence
and of the auxiliary parameter bound. These two open facts are detailed in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` and
`rem:ld-soundness-provider`, and are tracked by issue #16. -/
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
  sorry

end

end MIPStarRE.QPBT
