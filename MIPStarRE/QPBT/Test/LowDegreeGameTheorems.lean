import MIPStarRE.QPBT.Games.Consistency
import MIPStarRE.QPBT.Games.StrategyClasses
import MIPStarRE.QPBT.Observables.LineDefs

/-!
# Low-degree game interfaces

This file supplies the finite polynomial-measurement index and the imported
soundness provider required by the QPBT combining argument.  Polynomial
outcomes are the actual bounded `polyFunc` representatives.

## References

The source-facing declarations are `def:ld-meas` and `lem:ld-soundness` in
`blueprint/src/chapter/ch13_qpbt_test.tex:112-178`.  Their paper origin is
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:392-480`.
The imported-provider gap is documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.Quantum

noncomputable section

/-- The bounded multivariate polynomial outcome used by the low-degree
soundness theorem. -/
abbrev PolyIndex (L : LdParams) := ↥(polyFunc L.m (ScalarQ L) L.d)

/-- A simultaneous tuple of `L.k` bounded polynomial representatives. -/
abbrev PolyTuple (L : LdParams) := Fin L.k → PolyIndex L

/-- A complete POVM indexed by simultaneous bounded polynomial outcomes. -/
abbrev PolyMeasTuple (L : LdParams) (ι : Type*)
    [Fintype ι] [DecidableEq ι] := Measurement (PolyTuple L) ι

/-- Evaluate every component of a polynomial tuple at a point. -/
def evalPolyTupleAt {L : LdParams} (u : Fin L.m → ScalarQ L)
    (g : PolyTuple L) : Fin L.k → ScalarQ L :=
  fun j => MvPolynomial.eval u (g j).1

/-- Completed evaluation used to post-process a polynomial measurement. -/
def evalPolyTupleAtOpt {L : LdParams} (u : Fin L.m → ScalarQ L)
    (g : PolyTuple L) : Option (Fin L.k → ScalarQ L) :=
  some (evalPolyTupleAt u g)

/-- Extract a point-value tuple from a low-degree answer, using `none` for an
answer of the wrong constructor. -/
def pointAnswerOpt {L : LdParams} (a : LdAnswer L) :
    Option (Fin L.k → ScalarQ L) :=
  match a with
  | .pointVals values => some values
  | _ => none

/-- Embed a geometric point into the ambient coefficient space used by a
point question.  This is formalization-only question infrastructure. -/
def pointSpaceOf (L : LdParams) (u : Fin L.m → ScalarQ L) : LdSpace L :=
  fun i => match i with
  | .inl (.inl j) => u j
  | .inl (.inr _) => 0
  | .inr _ => 0

/-- The typed low-degree point question associated with `u`. -/
def ldPointQuestionOf (L : LdParams) (u : Fin L.m → ScalarQ L) : LdQuestion L :=
  (.point, pointSpaceOf L u)

/-- Alice's point measurement, completed by an explicit `none` outcome for
answers of the wrong constructor. -/
noncomputable def pointMeasurementA {L : LdParams} (S : Strategy (ldGame L))
    (u : Fin L.m → ScalarQ L) :
    Measurement (Option (Fin L.k → ScalarQ L)) S.ιA :=
  (S.A (ldPointQuestionOf L u)).postprocess pointAnswerOpt

/-- Bob's completed point measurement. -/
noncomputable def pointMeasurementB {L : LdParams} (S : Strategy (ldGame L))
    (u : Fin L.m → ScalarQ L) :
    Measurement (Option (Fin L.k → ScalarQ L)) S.ιB :=
  (S.B (ldPointQuestionOf L u)).postprocess pointAnswerOpt

/-- The quantitative error function in `lem:ld-soundness`.  Its argument order
is `(a, b, ε, q, m, d, k)`. -/
noncomputable def deltaLd (a b ε : ℝ) (q m d k : ℕ) : ℝ :=
  a * Real.rpow (((d * m * k : ℕ) : ℝ)) a *
    (Real.rpow ε b + Real.rpow (q : ℝ) (-b) +
      Real.rpow 2 (-(b * ((m * d : ℕ) : ℝ))))

/-- Quantum soundness of the simultaneous classical low individual degree
test (`lem:ld-soundness`, blueprint lines 125--178; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:392-480`).

The `Option` completion makes malformed point answers explicit on both sides
of the first two relations.  It adds no hypothesis and agrees with the game's
rejection convention.

**Unfaithful:** This imported proof remains open because the asserted game
correspondence and the provider's auxiliary-parameter bound have not been
derived.  They are documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.  Elimination: prove the
typed-game reduction and repair the parameter choice, then instantiate the
low-individual-degree soundness provider.
-/
theorem exists_ld_soundness :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b ≤ 1 ∧
      ∀ (L : LdParams) (ε : ℝ), 0 < ε →
        ∀ S : Strategy (ldGame L), S.IsProjective → 1 - ε ≤ S.value →
          ∃ GA : PolyMeasTuple L S.ιA, ∃ GB : PolyMeasTuple L S.ιB,
            consistencyDefect (uniformDistribution (Fin L.m → ScalarQ L))
                (fun u outcome =>
                  heteroKron ((pointMeasurementA S u).effect outcome) 1)
                (fun u outcome =>
                  heteroKron 1
                    ((GB.postprocess (evalPolyTupleAtOpt u)).effect outcome))
                S.ψ ≤ deltaLd a b ε L.q L.m L.d L.k ∧
            consistencyDefect (uniformDistribution (Fin L.m → ScalarQ L))
                (fun u outcome =>
                  heteroKron
                    ((GA.postprocess (evalPolyTupleAtOpt u)).effect outcome) 1)
                (fun u outcome =>
                  heteroKron 1 ((pointMeasurementB S u).effect outcome))
                S.ψ ≤ deltaLd a b ε L.q L.m L.d L.k ∧
            consistencyDefect (uniformDistribution Unit)
                (fun _ g => heteroKron (GA.effect g) 1)
                (fun _ g => heteroKron 1 (GB.effect g))
                S.ψ ≤ deltaLd a b ε L.q L.m L.d L.k := by
  sorry

end

end MIPStarRE.QPBT
