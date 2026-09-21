import Mathlib
import Challenge.MIPStarRE.LDT.Preliminaries.Polynomials
import Challenge.MIPStarRE.QPBT.Games.StrategyClasses
import Challenge.MIPStarRE.QPBT.Games.TypedCondLinear
import Challenge.MIPStarRE.QPBT.Test.LowDegreeGame

/-! Challenge mirror of `MIPStarRE/QPBT/Test/LowDegreeGameMeasurements.lean`.

One challenge module per contributing library module, importing the
mirrors of the library modules this one imports.  The partition is
what makes Lean generate the same auxiliary declarations, under the
same names, as the library does. -/

open scoped BigOperators MatrixOrder Matrix ComplexOrder
namespace MIPStarRE.QPBT

-- elaboration context of MIPStarRE/QPBT/Test/LowDegreeGameMeasurements.lean
noncomputable section
open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.Quantum

-- source: MIPStarRE/QPBT/Test/LowDegreeGameMeasurements.lean:39-58  (_private.MIPStarRE.QPBT.Test.LowDegreeGameMeasurements.0.MIPStarRE.QPBT.ldSpaceSplit)
/-- Formalization-only auxiliary equivalence splitting an ambient low-degree
vector into its point, seed, and direction blocks. -/
private def ldSpaceSplit (L : LdParams) :
    LdSpace L ≃ ((Fin L.m → ScalarQ L) × ScalarQ L) × (Fin L.m → ScalarQ L) where
  toFun z := ((LdSpace.point z, LdSpace.seed z), LdSpace.direction z)
  invFun p := fun i =>
    match i with
    | .inl (.inl j) => p.1.1 j
    | .inl (.inr _) => p.1.2
    | .inr j => p.2 j
  left_inv z := by
    funext i
    rcases i with (j | u) | j
    · rfl
    · cases u
      rfl
    · rfl
  right_inv p := by
    obtain ⟨⟨a, b⟩, c⟩ := p
    rfl

-- source: MIPStarRE/QPBT/Test/LowDegreeGameMeasurements.lean:311-318  (MIPStarRE.QPBT.polyFuncFintype)
/-- Bounded multivariate polynomials form a finite set over a finite coefficient
semiring. This is the finite outcome set required by blueprint
`def:ld-meas`, paper
`08_classical_and_quantum_low_degree_tests.tex:394-408`. -/
noncomputable instance polyFuncFintype (m : ℕ) (K : Type*)
    [CommSemiring K] [Fintype K] (d : ℕ) : Fintype ↥(polyFunc m K d) := by
  letI : Finite ↥(polyFunc m K d) := Module.finite_of_finite K
  exact Fintype.ofFinite _

-- source: MIPStarRE/QPBT/Test/LowDegreeGameMeasurements.lean:320-323  (MIPStarRE.QPBT.PolyIndex)
/-- A bounded multivariate polynomial outcome over an arbitrary finite
coefficient semiring. -/
noncomputable abbrev PolyIndex (m : ℕ) (K : Type*) [CommSemiring K]
    [Fintype K] (d : ℕ) := ↥(polyFunc m K d)

-- source: MIPStarRE/QPBT/Test/LowDegreeGameMeasurements.lean:331-339  (MIPStarRE.QPBT.PolyMeasFamily)
/-- The dependent family in `def:ld-meas`: component `i` may
have its own coefficient field, number of variables, and degree bound.
Blueprint `def:ld-meas`, paper
`08_classical_and_quantum_low_degree_tests.tex:394-408`. -/
noncomputable abbrev PolyMeasFamily (k : ℕ) (K : Fin k → Type*)
    [∀ i, CommSemiring (K i)] [∀ i, Fintype (K i)]
    [∀ i, DecidableEq (K i)] (m d : Fin k → ℕ) (ι : Type*)
    [Fintype ι] [DecidableEq ι] :=
  MIPStarRE.Quantum.Measurement ((i : Fin k) → PolyIndex (m i) (K i) (d i)) ι

-- source: MIPStarRE/QPBT/Test/LowDegreeGameMeasurements.lean:341-343  (MIPStarRE.QPBT.PolyTuple)
/-- A simultaneous tuple of `L.k` bounded polynomial representatives. -/
noncomputable abbrev PolyTuple (L : LdParams) :=
  Fin L.k → PolyIndex L.m (ScalarQ L) L.d

-- source: MIPStarRE/QPBT/Test/LowDegreeGameMeasurements.lean:345-348  (MIPStarRE.QPBT.PolyMeasTuple)
/-- The constant-family specialization used by `lem:ld-soundness`. -/
noncomputable abbrev PolyMeasTuple (L : LdParams) (ι : Type*)
    [Fintype ι] [DecidableEq ι] :=
  PolyMeasFamily L.k (fun _ => ScalarQ L) (fun _ => L.m) (fun _ => L.d) ι

-- source: MIPStarRE/QPBT/Test/LowDegreeGameMeasurements.lean:350-353  (MIPStarRE.QPBT.evalPolyTupleAt)
/-- Evaluate every component of a polynomial tuple at a point. -/
def evalPolyTupleAt {L : LdParams} (u : Fin L.m → ScalarQ L)
    (g : PolyTuple L) : Fin L.k → ScalarQ L :=
  fun j => MvPolynomial.eval u (g j).1

-- source: MIPStarRE/QPBT/Test/LowDegreeGameMeasurements.lean:355-361  (MIPStarRE.QPBT.pointSpaceOf)
/-- Embed a geometric point into the ambient coefficient space used by a
point question. -/
def pointSpaceOf (L : LdParams) (u : Fin L.m → ScalarQ L) : LdSpace L :=
  fun i => match i with
  | .inl (.inl j) => u j
  | .inl (.inr _) => 0
  | .inr _ => 0

-- source: MIPStarRE/QPBT/Test/LowDegreeGameMeasurements.lean:363-365  (MIPStarRE.QPBT.ldPointQuestionOf)
/-- The typed low-degree point question associated with `u`. -/
def ldPointQuestionOf (L : LdParams) (u : Fin L.m → ScalarQ L) : LdQuestion L :=
  (.point, pointSpaceOf L u)

-- source: MIPStarRE/QPBT/Test/LowDegreeGameMeasurements.lean:367-373  (MIPStarRE.QPBT.ldPointValuesOrZero)
/-- Read the point component of a low-degree answer, sending answers of the
wrong form to the fixed zero tuple. This total relabeling turns the strategy's
answer measurement into the point POVM used by `lem:ld-soundness`. -/
def ldPointValuesOrZero (L : LdParams) : LdAnswer L → Fin L.k → ScalarQ L
  | .pointVals values => values
  | .alinePolys _ => 0
  | .dlinePolys _ => 0

-- source: MIPStarRE/QPBT/Test/LowDegreeGameMeasurements.lean:375-380  (MIPStarRE.QPBT.deltaLd)
/-- The quantitative error function in `lem:ld-soundness`.  Its argument order
is `(a, b, ε, q, m, d, k)`. -/
noncomputable def deltaLd (a b ε : ℝ) (q m d k : ℕ) : ℝ :=
  a * Real.rpow (((d * m * k : ℕ) : ℝ)) a *
    (Real.rpow ε b + Real.rpow (q : ℝ) (-b) +
      Real.rpow 2 (-(b * ((m * d : ℕ) : ℝ))))
end  -- module scope
end MIPStarRE.QPBT
