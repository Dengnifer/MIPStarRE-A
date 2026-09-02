import MIPStarRE.QPBT.Games.DistributionAux
import MIPStarRE.QPBT.Test.LowDegreeGame
import MIPStarRE.LDT.Preliminaries.Polynomials
import Mathlib.Data.Finsupp.Fintype

/-!
# Lines, bounded line polynomials, and line-point distributions

This file provides the seed-bearing line descriptions and coefficient-list
polynomials shared by the observable and combining chapters.  It also realizes
the line-point distribution directly from the conditionally linear sampler.

The bounded multivariate polynomial index remains the actual Mathlib
`polyFunc` subtype.  Its finite instance is derived by injecting it into the
finite table of coefficients with coordinatewise-bounded exponents.

## References

The line and bounded-polynomial interface is `def:ideg-deg-polynomials` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:51-62`.  The line-point sampler
is `def:line-point-dist` in `blueprint/src/chapter/ch13_qpbt_test.tex`, used in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:882-1019`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries

noncomputable section

/-- The two presentations of lines used by the low-degree question sampler. -/
inductive LineKind where
  | axis
  | diagonal
  deriving DecidableEq, Fintype

/-- A line description retains the source seed as well as the canonical base
point and raw direction data.  Retaining `seed` is essential for the restricted
line distributions in the combining argument. -/
structure LineDesc (L : LdParams) where
  kind : LineKind
  base : Fin L.m → ScalarQ L
  seed : ScalarQ L
  rawDirection : Fin L.m → ScalarQ L
  deriving DecidableEq

/-- The geometric direction represented by a seed-bearing line description. -/
def LineDesc.direction {L : LdParams} (line : LineDesc L) :
    Fin L.m → ScalarQ L :=
  match line.kind with
  | .axis => coordinateDirection (chiIndex L line.seed)
  | .diagonal => prefixProjection (chiIndex L line.seed) line.rawDirection

/-- The point set represented by a seed-bearing line description. -/
def LineDesc.pointSet {L : LdParams} (line : LineDesc L) :
    Set (Fin L.m → ScalarQ L) :=
  linePoints line.base line.direction

/-- Coefficient-list representation of a univariate polynomial of degree at
most `c` over the scalar field of `L`. -/
abbrev DegPoly (L : LdParams) (c : ℕ) := Fin (c + 1) → ScalarQ L

/-- Evaluate a bounded coefficient-list polynomial. -/
def degPolyEval {L : LdParams} {c : ℕ}
    (f : DegPoly L c) (t : ScalarQ L) : ScalarQ L :=
  ∑ i : Fin (c + 1), f i * t ^ i.val

/-- Extend a coefficient list by zero from degree bound `c` to `c'`. -/
def DegPoly.padTo {L : LdParams} {c c' : ℕ} (_h : c ≤ c')
    (f : DegPoly L c) : DegPoly L c' :=
  fun i =>
    if hi : i.val < c + 1 then f ⟨i.val, hi⟩ else 0

/-- A line polynomial evaluates to `a` at `u` when `u` has a line parameter
and every such parameter gives the same value.  The universal clause handles
the zero-direction presentation without choosing a sentinel parameter. -/
def EvaluatesTo {L : LdParams} {c : ℕ} (line : LineDesc L)
    (f : DegPoly L c) (u : Fin L.m → ScalarQ L) (a : ScalarQ L) : Prop :=
  (∃ t : ScalarQ L, u = line.base + t • line.direction) ∧
    ∀ t : ScalarQ L, u = line.base + t • line.direction → degPolyEval f t = a

/-- Evaluate a line polynomial at a point, returning `none` precisely when the
point does not determine an evaluation.  The `Option` completion is the
paper's bottom outcome for malformed or nonincident answers. -/
noncomputable def evalOpt {L : LdParams} {c : ℕ} (line : LineDesc L)
    (u : Fin L.m → ScalarQ L) (f : DegPoly L c) : Option (ScalarQ L) := by
  classical
  exact if h : ∃ a : ScalarQ L, EvaluatesTo line f u a then
    some (Classical.choose h)
  else none

/-- Convert an axis-line CL output to its seed-bearing presentation. -/
def aLineDescOf (L : LdParams) (line : LdSpace L) : LineDesc L where
  kind := .axis
  base := line.point
  seed := line.seed
  rawDirection := 0

/-- Convert a diagonal-line CL output to its seed-bearing presentation. -/
def dLineDescOf (L : LdParams) (line : LdSpace L) : LineDesc L where
  kind := .diagonal
  base := line.point
  seed := line.seed
  rawDirection := line.direction

/-- The affine-line/point component of the low-degree line-point sampler. -/
noncomputable def aLinePointDist (L : LdParams) :
    Distribution (LineDesc L × (Fin L.m → ScalarQ L)) :=
  (clDistribution (ldALineCL L) (ldPointCL L)).map fun sample =>
    (aLineDescOf L sample.1, LdSpace.point sample.2)

/-- The diagonal-line/point component of the low-degree line-point sampler. -/
noncomputable def dLinePointDist (L : LdParams) :
    Distribution (LineDesc L × (Fin L.m → ScalarQ L)) :=
  (clDistribution (ldDLineCL L) (ldPointCL L)).map fun sample =>
    (dLineDescOf L sample.1, LdSpace.point sample.2)

/-- The equal mixture of affine and diagonal line-point samples.  The
parameter record is explicit, so the same definition works at every dimension. -/
noncomputable def linePointDist (L : LdParams) :
    Distribution (LineDesc L × (Fin L.m → ScalarQ L)) :=
  Distribution.mixture (uniformDistribution Bool) fun chooseAxis =>
    if chooseAxis then aLinePointDist L else dLinePointDist L

/-- The affine line-point component has total probability one. -/
theorem aLinePointDist_isProbability (L : LdParams) :
    (aLinePointDist L).IsProbability := by
  sorry

/-- The diagonal line-point component has total probability one. -/
theorem dLinePointDist_isProbability (L : LdParams) :
    (dLinePointDist L).IsProbability := by
  sorry

/-- The line-point mixture has total probability one. -/
theorem linePointDist_isProbability (L : LdParams) :
    (linePointDist L).IsProbability := by
  sorry

/-- Convert a bounded exponent table to the finitely supported exponent vector
used by `MvPolynomial.coeff`. -/
def boundedExponent {m d : ℕ} (e : Fin m → Fin (d + 1)) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => (e i).val

/-- The finite coefficient table of a low-individual-degree polynomial. -/
def polyFuncCoeffTable {m d : ℕ} {K : Type*} [CommSemiring K]
    (p : ↥(polyFunc m K d)) : (Fin m → Fin (d + 1)) → K :=
  fun e => MvPolynomial.coeff (boundedExponent e) p.1

/-- Bounded coefficient tables separate low-individual-degree polynomial
representatives.  This is a formalization-only finiteness lemma. -/
theorem polyFuncCoeffTable_injective {m d : ℕ} {K : Type*}
    [CommSemiring K] : Function.Injective
      (polyFuncCoeffTable : ↥(polyFunc m K d) → (Fin m → Fin (d + 1)) → K) := by
  intro p q hpq
  apply Subtype.ext
  apply MvPolynomial.ext
  intro exponent
  by_cases hbounded : ∀ i : Fin m, exponent i ≤ d
  · let e : Fin m → Fin (d + 1) := fun i => ⟨exponent i, Nat.lt_succ_iff.mpr (hbounded i)⟩
    have hexponent : boundedExponent e = exponent := by
      ext i
      simp [boundedExponent, e]
    have hcoeff := congrFun hpq e
    simpa [polyFuncCoeffTable, hexponent] using hcoeff
  · simp only [not_forall, not_le] at hbounded
    obtain ⟨i, hi⟩ := hbounded
    have hpzero : MvPolynomial.coeff exponent p.1 = 0 := by
      by_contra hpne
      have hmem : exponent ∈ p.1.support := MvPolynomial.mem_support_iff.mpr hpne
      have hle := (MvPolynomial.mem_restrictDegree
        (σ := Fin m) (R := K) p.1 d).mp p.2 exponent hmem i
      omega
    have hqzero : MvPolynomial.coeff exponent q.1 = 0 := by
      by_contra hqne
      have hmem : exponent ∈ q.1.support := MvPolynomial.mem_support_iff.mpr hqne
      have hle := (MvPolynomial.mem_restrictDegree
        (σ := Fin m) (R := K) q.1 d).mp q.2 exponent hmem i
      omega
    rw [hpzero, hqzero]

/-- The actual bounded `polyFunc` subtype is finite over a finite coefficient
semiring. -/
noncomputable instance polyFuncFintype (m d : ℕ) (K : Type*)
    [CommSemiring K] [Fintype K] [DecidableEq K] :
    Fintype ↥(polyFunc m K d) :=
  Fintype.ofInjective polyFuncCoeffTable polyFuncCoeffTable_injective

end

end MIPStarRE.QPBT
