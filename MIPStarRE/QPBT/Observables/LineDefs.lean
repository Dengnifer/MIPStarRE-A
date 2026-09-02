import MIPStarRE.QPBT.Games.DistributionAux
import MIPStarRE.QPBT.Test.LowDegreeGame
import MIPStarRE.LDT.Preliminaries.Polynomials

/-!
# Lines, bounded line polynomials, and line-point distributions

This file provides the seed-bearing line descriptions and coefficient-list
polynomials shared by the observable and combining chapters.  It also realizes
the line-point distribution directly from the conditionally linear sampler.

The bounded multivariate polynomial index remains the actual Mathlib
`polyFunc` subtype; its finite instance is supplied beside the measurement
aliases in `Test.LowDegreeGameTheorems`.

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

/-- Applying the canonical line-representative projection twice has the same
effect as applying it once. This is the fixed-point fact used by the tagged
carrier below. -/
theorem lineRepMap_apply_self {K : Type*} [Field K] {m : ℕ}
    (v u : Fin m → K) :
    lineRepMap v (lineRepMap v u) = lineRepMap v u := by
  simp [lineRepMap, canonicalProjOfKernel, LinearMap.comp_apply]

/-- The two presentations of lines used by the low-degree question sampler. -/
inductive LineKind where
  | axis
  | diagonal
  deriving DecidableEq, Fintype

/-- The tagged canonical carrier of `def:line-point-dist`, blueprint
`ch13_qpbt_test.tex:180-186`, paper
`08_classical_and_quantum_low_degree_tests.tex:174-186`.

An axis description stores its canonical base and seed. A diagonal description
stores only the projected direction, together with its prefix-zero invariant.
Both constructors carry the assertion that their base is fixed by the
appropriate `lineRepMap`. -/
inductive LineDesc (L : LdParams) where
  | axis (base : Fin L.m → ScalarQ L) (seed : ScalarQ L)
      (baseFixed : lineRepMap (coordinateDirection (chiIndex L seed)) base = base)
  | diagonal (base : Fin L.m → ScalarQ L) (seed : ScalarQ L)
      (direction : Fin L.m → ScalarQ L)
      (baseFixed : lineRepMap direction base = base)
      (prefixZero : ∀ j : Fin L.m, j.val < (chiIndex L seed).val → direction j = 0)
  deriving DecidableEq

/-- The tag of a canonical line description. -/
def LineDesc.kind {L : LdParams} : LineDesc L → LineKind
  | .axis _ _ _ => .axis
  | .diagonal _ _ _ _ _ => .diagonal

/-- The seed retained by a canonical line description. -/
def LineDesc.seed {L : LdParams} : LineDesc L → ScalarQ L
  | .axis _ seed _ => seed
  | .diagonal _ seed _ _ _ => seed

/-- The canonical base stored by a line description. -/
def LineDesc.base {L : LdParams} : LineDesc L → Fin L.m → ScalarQ L
  | .axis base _ _ => base
  | .diagonal base _ _ _ _ => base

/-- The geometric direction represented by a canonical line description.
Diagonal constructors already store the projected data, so this accessor does
not apply a second projection. -/
def LineDesc.direction {L : LdParams} (line : LineDesc L) :
    Fin L.m → ScalarQ L :=
  match line with
  | .axis _ seed _ => coordinateDirection (chiIndex L seed)
  | .diagonal _ _ direction _ _ => direction

/-- The canonical base is fixed by the representative map of the line's
geometric direction. -/
theorem LineDesc.base_fixed {L : LdParams} (line : LineDesc L) :
    lineRepMap line.direction line.base = line.base := by
  cases line with
  | axis base seed baseFixed => exact baseFixed
  | diagonal base seed direction baseFixed prefixZero => exact baseFixed

/-- Every diagonal description carries the source prefix-zero invariant. -/
theorem LineDesc.diagonal_prefix_zero {L : LdParams} (line : LineDesc L)
    (hline : line.kind = .diagonal) :
    ∀ j : Fin L.m, j.val < (chiIndex L line.seed).val → line.direction j = 0 := by
  cases line with
  | axis base seed baseFixed => simp [LineDesc.kind] at hline
  | diagonal base seed direction baseFixed prefixZero => exact prefixZero

/-- The point set represented by a seed-bearing line description. -/
noncomputable def LineDesc.pointSet {L : LdParams} (line : LineDesc L) :
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
def aLineDescOf (L : LdParams) (line : LdSpace L) : LineDesc L :=
  let direction := coordinateDirection (chiIndex L line.seed)
  let base := lineRepMap direction line.point
  LineDesc.axis base line.seed (lineRepMap_apply_self direction line.point)

/-- Convert a diagonal-line CL output to its seed-bearing presentation. -/
def dLineDescOf (L : LdParams) (line : LdSpace L) : LineDesc L :=
  let direction := prefixProjection (chiIndex L line.seed) line.direction
  let base := lineRepMap direction line.point
  LineDesc.diagonal base line.seed direction
    (lineRepMap_apply_self direction line.point) (by
      intro j hj
      change prefixProjection (chiIndex L line.seed) line.direction j = 0
      rw [prefixProjection, if_pos hj])

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
  Distribution.mix (1 / 2) (by norm_num) (by norm_num)
    (aLinePointDist L) (dLinePointDist L)

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
  exact Distribution.mix_isProbability _ _ _
    (aLinePointDist_isProbability L) (dLinePointDist_isProbability L)
    (by norm_num) (by norm_num)

end

end MIPStarRE.QPBT
