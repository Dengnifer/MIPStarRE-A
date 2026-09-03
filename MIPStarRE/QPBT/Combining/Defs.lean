import MIPStarRE.QPBT.Test.LowDegreeGameTheorems
import MIPStarRE.QPBT.Test.PauliBasisTest

/-!
# Polynomial combination and restricted line distributions

This file contains the concrete definitions at the foundation of the
Chapter 15 combining argument.  A pair of bounded individual-degree
polynomials is embedded into the two coordinate blocks of an extended
polynomial.  On lines, explicit affine reparameterizations are composed with
coefficient-list polynomials.  The original-dimensional restricted line laws
are formed before decoding, while their field seed is still present.

## References

The combining map is `def:combine-map` in
`blueprint/src/chapter/ch15_qpbt_combining.tex:445-480`, with paper origin
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`.
The restricted laws are `def:ith-restricted-line` in blueprint lines 578--592,
with paper origin in the same source at lines 1038--1048.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries

noncomputable section

/-- The bounded individual-degree polynomial outcome used by the global
pair measurement.  This is the actual `polyFunc` subtype from
`def:polyfunc`, not a coefficient-box replacement. -/
noncomputable abbrev Poly (P : AdmissibleParams) :=
  ↥(MIPStarRE.LDT.Preliminaries.polyFunc P.m (PauliScalar P) P.d)

/-- Pairs of bounded polynomial representatives returned by the global
measurement in `lem:qld-4-7`. -/
noncomputable abbrev PolyPair (P : AdmissibleParams) := Poly P × Poly P

/-- Split the extended coordinate set into the `X` block, the `Z` block, and
the two scalar coordinates.  This is formalization-only coordinate plumbing
for `def:combine-map`, blueprint
`blueprint/src/chapter/ch15_qpbt_combining.tex:445-480`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
def finCombineEquiv (m : ℕ) :
    Fin (2 * m + 2) ≃ ((Fin m ⊕ Fin m) ⊕ Fin 2) :=
  (finCongr (by omega)).trans
    (finSumFinEquiv.symm.trans
      (Equiv.sumCongr finSumFinEquiv.symm (Equiv.refl (Fin 2))))

/-- Embed an `X`-block coordinate into the extended coordinate set. -/
def embX (m : ℕ) : Fin m → Fin (2 * m + 2) :=
  fun i => (finCombineEquiv m).symm (.inl (.inl i))

/-- Embed a `Z`-block coordinate into the extended coordinate set. -/
def embZ (m : ℕ) : Fin m → Fin (2 * m + 2) :=
  fun i => (finCombineEquiv m).symm (.inl (.inr i))

/-- The extended coordinate occupied by the scalar `alpha`. -/
def alphaVar (m : ℕ) : Fin (2 * m + 2) :=
  (finCombineEquiv m).symm (.inr 0)

/-- The extended coordinate occupied by the scalar `beta`. -/
def betaVar (m : ℕ) : Fin (2 * m + 2) :=
  (finCombineEquiv m).symm (.inr 1)

/-- Project an extended point onto its `X` coordinate block. -/
def projX {K : Type*} {m : ℕ} (u : Fin (2 * m + 2) → K) : Fin m → K :=
  fun i => u (embX m i)

/-- Project an extended point onto its `Z` coordinate block. -/
def projZ {K : Type*} {m : ℕ} (u : Fin (2 * m + 2) → K) : Fin m → K :=
  fun i => u (embZ m i)

/-- Combine two multivariate polynomials by the formula
`alpha * f(x) + beta * g(z)` from `def:combine-map`.

Blueprint `blueprint/src/chapter/ch15_qpbt_combining.tex:445-480`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-983`. -/
noncomputable def combinePoly {K : Type*} [CommSemiring K] {m : ℕ}
    (f g : MvPolynomial (Fin m) K) : MvPolynomial (Fin (2 * m + 2)) K :=
  MvPolynomial.X (alphaVar m) * MvPolynomial.rename (embX m) f +
    MvPolynomial.X (betaVar m) * MvPolynomial.rename (embZ m) g

/-- Evaluation of `combinePoly` is the displayed combining formula. -/
theorem combinePoly_eval {K : Type*} [CommSemiring K] {m : ℕ}
    (f g : MvPolynomial (Fin m) K) (u : Fin (2 * m + 2) → K) :
    MvPolynomial.eval u (combinePoly f g) =
      u (alphaVar m) * MvPolynomial.eval (projX u) f +
        u (betaVar m) * MvPolynomial.eval (projZ u) g := by
  change MvPolynomial.eval u (combinePoly f g) =
    u (alphaVar m) * MvPolynomial.eval (u ∘ embX m) f +
      u (betaVar m) * MvPolynomial.eval (u ∘ embZ m) g
  simp [combinePoly, MvPolynomial.eval_rename]

/-- The combining polynomial has individual degree at most `d` when
`hd : 1 ≤ d`.  The coordinate blocks are disjoint: `f` depends only on the
`x` variables and `g` only on the `z` variables, so multiplication by `alpha`
or `beta` preserves the degree bound on those old coordinates and gives degree
one only in the corresponding fresh coordinate.  Thus `hd` supplies exactly
the needed bound on the two fresh coordinates; no `d + 1` bound is introduced.
The statement is the well-definedness assertion in
`def:combine-map`, blueprint
`blueprint/src/chapter/ch15_qpbt_combining.tex:445-480`, with source context
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-983` and the
boundary-hypothesis discussion in `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.
-/
theorem combinePoly_mem_polyFunc {K : Type*} [CommSemiring K] {m d : ℕ}
    (hd : 1 ≤ d) {f g : MvPolynomial (Fin m) K}
    (hf : f ∈ polyFunc m K d) (hg : g ∈ polyFunc m K d) :
    combinePoly f g ∈ polyFunc (2 * m + 2) K d := by
  sorry

/-- Evaluate one member of a global polynomial pair at a point, selecting the
component by Pauli basis.  This is formalization-only support for
`lem:qld-4-7`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1274`. -/
def evalAt {P : AdmissibleParams} (W : PauliKind)
    (u : Fin P.m → PauliScalar P) (pair : PolyPair P) : PauliScalar P :=
  match W with
  | .X => MvPolynomial.eval u pair.1.1
  | .Z => MvPolynomial.eval u pair.2.1

/-- Interpret a bounded coefficient list as an ordinary univariate
polynomial.  This helper makes the line-combination definition use Mathlib's
actual polynomial composition operation. -/
noncomputable def linePolynomialOfCoefficients {K : Type*} [Semiring K]
    {c : ℕ} (f : Fin (c + 1) → K) : Polynomial K :=
  ∑ i : Fin (c + 1), Polynomial.C (f i) * Polynomial.X ^ i.val

/-- Evaluating the polynomial represented by a coefficient list agrees with
`evalCoefficient`. -/
theorem linePolynomialOfCoefficients_eval {K : Type*} [Semiring K]
    {c : ℕ} (f : Fin (c + 1) → K) (t : K) :
    (linePolynomialOfCoefficients f).eval t = evalCoefficient f t := by
  change Polynomial.eval t
      (∑ i ∈ Finset.univ, Polynomial.C (f i) * Polynomial.X ^ i.val) =
    ∑ i ∈ Finset.univ, f i * t ^ i.val
  rw [Polynomial.eval_finsetSum]
  simp

/-- The univariate polynomial before coefficient extraction in
`combineLinePoly`.  The four first scalars describe the affine parameters on
the two projected lines; the last four are the affine `alpha` and `beta`
coordinates of the extended line. -/
noncomputable def combineLinePolynomial {K : Type*} [CommSemiring K] {c : ℕ}
    (aX bX aZ bZ uα vα uβ vβ : K)
    (f g : Fin (c + 1) → K) : Polynomial K :=
  (Polynomial.C uα + Polynomial.C vα * Polynomial.X) *
      (linePolynomialOfCoefficients f).comp
        (Polynomial.C aX + Polynomial.C bX * Polynomial.X) +
    (Polynomial.C uβ + Polynomial.C vβ * Polynomial.X) *
      (linePolynomialOfCoefficients g).comp
        (Polynomial.C aZ + Polynomial.C bZ * Polynomial.X)

/-- The polynomial underlying `combineLinePoly` has degree at most `c + 1`.
This is the degree assertion accompanying Equation `eq:combine-lines` in
`def:combine-map`, blueprint
`blueprint/src/chapter/ch15_qpbt_combining.tex:459-479`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:984-989`. -/
theorem combineLinePolynomial_natDegree_le {K : Type*} [CommSemiring K] {c : ℕ}
    (aX bX aZ bZ uα vα uβ vβ : K) (f g : Fin (c + 1) → K) :
    (combineLinePolynomial aX bX aZ bZ uα vα uβ vβ f g).natDegree ≤ c + 1 := by
  sorry

/-- Combine two degree-`c` line polynomials using explicit affine
reparameterizations.  Coefficients through degree `c + 1` are extracted from
the genuine composed polynomial, so the definition has no incompatibility
fallback.

This is Equation `eq:combine-lines` in `def:combine-map`, blueprint
`blueprint/src/chapter/ch15_qpbt_combining.tex:459-479`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:984-989`. -/
noncomputable def combineLinePoly {K : Type*} [CommSemiring K] {c : ℕ}
    (aX bX aZ bZ uα vα uβ vβ : K)
    (f g : Fin (c + 1) → K) : Fin (c + 1 + 1) → K :=
  fun i => (combineLinePolynomial aX bX aZ bZ uα vα uβ vβ f g).coeff i.val

/-- Compatibility of an extended line with two projected lines and their
explicit affine parameters.  This is precisely the domain condition preceding
Equation `eq:combine-lines`; it is data supplied by the future subline
construction, not a fallback branch in `combineLinePoly`. -/
def IsCombineLineCompatible {K : Type*} [Field K] {m : ℕ}
    (u v : Fin (2 * m + 2) → K)
    (uX vX uZ vZ : Fin m → K)
    (aX bX aZ bZ uα vα uβ vβ : K) : Prop :=
  u (alphaVar m) = uα ∧ v (alphaVar m) = vα ∧
    u (betaVar m) = uβ ∧ v (betaVar m) = vβ ∧
    ∀ t : K,
      projX (u + t • v) = uX + (aX + bX * t) • vX ∧
        projZ (u + t • v) = uZ + (aZ + bZ * t) • vZ

/-- Under explicit line compatibility, `combineLinePoly` satisfies the
advertised line equation and the two projected points have the stated affine
parameters.  This is the specification obligation for Equation
`eq:combine-lines`, blueprint
`blueprint/src/chapter/ch15_qpbt_combining.tex:459-479`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:984-989`. -/
theorem combineLinePoly_spec {K : Type*} [Field K] {m c : ℕ}
    (u v : Fin (2 * m + 2) → K) (uX vX uZ vZ : Fin m → K)
    (aX bX aZ bZ uα vα uβ vβ : K) (f g : Fin (c + 1) → K)
    (hcompat : IsCombineLineCompatible u v uX vX uZ vZ
      aX bX aZ bZ uα vα uβ vβ) :
    ∀ t : K,
      projX (u + t • v) = uX + (aX + bX * t) • vX ∧
      projZ (u + t • v) = uZ + (aZ + bZ * t) • vZ ∧
      evalCoefficient
          (combineLinePoly aX bX aZ bZ uα vα uβ vβ f g) t =
        (uα + t * vα) * evalCoefficient f (aX + bX * t) +
          (uβ + t * vβ) * evalCoefficient g (aZ + bZ * t) := by
  sorry

/-- The seed event defining the `i`-th original-dimensional restricted line
law.  It is applied before the `LineDesc` decoder, since a geometric line does
not determine the retained seed. -/
def restrictedLineSeedEvent (L : LdParams) (i : Fin L.m)
    (sample : LdSpace L × LdSpace L) : Prop :=
  chiIndex L sample.1.seed = i

/-- Decidability of the pre-decoding seed event. -/
instance restrictedLineSeedEvent_decidablePred (L : LdParams) (i : Fin L.m) :
    DecidablePred (restrictedLineSeedEvent L i) := by
  intro sample
  unfold restrictedLineSeedEvent
  infer_instance

/-- The axis-line seed event has positive mass.  This named obligation makes
normalization in `restrictedALinePreDist` explicit.  It belongs to
`def:ith-restricted-line`, blueprint
`blueprint/src/chapter/ch15_qpbt_combining.tex:578-592`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1038-1048`. -/
theorem restrictedALineSeedEvent_positive (L : LdParams) (i : Fin L.m) :
    0 < ∑ sample ∈
        (clDistribution (ldALineCL L) (ldPointCL L)).support.filter
          (restrictedLineSeedEvent L i),
      (clDistribution (ldALineCL L) (ldPointCL L)).weight sample := by
  sorry

/-- The diagonal-line seed event has positive mass.  This is the corresponding
normalization obligation from `def:ith-restricted-line`, blueprint lines
578--592 and paper lines 1038--1048. -/
theorem restrictedDLineSeedEvent_positive (L : LdParams) (i : Fin L.m) :
    0 < ∑ sample ∈
        (clDistribution (ldDLineCL L) (ldPointCL L)).support.filter
          (restrictedLineSeedEvent L i),
      (clDistribution (ldDLineCL L) (ldPointCL L)).weight sample := by
  sorry

/-- The normalized pre-decoding axis law conditioned on coordinate `i`. -/
noncomputable def restrictedALinePreDist (L : LdParams) (i : Fin L.m) :
    Distribution (LdSpace L × LdSpace L) :=
  Distribution.restrict
    (clDistribution (ldALineCL L) (ldPointCL L))
    (restrictedLineSeedEvent L i)
    (restrictedALineSeedEvent_positive L i)

/-- The normalized pre-decoding diagonal law conditioned on coordinate `i`. -/
noncomputable def restrictedDLinePreDist (L : LdParams) (i : Fin L.m) :
    Distribution (LdSpace L × LdSpace L) :=
  Distribution.restrict
    (clDistribution (ldDLineCL L) (ldPointCL L))
    (restrictedLineSeedEvent L i)
    (restrictedDLineSeedEvent_positive L i)

/-- The `i`-th restricted axis-line distribution from
`def:ith-restricted-line`.  Restriction precedes decoding so the seed fiber is
represented faithfully.  Blueprint
`blueprint/src/chapter/ch15_qpbt_combining.tex:578-592`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1038-1048`. -/
noncomputable def restrictedALineDist (L : LdParams) (i : Fin L.m) :
    Distribution (LineDesc L × (Fin L.m → ScalarQ L)) :=
  (restrictedALinePreDist L i).map fun sample =>
    (aLineDescOf L sample.1, sample.2.point)

/-- The `i`-th restricted diagonal-line distribution from
`def:ith-restricted-line`.  The decoded direction already has all coordinates
preceding `i` set to zero.  Blueprint lines 578--592; paper lines 1038--1048. -/
noncomputable def restrictedDLineDist (L : LdParams) (i : Fin L.m) :
    Distribution (LineDesc L × (Fin L.m → ScalarQ L)) :=
  (restrictedDLinePreDist L i).map fun sample =>
    (dLineDescOf L sample.1, sample.2.point)

/-- Every restricted axis-line law has total mass one. -/
theorem restrictedALineDist_isProbability (L : LdParams) (i : Fin L.m) :
    (restrictedALineDist L i).IsProbability := by
  unfold restrictedALineDist restrictedALinePreDist
  exact (Distribution.restrict_isProbability
    (clDistribution (ldALineCL L) (ldPointCL L))
    (restrictedLineSeedEvent L i) (restrictedALineSeedEvent_positive L i)).map _

/-- Every restricted diagonal-line law has total mass one. -/
theorem restrictedDLineDist_isProbability (L : LdParams) (i : Fin L.m) :
    (restrictedDLineDist L i).IsProbability := by
  unfold restrictedDLineDist restrictedDLinePreDist
  exact (Distribution.restrict_isProbability
    (clDistribution (ldDLineCL L) (ldPointCL L))
    (restrictedLineSeedEvent L i) (restrictedDLineSeedEvent_positive L i)).map _

end

end MIPStarRE.QPBT
