import MIPStarRE.QPBT.Algebra.LowDegreeCode

/-! # Decoding maps for the low-degree code

This file supplies `def:decoding-map` and the Boolean cube embedding from
`blueprint/src/chapter/ch11_qpbt_algebra.tex:445-455`, paper
`references/qpbt-paper/04_preliminaries.tex:917-924`.  The specialization to
polynomial representatives is `decodeFqRep`; its restriction to the bounded
class `Poly` is defined in `Algebra/Decoding`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.LDT.Preliminaries

/-- The formalization-only embedding of Boolean coordinates into a field used by
`def:decoding-map`; blueprint `ch11_qpbt_algebra.tex:445-455`, paper
`04_preliminaries.tex:917-924`. -/
def boolToScalar {K : Type*} [Field K] : Bool → K
  | false => 0
  | true => 1

/-- The coordinatewise Boolean-cube embedding used by
`def:decoding-map`; blueprint `ch11_qpbt_algebra.tex:445-455`, paper
`04_preliminaries.tex:917-924`. -/
def cubeEmbed {K : Type*} [Field K] {m : ℕ} : Cube m → (Fin m → K) :=
  fun y i => boolToScalar (y i)

/-- The decoding map `def:decoding-map`, blueprint
`ch11_qpbt_algebra.tex:445-455`, paper `04_preliminaries.tex:917-924`. -/
noncomputable def decodeAt {K : Type*} [Field K] [DecidableEq K] {m : ℕ}
    (H : Finset K) (g : (Fin m → K) → K) : Cube m → K :=
  fun y => if g (cubeEmbed y) ∈ H then g (cubeEmbed y) else 0

/-- Boolean specialization of `def:decoding-map`, blueprint
`ch11_qpbt_algebra.tex:445-455`, paper `04_preliminaries.tex:917-924`. -/
noncomputable abbrev decodeBool {K : Type*} [Field K] [DecidableEq K] {m : ℕ}
    (g : (Fin m → K) → K) : Cube m → K :=
  decodeAt ({0, 1} : Finset K) g

/-- The full-field specialization of `decodeAt` used by the generic algebra
layer.  The Chapter 16 `Poly`-facing name is defined in `Algebra/Decoding.lean`.
Every value is retained because the filter is `H = Finset.univ`, so this is the
cube-indexed evaluation of a polynomial representative.  The restricted
decoder identity remains separate and is only available for encoding
representatives; no unrestricted interpolation identity is asserted here.

This is the `H = \F_q` reading of `def:decoding-map`, blueprint
`blueprint/src/chapter/ch11_qpbt_algebra.tex:445-455`, used by Chapter 16 at
`blueprint/src/chapter/ch16_qpbt_extraction.tex:11-20`; paper origin
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1419-1420` and
the correction recorded in `docs/paper-gaps/qpbt_decoding-identity.tex`. -/
noncomputable def decodeFqRep {K : Type*} [Field K] [Fintype K] [DecidableEq K] {m : ℕ}
    (g : MvPolynomial (Fin m) K) : Cube m → K :=
  decodeAt (Finset.univ : Finset K) (fun x => MvPolynomial.eval x g)

/-- A polynomial representative lies in the low-degree encoding image when it
is exactly the multilinear representative reconstructed from its full-field
decoder.  This predicate is used to state the support restriction required by
the Chapter 16 decoding argument; it does not identify arbitrary polynomial
functions with their representatives.

See `docs/paper-gaps/qpbt_decoding-identity.tex:87-116`. -/
def IsEncodingRep {K : Type*} [Field K] [Fintype K] [DecidableEq K] {m : ℕ}
    (g : MvPolynomial (Fin m) K) : Prop :=
  lowDegreeEncoding (decodeFqRep g) = g

/-- The restricted decoding identity in `def:decoding-map`, blueprint
`ch11_qpbt_algebra.tex:445-455`, paper `04_preliminaries.tex:917-924`. -/
theorem decodeAt_lowDegreeEnc {K : Type*} [Field K] [DecidableEq K] {m : ℕ}
    (H : Finset K) (a : Cube m → K) (ha : ∀ y, a y ∈ H) :
    decodeAt H (lowDegreeEnc a) = a := by
  sorry

end MIPStarRE.QPBT
