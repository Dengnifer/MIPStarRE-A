import MIPStarRE.QPBT.Algebra.LowDegreeCode

/-! # Decoding maps for the low-degree code

This file supplies `def:decoding-map` and the Boolean cube embedding from
`def:decoding-map`, paper
`references/qpbt-paper/04_preliminaries.tex:917-924`.  The specialization to
polynomial representatives is `decodeFqRep`; its restriction to the bounded
class `Poly` is defined in `Algebra/Decoding`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.LDT.Preliminaries

/-- The formalization-only embedding of Boolean coordinates into a field used by
blueprint `def:decoding-map`, paper
`04_preliminaries.tex:917-924`. -/
def boolToScalar {K : Type*} [Field K] : Bool → K
  | false => 0
  | true => 1

/-- The coordinatewise Boolean-cube embedding used by
blueprint `def:decoding-map`, paper
`04_preliminaries.tex:917-924`. -/
def cubeEmbed {K : Type*} [Field K] {m : ℕ} : Cube m → (Fin m → K) :=
  fun y i => boolToScalar (y i)

/-- On the Boolean cube, an indicator polynomial evaluates to the corresponding
Kronecker delta.  This is the interpolation observation at paper lines 880-891. -/
private theorem eval_indicatorPoly_cubeEmbed {K : Type*} [Field K] {m : ℕ}
    (y z : Cube m) :
    MvPolynomial.eval (cubeEmbed (K := K) z) (indicatorPoly (K := K) y) =
      if y = z then 1 else 0 := by
  classical
  rw [indicatorPoly, MvPolynomial.eval_prod]
  simp only [apply_ite, MvPolynomial.eval_X, MvPolynomial.eval_sub, map_one]
  have hfactor (i : Fin m) :
      (if y i then cubeEmbed (K := K) z i else 1 - cubeEmbed (K := K) z i) =
        if y i = z i then 1 else 0 := by
    cases hy : y i <;> cases hz : z i <;> simp_all [cubeEmbed, boolToScalar]
  simp_rw [hfactor]
  rw [Fintype.prod_boole]
  split_ifs <;> simp_all [funext_iff]

/-- Evaluating a low-degree encoding at an embedded Boolean point recovers its
coefficient at that point, as stated at paper line 891. -/
private theorem lowDegreeEnc_cubeEmbed {K : Type*} [Field K] {m : ℕ}
    (a : Cube m → K) (z : Cube m) :
    lowDegreeEnc a (cubeEmbed z) = a z := by
  rw [lowDegreeEnc_eq_dotProduct]
  simp [dotProduct, indicatorVec, eval_indicatorPoly_cubeEmbed]

/-- The decoding map blueprint
`def:decoding-map`, paper `04_preliminaries.tex:917-924`. -/
noncomputable def decodeAt {K : Type*} [Field K] [DecidableEq K] {m : ℕ}
    (H : Finset K) (g : (Fin m → K) → K) : Cube m → K :=
  fun y => if g (cubeEmbed y) ∈ H then g (cubeEmbed y) else 0

/-- Boolean specialization of blueprint
`def:decoding-map`, paper `04_preliminaries.tex:917-924`. -/
noncomputable abbrev decodeBool {K : Type*} [Field K] [DecidableEq K] {m : ℕ}
    (g : (Fin m → K) → K) : Cube m → K :=
  decodeAt ({0, 1} : Finset K) g

/-- The full-field specialization of `decodeAt` for arbitrary polynomial
representatives.  Its restriction to bounded representatives is defined in
`Algebra/Decoding.lean`.
Every value is retained because the filter is `H = Finset.univ`, so this is the
cube-indexed evaluation of a polynomial representative.  The restricted
decoder identity remains separate and is only available for encoding
representatives; no unrestricted interpolation identity is asserted here.

This is the `H = \F_q` reading of blueprint `def:decoding-map`, used in
blueprint `sec:separating`; paper origin
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

/-- The restricted decoding identity in blueprint
`def:decoding-map`, paper `04_preliminaries.tex:917-924`. -/
theorem decodeAt_lowDegreeEnc {K : Type*} [Field K] [DecidableEq K] {m : ℕ}
    (H : Finset K) (a : Cube m → K) (ha : ∀ y, a y ∈ H) :
    decodeAt H (lowDegreeEnc a) = a := by
  funext y
  simp [decodeAt, lowDegreeEnc_cubeEmbed, ha y]

end MIPStarRE.QPBT
