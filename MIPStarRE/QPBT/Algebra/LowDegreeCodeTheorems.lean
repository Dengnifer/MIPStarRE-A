import MIPStarRE.QPBT.Algebra.LowDegreeCode

/-! # Decoding maps for the low-degree code

This file supplies `def:decoding-map` and the Boolean cube embedding from
`blueprint/src/chapter/ch11_qpbt_algebra.tex:445-455`, paper
`references/qpbt-paper/04_preliminaries.tex:917-924`.
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

/-- The restricted decoding identity in `def:decoding-map`, blueprint
`ch11_qpbt_algebra.tex:445-455`, paper `04_preliminaries.tex:917-924`. -/
theorem decodeAt_lowDegreeEnc {K : Type*} [Field K] [DecidableEq K] {m : ℕ}
    (H : Finset K) (a : Cube m → K) (ha : ∀ y, a y ∈ H) :
    decodeAt H (lowDegreeEnc a) = a := by
  funext y
  simp [decodeAt, lowDegreeEnc_cubeEmbed, ha y]

end MIPStarRE.QPBT
