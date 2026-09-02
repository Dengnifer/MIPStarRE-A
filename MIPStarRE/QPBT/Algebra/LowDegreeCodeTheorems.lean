import MIPStarRE.QPBT.Algebra.LowDegreeCode

/-! # Decoding maps for the low-degree code

This file supplies `def:decoding-map` and the Boolean cube embedding from
`blueprint/src/chapter/ch11_qpbt_algebra.tex:432-447`, paper
`references/qpbt-paper/04_preliminaries.tex:832-897`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.LDT.Preliminaries

def boolToScalar {K : Type*} [Field K] : Bool → K
  | false => 0
  | true => 1

def cubeEmbed {K : Type*} [Field K] {m : ℕ} : Cube m → (Fin m → K) :=
  fun y i => boolToScalar (y i)

noncomputable def decodeAt {K : Type*} [Field K] [DecidableEq K] {m : ℕ}
    (H : Finset K) (g : (Fin m → K) → K) : Cube m → K :=
  fun y => if g (cubeEmbed y) ∈ H then g (cubeEmbed y) else 0

noncomputable abbrev decodeBool {K : Type*} [Field K] [DecidableEq K] {m : ℕ}
    (g : (Fin m → K) → K) : Cube m → K :=
  decodeAt ({0, 1} : Finset K) g

theorem decodeAt_lowDegreeEnc {K : Type*} [Field K] [DecidableEq K] {m : ℕ}
    (H : Finset K) (a : Cube m → K) (ha : ∀ y, a y ∈ H) :
    decodeAt H (lowDegreeEnc a) = a := by
  sorry

end MIPStarRE.QPBT
