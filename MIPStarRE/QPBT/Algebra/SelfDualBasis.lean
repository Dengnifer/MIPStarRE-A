import MIPStarRE.QPBT.Algebra.FieldBasis
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Trace

/-! # Dual, self-dual, and normal bases

Source `def:dual-self-dual-normal-basis` and `def:binary-representation`;
blueprint `blueprint/src/chapter/ch11_qpbt_algebra.tex:234-246,298-315`; paper
`references/qpbt-paper/04_preliminaries.tex:653-680,702-725`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

def IsDualBasisPair {F K ι : Type*} [CommRing F] [CommRing K] [DecidableEq ι]
    [Algebra F K] (b b' : Module.Basis ι F K) : Prop :=
  ∀ i j, Algebra.trace F K (b i * b' j) = if i = j then 1 else 0

namespace Basis

def IsSelfDual {F K ι : Type*} [CommRing F] [CommRing K] [DecidableEq ι]
    [Algebra F K] (b : Module.Basis ι F K) : Prop :=
  IsDualBasisPair b b

def IsNormal {F K : Type*} [CommSemiring F] [Field K] [Algebra F K]
    {k : ℕ} (b : Module.Basis (Fin k) F K) (q : ℕ) : Prop :=
  ∃ α : K, ∀ j, b j = α ^ (q ^ j.1)

end Basis

theorem exists_selfDualNormalBasis {K : Type*} [Field K] [Fintype K]
    [Algebra (ZMod 2) K] (k : ℕ) (hk : Odd k) :
    ∃ b : Module.Basis (Fin k) (ZMod 2) K,
      Basis.IsSelfDual b ∧ Basis.IsNormal b 2 := by
  sorry

/-- Coordinates in the fixed model's chosen binary basis. -/
noncomputable abbrev FixedFieldModel.binaryCoordinates {q : ℕ}
    (F : FixedFieldModel q) : F.K ≃ₗ[ZMod 2] (Fin F.basisDim → ZMod 2) :=
  kappa F.basis

theorem binaryCoordinates_mul {q : ℕ} (F : FixedFieldModel q) (a b : F.K) :
    F.binaryCoordinates (a * b) =
      ∑ i : Fin F.basisDim, F.binaryCoordinates a i •
        (F.binaryCoordinates (F.basis i * b)) := by
  sorry

end MIPStarRE.QPBT
