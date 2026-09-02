import MIPStarRE.QPBT.Algebra.FieldBasis
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Trace

/-! # Dual, self-dual, and normal bases

Source `def:dual-self-dual-normal-basis` and `def:binary-representation`;
blueprint `blueprint/src/chapter/ch11_qpbt_algebra.tex:241-257,313-334`; paper
`references/qpbt-paper/04_preliminaries.tex:494-502,669-700`.
-/

namespace MIPStarRE.QPBT

open scoped BigOperators Matrix

open MIPStarRE.LDT

/-- A dual pair of bases for `def:dual-self-dual-normal-basis`, blueprint
`ch11_qpbt_algebra.tex:241-257`, paper `04_preliminaries.tex:494-496`. -/
def IsDualBasisPair {F K ι : Type*} [CommRing F] [CommRing K] [DecidableEq ι]
    [Algebra F K] (b b' : Module.Basis ι F K) : Prop :=
  ∀ i j, Algebra.trace F K (b i * b' j) = if i = j then 1 else 0

namespace Basis

/-- Self-duality in `def:dual-self-dual-normal-basis`, blueprint
`ch11_qpbt_algebra.tex:241-257`, paper `04_preliminaries.tex:494-497`. -/
def IsSelfDual {F K ι : Type*} [CommRing F] [CommRing K] [DecidableEq ι]
    [Algebra F K] (b : Module.Basis ι F K) : Prop :=
  IsDualBasisPair b b

/-- Normality in `def:dual-self-dual-normal-basis`, blueprint
`ch11_qpbt_algebra.tex:241-257`, paper `04_preliminaries.tex:498-502`. The
Frobenius exponent uses the cardinality of the base field. -/
def IsNormal {F K : Type*} [CommSemiring F] [Fintype F] [Field K] [Algebra F K]
    {k : ℕ} (b : Module.Basis (Fin k) F K) : Prop :=
  ∃ α : K, ∀ j, b j = α ^ (Fintype.card F ^ j.1)

end Basis

/-- Existence over the binary extension of cardinality `2^k` for odd `k`;
`def:dual-self-dual-normal-basis`, blueprint `ch11_qpbt_algebra.tex:241-257`,
paper `04_preliminaries.tex:702-725`. -/
theorem exists_selfDualNormalBasis {K : Type*} [Field K] [Fintype K]
    [Algebra (ZMod 2) K] (k : ℕ) (hk : Odd k)
    (hcard : Fintype.card K = 2 ^ k) :
    ∃ b : Module.Basis (Fin k) (ZMod 2) K,
      Basis.IsSelfDual b ∧ Basis.IsNormal b := by
  sorry

/-- Coordinates in the fixed model's chosen binary basis;
`def:binary-representation`, blueprint `ch11_qpbt_algebra.tex:313-334`, paper
`04_preliminaries.tex:669-700`. -/
noncomputable abbrev FixedFieldModel.binaryCoordinates {q : ℕ}
    (F : FixedFieldModel q) : F.K ≃ₗ[ZMod 2] (Fin F.basisDim → ZMod 2) :=
  kappa F.basis

/-- Equation `eq:eq-mult`, blueprint `ch11_qpbt_algebra.tex:313-334`, paper
`04_preliminaries.tex:684-700`. -/
theorem binaryCoordinates_mul {q : ℕ} (F : FixedFieldModel q) (a b : F.K) :
    F.binaryCoordinates (a * b) =
      ∑ i : Fin F.basisDim, F.binaryCoordinates a i •
        (F.binaryCoordinates (F.basis i * b)) := by
  sorry

/-- Multiplication by a basis element is multiplication-table action in binary
coordinates; this is the second equality of `eq:eq-mult`, blueprint
`ch11_qpbt_algebra.tex:327-330`, paper `04_preliminaries.tex:684-700`. -/
theorem binaryCoordinates_basis_mul {q : ℕ} (F : FixedFieldModel q)
    (i : Fin F.basisDim) (b : F.K) :
    F.binaryCoordinates (F.basis i * b) =
      multiplicationTable F.basis (F.basis i) *ᵥ F.binaryCoordinates b := by
  simpa only [FixedFieldModel.binaryCoordinates, kappa, multiplicationTable,
    Module.Basis.equivFun_apply] using
    (Algebra.leftMulMatrix_mulVec_repr F.basis (F.basis i) b).symm

/-- Matrix coordinate expansion for an arbitrary basis. This is the `chi_q`
construction of `def:subfields-kappa`, blueprint `ch11_qpbt_algebra.tex:207-214`,
paper `04_preliminaries.tex:462-475`; it is used in item 3 of
`lem:downsize_field`, blueprint lines 259-277, paper lines 509-550. -/
noncomputable def chiOfBasis {F K ρ κ σ : Type*} [Field F] [Field K]
    [Algebra F K] [Fintype κ] (b : Module.Basis κ F K) (M : Matrix ρ σ K) :
    Matrix (ρ × κ) (σ × κ) F :=
  fun p r => b.equivFun (M p.1 r.1 * b r.2) p.2

/-- Coordinates of a vector, block-indexed by its vector and basis indices.
This is the vector `kappa_q(v)` of `def:subfields-kappa`, blueprint
`ch11_qpbt_algebra.tex:207-214`, paper `04_preliminaries.tex:462-475`; it is used
in item 3 of `lem:downsize_field`, blueprint lines 259-277, paper lines 509-550. -/
noncomputable def basisCoordVec {F K ι κ : Type*} [Field F] [Field K]
    [Algebra F K] [Fintype κ] (b : Module.Basis κ F K) (v : ι → K) : ι × κ → F :=
  fun p => b.equivFun (v p.1) p.2

/-- Canonical fixed-model specialization of `chiOfBasis`, with the product
indices required by `def:binary-representation`, blueprint
`ch11_qpbt_algebra.tex:313-334`, paper `04_preliminaries.tex:684-700`. -/
noncomputable def chi {q s t : ℕ} (F : FixedFieldModel q)
    (M : Matrix (Fin s) (Fin t) F.K) :
    Matrix (Fin s × Fin F.basisDim) (Fin t × Fin F.basisDim) (ZMod 2) :=
  chiOfBasis F.basis M

end MIPStarRE.QPBT
