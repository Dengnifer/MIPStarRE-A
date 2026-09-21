import Mathlib
import Challenge.MIPStarRE.QPBT.Algebra.FieldBasis

/-! Challenge mirror of `MIPStarRE/QPBT/Algebra/SelfDualBasis.lean`.

One challenge module per contributing library module, importing the
mirrors of the library modules this one imports.  The partition is
what makes Lean generate the same auxiliary declarations, under the
same names, as the library does. -/

open scoped BigOperators MatrixOrder Matrix ComplexOrder
namespace MIPStarRE.QPBT

-- source: MIPStarRE/QPBT/Algebra/SelfDualBasis.lean:47-54  (MIPStarRE.QPBT.chiOfBasis)
/-- Matrix coordinate expansion for an arbitrary basis. This is the `chi_q`
construction of blueprint `def:subfields-kappa`,
paper `04_preliminaries.tex:462-475`; it is used in item 3 of blueprint
`lem:downsize_field`, paper lines 509-550. -/
noncomputable def chiOfBasis {F K ρ κ σ : Type*} [Field F] [Field K]
    [Algebra F K] [Fintype κ] (b : Module.Basis κ F K) (M : Matrix ρ σ K) :
    Matrix (ρ × κ) (σ × κ) F :=
  fun p r => b.equivFun (M p.1 r.1 * b r.2) p.2

-- source: MIPStarRE/QPBT/Algebra/SelfDualBasis.lean:56-62  (MIPStarRE.QPBT.basisCoordVec)
/-- Coordinates of a vector, block-indexed by its vector and basis indices.
This is the vector `kappa_q(v)` of blueprint
`def:subfields-kappa`, paper `04_preliminaries.tex:462-475`; it is used
in item 3 of blueprint `lem:downsize_field`, paper lines 509-550. -/
noncomputable def basisCoordVec {F K ι κ : Type*} [Field F] [Field K]
    [Algebra F K] [Fintype κ] (b : Module.Basis κ F K) (v : ι → K) : ι × κ → F :=
  fun p => b.equivFun (v p.1) p.2
end MIPStarRE.QPBT
