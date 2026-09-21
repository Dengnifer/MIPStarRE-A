import Mathlib
import Challenge.MIPStarRE.Quantum.FiniteMatrix.Basic

/-! Challenge mirror of `MIPStarRE/QPBT/State.lean`.

One challenge module per contributing library module, importing the
mirrors of the library modules this one imports.  The partition is
what makes Lean generate the same auxiliary declarations, under the
same names, as the library does. -/

open scoped BigOperators MatrixOrder Matrix ComplexOrder
namespace MIPStarRE.QPBT

-- elaboration context of MIPStarRE/QPBT/State.lean
section
open MIPStarRE.Quantum

-- source: MIPStarRE/QPBT/State.lean:17-27  (MIPStarRE.QPBT.conjIsometry)
/-- Conjugation by the local isometries in `thm:ms-rigidity` and
`lem:pauli-binary`; blueprint `thm:ms-rigidity` and
`lem:pauli-binary`, paper
`08_classical_and_quantum_low_degree_tests.tex:620-652` and
`04_preliminaries.tex:1163-1208`. -/
noncomputable def conjIsometry {ι ι' : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ι')
    (M : Op ι) : Op ι' :=
  let U : Matrix ι' ι ℂ := Matrix.toEuclideanLin.symm φ.toLinearMap
  U * M * Uᴴ

-- source: MIPStarRE/QPBT/State.lean:29-35  (MIPStarRE.QPBT.reindexState)
/-- Coordinate transport used by blueprint
`def:strategy-distance`, paper `06_nonlocal_games_and_mipstar.tex:273-285`. -/
noncomputable def reindexState {ι ι' : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] (e : ι ≃ ι')
    (ψ : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι' :=
  (EuclideanSpace.equiv ι' ℂ).symm
    (fun j => (EuclideanSpace.equiv ι ℂ ψ) (e.symm j))

-- source: MIPStarRE/QPBT/State.lean:37-55  (MIPStarRE.QPBT.isometryTensor)
/-- Apply the two independent local isometries of blueprint
`thm:ms-rigidity`, paper
`08_classical_and_quantum_low_degree_tests.tex:620-652`. -/
noncomputable def isometryTensor
    {ιA ιB κA κB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]
    (φA : EuclideanSpace ℂ ιA →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (φB : EuclideanSpace ℂ ιB →ₗᵢ[ℂ] EuclideanSpace ℂ κB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    EuclideanSpace ℂ (κA × κB) :=
  (EuclideanSpace.equiv (κA × κB) ℂ).symm
    (fun p =>
      ∑ i : ιA, ∑ j : ιB,
        ((EuclideanSpace.equiv κA ℂ)
            (φA ((EuclideanSpace.equiv ιA ℂ).symm (Pi.single i 1))) p.1) *
          ((EuclideanSpace.equiv κB ℂ)
            (φB ((EuclideanSpace.equiv ιB ℂ).symm (Pi.single j 1))) p.2) *
          ((EuclideanSpace.equiv (ιA × ιB) ℂ) ψ (i, j)))
end  -- module scope
end MIPStarRE.QPBT
