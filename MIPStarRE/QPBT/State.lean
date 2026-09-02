import MIPStarRE.Quantum.FiniteMatrix.Basic

/-!
# Neutral finite-dimensional state constructions

This leaf contains tensor and reindexing operations shared by the QPBT game and
test layers.  The definitions support the state transports used in the Pauli
basis test (`blueprint/src/chapter/ch13_qpbt_test.tex:386-403`; paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`).
-/

open scoped Matrix

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum

/-- Conjugation by the local isometries in `thm:ms-rigidity` and
`lem:pauli-binary`; blueprint `ch13_qpbt_test.tex:386-403` and
`ch11_qpbt_algebra.tex:675-708`, paper `08_classical_and_quantum_low_degree_tests.tex:1426-1447`. -/
noncomputable def conjIsometry {ι ι' : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ι')
    (M : Op ι) : Op ι' :=
  let U : Matrix ι' ι ℂ := Matrix.toEuclideanLin.symm φ.toLinearMap
  U * M * Uᴴ

/-- Coordinate transport used by `def:strategy-distance`, blueprint
`ch12_qpbt_games.tex:212-219`, paper `06_nonlocal_games_and_mipstar.tex:273-285`. -/
noncomputable def reindexState {ι ι' : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] (e : ι ≃ ι')
    (ψ : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι' :=
  (EuclideanSpace.equiv ι' ℂ).symm
    (fun j => (EuclideanSpace.equiv ι ℂ ψ) (e.symm j))

/-- Apply the two independent local isometries of `thm:ms-rigidity`; blueprint
`ch13_qpbt_test.tex:386-403`, paper
`08_classical_and_quantum_low_degree_tests.tex:1426-1447`. -/
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

/-- Coordinate tensor used in the ideal state of `thm:ms-rigidity`; blueprint
`ch13_qpbt_test.tex:386-403`, paper
`08_classical_and_quantum_low_degree_tests.tex:1426-1447`. -/
noncomputable def vecTensor {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (u : EuclideanSpace ℂ ι) (v : EuclideanSpace ℂ κ) :
    EuclideanSpace ℂ (ι × κ) :=
  (EuclideanSpace.equiv (ι × κ) ℂ).symm
    (fun p => (EuclideanSpace.equiv ι ℂ u) p.1 * (EuclideanSpace.equiv κ ℂ v) p.2)

/-- Operator transport used by `def:strategy-distance`, blueprint
`ch12_qpbt_games.tex:212-219`, paper `06_nonlocal_games_and_mipstar.tex:273-285`. -/
def reindexOp {ι ι' : Type*} (e : ι ≃ ι') (M : Op ι') : Op ι :=
  (Matrix.reindex e.symm e.symm) M

/-- Four-factor tensor shuffle used by `thm:ms-rigidity`; blueprint
`ch13_qpbt_test.tex:386-403`, paper
`08_classical_and_quantum_low_degree_tests.tex:1426-1447`. -/
def prodShuffle {α β γ δ : Type*} :
    (α × β) × (γ × δ) ≃ (α × γ) × (β × δ) where
  toFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  invFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

end MIPStarRE.QPBT
