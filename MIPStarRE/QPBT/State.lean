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

/-- Conjugate a finite operator by a linear isometry. -/
noncomputable def conjIsometry {ι ι' : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ι')
    (M : Op ι) : Op ι' :=
  let U : Matrix ι' ι ℂ := Matrix.toEuclideanLin.symm φ.toLinearMap
  U * M * Uᴴ

/-- Reindex a finite Euclidean-space vector along an equivalence. -/
noncomputable def reindexState {ι ι' : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] (e : ι ≃ ι')
    (ψ : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι' :=
  (EuclideanSpace.equiv ι' ℂ).symm
    (fun j => (EuclideanSpace.equiv ι ℂ ψ) (e.symm j))

/-- Apply two local isometries to a bipartite state, with arbitrary finite
codomain index types. -/
noncomputable def isometryTensor
    {ιA ιB κA κB R : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]
    [Fintype R] [DecidableEq R]
    (φA : EuclideanSpace ℂ ιA →ₗᵢ[ℂ] EuclideanSpace ℂ (κA × R))
    (φB : EuclideanSpace ℂ ιB →ₗᵢ[ℂ] EuclideanSpace ℂ (κB × R))
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    EuclideanSpace ℂ ((κA × R) × (κB × R)) :=
  (EuclideanSpace.equiv ((κA × R) × (κB × R)) ℂ).symm
    (fun p =>
      ∑ i : ιA, ∑ j : ιB,
        ((EuclideanSpace.equiv (κA × R) ℂ)
            (φA ((EuclideanSpace.equiv ιA ℂ).symm (Pi.single i 1))) p.1) *
          ((EuclideanSpace.equiv (κB × R) ℂ)
            (φB ((EuclideanSpace.equiv ιB ℂ).symm (Pi.single j 1))) p.2) *
          ((EuclideanSpace.equiv (ιA × ιB) ℂ) ψ (i, j)))

/-- Tensor two real coordinate vectors, indexed by a product. -/
def vecTensor {ι κ : Type*} (u : ι → ℝ) (v : κ → ℝ) : ι × κ → ℝ :=
  fun p => u p.1 * v p.2

/-- Reindex a finite matrix along equivalences of its row and column types. -/
def reindexOp {ι ι' : Type*} (e : ι ≃ ι') (M : Op ι') : Op ι :=
  (Matrix.reindex e.symm e.symm) M

/-- The four-factor product shuffle used to compare bipartite tensor orderings. -/
def prodShuffle {α β γ δ : Type*} :
    (α × β) × (γ × δ) ≃ (α × γ) × (β × δ) where
  toFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  invFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

end MIPStarRE.QPBT
