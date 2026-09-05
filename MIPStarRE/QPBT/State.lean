import MIPStarRE.Quantum.FiniteMatrix.Basic

/-!
# Finite-dimensional state transformations

This file defines the tensor and reindexing operations used for strategy
distance, Magic Square rigidity, and the qudit-to-qubit isomorphism. See
blueprint chapters 11--13 and the declaration-level references below.
-/

open scoped Matrix

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum

/-- Conjugation by the local isometries in `thm:ms-rigidity` and
`lem:pauli-binary`; blueprint `ch13_qpbt_test.tex:222-244` and
`ch11_qpbt_algebra.tex:710-741`, paper
`08_classical_and_quantum_low_degree_tests.tex:620-652` and
`04_preliminaries.tex:1163-1208`. -/
noncomputable def conjIsometry {ι ι' : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ι')
    (M : Op ι) : Op ι' :=
  let U : Matrix ι' ι ℂ := Matrix.toEuclideanLin.symm φ.toLinearMap
  U * M * Uᴴ

/-- Coordinate transport used by `def:strategy-distance`, blueprint
`ch12_qpbt_games.tex:228-237`, paper `06_nonlocal_games_and_mipstar.tex:273-285`. -/
noncomputable def reindexState {ι ι' : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] (e : ι ≃ ι')
    (ψ : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι' :=
  (EuclideanSpace.equiv ι' ℂ).symm
    (fun j => (EuclideanSpace.equiv ι ℂ ψ) (e.symm j))

/-- Apply the two independent local isometries of `thm:ms-rigidity`; blueprint
`ch13_qpbt_test.tex:222-244`, paper
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

/-- Coordinate tensor used in the ideal state of `thm:ms-rigidity`; blueprint
`ch13_qpbt_test.tex:222-244`, paper
`08_classical_and_quantum_low_degree_tests.tex:620-652`. -/
noncomputable def vecTensor {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (u : EuclideanSpace ℂ ι) (v : EuclideanSpace ℂ κ) :
    EuclideanSpace ℂ (ι × κ) :=
  (EuclideanSpace.equiv (ι × κ) ℂ).symm
    (fun p => (EuclideanSpace.equiv ι ℂ u) p.1 * (EuclideanSpace.equiv κ ℂ v) p.2)

/-- Operator transport used by `def:strategy-distance`, blueprint
`ch12_qpbt_games.tex:228-237`, paper `06_nonlocal_games_and_mipstar.tex:273-285`. -/
def reindexOp {ι ι' : Type*} (e : ι ≃ ι') (M : Op ι') : Op ι :=
  (Matrix.reindex e.symm e.symm) M

/-- Four-factor tensor shuffle used by `thm:ms-rigidity`; blueprint
`ch13_qpbt_test.tex:222-244`, paper
`08_classical_and_quantum_low_degree_tests.tex:620-652`. -/
def prodShuffle {α β γ δ : Type*} :
    (α × β) × (γ × δ) ≃ (α × γ) × (β × δ) where
  toFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  invFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

/-! ## Norm identities for the coordinate operations -/

/-- Reindexing Euclidean coordinates along an equivalence preserves norm. -/
theorem reindexState_norm_eq
    {iota kappa : Type*}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (e : iota ≃ kappa) (psi : EuclideanSpace ℂ iota) :
    ‖reindexState e psi‖ = ‖psi‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  change (∑ j : kappa, ‖psi (e.symm j)‖ ^ 2) = ∑ i : iota, ‖psi i‖ ^ 2
  exact e.symm.sum_comp (fun i => ‖psi i‖ ^ 2)

/-- The coordinate tensor of two Euclidean vectors has the product norm. -/
theorem vecTensor_norm_eq
    {iota kappa : Type*}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (u : EuclideanSpace ℂ iota) (v : EuclideanSpace ℂ kappa) :
    ‖vecTensor u v‖ = ‖u‖ * ‖v‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq]
  change (∑ p : iota × kappa, ‖u p.1 * v p.2‖ ^ 2) =
    (∑ i : iota, ‖u i‖ ^ 2) * ∑ j : kappa, ‖v j‖ ^ 2
  simp only [norm_mul, mul_pow]
  rw [← Finset.univ_product_univ, Finset.sum_product, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]

end MIPStarRE.QPBT
