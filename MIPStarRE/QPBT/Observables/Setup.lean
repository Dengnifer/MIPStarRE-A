import MIPStarRE.QPBT.Games.StrategyClasses
import MIPStarRE.QPBT.State

/-!
# Projective strategy setup

This module records the finite-dimensional projective dilation used before
the observable analysis and gives its explicit zero-padding isometries.

## References

The setup is `lem:projective-strategy-setup` and
`def:projective-strategy-general` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:385-475`, with paper origin
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:155-172`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

noncomputable section

/-- Embed a finite Euclidean space into an equivalently indexed space by
placing its coordinates in the all-zero ancilla sector. This is Lean-only
infrastructure for the padding in `lem:projective-strategy-setup`, blueprint
`ch14_qpbt_observables.tex:412-475`, paper
`14_analysis_of_the_pauli_basis_test.tex:155-172`. -/
noncomputable def padWithZeros {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {n : ℕ}
    (e : κ ≃ ι × (Fin n → Bool)) :
    EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ := by
  let L : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ κ :=
    { toFun := fun ψ => (EuclideanSpace.equiv κ ℂ).symm fun j =>
        if (e j).2 = 0 then (EuclideanSpace.equiv ι ℂ ψ) (e j).1 else 0
      map_add' := by
        intro ψ φ
        apply (EuclideanSpace.equiv κ ℂ).injective
        change (fun j => if (e j).2 = 0 then
          (EuclideanSpace.equiv ι ℂ (ψ + φ)) (e j).1 else 0) = _
        ext j
        simp only [map_add, Pi.add_apply]
        split_ifs with h <;> simp [h]
      map_smul' := by
        intro c ψ
        apply (EuclideanSpace.equiv κ ℂ).injective
        change (fun j => if (e j).2 = 0 then
          (EuclideanSpace.equiv ι ℂ (c • ψ)) (e j).1 else 0) = _
        ext j
        simp only [map_smul, Pi.smul_apply]
        split_ifs with h <;> simp [h] }
  refine { toLinearMap := L, norm_map' := fun ψ => ?_ }
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  change (∑ j : κ, ‖if (e j).2 = 0 then ψ (e j).1 else 0‖ ^ 2) = _
  change (∑ j : κ, (fun p : ι × (Fin n → Bool) =>
    ‖if p.2 = 0 then ψ p.1 else 0‖ ^ 2) (e j)) = _
  calc
    _ = ∑ p : ι × (Fin n → Bool),
        ‖if p.2 = 0 then ψ p.1 else 0‖ ^ 2 := e.sum_comp _
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single (0 : Fin n → Bool)]
      · simp
      · intro b _ hb
        simp [hb]
      · intro h
        exact (h (Finset.mem_univ _)).elim

/-- Reindex the product of two padded local spaces into the source bipartite
space followed by the two ancilla spaces. This is the explicit shuffle in
`lem:projective-strategy-setup`, blueprint
`ch14_qpbt_observables.tex:412-475`. -/
def paddedProdShuffle {ιA ιB κA κB : Type*} {nA nB : ℕ}
    (eA : κA ≃ ιA × (Fin nA → Bool))
    (eB : κB ≃ ιB × (Fin nB → Bool)) :
    κA × κB ≃ (ιA × ιB) × ((Fin nA → Bool) × (Fin nB → Bool)) :=
  (Equiv.prodCongr eA eB).trans prodShuffle

/-- Every finite tensor-product strategy has an equal-value projective
dilation whose state is obtained by local zero padding. This is
`lem:projective-strategy-setup`, blueprint
`blueprint/src/chapter/ch14_qpbt_observables.tex:412-475`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:155-172`.
The proof route is Naimark dilation followed by residual-projector completion. -/
theorem exists_projective_padded_strategy (G : Game) (S : Strategy G) :
    ∃ (nA nB : ℕ) (T : Strategy G)
      (eA : T.ιA ≃ S.ιA × (Fin nA → Bool))
      (eB : T.ιB ≃ S.ιB × (Fin nB → Bool)),
      T.IsProjective ∧
        reindexState (paddedProdShuffle eA eB) T.ψ =
          reindexState (paddedProdShuffle eA eB)
            (isometryTensor (padWithZeros eA) (padWithZeros eB) S.ψ) ∧
        T.value = S.value := by
  sorry

end

end MIPStarRE.QPBT
