import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.SwapTransport
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.IdealTarget

/-!
# The joint state estimate of Magic Square rigidity

This file proves the state estimate of `thm:ms-rigidity` on the dilated
strategy: the tensor of the two players' two-qubit controlled-swap embeddings
carries the shared state to within `O(sqrt ε + sqrt δ)` of two EPR pairs
tensored with a residual bipartite vector, and that residual can be normalized
to the unit auxiliary state of the conclusion.

The argument is the coordinatewise one.  The image of the state under the two
embeddings has, at the pair of register labels `(e, f)`, the component

    `(A_e ⊗ B_f) ψ`,

where `A_e` and `B_f` are the residual factors of the two controlled swaps.
Since the two logical pairs are applied in succession, each component factors as
a second-pair component applied to a first-pair component, so the estimates of
`Rigidity/SwapPair.lean` apply twice: once on the state, once on the residual of
the first pair, whose second-pair hypotheses are supplied by
`Rigidity/SwapTransport.lean`.  Every component with `e ≠ f` is small and every
component with `e = f` is close to the one at the zero label; sixteen labels
then give the estimate.

## References

`thm:ms-rigidity`, blueprint `blueprint/src/chapter/ch13_qpbt_test.tex:224-253`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`;
the cited robust self-test is Coladangelo--Stark, arXiv:1709.09267v2,
Theorem 6.9, `references/cs-paper/self-testing.tex:660-730`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

variable {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]

/-! ## Coordinates -/

/-- The coordinates of the action of an operator on a state. -/
theorem applyOperatorToState_coord {ι : Type} [Fintype ι] [DecidableEq ι] (M : Op ι)
    (ψ : EuclideanSpace ℂ ι) (p : ι) :
    applyOperatorToState M ψ p = ∑ q : ι, M p q * ψ q := by
  simp [applyOperatorToState, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct]

/-- The matrix of an isometry given by a family of operators on the residual
space. -/
theorem isometryMatrix_of_family {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ (κ × ι)) (A : κ → Op ι)
    (hφ : ∀ (x : EuclideanSpace ℂ ι) (k : κ) (i : ι),
      φ x (k, i) = applyOperatorToState (A k) x i)
    (k : κ) (i i' : ι) : isometryMatrix φ (k, i) i' = A k i i' := by
  rw [isometryMatrix_apply, hφ, applyOperatorToState_coord]
  simp [EuclideanSpace.equiv, eq_comm]

/-- The two-sided image of a state under two isometries given by families of
operators is the family of placed pairs of those operators. -/
theorem isometryTensor_family_apply {κA κB : Type} [Fintype κA] [DecidableEq κA]
    [Fintype κB] [DecidableEq κB]
    (φA : EuclideanSpace ℂ ιA →ₗᵢ[ℂ] EuclideanSpace ℂ (κA × ιA))
    (φB : EuclideanSpace ℂ ιB →ₗᵢ[ℂ] EuclideanSpace ℂ (κB × ιB))
    (A : κA → Op ιA) (B : κB → Op ιB)
    (hA : ∀ (x : EuclideanSpace ℂ ιA) (k : κA) (i : ιA),
      φA x (k, i) = applyOperatorToState (A k) x i)
    (hB : ∀ (y : EuclideanSpace ℂ ιB) (l : κB) (j : ιB),
      φB y (l, j) = applyOperatorToState (B l) y j)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (k : κA) (i : ιA) (l : κB) (j : ιB) :
    isometryTensor φA φB ψ ((k, i), (l, j)) =
      applyOperatorToState (heteroKron (A k) (B l)) ψ (i, j) := by
  rw [isometryTensor_apply_eq, applyOperatorToState_coord]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hk : (Matrix.kronecker (isometryMatrix φA) (isometryMatrix φB))
      ((k, i), (l, j)) q = isometryMatrix φA (k, i) q.1 * isometryMatrix φB (l, j) q.2 := rfl
  have hh : heteroKron (A k) (B l) (i, j) q = A k i q.1 * B l j q.2 := rfl
  rw [hk, hh, isometryMatrix_of_family φA A hA, isometryMatrix_of_family φB B hB]

/-! ## The target state in coordinates -/

/-- The coordinates of the ideal state of `thm:ms-rigidity`. -/
theorem reindexState_prodShuffle_vecTensor_eprState_apply {V : Type}
    [Fintype V] [DecidableEq V] [Nonempty V]
    (r : EuclideanSpace ℂ (ιA × ιB)) (e f : V) (i : ιA) (j : ιB) :
    reindexState prodShuffle (vecTensor (eprState V) r) ((e, i), (f, j)) =
      (if e = f then ((Real.sqrt (Fintype.card V : ℝ) : ℂ))⁻¹ else 0) * r (i, j) := by
  simp [reindexState, vecTensor, eprState, prodShuffle, EuclideanSpace.equiv]

/-- The cardinality of the two-qubit register. -/
theorem card_two_qubit_register : Fintype.card (Fin 2 → ZMod 2) = 4 := by
  simp

/-! ## From componentwise bounds to the joint estimate -/

omit [DecidableEq ιA] [DecidableEq ιB] in
/-- A vector of a doubly indexed register is bounded by the number of register
labels times a uniform bound on its components. -/
theorem norm_le_card_mul_of_components {κ : Type} [Fintype κ] [DecidableEq κ]
    (u : EuclideanSpace ℂ ((κ × ιA) × (κ × ιB)))
    (D : κ → κ → EuclideanSpace ℂ (ιA × ιB))
    (hD : ∀ (e : κ) (i : ιA) (f : κ) (j : ιB), u ((e, i), (f, j)) = D e f (i, j))
    (s : ℝ) (hs : 0 ≤ s) (hb : ∀ e f, ‖D e f‖ ≤ s) :
    ‖u‖ ≤ (Fintype.card κ : ℝ) * s := by
  have hcomp : ∀ (e f : κ), (∑ i : ιA, ∑ j : ιB, ‖u ((e, i), (f, j))‖ ^ 2) = ‖D e f‖ ^ 2 := by
    intro e f
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hD]
  have hsq : ‖u‖ ^ 2 = ∑ e : κ, ∑ f : κ, ‖D e f‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    have hstep : ∀ p : κ × ιA, (∑ q : κ × ιB, ‖u (p, q)‖ ^ 2) =
        ∑ f : κ, ∑ j : ιB, ‖u (p, (f, j))‖ ^ 2 := fun p => Fintype.sum_prod_type _
    rw [Finset.sum_congr rfl fun p (_ : p ∈ (Finset.univ : Finset (κ × ιA))) => hstep p,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun f _ => hcomp e f
  have hbound : ∑ e : κ, ∑ f : κ, ‖D e f‖ ^ 2 ≤
      (Fintype.card κ : ℝ) * (Fintype.card κ : ℝ) * s ^ 2 := by
    have hrow : ∀ e : κ, (∑ f : κ, ‖D e f‖ ^ 2) ≤ (Fintype.card κ : ℝ) * s ^ 2 := by
      intro e
      calc (∑ f : κ, ‖D e f‖ ^ 2) ≤ ∑ _f : κ, s ^ 2 := by
            refine Finset.sum_le_sum fun f _ => ?_
            have := hb e f
            nlinarith [norm_nonneg (D e f)]
        _ = (Fintype.card κ : ℝ) * s ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc (∑ e : κ, ∑ f : κ, ‖D e f‖ ^ 2) ≤ ∑ _e : κ, (Fintype.card κ : ℝ) * s ^ 2 :=
          Finset.sum_le_sum fun e _ => hrow e
      _ = (Fintype.card κ : ℝ) * (Fintype.card κ : ℝ) * s ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
  have hcard : (0 : ℝ) ≤ (Fintype.card κ : ℝ) := Nat.cast_nonneg _
  nlinarith [hsq, hbound, norm_nonneg u, mul_nonneg hcard hs]

end

end MIPStarRE.QPBT.MagicSquareRigidity
