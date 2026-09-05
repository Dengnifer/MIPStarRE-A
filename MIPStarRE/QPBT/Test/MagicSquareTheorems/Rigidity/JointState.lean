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
/-- The squared norm of a vector of a doubly indexed register is the sum of the
squared norms of its components. -/
theorem norm_sq_eq_sum_components {κA κB : Type} [Fintype κA] [Fintype κB]
    (u : EuclideanSpace ℂ ((κA × ιA) × (κB × ιB)))
    (D : κA → κB → EuclideanSpace ℂ (ιA × ιB))
    (hD : ∀ (e : κA) (i : ιA) (f : κB) (j : ιB), u ((e, i), (f, j)) = D e f (i, j)) :
    ‖u‖ ^ 2 = ∑ e : κA, ∑ f : κB, ‖D e f‖ ^ 2 := by
  have hcomp : ∀ (e : κA) (f : κB),
      (∑ i : ιA, ∑ j : ιB, ‖u ((e, i), (f, j))‖ ^ 2) = ‖D e f‖ ^ 2 := by
    intro e f
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hD]
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  have hstep : ∀ p : κA × ιA, (∑ q : κB × ιB, ‖u (p, q)‖ ^ 2) =
      ∑ f : κB, ∑ j : ιB, ‖u (p, (f, j))‖ ^ 2 := fun p => Fintype.sum_prod_type _
  rw [Finset.sum_congr rfl fun p (_ : p ∈ (Finset.univ : Finset (κA × ιA))) => hstep p,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun f _ => hcomp e f

omit [DecidableEq ιA] [DecidableEq ιB] in
/-- A vector of a doubly indexed register is bounded by the number of register
labels times a uniform bound on its components. -/
theorem norm_le_card_mul_of_components {κ : Type} [Fintype κ] [DecidableEq κ]
    (u : EuclideanSpace ℂ ((κ × ιA) × (κ × ιB)))
    (D : κ → κ → EuclideanSpace ℂ (ιA × ιB))
    (hD : ∀ (e : κ) (i : ιA) (f : κ) (j : ιB), u ((e, i), (f, j)) = D e f (i, j))
    (s : ℝ) (hs : 0 ≤ s) (hb : ∀ e f, ‖D e f‖ ≤ s) :
    ‖u‖ ≤ (Fintype.card κ : ℝ) * s := by
  have hsq : ‖u‖ ^ 2 = ∑ e : κ, ∑ f : κ, ‖D e f‖ ^ 2 :=
    norm_sq_eq_sum_components u D hD
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

/-! ## Residual factors -/

/-- The residual factor of a one-qubit controlled swap at a register label. -/
def swapFactor {ι : Type} [Fintype ι] [DecidableEq ι] (X Z : Op ι) (b : ZMod 2) : Op ι :=
  X ^ b.val * reflectionEffect Z b

/-- The residual factor at the zero label is the positive spectral effect. -/
theorem swapFactor_zero {ι : Type} [Fintype ι] [DecidableEq ι] (X Z : Op ι) :
    swapFactor X Z 0 = reflectionEffect Z 0 := by
  rw [swapFactor, ZMod.val_zero, pow_zero, one_mul]

/-- The residual factor at the unit label is the shift times the negative
spectral effect. -/
theorem swapFactor_one {ι : Type} [Fintype ι] [DecidableEq ι] (X Z : Op ι) :
    swapFactor X Z 1 = X * reflectionEffect Z 1 := by
  rw [swapFactor, ZMod.val_one, pow_one]

/-- The residual factors are contractions. -/
theorem contraction_swapFactor' {ι : Type} [Fintype ι] [DecidableEq ι] {X Z : Op ι}
    (hX : IsBinaryObservable X) (hZ : IsBinaryObservable Z) (b : ZMod 2) :
    (swapFactor X Z b)ᴴ * swapFactor X Z b ≤ 1 :=
  contraction_swapFactor hX hZ b

/-! ## The commutator of an anticommutator with a first-pair reflection -/

/-- The commutator of the anticommutator of the second pair with a first-pair
reflection, from the two commutators of the individual second-pair reflections
and the cross-player agreement of the second pair. -/
theorem norm_anticommutator_comm_first_le
    {X₂A Z₂A Y : Op ιA} {X₂B Z₂B : Op ιB} {t : ℝ}
    (hX₂A : IsBinaryObservable X₂A) (hZ₂A : IsBinaryObservable Z₂A)
    (hX₂B : IsBinaryObservable X₂B) (hZ₂B : IsBinaryObservable Z₂B)
    (hY : IsBinaryObservable Y) (ψ : EuclideanSpace ℂ (ιA × ιB)) (_ht : 0 ≤ t)
    (hx2 : ‖applyOperatorToState
      (heteroKron X₂A (1 : Op ιB) - heteroKron (1 : Op ιA) X₂B) ψ‖ ≤ t)
    (hz2 : ‖applyOperatorToState
      (heteroKron Z₂A (1 : Op ιB) - heteroKron (1 : Op ιA) Z₂B) ψ‖ ≤ t)
    (hcx : ‖applyOperatorToState (heteroKron (X₂A * Y - Y * X₂A) (1 : Op ιB)) ψ‖ ≤ t)
    (hcz : ‖applyOperatorToState (heteroKron (Z₂A * Y - Y * Z₂A) (1 : Op ιB)) ψ‖ ≤ t) :
    ‖applyOperatorToState (heteroKron
        ((X₂A * Z₂A + Z₂A * X₂A) * Y - Y * (X₂A * Z₂A + Z₂A * X₂A)) (1 : Op ιB)) ψ‖ ≤
      8 * t := by
  have hid : (X₂A * Z₂A + Z₂A * X₂A) * Y - Y * (X₂A * Z₂A + Z₂A * X₂A) =
      X₂A * (Z₂A * Y - Y * Z₂A) + (X₂A * Y - Y * X₂A) * Z₂A +
        (Z₂A * (X₂A * Y - Y * X₂A) + (Z₂A * Y - Y * Z₂A) * X₂A) := by
    noncomm_ring
  have hbdX : NormBoundedBy (heteroKron (X₂A * Y - Y * X₂A) (1 : Op ιB)) 2 := by
    have h1 : NormBoundedBy (heteroKron (X₂A * Y) (1 : Op ιB)) (1 * 1) := by
      rw [show heteroKron (X₂A * Y) (1 : Op ιB) =
          heteroKron X₂A (1 : Op ιB) * heteroKron Y (1 : Op ιB) by
        rw [heteroKron_mul, mul_one]]
      exact (normBoundedBy_leftTensor (le_of_eq hX₂A.isometry)).mul
        (normBoundedBy_leftTensor (le_of_eq hY.isometry)) zero_le_one
    have h2 : NormBoundedBy (heteroKron (Y * X₂A) (1 : Op ιB)) (1 * 1) := by
      rw [show heteroKron (Y * X₂A) (1 : Op ιB) =
          heteroKron Y (1 : Op ιB) * heteroKron X₂A (1 : Op ιB) by
        rw [heteroKron_mul, mul_one]]
      exact (normBoundedBy_leftTensor (le_of_eq hY.isometry)).mul
        (normBoundedBy_leftTensor (le_of_eq hX₂A.isometry)) zero_le_one
    have h3 := h1.sub h2
    rw [← heteroKron_sub_left] at h3
    exact h3.mono (by norm_num)
  have hbdZ : NormBoundedBy (heteroKron (Z₂A * Y - Y * Z₂A) (1 : Op ιB)) 2 := by
    have h1 : NormBoundedBy (heteroKron (Z₂A * Y) (1 : Op ιB)) (1 * 1) := by
      rw [show heteroKron (Z₂A * Y) (1 : Op ιB) =
          heteroKron Z₂A (1 : Op ιB) * heteroKron Y (1 : Op ιB) by
        rw [heteroKron_mul, mul_one]]
      exact (normBoundedBy_leftTensor (le_of_eq hZ₂A.isometry)).mul
        (normBoundedBy_leftTensor (le_of_eq hY.isometry)) zero_le_one
    have h2 : NormBoundedBy (heteroKron (Y * Z₂A) (1 : Op ιB)) (1 * 1) := by
      rw [show heteroKron (Y * Z₂A) (1 : Op ιB) =
          heteroKron Y (1 : Op ιB) * heteroKron Z₂A (1 : Op ιB) by
        rw [heteroKron_mul, mul_one]]
      exact (normBoundedBy_leftTensor (le_of_eq hY.isometry)).mul
        (normBoundedBy_leftTensor (le_of_eq hZ₂A.isometry)) zero_le_one
    have h3 := h1.sub h2
    rw [← heteroKron_sub_left] at h3
    exact h3.mono (by norm_num)
  have hT1 : ‖applyOperatorToState
      (heteroKron (X₂A * (Z₂A * Y - Y * Z₂A)) (1 : Op ιB)) ψ‖ ≤ t := by
    rw [show heteroKron (X₂A * (Z₂A * Y - Y * Z₂A)) (1 : Op ιB) =
        heteroKron X₂A (1 : Op ιB) * heteroKron (Z₂A * Y - Y * Z₂A) (1 : Op ιB) by
      rw [heteroKron_mul, mul_one],
      norm_applyOperatorToState_isometry_mul
        (isBinaryObservable_heteroKron_one (ι' := ιB) hX₂A).isometry]
    exact hcz
  have hT2 : ‖applyOperatorToState
      (heteroKron ((X₂A * Y - Y * X₂A) * Z₂A) (1 : Op ιB)) ψ‖ ≤ t + 2 * t :=
    norm_leftTransport_le hbdX (by norm_num) hZ₂B ψ hcx hz2
  have hT3 : ‖applyOperatorToState
      (heteroKron (Z₂A * (X₂A * Y - Y * X₂A)) (1 : Op ιB)) ψ‖ ≤ t := by
    rw [show heteroKron (Z₂A * (X₂A * Y - Y * X₂A)) (1 : Op ιB) =
        heteroKron Z₂A (1 : Op ιB) * heteroKron (X₂A * Y - Y * X₂A) (1 : Op ιB) by
      rw [heteroKron_mul, mul_one],
      norm_applyOperatorToState_isometry_mul
        (isBinaryObservable_heteroKron_one (ι' := ιB) hZ₂A).isometry]
    exact hcx
  have hT4 : ‖applyOperatorToState
      (heteroKron ((Z₂A * Y - Y * Z₂A) * X₂A) (1 : Op ιB)) ψ‖ ≤ t + 2 * t :=
    norm_leftTransport_le hbdZ (by norm_num) hX₂B ψ hcz hx2
  rw [hid, heteroKron_add_left, heteroKron_add_left, heteroKron_add_left,
    applyOperatorToState_add_op, applyOperatorToState_add_op,
    applyOperatorToState_add_op]
  have hs1 := norm_add_le
    (applyOperatorToState (heteroKron (X₂A * (Z₂A * Y - Y * Z₂A)) (1 : Op ιB)) ψ +
      applyOperatorToState (heteroKron ((X₂A * Y - Y * X₂A) * Z₂A) (1 : Op ιB)) ψ)
    (applyOperatorToState (heteroKron (Z₂A * (X₂A * Y - Y * X₂A)) (1 : Op ιB)) ψ +
      applyOperatorToState (heteroKron ((Z₂A * Y - Y * Z₂A) * X₂A) (1 : Op ιB)) ψ)
  have hs2 := norm_add_le
    (applyOperatorToState (heteroKron (X₂A * (Z₂A * Y - Y * Z₂A)) (1 : Op ιB)) ψ)
    (applyOperatorToState (heteroKron ((X₂A * Y - Y * X₂A) * Z₂A) (1 : Op ιB)) ψ)
  have hs3 := norm_add_le
    (applyOperatorToState (heteroKron (Z₂A * (X₂A * Y - Y * X₂A)) (1 : Op ιB)) ψ)
    (applyOperatorToState (heteroKron ((Z₂A * Y - Y * Z₂A) * X₂A) (1 : Op ιB)) ψ)
  linarith [hs1, hs2, hs3, hT1, hT2, hT3, hT4]

/-! ## The second-pair defects on the residual of the first swap -/

section SecondPair

variable {X₁A Z₁A X₂A Z₂A : Op ιA} {X₁B Z₁B X₂B Z₂B : Op ιB} {t : ℝ}

/-- A second-pair cross-player defect, transported to the residual of the first
controlled swap.  The operator `n` is Alice's reflection and `m` is Bob's. -/
theorem norm_secondPair_cross_le
    {n : Op ιA} {m : Op ιB}
    (hX₁A : IsBinaryObservable X₁A) (hZ₁A : IsBinaryObservable Z₁A)
    (hX₁B : IsBinaryObservable X₁B) (hZ₁B : IsBinaryObservable Z₁B)
    (hn : IsBinaryObservable n) (hm : IsBinaryObservable m)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (ht : 0 ≤ t)
    (hN : ‖applyOperatorToState
      (heteroKron n (1 : Op ιB) - heteroKron (1 : Op ιA) m) ψ‖ ≤ t)
    (hz1 : ‖applyOperatorToState
      (heteroKron Z₁A (1 : Op ιB) - heteroKron (1 : Op ιA) Z₁B) ψ‖ ≤ t)
    (hnz : ‖applyOperatorToState (heteroKron (n * Z₁A - Z₁A * n) (1 : Op ιB)) ψ‖ ≤ t)
    (hnx : ‖applyOperatorToState (heteroKron (n * X₁A - X₁A * n) (1 : Op ιB)) ψ‖ ≤ t)
    (hmz : ‖applyOperatorToState (heteroKron (1 : Op ιA) (m * Z₁B - Z₁B * m)) ψ‖ ≤ t)
    (hmx : ‖applyOperatorToState (heteroKron (1 : Op ιA) (m * X₁B - X₁B * m)) ψ‖ ≤ t)
    (b : ZMod 2) :
    ‖applyOperatorToState (heteroKron n (1 : Op ιB) - heteroKron (1 : Op ιA) m)
        (applyOperatorToState
          (heteroKron (swapFactor X₁A Z₁A b) (swapFactor X₁B Z₁B b)) ψ)‖ ≤ 6 * t := by
  rw [← MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul]
  have h := norm_defect_transported_le (n := n) (m := m) hX₁A hZ₁A hX₁B hZ₁B
    (normBoundedBy_leftTensor (le_of_eq hn.isometry))
    (normBoundedBy_rightTensor (le_of_eq hm.isometry)) zero_le_one ψ ht ht hN hz1
    hnz hnx hmz hmx b
  have hrw : heteroKron (swapFactor X₁A Z₁A b) (swapFactor X₁B Z₁B b) =
      heteroKron (X₁A ^ b.val * reflectionEffect Z₁A b)
        (X₁B ^ b.val * reflectionEffect Z₁B b) := rfl
  rw [hrw]
  linarith [h]

/-- Alice's second-pair anticommutator defect, transported to the residual of
the first controlled swap. -/
theorem norm_secondPair_anticommutator_le
    (hX₁A : IsBinaryObservable X₁A) (hZ₁A : IsBinaryObservable Z₁A)
    (hX₁B : IsBinaryObservable X₁B) (hZ₁B : IsBinaryObservable Z₁B)
    (hX₂A : IsBinaryObservable X₂A) (hZ₂A : IsBinaryObservable Z₂A)
    (hX₂B : IsBinaryObservable X₂B) (hZ₂B : IsBinaryObservable Z₂B)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (ht : 0 ≤ t)
    (ha2 : ‖applyOperatorToState
      (heteroKron (X₂A * Z₂A + Z₂A * X₂A) (1 : Op ιB)) ψ‖ ≤ t)
    (hz1 : ‖applyOperatorToState
      (heteroKron Z₁A (1 : Op ιB) - heteroKron (1 : Op ιA) Z₁B) ψ‖ ≤ t)
    (hx2 : ‖applyOperatorToState
      (heteroKron X₂A (1 : Op ιB) - heteroKron (1 : Op ιA) X₂B) ψ‖ ≤ t)
    (hz2 : ‖applyOperatorToState
      (heteroKron Z₂A (1 : Op ιB) - heteroKron (1 : Op ιA) Z₂B) ψ‖ ≤ t)
    (hc1 : ‖applyOperatorToState (heteroKron (X₂A * X₁A - X₁A * X₂A) (1 : Op ιB)) ψ‖ ≤ t)
    (hc2 : ‖applyOperatorToState (heteroKron (X₂A * Z₁A - Z₁A * X₂A) (1 : Op ιB)) ψ‖ ≤ t)
    (hc3 : ‖applyOperatorToState (heteroKron (Z₂A * X₁A - X₁A * Z₂A) (1 : Op ιB)) ψ‖ ≤ t)
    (hc4 : ‖applyOperatorToState (heteroKron (Z₂A * Z₁A - Z₁A * Z₂A) (1 : Op ιB)) ψ‖ ≤ t)
    (b : ZMod 2) :
    ‖applyOperatorToState (heteroKron (X₂A * Z₂A + Z₂A * X₂A) (1 : Op ιB))
        (applyOperatorToState
          (heteroKron (swapFactor X₁A Z₁A b) (swapFactor X₁B Z₁B b)) ψ)‖ ≤ 29 * t := by
  rw [← MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul]
  have hzero : heteroKron (1 : Op ιA) (0 : Op ιB) = 0 := by
    ext p q
    simp [heteroKron, Matrix.kronecker]
  have hκA : NormBoundedBy (heteroKron (X₂A * Z₂A + Z₂A * X₂A) (1 : Op ιB)) 2 := by
    have h1 : NormBoundedBy (heteroKron (X₂A * Z₂A) (1 : Op ιB)) (1 * 1) := by
      rw [show heteroKron (X₂A * Z₂A) (1 : Op ιB) =
          heteroKron X₂A (1 : Op ιB) * heteroKron Z₂A (1 : Op ιB) by
        rw [heteroKron_mul, mul_one]]
      exact (normBoundedBy_leftTensor (le_of_eq hX₂A.isometry)).mul
        (normBoundedBy_leftTensor (le_of_eq hZ₂A.isometry)) zero_le_one
    have h2 : NormBoundedBy (heteroKron (Z₂A * X₂A) (1 : Op ιB)) (1 * 1) := by
      rw [show heteroKron (Z₂A * X₂A) (1 : Op ιB) =
          heteroKron Z₂A (1 : Op ιB) * heteroKron X₂A (1 : Op ιB) by
        rw [heteroKron_mul, mul_one]]
      exact (normBoundedBy_leftTensor (le_of_eq hZ₂A.isometry)).mul
        (normBoundedBy_leftTensor (le_of_eq hX₂A.isometry)) zero_le_one
    have h3 := h1.add h2
    rw [← heteroKron_add_left] at h3
    exact h3.mono (by norm_num)
  have hκB : NormBoundedBy (heteroKron (1 : Op ιA) (0 : Op ιB)) 2 := by
    rw [hzero]
    intro v
    have h0 : applyOperatorToState (0 : Op (ιA × ιB)) v = 0 := by
      simp [applyOperatorToState]
    rw [h0, norm_zero]
    positivity
  have hN : ‖applyOperatorToState (heteroKron (X₂A * Z₂A + Z₂A * X₂A) (1 : Op ιB) -
      heteroKron (1 : Op ιA) (0 : Op ιB)) ψ‖ ≤ t := by
    rw [hzero, sub_zero]
    exact ha2
  have hnz := norm_anticommutator_comm_first_le hX₂A hZ₂A hX₂B hZ₂B hZ₁A ψ ht
    hx2 hz2 hc2 hc4
  have hnx := norm_anticommutator_comm_first_le hX₂A hZ₂A hX₂B hZ₂B hX₁A ψ ht
    hx2 hz2 hc1 hc3
  have hmz : ‖applyOperatorToState
      (heteroKron (1 : Op ιA) ((0 : Op ιB) * Z₁B - Z₁B * (0 : Op ιB))) ψ‖ ≤ 8 * t := by
    rw [zero_mul, mul_zero, sub_zero, hzero]
    have h0 : applyOperatorToState (0 : Op (ιA × ιB)) ψ = 0 := by
      simp [applyOperatorToState]
    rw [h0, norm_zero]
    linarith
  have hmx : ‖applyOperatorToState
      (heteroKron (1 : Op ιA) ((0 : Op ιB) * X₁B - X₁B * (0 : Op ιB))) ψ‖ ≤ 8 * t := by
    rw [zero_mul, mul_zero, sub_zero, hzero]
    have h0 : applyOperatorToState (0 : Op (ιA × ιB)) ψ = 0 := by
      simp [applyOperatorToState]
    rw [h0, norm_zero]
    linarith
  have h := norm_defect_transported_le (n := X₂A * Z₂A + Z₂A * X₂A) (m := (0 : Op ιB))
    hX₁A hZ₁A hX₁B hZ₁B hκA hκB (by norm_num) ψ ht (by linarith) hN hz1 hnz hnx hmz hmx b
  have hrw : heteroKron (swapFactor X₁A Z₁A b) (swapFactor X₁B Z₁B b) =
      heteroKron (X₁A ^ b.val * reflectionEffect Z₁A b)
        (X₁B ^ b.val * reflectionEffect Z₁B b) := rfl
  rw [hrw]
  rw [hzero, sub_zero] at h
  linarith [h]

end SecondPair

/-! ## The joint state estimate -/

/-- Two register labels of the two-qubit register agree as soon as their two
coordinates do. -/
theorem pi_fin_two_ext {α : Type*} {e f : Fin 2 → α} (h0 : e 0 = f 0) (h1 : e 1 = f 1) :
    e = f := by
  funext i
  fin_cases i
  · exact h0
  · exact h1

/-- The square root of the two-qubit register cardinality. -/
theorem sqrt_card_two_qubit_register :
    ((Real.sqrt ((Fintype.card (Fin 2 → ZMod 2) : ℕ) : ℝ) : ℂ)) = 2 := by
  rw [card_two_qubit_register]
  norm_num

/-- The state estimate of `thm:ms-rigidity` on a bipartite state carrying two
approximately anticommuting pairs per player which approximately agree across
the players and approximately commute with each other: the tensor of the two
two-qubit controlled-swap embeddings carries the state to within `116 t` of two
EPR pairs tensored with a residual bipartite vector. -/
theorem exists_residual_of_two_pairs
    (X₁A Z₁A X₂A Z₂A : Op ιA) (X₁B Z₁B X₂B Z₂B : Op ιB)
    (hX₁A : IsBinaryObservable X₁A) (hZ₁A : IsBinaryObservable Z₁A)
    (hX₂A : IsBinaryObservable X₂A) (hZ₂A : IsBinaryObservable Z₂A)
    (hX₁B : IsBinaryObservable X₁B) (hZ₁B : IsBinaryObservable Z₁B)
    (hX₂B : IsBinaryObservable X₂B) (hZ₂B : IsBinaryObservable Z₂B)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (t : ℝ) (ht : 0 ≤ t)
    (hx1 : ‖applyOperatorToState
      (heteroKron X₁A (1 : Op ιB) - heteroKron (1 : Op ιA) X₁B) ψ‖ ≤ t)
    (hz1 : ‖applyOperatorToState
      (heteroKron Z₁A (1 : Op ιB) - heteroKron (1 : Op ιA) Z₁B) ψ‖ ≤ t)
    (hx2 : ‖applyOperatorToState
      (heteroKron X₂A (1 : Op ιB) - heteroKron (1 : Op ιA) X₂B) ψ‖ ≤ t)
    (hz2 : ‖applyOperatorToState
      (heteroKron Z₂A (1 : Op ιB) - heteroKron (1 : Op ιA) Z₂B) ψ‖ ≤ t)
    (ha1 : ‖applyOperatorToState
      (heteroKron (X₁A * Z₁A + Z₁A * X₁A) (1 : Op ιB)) ψ‖ ≤ t)
    (ha2 : ‖applyOperatorToState
      (heteroKron (X₂A * Z₂A + Z₂A * X₂A) (1 : Op ιB)) ψ‖ ≤ t)
    (hc1 : ‖applyOperatorToState (heteroKron (X₂A * X₁A - X₁A * X₂A) (1 : Op ιB)) ψ‖ ≤ t)
    (hc2 : ‖applyOperatorToState (heteroKron (X₂A * Z₁A - Z₁A * X₂A) (1 : Op ιB)) ψ‖ ≤ t)
    (hc3 : ‖applyOperatorToState (heteroKron (Z₂A * X₁A - X₁A * Z₂A) (1 : Op ιB)) ψ‖ ≤ t)
    (hc4 : ‖applyOperatorToState (heteroKron (Z₂A * Z₁A - Z₁A * Z₂A) (1 : Op ιB)) ψ‖ ≤ t)
    (hd1 : ‖applyOperatorToState (heteroKron (1 : Op ιA) (X₂B * X₁B - X₁B * X₂B)) ψ‖ ≤ t)
    (hd2 : ‖applyOperatorToState (heteroKron (1 : Op ιA) (X₂B * Z₁B - Z₁B * X₂B)) ψ‖ ≤ t)
    (hd3 : ‖applyOperatorToState (heteroKron (1 : Op ιA) (Z₂B * X₁B - X₁B * Z₂B)) ψ‖ ≤ t)
    (hd4 : ‖applyOperatorToState (heteroKron (1 : Op ιA) (Z₂B * Z₁B - Z₁B * Z₂B)) ψ‖ ≤ t) :
    ∃ r : EuclideanSpace ℂ (ιA × ιB),
      ‖isometryTensor
          (twoBinarySwapIsometry X₁A Z₁A X₂A Z₂A hX₁A hZ₁A hX₂A hZ₂A)
          (twoBinarySwapIsometry X₁B Z₁B X₂B Z₂B hX₁B hZ₁B hX₂B hZ₂B) ψ -
        reindexState prodShuffle
          (vecTensor (eprState (Fin 2 → ZMod 2)) r)‖ ≤ 116 * t := by
  classical
  obtain ⟨W, hW⟩ : ∃ W : ZMod 2 → ZMod 2 → EuclideanSpace ℂ (ιA × ιB),
      ∀ b c, W b c = applyOperatorToState
        (heteroKron (swapFactor X₁A Z₁A b) (swapFactor X₁B Z₁B c)) ψ :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : (Fin 2 → ZMod 2) → (Fin 2 → ZMod 2) →
      EuclideanSpace ℂ (ιA × ιB),
      ∀ e f, C e f = applyOperatorToState
        (heteroKron (swapFactor X₂A Z₂A (e 1)) (swapFactor X₂B Z₂B (f 1)))
        (W (e 0) (f 0)) := ⟨_, fun _ _ => rfl⟩
  -- contractions of the second-pair residual factors
  have hSA : ∀ c : ZMod 2, (swapFactor X₂A Z₂A c)ᴴ * swapFactor X₂A Z₂A c ≤ 1 :=
    fun c => contraction_swapFactor' hX₂A hZ₂A c
  have hSB : ∀ c : ZMod 2, (swapFactor X₂B Z₂B c)ᴴ * swapFactor X₂B Z₂B c ≤ 1 :=
    fun c => contraction_swapFactor' hX₂B hZ₂B c
  have hSprod : ∀ c c' : ZMod 2,
      (heteroKron (swapFactor X₂A Z₂A c) (swapFactor X₂B Z₂B c'))ᴴ *
        heteroKron (swapFactor X₂A Z₂A c) (swapFactor X₂B Z₂B c') ≤ 1 :=
    fun c c' => contraction_heteroKron (hSA c) (hSB c')
  -- the first pair on the state
  have hW01 : ‖W 0 1‖ ≤ t / 2 := by
    rw [hW, show heteroKron (swapFactor X₁A Z₁A 0) (swapFactor X₁B Z₁B 1) =
        heteroKron (reflectionEffect Z₁A 0) (X₁B * reflectionEffect Z₁B 1) by
      rw [swapFactor_zero, swapFactor_one]]
    linarith [norm_swapComponent_01_le (ZB := Z₁B) hZ₁A hX₁B ψ, hz1]
  have hW10 : ‖W 1 0‖ ≤ t / 2 := by
    rw [hW, show heteroKron (swapFactor X₁A Z₁A 1) (swapFactor X₁B Z₁B 0) =
        heteroKron (X₁A * reflectionEffect Z₁A 1) (reflectionEffect Z₁B 0) by
      rw [swapFactor_zero, swapFactor_one]]
    linarith [norm_swapComponent_10_le (ZB := Z₁B) hX₁A hZ₁A ψ, hz1]
  have hWdiag : ‖W 1 1 - W 0 0‖ ≤ 5 * t / 2 := by
    rw [hW, hW, show heteroKron (swapFactor X₁A Z₁A 1) (swapFactor X₁B Z₁B 1) =
        heteroKron (X₁A * reflectionEffect Z₁A 1) (X₁B * reflectionEffect Z₁B 1) by
      rw [swapFactor_one, swapFactor_one],
      show heteroKron (swapFactor X₁A Z₁A 0) (swapFactor X₁B Z₁B 0) =
        heteroKron (reflectionEffect Z₁A 0) (reflectionEffect Z₁B 0) by
      rw [swapFactor_zero, swapFactor_zero]]
    linarith [norm_swapComponent_diag_sub_le hX₁A hZ₁A hX₁B hZ₁B ψ, hz1, hx1, ha1]
  -- the second pair on the residual of the first
  have hdz : ∀ b : ZMod 2, ‖applyOperatorToState
      (heteroKron Z₂A (1 : Op ιB) - heteroKron (1 : Op ιA) Z₂B) (W b b)‖ ≤ 6 * t := by
    intro b
    rw [hW]
    exact norm_secondPair_cross_le hX₁A hZ₁A hX₁B hZ₁B hZ₂A hZ₂B ψ ht hz2 hz1
      hc4 hc3 hd4 hd3 b
  have hdx : ∀ b : ZMod 2, ‖applyOperatorToState
      (heteroKron X₂A (1 : Op ιB) - heteroKron (1 : Op ιA) X₂B) (W b b)‖ ≤ 6 * t := by
    intro b
    rw [hW]
    exact norm_secondPair_cross_le hX₁A hZ₁A hX₁B hZ₁B hX₂A hX₂B ψ ht hx2 hz1
      hc2 hc1 hd2 hd1 b
  have hda : ∀ b : ZMod 2, ‖applyOperatorToState
      (heteroKron (X₂A * Z₂A + Z₂A * X₂A) (1 : Op ιB)) (W b b)‖ ≤ 29 * t := by
    intro b
    rw [hW]
    exact norm_secondPair_anticommutator_le hX₁A hZ₁A hX₁B hZ₁B hX₂A hZ₂A hX₂B hZ₂B
      ψ ht ha2 hz1 hx2 hz2 hc1 hc2 hc3 hc4 b
  -- the sixteen components
  have hCcontr : ∀ (e f : Fin 2 → ZMod 2), ‖C e f‖ ≤ ‖W (e 0) (f 0)‖ := by
    intro e f
    rw [hC]
    exact norm_applyOperatorToState_le (hSprod (e 1) (f 1)) _
  have hCoff0 : ∀ e f : Fin 2 → ZMod 2, e 0 ≠ f 0 → ‖C e f‖ ≤ 29 * t := by
    intro e f hne
    have hb : ‖W (e 0) (f 0)‖ ≤ t / 2 := by
      rcases zmod_two_eq_zero_or_one (e 0) with h0 | h0 <;>
        rcases zmod_two_eq_zero_or_one (f 0) with h1 | h1 <;>
          rw [h0, h1] at hne ⊢
      · exact absurd rfl hne
      · exact hW01
      · exact hW10
      · exact absurd rfl hne
    linarith [hCcontr e f, hb]
  have hCoff1 : ∀ e f : Fin 2 → ZMod 2, e 0 = f 0 → e 1 ≠ f 1 → ‖C e f‖ ≤ 29 * t := by
    intro e f h0 hne
    rw [hC, ← h0]
    rcases zmod_two_eq_zero_or_one (e 1) with h1 | h1 <;>
      rcases zmod_two_eq_zero_or_one (f 1) with h2 | h2 <;> rw [h1, h2] at hne ⊢
    · exact absurd rfl hne
    · rw [show heteroKron (swapFactor X₂A Z₂A 0) (swapFactor X₂B Z₂B 1) =
          heteroKron (reflectionEffect Z₂A 0) (X₂B * reflectionEffect Z₂B 1) by
        rw [swapFactor_zero, swapFactor_one]]
      linarith [norm_swapComponent_01_le (ZB := Z₂B) hZ₂A hX₂B (W (e 0) (e 0)),
        hdz (e 0)]
    · rw [show heteroKron (swapFactor X₂A Z₂A 1) (swapFactor X₂B Z₂B 0) =
          heteroKron (X₂A * reflectionEffect Z₂A 1) (reflectionEffect Z₂B 0) by
        rw [swapFactor_zero, swapFactor_one]]
      linarith [norm_swapComponent_10_le (ZB := Z₂B) hX₂A hZ₂A (W (e 0) (e 0)),
        hdz (e 0)]
    · exact absurd rfl hne
  have hCzero : C 0 0 = applyOperatorToState
      (heteroKron (swapFactor X₂A Z₂A 0) (swapFactor X₂B Z₂B 0)) (W 0 0) := by
    rw [hC]
    simp
  have hCdiag : ∀ e : Fin 2 → ZMod 2, ‖C e e - C 0 0‖ ≤ 29 * t := by
    intro e
    have hmid : ‖applyOperatorToState
        (heteroKron (swapFactor X₂A Z₂A 0) (swapFactor X₂B Z₂B 0)) (W (e 0) (e 0)) -
        C 0 0‖ ≤ 5 * t / 2 := by
      rw [hCzero, applyOperatorToState_sub_vec]
      refine le_trans (norm_applyOperatorToState_le (hSprod 0 0) _) ?_
      rcases zmod_two_eq_zero_or_one (e 0) with h0 | h0 <;> rw [h0]
      · simp
        linarith
      · exact hWdiag
    have hfirst : ‖C e e - applyOperatorToState
        (heteroKron (swapFactor X₂A Z₂A 0) (swapFactor X₂B Z₂B 0)) (W (e 0) (e 0))‖ ≤
        53 * t / 2 := by
      rw [hC]
      rcases zmod_two_eq_zero_or_one (e 1) with h1 | h1 <;> rw [h1]
      · simp
        linarith
      · rw [show heteroKron (swapFactor X₂A Z₂A 1) (swapFactor X₂B Z₂B 1) =
            heteroKron (X₂A * reflectionEffect Z₂A 1) (X₂B * reflectionEffect Z₂B 1) by
          rw [swapFactor_one, swapFactor_one],
          show heteroKron (swapFactor X₂A Z₂A 0) (swapFactor X₂B Z₂B 0) =
            heteroKron (reflectionEffect Z₂A 0) (reflectionEffect Z₂B 0) by
          rw [swapFactor_zero, swapFactor_zero]]
        linarith [norm_swapComponent_diag_sub_le hX₂A hZ₂A hX₂B hZ₂B (W (e 0) (e 0)),
          hdz (e 0), hdx (e 0), hda (e 0)]
    have htri := norm_sub_le_norm_sub_add_norm_sub (C e e)
      (applyOperatorToState
        (heteroKron (swapFactor X₂A Z₂A 0) (swapFactor X₂B Z₂B 0)) (W (e 0) (e 0)))
      (C 0 0)
    linarith [htri, hmid, hfirst]
  -- assemble
  refine ⟨(2 : ℂ) • C 0 0, ?_⟩
  have hfamA : ∀ (x : EuclideanSpace ℂ ιA) (e : Fin 2 → ZMod 2) (i : ιA),
      twoBinarySwapIsometry X₁A Z₁A X₂A Z₂A hX₁A hZ₁A hX₂A hZ₂A x (e, i) =
        applyOperatorToState
          (swapFactor X₂A Z₂A (e 1) * swapFactor X₁A Z₁A (e 0)) x i :=
    fun _ _ _ => rfl
  have hfamB : ∀ (y : EuclideanSpace ℂ ιB) (f : Fin 2 → ZMod 2) (j : ιB),
      twoBinarySwapIsometry X₁B Z₁B X₂B Z₂B hX₁B hZ₁B hX₂B hZ₂B y (f, j) =
        applyOperatorToState
          (swapFactor X₂B Z₂B (f 1) * swapFactor X₁B Z₁B (f 0)) y j :=
    fun _ _ _ => rfl
  have hcoord : ∀ (e : Fin 2 → ZMod 2) (i : ιA) (f : Fin 2 → ZMod 2) (j : ιB),
      (isometryTensor
          (twoBinarySwapIsometry X₁A Z₁A X₂A Z₂A hX₁A hZ₁A hX₂A hZ₂A)
          (twoBinarySwapIsometry X₁B Z₁B X₂B Z₂B hX₁B hZ₁B hX₂B hZ₂B) ψ -
        reindexState prodShuffle
          (vecTensor (eprState (Fin 2 → ZMod 2)) ((2 : ℂ) • C 0 0))) ((e, i), (f, j)) =
      (C e f - (if e = f then C 0 0 else 0)) (i, j) := by
    intro e i f j
    have hLHS : isometryTensor
        (twoBinarySwapIsometry X₁A Z₁A X₂A Z₂A hX₁A hZ₁A hX₂A hZ₂A)
        (twoBinarySwapIsometry X₁B Z₁B X₂B Z₂B hX₁B hZ₁B hX₂B hZ₂B) ψ
          ((e, i), (f, j)) = C e f (i, j) := by
      rw [isometryTensor_family_apply _ _
        (fun e : Fin 2 → ZMod 2 => swapFactor X₂A Z₂A (e 1) * swapFactor X₁A Z₁A (e 0))
        (fun f : Fin 2 → ZMod 2 => swapFactor X₂B Z₂B (f 1) * swapFactor X₁B Z₁B (f 0))
        hfamA hfamB, hC, hW,
        ← MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul, heteroKron_mul]
    have hRHS : reindexState prodShuffle
        (vecTensor (eprState (Fin 2 → ZMod 2)) ((2 : ℂ) • C 0 0)) ((e, i), (f, j)) =
        (if e = f then C 0 0 else 0) (i, j) := by
      rw [reindexState_prodShuffle_vecTensor_eprState_apply, sqrt_card_two_qubit_register]
      by_cases hef : e = f
      · rw [if_pos hef, if_pos hef, PiLp.smul_apply, smul_eq_mul, ← mul_assoc,
          inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_mul]
      · rw [if_neg hef, if_neg hef]
        simp
    rw [PiLp.sub_apply, PiLp.sub_apply, hLHS, hRHS]
  have hbound : ∀ e f : Fin 2 → ZMod 2,
      ‖C e f - (if e = f then C 0 0 else 0)‖ ≤ 29 * t := by
    intro e f
    by_cases hef : e = f
    · rw [if_pos hef]
      subst hef
      exact hCdiag e
    · rw [if_neg hef, sub_zero]
      by_cases h0 : e 0 = f 0
      · exact hCoff1 e f h0 (fun h1 => hef (pi_fin_two_ext h0 h1))
      · exact hCoff0 e f h0
  have hfinal := norm_le_card_mul_of_components
    (isometryTensor
        (twoBinarySwapIsometry X₁A Z₁A X₂A Z₂A hX₁A hZ₁A hX₂A hZ₂A)
        (twoBinarySwapIsometry X₁B Z₁B X₂B Z₂B hX₁B hZ₁B hX₂B hZ₂B) ψ -
      reindexState prodShuffle
        (vecTensor (eprState (Fin 2 → ZMod 2)) ((2 : ℂ) • C 0 0)))
    (fun e f => C e f - (if e = f then C 0 0 else 0)) hcoord (29 * t) (by linarith) hbound
  rw [card_two_qubit_register] at hfinal
  norm_num at hfinal
  linarith [hfinal]

/-! ## Normalizing the residual -/

/-- The coordinate tensor is homogeneous in its second argument. -/
theorem vecTensor_smul_right {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (c : ℂ) (u : EuclideanSpace ℂ ι) (v : EuclideanSpace ℂ κ) :
    vecTensor u (c • v) = c • vecTensor u v := by
  ext p
  simp [vecTensor, EuclideanSpace.equiv]
  ring

/-- Reindexing is homogeneous. -/
theorem reindexState_smul {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (c : ℂ) (x : EuclideanSpace ℂ ι) :
    reindexState e (c • x) = c • reindexState e x := by
  ext p
  simp [reindexState, EuclideanSpace.equiv]

/-- The residual of the joint state estimate can be replaced by a unit vector at
twice the cost.  This is the normalization step of the conclusion of
`thm:ms-rigidity`, whose auxiliary state is required to be a unit vector. -/
theorem exists_unit_residual {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (u : EuclideanSpace ℂ ((V × ιA) × (V × ιB))) (hu : ‖u‖ = 1)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (hψ : ‖ψ‖ = 1) (c : ℝ)
    (r0 : EuclideanSpace ℂ (ιA × ιB))
    (h : ‖u - reindexState prodShuffle (vecTensor (eprState V) r0)‖ ≤ c) :
    ∃ r : EuclideanSpace ℂ (ιA × ιB), ‖r‖ = 1 ∧
      ‖u - reindexState prodShuffle (vecTensor (eprState V) r)‖ ≤ 2 * c := by
  have htarget : ∀ r : EuclideanSpace ℂ (ιA × ιB),
      ‖reindexState prodShuffle (vecTensor (eprState V) r)‖ = ‖r‖ :=
    fun r => norm_reindexState_prodShuffle_vecTensor_eprState r
  have hgap : |1 - ‖r0‖| ≤ c := by
    have h1 := abs_norm_sub_norm_le u
      (reindexState prodShuffle (vecTensor (eprState V) r0))
    rw [hu, htarget] at h1
    exact le_trans h1 h
  have hc0 : 0 ≤ c := le_trans (abs_nonneg _) hgap
  by_cases h0 : r0 = 0
  · refine ⟨ψ, hψ, ?_⟩
    have h1 : (1 : ℝ) ≤ c := by
      rw [h0, norm_zero] at hgap
      simpa using hgap
    calc ‖u - reindexState prodShuffle (vecTensor (eprState V) ψ)‖
        ≤ ‖u‖ + ‖reindexState prodShuffle (vecTensor (eprState V) ψ)‖ := norm_sub_le _ _
      _ = 2 := by rw [hu, htarget, hψ]; norm_num
      _ ≤ 2 * c := by linarith
  · have hN : 0 < ‖r0‖ := norm_pos_iff.mpr h0
    refine ⟨((‖r0‖ : ℝ) : ℂ)⁻¹ • r0, ?_, ?_⟩
    · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hN,
        inv_mul_cancel₀ (ne_of_gt hN)]
    · have hscal : reindexState prodShuffle
          (vecTensor (eprState V) (((‖r0‖ : ℝ) : ℂ)⁻¹ • r0)) =
          ((‖r0‖ : ℝ) : ℂ)⁻¹ • reindexState prodShuffle (vecTensor (eprState V) r0) := by
        rw [vecTensor_smul_right, reindexState_smul]
      have hdiff : ‖reindexState prodShuffle (vecTensor (eprState V) r0) -
          reindexState prodShuffle
            (vecTensor (eprState V) (((‖r0‖ : ℝ) : ℂ)⁻¹ • r0))‖ = |1 - ‖r0‖| := by
        have hcollect : reindexState prodShuffle (vecTensor (eprState V) r0) -
            ((‖r0‖ : ℝ) : ℂ)⁻¹ •
              reindexState prodShuffle (vecTensor (eprState V) r0) =
            ((1 : ℂ) - ((‖r0‖ : ℝ) : ℂ)⁻¹) •
              reindexState prodShuffle (vecTensor (eprState V) r0) := by
          module
        have hs : ‖(1 : ℂ) - ((‖r0‖ : ℝ) : ℂ)⁻¹‖ = |1 - ‖r0‖⁻¹| := by
          rw [show (1 : ℂ) - ((‖r0‖ : ℝ) : ℂ)⁻¹ = (((1 - ‖r0‖⁻¹ : ℝ)) : ℂ) by
            push_cast
            ring]
          rw [Complex.norm_real, Real.norm_eq_abs]
        have hfin : |1 - ‖r0‖⁻¹| * ‖r0‖ = |1 - ‖r0‖| := by
          have h1 : (1 - ‖r0‖⁻¹) * ‖r0‖ = -(1 - ‖r0‖) := by
            field_simp
            ring
          calc |1 - ‖r0‖⁻¹| * ‖r0‖ = |1 - ‖r0‖⁻¹| * |‖r0‖| := by rw [abs_of_pos hN]
            _ = |(1 - ‖r0‖⁻¹) * ‖r0‖| := (abs_mul _ _).symm
            _ = |-(1 - ‖r0‖)| := by rw [h1]
            _ = |1 - ‖r0‖| := abs_neg _
        rw [hscal, hcollect, norm_smul, htarget, hs, hfin]
      have htri := norm_sub_le_norm_sub_add_norm_sub u
        (reindexState prodShuffle (vecTensor (eprState V) r0))
        (reindexState prodShuffle (vecTensor (eprState V) (((‖r0‖ : ℝ) : ℂ)⁻¹ • r0)))
      rw [hdiff] at htri
      linarith [htri, h, hgap]

end

end MIPStarRE.QPBT.MagicSquareRigidity
