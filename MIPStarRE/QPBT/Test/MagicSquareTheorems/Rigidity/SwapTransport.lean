import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.SwapPair

/-!
# Transport of the second logical pair through the first controlled swap

The two-qubit controlled swap of `Rigidity/TwoQubitSwap.lean` applies the first
logical pair innermost.  Its residual after the first pair is therefore not the
shared state but the vector

    `v_b = (X_1^b P^{Z_1}_b ⊗ Y_1^b P^{W_1}_b) ψ`,

and the estimates of `Rigidity/SwapPair.lean` are applied to the second logical
pair *on that vector*.  This file transports the state-dependent hypotheses of
the second pair from `ψ` to `v_b`, at the cost of the commutation defects
between the two pairs and of the cross-player agreement of the first pair.

The two mechanisms are elementary and are isolated as
`norm_leftTransport_le` / `norm_rightTransport_le` — a commutator evaluated on
`Z ψ` is controlled by the same commutator on `ψ` once Alice's reflection is
traded for Bob's, which commutes with everything on Alice's side — and
`norm_mul_le_commutator_add`, which moves an operator across the residual
factor at the cost of its commutator with that factor.

## References

blueprint `thm:ms-rigidity`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`;
the cited robust self-test is Coladangelo--Stark, arXiv:1709.09267v2,
Theorem 6.9, `references/cs-paper/self-testing.tex:660-730`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

variable {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]

/-! ## A state-independent norm bound -/

/-- Formalization-only bookkeeping predicate: the operator `M` multiplies norms
by at most `c`.  It records the crude operator-norm bounds that the transport
estimates below need for operators which are sums of products of contractions
and hence not contractions themselves. -/
def NormBoundedBy {ι : Type} [Fintype ι] [DecidableEq ι] (M : Op ι) (c : ℝ) : Prop :=
  ∀ v : EuclideanSpace ℂ ι, ‖applyOperatorToState M v‖ ≤ c * ‖v‖

namespace NormBoundedBy

variable {ι : Type} [Fintype ι] [DecidableEq ι] {M N : Op ι} {a b : ℝ}

/-- A contraction has norm bound one. -/
theorem of_contraction (h : Mᴴ * M ≤ 1) : NormBoundedBy M 1 := fun v => by
  simpa using norm_applyOperatorToState_le h v

/-- Norm bounds are monotone in the constant. -/
theorem mono (h : NormBoundedBy M a) (hab : a ≤ b) : NormBoundedBy M b := fun v => by
  have h1 := h v
  nlinarith [norm_nonneg v]

/-- Norm bounds add over sums. -/
theorem add (hM : NormBoundedBy M a) (hN : NormBoundedBy N b) :
    NormBoundedBy (M + N) (a + b) := fun v => by
  rw [applyOperatorToState_add_op]
  refine le_trans (norm_add_le _ _) ?_
  have h1 := hM v
  have h2 := hN v
  nlinarith

/-- Norm bounds add over differences. -/
theorem sub (hM : NormBoundedBy M a) (hN : NormBoundedBy N b) :
    NormBoundedBy (M - N) (a + b) := fun v => by
  rw [applyOperatorToState_sub_op]
  refine le_trans (norm_sub_le _ _) ?_
  have h1 := hM v
  have h2 := hN v
  nlinarith

/-- Norm bounds multiply over products. -/
theorem mul (hM : NormBoundedBy M a) (hN : NormBoundedBy N b) (ha : 0 ≤ a) :
    NormBoundedBy (M * N) (a * b) := fun v => by
  rw [MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul]
  have h1 := hM (applyOperatorToState N v)
  have h2 := hN v
  nlinarith

end NormBoundedBy

/-- The left placement of a contraction has norm bound one. -/
theorem normBoundedBy_leftTensor {M : Op ιA} (hM : Mᴴ * M ≤ 1) :
    NormBoundedBy (heteroKron M (1 : Op ιB)) 1 :=
  NormBoundedBy.of_contraction (conjTranspose_mul_le_one_leftTensor hM)

/-- The right placement of a contraction has norm bound one. -/
theorem normBoundedBy_rightTensor {N : Op ιB} (hN : Nᴴ * N ≤ 1) :
    NormBoundedBy (heteroKron (1 : Op ιA) N) 1 :=
  NormBoundedBy.of_contraction (conjTranspose_mul_le_one_rightTensor hN)

/-! ## Trading one player's reflection for the other's -/

/-- Alice's operator applied after her own binary reflection is controlled by
the same operator applied to the state, once her reflection is traded for Bob's
agreeing one.  This is the mechanism that lets a commutation estimate valid on
the state be used on a vector obtained by acting with the first pair. -/
theorem norm_leftTransport_le {K P : Op ιA} {Q : Op ιB} {κ a d : ℝ}
    (hκ : NormBoundedBy (heteroKron K (1 : Op ιB)) κ) (hκ0 : 0 ≤ κ)
    (hQ : IsBinaryObservable Q) (ψ : EuclideanSpace ℂ (ιA × ιB))
    (hK : ‖applyOperatorToState (heteroKron K (1 : Op ιB)) ψ‖ ≤ a)
    (hPQ : ‖applyOperatorToState
      (heteroKron P (1 : Op ιB) - heteroKron (1 : Op ιA) Q) ψ‖ ≤ d) :
    ‖applyOperatorToState (heteroKron (K * P) (1 : Op ιB)) ψ‖ ≤ a + κ * d := by
  have hsplit : heteroKron (K * P) (1 : Op ιB) =
      heteroKron K (1 : Op ιB) * heteroKron P (1 : Op ιB) := by
    rw [heteroKron_mul, mul_one]
  have hcomm : heteroKron K (1 : Op ιB) * heteroKron (1 : Op ιA) Q =
      heteroKron (1 : Op ιA) Q * heteroKron K (1 : Op ιB) :=
    heteroKron_left_comm_right K Q
  have hop : heteroKron (K * P) (1 : Op ιB) =
      heteroKron (1 : Op ιA) Q * heteroKron K (1 : Op ιB) +
        heteroKron K (1 : Op ιB) *
          (heteroKron P (1 : Op ιB) - heteroKron (1 : Op ιA) Q) := by
    rw [hsplit, ← hcomm]
    noncomm_ring
  have hdecomp : applyOperatorToState (heteroKron (K * P) (1 : Op ιB)) ψ =
      applyOperatorToState (heteroKron (1 : Op ιA) Q)
          (applyOperatorToState (heteroKron K (1 : Op ιB)) ψ) +
        applyOperatorToState (heteroKron K (1 : Op ιB))
          (applyOperatorToState (heteroKron P (1 : Op ιB) -
            heteroKron (1 : Op ιA) Q) ψ) := by
    rw [hop, applyOperatorToState_add_op,
      MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul,
      MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul]
  rw [hdecomp]
  refine le_trans (norm_add_le _ _) ?_
  have h1 : ‖applyOperatorToState (heteroKron (1 : Op ιA) Q)
      (applyOperatorToState (heteroKron K (1 : Op ιB)) ψ)‖ ≤ a := by
    rw [norm_applyOperatorToState_of_isometry
      (isBinaryObservable_heteroKron_right (ι := ιA) hQ).isometry]
    exact hK
  have h2 := hκ (applyOperatorToState
    (heteroKron P (1 : Op ιB) - heteroKron (1 : Op ιA) Q) ψ)
  nlinarith [h1, h2, hPQ, norm_nonneg (applyOperatorToState
    (heteroKron P (1 : Op ιB) - heteroKron (1 : Op ιA) Q) ψ)]

/-- Bob's operator applied after his own binary reflection is controlled by the
same operator applied to the state, once his reflection is traded for Alice's
agreeing one.  This is `norm_leftTransport_le` with the players exchanged. -/
theorem norm_rightTransport_le {K Q : Op ιB} {P : Op ιA} {κ a d : ℝ}
    (hκ : NormBoundedBy (heteroKron (1 : Op ιA) K) κ) (hκ0 : 0 ≤ κ)
    (hP : IsBinaryObservable P) (ψ : EuclideanSpace ℂ (ιA × ιB))
    (hK : ‖applyOperatorToState (heteroKron (1 : Op ιA) K) ψ‖ ≤ a)
    (hPQ : ‖applyOperatorToState
      (heteroKron P (1 : Op ιB) - heteroKron (1 : Op ιA) Q) ψ‖ ≤ d) :
    ‖applyOperatorToState (heteroKron (1 : Op ιA) (K * Q)) ψ‖ ≤ a + κ * d := by
  have hsplit : heteroKron (1 : Op ιA) (K * Q) =
      heteroKron (1 : Op ιA) K * heteroKron (1 : Op ιA) Q := by
    rw [heteroKron_mul, mul_one]
  have hcomm : heteroKron (1 : Op ιA) K * heteroKron P (1 : Op ιB) =
      heteroKron P (1 : Op ιB) * heteroKron (1 : Op ιA) K :=
    (heteroKron_left_comm_right P K).symm
  have hop : heteroKron (1 : Op ιA) (K * Q) =
      heteroKron P (1 : Op ιB) * heteroKron (1 : Op ιA) K -
        heteroKron (1 : Op ιA) K *
          (heteroKron P (1 : Op ιB) - heteroKron (1 : Op ιA) Q) := by
    rw [hsplit, ← hcomm]
    noncomm_ring
  have hdecomp : applyOperatorToState (heteroKron (1 : Op ιA) (K * Q)) ψ =
      applyOperatorToState (heteroKron P (1 : Op ιB))
          (applyOperatorToState (heteroKron (1 : Op ιA) K) ψ) -
        applyOperatorToState (heteroKron (1 : Op ιA) K)
          (applyOperatorToState (heteroKron P (1 : Op ιB) -
            heteroKron (1 : Op ιA) Q) ψ) := by
    rw [hop, applyOperatorToState_sub_op,
      MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul,
      MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul]
  rw [hdecomp]
  refine le_trans (norm_sub_le _ _) ?_
  have h1 : ‖applyOperatorToState (heteroKron P (1 : Op ιB))
      (applyOperatorToState (heteroKron (1 : Op ιA) K) ψ)‖ ≤ a := by
    rw [norm_applyOperatorToState_of_isometry
      (isBinaryObservable_heteroKron_one (ι' := ιB) hP).isometry]
    exact hK
  have h2 := hκ (applyOperatorToState
    (heteroKron P (1 : Op ιB) - heteroKron (1 : Op ιA) Q) ψ)
  nlinarith [h1, h2, hPQ, norm_nonneg (applyOperatorToState
    (heteroKron P (1 : Op ιB) - heteroKron (1 : Op ιA) Q) ψ)]

/-! ## Moving an operator across the residual factor -/

/-- Moving an operator across a contraction costs the commutator of the two on
the state. -/
theorem norm_mul_le_commutator_add {ι : Type} [Fintype ι] [DecidableEq ι]
    (N C : Op ι) (hC : Cᴴ * C ≤ 1) (ψ : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState (N * C) ψ‖ ≤
      ‖applyOperatorToState N ψ‖ + ‖applyOperatorToState (N * C - C * N) ψ‖ := by
  have hsplit : applyOperatorToState (N * C) ψ =
      applyOperatorToState C (applyOperatorToState N ψ) +
        applyOperatorToState (N * C - C * N) ψ := by
    rw [← MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul,
      ← applyOperatorToState_add_op]
    congr 1
    noncomm_ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  have := norm_applyOperatorToState_le hC (applyOperatorToState N ψ)
  linarith

/-- The commutator of a two-sided difference with a placed residual factor
splits into the two one-sided commutators. -/
theorem commutator_heteroKron_eq (n u : Op ιA) (m w : Op ιB) :
    (heteroKron n (1 : Op ιB) - heteroKron (1 : Op ιA) m) * heteroKron u w -
        heteroKron u w * (heteroKron n (1 : Op ιB) - heteroKron (1 : Op ιA) m) =
      heteroKron (n * u - u * n) w - heteroKron u (m * w - w * m) := by
  rw [heteroKron_sub_left, heteroKron_sub_right]
  simp only [sub_mul, mul_sub, heteroKron_mul, one_mul, mul_one]
  abel

/-- A placed operator with a contraction on the right of the other factor is
controlled by the placed operator alone. -/
theorem norm_heteroKron_left_le {c : Op ιA} {w : Op ιB} (hw : wᴴ * w ≤ 1)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    ‖applyOperatorToState (heteroKron c w) ψ‖ ≤
      ‖applyOperatorToState (heteroKron c (1 : Op ιB)) ψ‖ := by
  have hsplit : heteroKron c w = heteroKron (1 : Op ιA) w * heteroKron c (1 : Op ιB) := by
    rw [heteroKron_mul, one_mul, mul_one]
  rw [hsplit, MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul]
  exact norm_applyOperatorToState_le (conjTranspose_mul_le_one_rightTensor hw) _

/-- A placed operator with a contraction on the left of the other factor is
controlled by the placed operator alone. -/
theorem norm_heteroKron_right_le {u : Op ιA} {d : Op ιB} (hu : uᴴ * u ≤ 1)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    ‖applyOperatorToState (heteroKron u d) ψ‖ ≤
      ‖applyOperatorToState (heteroKron (1 : Op ιA) d) ψ‖ := by
  have hsplit : heteroKron u d = heteroKron u (1 : Op ιB) * heteroKron (1 : Op ιA) d := by
    rw [heteroKron_mul, one_mul, mul_one]
  rw [hsplit, MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul]
  exact norm_applyOperatorToState_le (conjTranspose_mul_le_one_leftTensor hu) _

/-! ## The commutator with the residual factor of the first pair -/

/-- Alice's commutator of a second-pair operator with her residual factor of the
first controlled swap, at either register label. -/
theorem norm_comm_swapFactor_left_le
    {X₁A Z₁A n : Op ιA} {Z₁B : Op ιB} {κ t s : ℝ}
    (hX₁A : IsBinaryObservable X₁A) (hZ₁B : IsBinaryObservable Z₁B)
    (hκA : NormBoundedBy (heteroKron n (1 : Op ιB)) κ) (hκ0 : 0 ≤ κ)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (ht : 0 ≤ t) (hs : 0 ≤ s)
    (hz1 : ‖applyOperatorToState
      (heteroKron Z₁A (1 : Op ιB) - heteroKron (1 : Op ιA) Z₁B) ψ‖ ≤ t)
    (hnz : ‖applyOperatorToState (heteroKron (n * Z₁A - Z₁A * n) (1 : Op ιB)) ψ‖ ≤ s)
    (hnx : ‖applyOperatorToState (heteroKron (n * X₁A - X₁A * n) (1 : Op ιB)) ψ‖ ≤ s)
    (b : ZMod 2) :
    ‖applyOperatorToState (heteroKron
        (n * (X₁A ^ b.val * reflectionEffect Z₁A b) -
          (X₁A ^ b.val * reflectionEffect Z₁A b) * n) (1 : Op ιB)) ψ‖ ≤
      (3 * s + 2 * κ * t) / 2 := by
  have hhalf : ‖((2 : ℂ)⁻¹ : ℂ)‖ = (2 : ℝ)⁻¹ := by norm_num
  have hκt : 0 ≤ κ * t := mul_nonneg hκ0 ht
  rcases zmod_two_eq_zero_or_one b with rfl | rfl
  · have hu : X₁A ^ (0 : ZMod 2).val * reflectionEffect Z₁A 0 =
        (2 : ℂ)⁻¹ • (1 + Z₁A) := by
      rw [ZMod.val_zero, pow_zero, one_mul, reflectionEffect, if_pos rfl]
    have hcomm : n * ((2 : ℂ)⁻¹ • (1 + Z₁A)) - ((2 : ℂ)⁻¹ • (1 + Z₁A)) * n =
        (2 : ℂ)⁻¹ • (n * Z₁A - Z₁A * n) := by
      rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub]
      congr 1
      noncomm_ring
    rw [hu, hcomm, heteroKron_smul_left, applyOperatorToState_smul, norm_smul, hhalf]
    nlinarith [hnz, hs, hκt]
  · have hu : X₁A ^ (1 : ZMod 2).val * reflectionEffect Z₁A 1 =
        (2 : ℂ)⁻¹ • (X₁A - X₁A * Z₁A) := by
      rw [ZMod.val_one, pow_one, reflectionEffect, if_neg one_ne_zero, Matrix.mul_smul]
      congr 1
      noncomm_ring
    have hcomm : n * ((2 : ℂ)⁻¹ • (X₁A - X₁A * Z₁A)) -
        ((2 : ℂ)⁻¹ • (X₁A - X₁A * Z₁A)) * n =
        (2 : ℂ)⁻¹ • ((n * X₁A - X₁A * n) -
          ((n * X₁A - X₁A * n) * Z₁A + X₁A * (n * Z₁A - Z₁A * n))) := by
      rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub]
      congr 1
      noncomm_ring
    have hKb : NormBoundedBy (heteroKron (n * X₁A - X₁A * n) (1 : Op ιB)) (2 * κ) := by
      have h1 : NormBoundedBy (heteroKron (n * X₁A) (1 : Op ιB)) (κ * 1) := by
        rw [show heteroKron (n * X₁A) (1 : Op ιB) =
            heteroKron n (1 : Op ιB) * heteroKron X₁A (1 : Op ιB) by
          rw [heteroKron_mul, mul_one]]
        exact hκA.mul (normBoundedBy_leftTensor (le_of_eq hX₁A.isometry)) hκ0
      have h2 : NormBoundedBy (heteroKron (X₁A * n) (1 : Op ιB)) (1 * κ) := by
        rw [show heteroKron (X₁A * n) (1 : Op ιB) =
            heteroKron X₁A (1 : Op ιB) * heteroKron n (1 : Op ιB) by
          rw [heteroKron_mul, mul_one]]
        exact (normBoundedBy_leftTensor (le_of_eq hX₁A.isometry)).mul hκA zero_le_one
      have h3 := h1.sub h2
      rw [← heteroKron_sub_left] at h3
      exact h3.mono (by linarith)
    have hb1 : ‖applyOperatorToState
        (heteroKron ((n * X₁A - X₁A * n) * Z₁A) (1 : Op ιB)) ψ‖ ≤ s + 2 * κ * t :=
      norm_leftTransport_le hKb (by linarith) hZ₁B ψ hnx hz1
    have hb2 : ‖applyOperatorToState
        (heteroKron (X₁A * (n * Z₁A - Z₁A * n)) (1 : Op ιB)) ψ‖ ≤ s := by
      rw [show heteroKron (X₁A * (n * Z₁A - Z₁A * n)) (1 : Op ιB) =
          heteroKron X₁A (1 : Op ιB) * heteroKron (n * Z₁A - Z₁A * n) (1 : Op ιB) by
        rw [heteroKron_mul, mul_one],
        norm_applyOperatorToState_isometry_mul
          (isBinaryObservable_heteroKron_one (ι' := ιB) hX₁A).isometry]
      exact hnz
    rw [hu, hcomm, heteroKron_smul_left, applyOperatorToState_smul, norm_smul, hhalf,
      heteroKron_sub_left, heteroKron_add_left, applyOperatorToState_sub_op,
      applyOperatorToState_add_op]
    have hadd := norm_add_le
      (applyOperatorToState (heteroKron ((n * X₁A - X₁A * n) * Z₁A) (1 : Op ιB)) ψ)
      (applyOperatorToState (heteroKron (X₁A * (n * Z₁A - Z₁A * n)) (1 : Op ιB)) ψ)
    have htri : ‖applyOperatorToState (heteroKron (n * X₁A - X₁A * n) (1 : Op ιB)) ψ -
        (applyOperatorToState (heteroKron ((n * X₁A - X₁A * n) * Z₁A) (1 : Op ιB)) ψ +
          applyOperatorToState
            (heteroKron (X₁A * (n * Z₁A - Z₁A * n)) (1 : Op ιB)) ψ)‖ ≤
        ‖applyOperatorToState (heteroKron (n * X₁A - X₁A * n) (1 : Op ιB)) ψ‖ +
          (‖applyOperatorToState
              (heteroKron ((n * X₁A - X₁A * n) * Z₁A) (1 : Op ιB)) ψ‖ +
            ‖applyOperatorToState
              (heteroKron (X₁A * (n * Z₁A - Z₁A * n)) (1 : Op ιB)) ψ‖) :=
      le_trans (norm_sub_le _ _) (by linarith [hadd])
    linarith [htri, hnx, hb1, hb2]

/-- Bob's commutator of a second-pair operator with his residual factor of the
first controlled swap, at either register label.  This is
`norm_comm_swapFactor_left_le` with the players exchanged. -/
theorem norm_comm_swapFactor_right_le
    {X₁B Z₁B m : Op ιB} {Z₁A : Op ιA} {κ t s : ℝ}
    (hX₁B : IsBinaryObservable X₁B) (hZ₁A : IsBinaryObservable Z₁A)
    (hκB : NormBoundedBy (heteroKron (1 : Op ιA) m) κ) (hκ0 : 0 ≤ κ)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (ht : 0 ≤ t) (hs : 0 ≤ s)
    (hz1 : ‖applyOperatorToState
      (heteroKron Z₁A (1 : Op ιB) - heteroKron (1 : Op ιA) Z₁B) ψ‖ ≤ t)
    (hmz : ‖applyOperatorToState (heteroKron (1 : Op ιA) (m * Z₁B - Z₁B * m)) ψ‖ ≤ s)
    (hmx : ‖applyOperatorToState (heteroKron (1 : Op ιA) (m * X₁B - X₁B * m)) ψ‖ ≤ s)
    (b : ZMod 2) :
    ‖applyOperatorToState (heteroKron (1 : Op ιA)
        (m * (X₁B ^ b.val * reflectionEffect Z₁B b) -
          (X₁B ^ b.val * reflectionEffect Z₁B b) * m)) ψ‖ ≤
      (3 * s + 2 * κ * t) / 2 := by
  have hhalf : ‖((2 : ℂ)⁻¹ : ℂ)‖ = (2 : ℝ)⁻¹ := by norm_num
  have hκt : 0 ≤ κ * t := mul_nonneg hκ0 ht
  rcases zmod_two_eq_zero_or_one b with rfl | rfl
  · have hu : X₁B ^ (0 : ZMod 2).val * reflectionEffect Z₁B 0 =
        (2 : ℂ)⁻¹ • (1 + Z₁B) := by
      rw [ZMod.val_zero, pow_zero, one_mul, reflectionEffect, if_pos rfl]
    have hcomm : m * ((2 : ℂ)⁻¹ • (1 + Z₁B)) - ((2 : ℂ)⁻¹ • (1 + Z₁B)) * m =
        (2 : ℂ)⁻¹ • (m * Z₁B - Z₁B * m) := by
      rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub]
      congr 1
      noncomm_ring
    rw [hu, hcomm, heteroKron_smul_right, applyOperatorToState_smul, norm_smul, hhalf]
    nlinarith [hmz, hs, hκt]
  · have hu : X₁B ^ (1 : ZMod 2).val * reflectionEffect Z₁B 1 =
        (2 : ℂ)⁻¹ • (X₁B - X₁B * Z₁B) := by
      rw [ZMod.val_one, pow_one, reflectionEffect, if_neg one_ne_zero, Matrix.mul_smul]
      congr 1
      noncomm_ring
    have hcomm : m * ((2 : ℂ)⁻¹ • (X₁B - X₁B * Z₁B)) -
        ((2 : ℂ)⁻¹ • (X₁B - X₁B * Z₁B)) * m =
        (2 : ℂ)⁻¹ • ((m * X₁B - X₁B * m) -
          ((m * X₁B - X₁B * m) * Z₁B + X₁B * (m * Z₁B - Z₁B * m))) := by
      rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub]
      congr 1
      noncomm_ring
    have hKb : NormBoundedBy (heteroKron (1 : Op ιA) (m * X₁B - X₁B * m)) (2 * κ) := by
      have h1 : NormBoundedBy (heteroKron (1 : Op ιA) (m * X₁B)) (κ * 1) := by
        rw [show heteroKron (1 : Op ιA) (m * X₁B) =
            heteroKron (1 : Op ιA) m * heteroKron (1 : Op ιA) X₁B by
          rw [heteroKron_mul, mul_one]]
        exact hκB.mul (normBoundedBy_rightTensor (le_of_eq hX₁B.isometry)) hκ0
      have h2 : NormBoundedBy (heteroKron (1 : Op ιA) (X₁B * m)) (1 * κ) := by
        rw [show heteroKron (1 : Op ιA) (X₁B * m) =
            heteroKron (1 : Op ιA) X₁B * heteroKron (1 : Op ιA) m by
          rw [heteroKron_mul, mul_one]]
        exact (normBoundedBy_rightTensor (le_of_eq hX₁B.isometry)).mul hκB zero_le_one
      have h3 := h1.sub h2
      rw [← heteroKron_sub_right] at h3
      exact h3.mono (by linarith)
    have hb1 : ‖applyOperatorToState
        (heteroKron (1 : Op ιA) ((m * X₁B - X₁B * m) * Z₁B)) ψ‖ ≤ s + 2 * κ * t :=
      norm_rightTransport_le hKb (by linarith) hZ₁A ψ hmx hz1
    have hb2 : ‖applyOperatorToState
        (heteroKron (1 : Op ιA) (X₁B * (m * Z₁B - Z₁B * m))) ψ‖ ≤ s := by
      rw [show heteroKron (1 : Op ιA) (X₁B * (m * Z₁B - Z₁B * m)) =
          heteroKron (1 : Op ιA) X₁B * heteroKron (1 : Op ιA) (m * Z₁B - Z₁B * m) by
        rw [heteroKron_mul, mul_one],
        norm_applyOperatorToState_isometry_mul
          (isBinaryObservable_heteroKron_right (ι := ιA) hX₁B).isometry]
      exact hmz
    rw [hu, hcomm, heteroKron_smul_right, applyOperatorToState_smul, norm_smul, hhalf,
      heteroKron_sub_right, heteroKron_add_right, applyOperatorToState_sub_op,
      applyOperatorToState_add_op]
    have hadd := norm_add_le
      (applyOperatorToState (heteroKron (1 : Op ιA) ((m * X₁B - X₁B * m) * Z₁B)) ψ)
      (applyOperatorToState (heteroKron (1 : Op ιA) (X₁B * (m * Z₁B - Z₁B * m))) ψ)
    have htri : ‖applyOperatorToState (heteroKron (1 : Op ιA) (m * X₁B - X₁B * m)) ψ -
        (applyOperatorToState (heteroKron (1 : Op ιA) ((m * X₁B - X₁B * m) * Z₁B)) ψ +
          applyOperatorToState
            (heteroKron (1 : Op ιA) (X₁B * (m * Z₁B - Z₁B * m))) ψ)‖ ≤
        ‖applyOperatorToState (heteroKron (1 : Op ιA) (m * X₁B - X₁B * m)) ψ‖ +
          (‖applyOperatorToState
              (heteroKron (1 : Op ιA) ((m * X₁B - X₁B * m) * Z₁B)) ψ‖ +
            ‖applyOperatorToState
              (heteroKron (1 : Op ιA) (X₁B * (m * Z₁B - Z₁B * m))) ψ‖) :=
      le_trans (norm_sub_le _ _) (by linarith [hadd])
    linarith [htri, hmx, hb1, hb2]

/-! ## The transported second-pair defect -/

/-- A state-dependent defect of the second logical pair, transported from the
shared state to the residual of the first controlled swap at the register label
`b`.  The cost is the commutation defect of the two pairs on each side and the
cross-player agreement of the first pair. -/
theorem norm_defect_transported_le
    {X₁A Z₁A n : Op ιA} {X₁B Z₁B m : Op ιB} {κ t s : ℝ}
    (hX₁A : IsBinaryObservable X₁A) (hZ₁A : IsBinaryObservable Z₁A)
    (hX₁B : IsBinaryObservable X₁B) (hZ₁B : IsBinaryObservable Z₁B)
    (hκA : NormBoundedBy (heteroKron n (1 : Op ιB)) κ)
    (hκB : NormBoundedBy (heteroKron (1 : Op ιA) m) κ) (hκ0 : 0 ≤ κ)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (ht : 0 ≤ t) (hs : 0 ≤ s)
    (hN : ‖applyOperatorToState
      (heteroKron n (1 : Op ιB) - heteroKron (1 : Op ιA) m) ψ‖ ≤ t)
    (hz1 : ‖applyOperatorToState
      (heteroKron Z₁A (1 : Op ιB) - heteroKron (1 : Op ιA) Z₁B) ψ‖ ≤ t)
    (hnz : ‖applyOperatorToState (heteroKron (n * Z₁A - Z₁A * n) (1 : Op ιB)) ψ‖ ≤ s)
    (hnx : ‖applyOperatorToState (heteroKron (n * X₁A - X₁A * n) (1 : Op ιB)) ψ‖ ≤ s)
    (hmz : ‖applyOperatorToState (heteroKron (1 : Op ιA) (m * Z₁B - Z₁B * m)) ψ‖ ≤ s)
    (hmx : ‖applyOperatorToState (heteroKron (1 : Op ιA) (m * X₁B - X₁B * m)) ψ‖ ≤ s)
    (b : ZMod 2) :
    ‖applyOperatorToState
        ((heteroKron n (1 : Op ιB) - heteroKron (1 : Op ιA) m) *
          heteroKron (X₁A ^ b.val * reflectionEffect Z₁A b)
            (X₁B ^ b.val * reflectionEffect Z₁B b)) ψ‖ ≤ t + 3 * s + 2 * κ * t := by
  have hu : (X₁A ^ b.val * reflectionEffect Z₁A b)ᴴ *
      (X₁A ^ b.val * reflectionEffect Z₁A b) ≤ 1 :=
    contraction_swapFactor hX₁A hZ₁A b
  have hw : (X₁B ^ b.val * reflectionEffect Z₁B b)ᴴ *
      (X₁B ^ b.val * reflectionEffect Z₁B b) ≤ 1 :=
    contraction_swapFactor hX₁B hZ₁B b
  have hstep := norm_mul_le_commutator_add
    (heteroKron n (1 : Op ιB) - heteroKron (1 : Op ιA) m)
    (heteroKron (X₁A ^ b.val * reflectionEffect Z₁A b)
      (X₁B ^ b.val * reflectionEffect Z₁B b)) (contraction_heteroKron hu hw) ψ
  rw [commutator_heteroKron_eq] at hstep
  have hsplit : ‖applyOperatorToState
      (heteroKron (n * (X₁A ^ b.val * reflectionEffect Z₁A b) -
          (X₁A ^ b.val * reflectionEffect Z₁A b) * n)
        (X₁B ^ b.val * reflectionEffect Z₁B b) -
        heteroKron (X₁A ^ b.val * reflectionEffect Z₁A b)
          (m * (X₁B ^ b.val * reflectionEffect Z₁B b) -
            (X₁B ^ b.val * reflectionEffect Z₁B b) * m)) ψ‖ ≤
      ‖applyOperatorToState
        (heteroKron (n * (X₁A ^ b.val * reflectionEffect Z₁A b) -
          (X₁A ^ b.val * reflectionEffect Z₁A b) * n)
          (X₁B ^ b.val * reflectionEffect Z₁B b)) ψ‖ +
      ‖applyOperatorToState
        (heteroKron (X₁A ^ b.val * reflectionEffect Z₁A b)
          (m * (X₁B ^ b.val * reflectionEffect Z₁B b) -
            (X₁B ^ b.val * reflectionEffect Z₁B b) * m)) ψ‖ := by
    rw [applyOperatorToState_sub_op]
    exact norm_sub_le _ _
  have hL := norm_heteroKron_left_le
    (c := n * (X₁A ^ b.val * reflectionEffect Z₁A b) -
      (X₁A ^ b.val * reflectionEffect Z₁A b) * n) hw ψ
  have hR := norm_heteroKron_right_le
    (d := m * (X₁B ^ b.val * reflectionEffect Z₁B b) -
      (X₁B ^ b.val * reflectionEffect Z₁B b) * m) hu ψ
  have hcA := norm_comm_swapFactor_left_le hX₁A hZ₁B hκA hκ0 ψ ht hs hz1 hnz hnx b
  have hcB := norm_comm_swapFactor_right_le hX₁B hZ₁A hκB hκ0 ψ ht hs hz1 hmz hmx b
  linarith [hstep, hsplit, hL, hR, hcA, hcB, hN]

end

end MIPStarRE.QPBT.MagicSquareRigidity
