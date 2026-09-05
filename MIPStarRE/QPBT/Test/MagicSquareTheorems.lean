import MIPStarRE.QPBT.Algebra.Pauli
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Basic
import MIPStarRE.QPBT.Test.MagicSquareTheorems.PerfectStrategy
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.Relations
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.Dilation
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.Anticommutation
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.Transfer
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.AnticommutatorB
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.Swap
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.Consistency
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.SecondPair
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.IdealTarget
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.Constants
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.TwoQubitSwap
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.Assembly
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.Marginals

/-!
# Magic Square rigidity

This stable public facade re-exports the elementary symmetry facts, the
value-to-parity relation layer, and the perfect strategy construction while
retaining the rigidity theorem and its supporting definitions.

The rigidity theorem is stated in the corrected form adopted on issue #172: the
source quantifies over all strategies, which is false for the role-symmetric
game (`docs/paper-gaps/qpbt_ms-rigidity-symmetric-strategies.tex`), and the
corrected statement assumes that the two players' `Variable_1` and `Variable_5`
measurements agree between the players up to `δ` in the squared
state-dependent distance of `def:povm-distance`
(`msVariableConsistencyDefect`, in `Rigidity/Consistency.lean`).  Symmetric
consistent strategies in the sense of `def:consistent-strategy`, which are
projective, and in particular the SPCC strategies of `def:spcc`, satisfy the
hypothesis with `δ = 0` (`exists_ms_rigidity_of_symmetric_consistent`).

## References

The source statement is blueprint
`thm:ms-rigidity`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`.

The variable indices below are zero-based: indices 0 and 4 represent the
paper's first and fifth variables, respectively.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum MagicSquareRigidity

noncomputable section

/-- The ideal two-qubit projector for one Magic Square output bit. The other
qubit is marginalized by summing the two-qubit Pauli basis projectors. -/
noncomputable def idealMagicBitProj (W : PauliKind) (b : ZMod 2) :
    Op (Fin 2 → ZMod 2) :=
  ∑ e : Fin 2 → ZMod 2, if e 0 = b then pauliProj W e else 0

/-- The ideal state in `thm:ms-rigidity`: two EPR pairs followed by the
auxiliary bipartite state, in local-player register order. -/
noncomputable def idealMsState {ιA'' ιB'' : Type*}
    [Fintype ιA''] [DecidableEq ιA''] [Fintype ιB''] [DecidableEq ιB'']
    (aux : EuclideanSpace ℂ (ιA'' × ιB'')) :
    EuclideanSpace ℂ
      (((Fin 2 → ZMod 2) × ιA'') × ((Fin 2 → ZMod 2) × ιB'')) :=
  reindexState prodShuffle (vecTensor (eprState (Fin 2 → ZMod 2)) aux)

/-- The isometries and auxiliary unit state in the conclusion of
`thm:ms-rigidity`. -/
structure MsRigidityWitness (S : Strategy msGame) where
  ιA'' : Type
  ιB'' : Type
  [ιA''Fintype : Fintype ιA'']
  [ιB''Fintype : Fintype ιB'']
  [ιA''DecidableEq : DecidableEq ιA'']
  [ιB''DecidableEq : DecidableEq ιB'']
  φA : EuclideanSpace ℂ S.ιA →ₗᵢ[ℂ]
    EuclideanSpace ℂ ((Fin 2 → ZMod 2) × ιA'')
  φB : EuclideanSpace ℂ S.ιB →ₗᵢ[ℂ]
    EuclideanSpace ℂ ((Fin 2 → ZMod 2) × ιB'')
  aux : EuclideanSpace ℂ (ιA'' × ιB'')
  aux_norm : ‖aux‖ = 1

attribute [instance] MsRigidityWitness.ιA''Fintype
  MsRigidityWitness.ιB''Fintype MsRigidityWitness.ιA''DecidableEq
  MsRigidityWitness.ιB''DecidableEq

/-- Alice's bit-measurement distance in `thm:ms-rigidity`. -/
noncomputable def msOperatorDistanceA (S : Strategy msGame)
    (w : MsRigidityWitness S) (j : Fin 9) (W : PauliKind) : ℝ :=
  opFamilyDistSq (uniformDistribution Unit)
    (fun _ b => heteroKron
      (conjIsometry w.φA
        (((S.A (.var j)).postprocess msBitOrZero).effect b)) 1)
    (fun _ b => heteroKron
      (heteroKron (idealMagicBitProj W b) (1 : Op w.ιA'')) 1)
    (idealMsState w.aux)

/-- Bob's bit-measurement distance in `thm:ms-rigidity`. -/
noncomputable def msOperatorDistanceB (S : Strategy msGame)
    (w : MsRigidityWitness S) (j : Fin 9) (W : PauliKind) : ℝ :=
  opFamilyDistSq (uniformDistribution Unit)
    (fun _ b => heteroKron 1
      (conjIsometry w.φB
        (((S.B (.var j)).postprocess msBitOrZero).effect b)))
    (fun _ b => heteroKron 1
      (heteroKron (idealMagicBitProj W b) (1 : Op w.ιB'')))
    (idealMsState w.aux)

/-- Alice's anticommutator defect from the consequence in
`thm:ms-rigidity`. -/
noncomputable def msAnticommutatorDistanceA (S : Strategy msGame)
    (w : MsRigidityWitness S) : ℝ :=
  let X := heteroKron
    (conjIsometry w.φA (obsOf ((S.A (.var 0)).postprocess msBitOrZero))) 1
  let Z := heteroKron
    (conjIsometry w.φA (obsOf ((S.A (.var 4)).postprocess msBitOrZero))) 1
  opDistSq (uniformDistribution Unit) (fun _ => X * Z)
    (fun _ => -(Z * X)) (idealMsState w.aux)

/-- Bob's anticommutator defect from the consequence in
`thm:ms-rigidity`. -/
noncomputable def msAnticommutatorDistanceB (S : Strategy msGame)
    (w : MsRigidityWitness S) : ℝ :=
  let X := heteroKron 1
    (conjIsometry w.φB (obsOf ((S.B (.var 0)).postprocess msBitOrZero)))
  let Z := heteroKron 1
    (conjIsometry w.φB (obsOf ((S.B (.var 4)).postprocess msBitOrZero)))
  opDistSq (uniformDistribution Unit) (fun _ => X * Z)
    (fun _ => -(Z * X)) (idealMsState w.aux)

/-! ## The coarse witness and the large-error regime -/

/-- Every strategy of the Magic Square game admits a witness of the shape
required by `thm:ms-rigidity` for which all seven quantities of the conclusion
are at most `8`.

The witness embeds each player's space as the fiber of the extracted register
over one fixed basis vector (`MagicSquareRigidity.registerFiberEmbedding`) and
takes the strategy state itself as the auxiliary state.  No property of the
strategy is used: the estimates are the trivial ones available for any two
contractions on a unit vector, namely that the two operator families of each
conclusion are contractions and that the ideal state is a unit vector
(`norm_reindexState_prodShuffle_vecTensor_eprState`,
`conjTranspose_mul_le_one_sum_ite_pauliProj`).  This is the coarse construction
that carries the regime `1 ≤ sqrt ε + sqrt δ` of `exists_ms_rigidity`, in which
the asserted bound `C * (sqrt ε + sqrt δ)` is at least the constant `C`; see
`exists_ms_rigidity_of_one_le_sqrt_add`.  Blueprint
`thm:ms-rigidity`, paper
`08_classical_and_quantum_low_degree_tests.tex:612-652`. -/
theorem ms_rigidity_coarse_bounds (S : Strategy msGame) :
    ∃ w : MsRigidityWitness S,
      ‖isometryTensor w.φA w.φB S.ψ - idealMsState w.aux‖ ≤ 8 ∧
      (∀ (j : Fin 9) (W : PauliKind), msOperatorDistanceA S w j W ≤ 8) ∧
      (∀ (j : Fin 9) (W : PauliKind), msOperatorDistanceB S w j W ≤ 8) ∧
      msAnticommutatorDistanceA S w ≤ 8 ∧ msAnticommutatorDistanceB S w ≤ 8 := by
  classical
  refine ⟨{ ιA'' := S.ιA
            ιB'' := S.ιB
            φA := MagicSquareRigidity.registerFiberEmbedding (Fin 2 → ZMod 2) S.ιA 0
            φB := MagicSquareRigidity.registerFiberEmbedding (Fin 2 → ZMod 2) S.ιB 0
            aux := S.ψ
            aux_norm := S.ψ_norm }, ?_, ?_, ?_, ?_, ?_⟩
  · have hxi : ‖idealMsState S.ψ‖ = 1 := by
      rw [idealMsState, norm_reindexState_prodShuffle_vecTensor_eprState]
      exact S.ψ_norm
    calc ‖isometryTensor
            (MagicSquareRigidity.registerFiberEmbedding (Fin 2 → ZMod 2) S.ιA 0)
            (MagicSquareRigidity.registerFiberEmbedding (Fin 2 → ZMod 2) S.ιB 0) S.ψ -
            idealMsState S.ψ‖
        ≤ ‖isometryTensor
            (MagicSquareRigidity.registerFiberEmbedding (Fin 2 → ZMod 2) S.ιA 0)
            (MagicSquareRigidity.registerFiberEmbedding (Fin 2 → ZMod 2) S.ιB 0) S.ψ‖ +
          ‖idealMsState S.ψ‖ := norm_sub_le _ _
      _ ≤ 8 := by
          rw [MagicSquareRigidity.norm_isometryTensor, S.ψ_norm, hxi]
          norm_num
  · intro j W
    have hxi : ‖idealMsState S.ψ‖ = 1 := by
      rw [idealMsState, norm_reindexState_prodShuffle_vecTensor_eprState]
      exact S.ψ_norm
    refine MagicSquareRigidity.opFamilyDistSq_uniform_unit_binary_le _ _ _ hxi
      (fun b => ?_) (fun b => ?_)
    · exact MagicSquareRigidity.conjTranspose_mul_le_one_leftTensor
        (MagicSquareRigidity.conjTranspose_mul_le_one_conjIsometry _
          (MagicSquareRigidity.conjTranspose_mul_le_one_of_effect
            ((S.A (.var j)).postprocess msBitOrZero) b))
    · exact MagicSquareRigidity.conjTranspose_mul_le_one_leftTensor
        (MagicSquareRigidity.conjTranspose_mul_le_one_leftTensor
          (conjTranspose_mul_le_one_sum_ite_pauliProj (K := ZMod 2) (ι := Fin 2) W
            (fun e => e 0) b))
  · intro j W
    have hxi : ‖idealMsState S.ψ‖ = 1 := by
      rw [idealMsState, norm_reindexState_prodShuffle_vecTensor_eprState]
      exact S.ψ_norm
    refine MagicSquareRigidity.opFamilyDistSq_uniform_unit_binary_le _ _ _ hxi
      (fun b => ?_) (fun b => ?_)
    · exact MagicSquareRigidity.conjTranspose_mul_le_one_rightTensor
        (MagicSquareRigidity.conjTranspose_mul_le_one_conjIsometry _
          (MagicSquareRigidity.conjTranspose_mul_le_one_of_effect
            ((S.B (.var j)).postprocess msBitOrZero) b))
    · exact MagicSquareRigidity.conjTranspose_mul_le_one_rightTensor
        (MagicSquareRigidity.conjTranspose_mul_le_one_leftTensor
          (conjTranspose_mul_le_one_sum_ite_pauliProj (K := ZMod 2) (ι := Fin 2) W
            (fun e => e 0) b))
  · have hxi : ‖idealMsState S.ψ‖ = 1 := by
      rw [idealMsState, norm_reindexState_prodShuffle_vecTensor_eprState]
      exact S.ψ_norm
    have hX := MagicSquareRigidity.conjTranspose_mul_le_one_leftTensor
      (ιB := (Fin 2 → ZMod 2) × S.ιB)
      (MagicSquareRigidity.conjTranspose_mul_le_one_conjIsometry
        (MagicSquareRigidity.registerFiberEmbedding (Fin 2 → ZMod 2) S.ιA 0)
        (MagicSquareRigidity.conjTranspose_mul_le_one_of_obsOf
          ((S.A (.var 0)).postprocess msBitOrZero)))
    have hZ := MagicSquareRigidity.conjTranspose_mul_le_one_leftTensor
      (ιB := (Fin 2 → ZMod 2) × S.ιB)
      (MagicSquareRigidity.conjTranspose_mul_le_one_conjIsometry
        (MagicSquareRigidity.registerFiberEmbedding (Fin 2 → ZMod 2) S.ιA 0)
        (MagicSquareRigidity.conjTranspose_mul_le_one_of_obsOf
          ((S.A (.var 4)).postprocess msBitOrZero)))
    refine le_trans (MagicSquareRigidity.opDistSq_uniform_unit_le _ _ _ hxi
      (MagicSquareRigidity.conjTranspose_mul_le_one_mul hX hZ)
      (MagicSquareRigidity.conjTranspose_mul_le_one_neg
        (MagicSquareRigidity.conjTranspose_mul_le_one_mul hZ hX))) (by norm_num)
  · have hxi : ‖idealMsState S.ψ‖ = 1 := by
      rw [idealMsState, norm_reindexState_prodShuffle_vecTensor_eprState]
      exact S.ψ_norm
    have hX := MagicSquareRigidity.conjTranspose_mul_le_one_rightTensor
      (ιA := (Fin 2 → ZMod 2) × S.ιA)
      (MagicSquareRigidity.conjTranspose_mul_le_one_conjIsometry
        (MagicSquareRigidity.registerFiberEmbedding (Fin 2 → ZMod 2) S.ιB 0)
        (MagicSquareRigidity.conjTranspose_mul_le_one_of_obsOf
          ((S.B (.var 0)).postprocess msBitOrZero)))
    have hZ := MagicSquareRigidity.conjTranspose_mul_le_one_rightTensor
      (ιA := (Fin 2 → ZMod 2) × S.ιA)
      (MagicSquareRigidity.conjTranspose_mul_le_one_conjIsometry
        (MagicSquareRigidity.registerFiberEmbedding (Fin 2 → ZMod 2) S.ιB 0)
        (MagicSquareRigidity.conjTranspose_mul_le_one_of_obsOf
          ((S.B (.var 4)).postprocess msBitOrZero)))
    refine le_trans (MagicSquareRigidity.opDistSq_uniform_unit_le _ _ _ hxi
      (MagicSquareRigidity.conjTranspose_mul_le_one_mul hX hZ)
      (MagicSquareRigidity.conjTranspose_mul_le_one_neg
        (MagicSquareRigidity.conjTranspose_mul_le_one_mul hZ hX))) (by norm_num)

/-- The regime of `thm:ms-rigidity` in which the asserted scale is at least the
constant.  For `1 ≤ sqrt ε + sqrt δ` and any constant `C ≥ 8`, the coarse
witness of `ms_rigidity_coarse_bounds` already satisfies all seven conclusions,
whatever the strategy.  The remaining content of `exists_ms_rigidity` is
therefore the complementary regime `sqrt ε + sqrt δ < 1`. -/
theorem exists_ms_rigidity_of_one_le_sqrt_add (C ε δ : ℝ) (hC : 8 ≤ C)
    (hbig : 1 ≤ Real.sqrt ε + Real.sqrt δ) (S : Strategy msGame) :
    ∃ w : MsRigidityWitness S,
      ‖isometryTensor w.φA w.φB S.ψ - idealMsState w.aux‖ ≤
          C * (Real.sqrt ε + Real.sqrt δ) ∧
      msOperatorDistanceA S w 0 .X ≤ C * (Real.sqrt ε + Real.sqrt δ) ∧
      msOperatorDistanceA S w 4 .Z ≤ C * (Real.sqrt ε + Real.sqrt δ) ∧
      msOperatorDistanceB S w 0 .X ≤ C * (Real.sqrt ε + Real.sqrt δ) ∧
      msOperatorDistanceB S w 4 .Z ≤ C * (Real.sqrt ε + Real.sqrt δ) ∧
      msAnticommutatorDistanceA S w ≤ C * (Real.sqrt ε + Real.sqrt δ) ∧
      msAnticommutatorDistanceB S w ≤ C * (Real.sqrt ε + Real.sqrt δ) := by
  obtain ⟨w, h1, hA, hB, h6, h7⟩ := ms_rigidity_coarse_bounds S
  have hCbound : (8 : ℝ) ≤ C * (Real.sqrt ε + Real.sqrt δ) := by nlinarith
  exact ⟨w, h1.trans hCbound, (hA 0 .X).trans hCbound, (hA 4 .Z).trans hCbound,
    (hB 0 .X).trans hCbound, (hB 4 .Z).trans hCbound, h6.trans hCbound,
    h7.trans hCbound⟩

/-! ## The bit-measurement and anticommutator estimates on the dilation -/

/-- Formalization-only: a state-dependent estimate for a difference of two
contractions transfers from the transported dilated state to the ideal state at
the cost of twice the distance between the two states. -/
theorem norm_applyOperatorToState_sub_le_of_close {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : Op ι) (u ξ : EuclideanSpace ℂ ι) (κ η : ℝ)
    (hA : Aᴴ * A ≤ 1) (hB : Bᴴ * B ≤ 1)
    (hu : ‖applyOperatorToState (A - B) u‖ ≤ κ) (hξ : ‖u - ξ‖ ≤ η) :
    ‖applyOperatorToState (A - B) ξ‖ ≤ κ + 2 * η := by
  have hadd : applyOperatorToState (A - B) (u + (ξ - u)) =
      applyOperatorToState (A - B) u + applyOperatorToState (A - B) (ξ - u) := by
    simp only [applyOperatorToState]
    rw [map_add]
  have hsplit : applyOperatorToState (A - B) ξ =
      applyOperatorToState (A - B) u + applyOperatorToState (A - B) (ξ - u) := by
    rw [← hadd]
    congr 1
    abel
  have h2 : ‖applyOperatorToState (A - B) (ξ - u)‖ ≤ 2 * η := by
    refine le_trans (norm_applyOperatorToState_sub_le hA hB _) ?_
    have hrev : ‖ξ - u‖ = ‖u - ξ‖ := norm_sub_rev _ _
    linarith
  rw [hsplit]
  exact le_trans (norm_add_le _ _) (add_le_add hu h2)

/-- Formalization-only: summing a uniform per-outcome estimate over the two
outcomes. -/
theorem sum_sq_le_two_mul {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ZMod 2 → EuclideanSpace ℂ ι) (c : ℝ) (h : ∀ b, ‖f b‖ ≤ c) :
    (∑ b : ZMod 2, ‖f b‖ ^ 2) ≤ 2 * c ^ 2 := by
  calc (∑ b : ZMod 2, ‖f b‖ ^ 2) ≤ ∑ _b : ZMod 2, c ^ 2 :=
        Finset.sum_le_sum fun b _ => by nlinarith [h b, norm_nonneg (f b)]
    _ = 2 * c ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
        norm_num

/-- The bit-measurement estimate of `thm:ms-rigidity` on the projective
dilation for Alice: her variable effects, conjugated by her two-qubit
controlled-swap embedding, are close on the ideal state to the marginals of the
two-qubit Pauli basis, at the scale of the transport defect plus twice the state
distance.  Blueprint `thm:ms-rigidity`, paper
`08_classical_and_quantum_low_degree_tests.tex:612-652`. -/
theorem ms_dilated_operator_distance_A (S : Strategy msGame) (j : Fin 9) (W : PauliKind)
    (r : EuclideanSpace ℂ ((msDilatedStrategy S).ιA × (msDilatedStrategy S).ιB))
    (κ η : ℝ)
    (hξ : ‖isometryTensor (msAliceTwoQubitSwapIsometry S)
        (msBobTwoQubitSwapIsometry S) (msDilatedStrategy S).ψ -
      idealMsState r‖ ≤ η)
    (hdef : ∀ b : ZMod 2,
      ‖applyOperatorToState (heteroKron (heteroKron (idealMagicBitProj W b) 1) 1)
          (isometryTensor (msAliceTwoQubitSwapIsometry S)
            (msBobTwoQubitSwapIsometry S) (msDilatedStrategy S).ψ) -
        isometryTensor (msAliceTwoQubitSwapIsometry S)
          (msBobTwoQubitSwapIsometry S)
          (applyOperatorToState (heteroKron
            ((((msDilatedStrategy S).A (.var j)).postprocess msBitOrZero).effect b) 1)
            (msDilatedStrategy S).ψ)‖ ≤ κ) :
    opFamilyDistSq (uniformDistribution Unit)
        (fun _ b => heteroKron (conjIsometry
          (msAliceTwoQubitSwapIsometry S)
          ((((msDilatedStrategy S).A (.var j)).postprocess msBitOrZero).effect b)) 1)
        (fun _ b => heteroKron (heteroKron (idealMagicBitProj W b) 1) 1)
        (idealMsState r) ≤ 2 * (κ + 2 * η) ^ 2 := by
  rw [opFamilyDistSq_uniform_unit]
  refine sum_sq_le_two_mul _ (κ + 2 * η) fun b => ?_
  refine norm_applyOperatorToState_sub_le_of_close _ _
    (isometryTensor (msAliceTwoQubitSwapIsometry S)
      (msBobTwoQubitSwapIsometry S) (msDilatedStrategy S).ψ)
    _ κ η ?_ ?_ ?_ hξ
  · exact conjTranspose_mul_le_one_leftTensor
      (conjTranspose_mul_le_one_conjIsometry _
        (conjTranspose_mul_le_one_of_effect _ b))
  · exact conjTranspose_mul_le_one_leftTensor
      (conjTranspose_mul_le_one_leftTensor
        (conjTranspose_mul_le_one_sum_ite_pauliProj (K := ZMod 2) (ι := Fin 2) W
          (fun e => e 0) b))
  · rw [applyOperatorToState_sub_op,
      applyOperatorToState_leftTensor_conjIsometry, ← norm_neg,
      neg_sub]
    exact hdef b

/-- The bit-measurement estimate of `thm:ms-rigidity` on the projective
dilation for Bob; see `ms_dilated_operator_distance_A`. -/
theorem ms_dilated_operator_distance_B (S : Strategy msGame) (j : Fin 9) (W : PauliKind)
    (r : EuclideanSpace ℂ ((msDilatedStrategy S).ιA × (msDilatedStrategy S).ιB))
    (κ η : ℝ)
    (hξ : ‖isometryTensor (msAliceTwoQubitSwapIsometry S)
        (msBobTwoQubitSwapIsometry S) (msDilatedStrategy S).ψ -
      idealMsState r‖ ≤ η)
    (hdef : ∀ b : ZMod 2,
      ‖applyOperatorToState (heteroKron 1 (heteroKron (idealMagicBitProj W b) 1))
          (isometryTensor (msAliceTwoQubitSwapIsometry S)
            (msBobTwoQubitSwapIsometry S) (msDilatedStrategy S).ψ) -
        isometryTensor (msAliceTwoQubitSwapIsometry S)
          (msBobTwoQubitSwapIsometry S)
          (applyOperatorToState (heteroKron 1
            ((((msDilatedStrategy S).B (.var j)).postprocess msBitOrZero).effect b))
            (msDilatedStrategy S).ψ)‖ ≤ κ) :
    opFamilyDistSq (uniformDistribution Unit)
        (fun _ b => heteroKron 1 (conjIsometry
          (msBobTwoQubitSwapIsometry S)
          ((((msDilatedStrategy S).B (.var j)).postprocess msBitOrZero).effect b)))
        (fun _ b => heteroKron 1 (heteroKron (idealMagicBitProj W b) 1))
        (idealMsState r) ≤ 2 * (κ + 2 * η) ^ 2 := by
  rw [opFamilyDistSq_uniform_unit]
  refine sum_sq_le_two_mul _ (κ + 2 * η) fun b => ?_
  refine norm_applyOperatorToState_sub_le_of_close _ _
    (isometryTensor (msAliceTwoQubitSwapIsometry S)
      (msBobTwoQubitSwapIsometry S) (msDilatedStrategy S).ψ)
    _ κ η ?_ ?_ ?_ hξ
  · exact conjTranspose_mul_le_one_rightTensor
      (conjTranspose_mul_le_one_conjIsometry _
        (conjTranspose_mul_le_one_of_effect _ b))
  · exact conjTranspose_mul_le_one_rightTensor
      (conjTranspose_mul_le_one_leftTensor
        (conjTranspose_mul_le_one_sum_ite_pauliProj (K := ZMod 2) (ι := Fin 2) W
          (fun e => e 0) b))
  · rw [applyOperatorToState_sub_op,
      applyOperatorToState_rightTensor_conjIsometry, ← norm_neg,
      neg_sub]
    exact hdef b

/-- The anticommutator estimate of `thm:ms-rigidity` on the projective dilation
for Alice: products compose under conjugation by an isometry, so the estimate is
the anticommutator defect of her first logical pair transported to the ideal
state.  Blueprint `thm:ms-rigidity`. -/
theorem ms_dilated_anticommutator_A (S : Strategy msGame)
    (r : EuclideanSpace ℂ ((msDilatedStrategy S).ιA × (msDilatedStrategy S).ιB))
    (κ η : ℝ)
    (hξ : ‖isometryTensor (msAliceTwoQubitSwapIsometry S)
        (msBobTwoQubitSwapIsometry S) (msDilatedStrategy S).ψ -
      idealMsState r‖ ≤ η)
    (hac : ‖applyOperatorToState (msJointAnticommutatorA S)
      (msDilatedStrategy S).ψ‖ ≤ κ) :
    opDistSq (uniformDistribution Unit)
        (fun _ => heteroKron (conjIsometry
            (msAliceTwoQubitSwapIsometry S)
            (obsOf (((msDilatedStrategy S).A (.var 0)).postprocess msBitOrZero))) 1 *
          heteroKron (conjIsometry
            (msAliceTwoQubitSwapIsometry S)
            (obsOf (((msDilatedStrategy S).A (.var 4)).postprocess msBitOrZero))) 1)
        (fun _ => -(heteroKron (conjIsometry
            (msAliceTwoQubitSwapIsometry S)
            (obsOf (((msDilatedStrategy S).A (.var 4)).postprocess msBitOrZero))) 1 *
          heteroKron (conjIsometry
            (msAliceTwoQubitSwapIsometry S)
            (obsOf (((msDilatedStrategy S).A (.var 0)).postprocess msBitOrZero))) 1))
        (idealMsState r) ≤ (κ + 2 * η) ^ 2 := by
  have hY : ∀ j : Fin 9,
      obsOf (((msDilatedStrategy S).A (.var j)).postprocess msBitOrZero) =
        msLocalVarObsA S j := fun j => by
    rw [msLocalVarObsA,
      signObs_eq_obsOf_postprocess]
  have hcadd : ∀ A B : Op (msDilatedStrategy S).ιA,
      conjIsometry (msAliceTwoQubitSwapIsometry S) (A + B) =
        conjIsometry (msAliceTwoQubitSwapIsometry S) A +
          conjIsometry (msAliceTwoQubitSwapIsometry S) B := by
    intro A B
    simp only [conjIsometry_eq, Matrix.add_mul, Matrix.mul_add]
  rw [opDistSq_uniform_unit]
  have hX0 := conjTranspose_mul_le_one_leftTensor
    (ιB := (Fin 2 → ZMod 2) × (msDilatedStrategy S).ιB)
    (conjTranspose_mul_le_one_conjIsometry
      (msAliceTwoQubitSwapIsometry S)
      (conjTranspose_mul_le_one_of_obsOf
        (((msDilatedStrategy S).A (.var 0)).postprocess msBitOrZero)))
  have hX4 := conjTranspose_mul_le_one_leftTensor
    (ιB := (Fin 2 → ZMod 2) × (msDilatedStrategy S).ιB)
    (conjTranspose_mul_le_one_conjIsometry
      (msAliceTwoQubitSwapIsometry S)
      (conjTranspose_mul_le_one_of_obsOf
        (((msDilatedStrategy S).A (.var 4)).postprocess msBitOrZero)))
  have hbound : ‖applyOperatorToState
      (heteroKron (conjIsometry (msAliceTwoQubitSwapIsometry S)
          (obsOf (((msDilatedStrategy S).A (.var 0)).postprocess msBitOrZero))) 1 *
        heteroKron (conjIsometry (msAliceTwoQubitSwapIsometry S)
          (obsOf (((msDilatedStrategy S).A (.var 4)).postprocess msBitOrZero))) 1 -
      -(heteroKron (conjIsometry (msAliceTwoQubitSwapIsometry S)
          (obsOf (((msDilatedStrategy S).A (.var 4)).postprocess msBitOrZero))) 1 *
        heteroKron (conjIsometry (msAliceTwoQubitSwapIsometry S)
          (obsOf (((msDilatedStrategy S).A (.var 0)).postprocess msBitOrZero))) 1))
      (idealMsState r)‖ ≤ κ + 2 * η := by
    refine norm_applyOperatorToState_sub_le_of_close _ _
      (isometryTensor (msAliceTwoQubitSwapIsometry S)
        (msBobTwoQubitSwapIsometry S) (msDilatedStrategy S).ψ)
      _ κ η (conjTranspose_mul_le_one_mul hX0 hX4)
      (conjTranspose_mul_le_one_neg
        (conjTranspose_mul_le_one_mul hX4 hX0)) ?_ hξ
    have hprod : heteroKron (conjIsometry
          (msAliceTwoQubitSwapIsometry S)
          (obsOf (((msDilatedStrategy S).A (.var 0)).postprocess msBitOrZero))) 1 *
        heteroKron (conjIsometry (msAliceTwoQubitSwapIsometry S)
          (obsOf (((msDilatedStrategy S).A (.var 4)).postprocess msBitOrZero))) 1 -
        -(heteroKron (conjIsometry (msAliceTwoQubitSwapIsometry S)
          (obsOf (((msDilatedStrategy S).A (.var 4)).postprocess msBitOrZero))) 1 *
        heteroKron (conjIsometry (msAliceTwoQubitSwapIsometry S)
          (obsOf (((msDilatedStrategy S).A (.var 0)).postprocess msBitOrZero))) 1) =
        heteroKron (conjIsometry (msAliceTwoQubitSwapIsometry S)
          (msLocalVarObsA S 0 * msLocalVarObsA S 4 +
            msLocalVarObsA S 4 *
              msLocalVarObsA S 0))
          (1 : Op ((Fin 2 → ZMod 2) × (msDilatedStrategy S).ιB)) := by
      rw [hY 0, hY 4, heteroKron_mul, heteroKron_mul, one_mul, sub_neg_eq_add,
        ← heteroKron_add_left, conjIsometry_mul,
        conjIsometry_mul, ← hcadd]
    rw [hprod, applyOperatorToState_leftTensor_conjIsometry,
      norm_isometryTensor]
    rw [msJointAnticommutatorA] at hac
    exact hac
  nlinarith [hbound, norm_nonneg (applyOperatorToState
      (heteroKron (conjIsometry (msAliceTwoQubitSwapIsometry S)
          (obsOf (((msDilatedStrategy S).A (.var 0)).postprocess msBitOrZero))) 1 *
        heteroKron (conjIsometry (msAliceTwoQubitSwapIsometry S)
          (obsOf (((msDilatedStrategy S).A (.var 4)).postprocess msBitOrZero))) 1 -
      -(heteroKron (conjIsometry (msAliceTwoQubitSwapIsometry S)
          (obsOf (((msDilatedStrategy S).A (.var 4)).postprocess msBitOrZero))) 1 *
        heteroKron (conjIsometry (msAliceTwoQubitSwapIsometry S)
          (obsOf (((msDilatedStrategy S).A (.var 0)).postprocess msBitOrZero))) 1))
      (idealMsState r))]

/-- The anticommutator estimate of `thm:ms-rigidity` on the projective dilation
for Bob; see `ms_dilated_anticommutator_A`. -/
theorem ms_dilated_anticommutator_B (S : Strategy msGame)
    (r : EuclideanSpace ℂ ((msDilatedStrategy S).ιA × (msDilatedStrategy S).ιB))
    (κ η : ℝ)
    (hξ : ‖isometryTensor (msAliceTwoQubitSwapIsometry S)
        (msBobTwoQubitSwapIsometry S) (msDilatedStrategy S).ψ -
      idealMsState r‖ ≤ η)
    (hac : ‖applyOperatorToState (msJointAnticommutatorB S)
      (msDilatedStrategy S).ψ‖ ≤ κ) :
    opDistSq (uniformDistribution Unit)
        (fun _ => heteroKron 1 (conjIsometry
            (msBobTwoQubitSwapIsometry S)
            (obsOf (((msDilatedStrategy S).B (.var 0)).postprocess msBitOrZero))) *
          heteroKron 1 (conjIsometry
            (msBobTwoQubitSwapIsometry S)
            (obsOf (((msDilatedStrategy S).B (.var 4)).postprocess msBitOrZero))))
        (fun _ => -(heteroKron 1 (conjIsometry
            (msBobTwoQubitSwapIsometry S)
            (obsOf (((msDilatedStrategy S).B (.var 4)).postprocess msBitOrZero))) *
          heteroKron 1 (conjIsometry
            (msBobTwoQubitSwapIsometry S)
            (obsOf (((msDilatedStrategy S).B (.var 0)).postprocess msBitOrZero)))))
        (idealMsState r) ≤ (κ + 2 * η) ^ 2 := by
  have hY : ∀ j : Fin 9,
      obsOf (((msDilatedStrategy S).B (.var j)).postprocess msBitOrZero) =
        msLocalVarObsB S j := fun j => by
    rw [msLocalVarObsB,
      signObs_eq_obsOf_postprocess]
  have hcadd : ∀ A B : Op (msDilatedStrategy S).ιB,
      conjIsometry (msBobTwoQubitSwapIsometry S) (A + B) =
        conjIsometry (msBobTwoQubitSwapIsometry S) A +
          conjIsometry (msBobTwoQubitSwapIsometry S) B := by
    intro A B
    simp only [conjIsometry_eq, Matrix.add_mul, Matrix.mul_add]
  rw [opDistSq_uniform_unit]
  have hX0 := conjTranspose_mul_le_one_rightTensor
    (ιA := (Fin 2 → ZMod 2) × (msDilatedStrategy S).ιA)
    (conjTranspose_mul_le_one_conjIsometry
      (msBobTwoQubitSwapIsometry S)
      (conjTranspose_mul_le_one_of_obsOf
        (((msDilatedStrategy S).B (.var 0)).postprocess msBitOrZero)))
  have hX4 := conjTranspose_mul_le_one_rightTensor
    (ιA := (Fin 2 → ZMod 2) × (msDilatedStrategy S).ιA)
    (conjTranspose_mul_le_one_conjIsometry
      (msBobTwoQubitSwapIsometry S)
      (conjTranspose_mul_le_one_of_obsOf
        (((msDilatedStrategy S).B (.var 4)).postprocess msBitOrZero)))
  have hbound : ‖applyOperatorToState
      (heteroKron 1 (conjIsometry (msBobTwoQubitSwapIsometry S)
          (obsOf (((msDilatedStrategy S).B (.var 0)).postprocess msBitOrZero))) *
        heteroKron 1 (conjIsometry (msBobTwoQubitSwapIsometry S)
          (obsOf (((msDilatedStrategy S).B (.var 4)).postprocess msBitOrZero))) -
      -(heteroKron 1 (conjIsometry (msBobTwoQubitSwapIsometry S)
          (obsOf (((msDilatedStrategy S).B (.var 4)).postprocess msBitOrZero))) *
        heteroKron 1 (conjIsometry (msBobTwoQubitSwapIsometry S)
          (obsOf (((msDilatedStrategy S).B (.var 0)).postprocess msBitOrZero)))))
      (idealMsState r)‖ ≤ κ + 2 * η := by
    refine norm_applyOperatorToState_sub_le_of_close _ _
      (isometryTensor (msAliceTwoQubitSwapIsometry S)
        (msBobTwoQubitSwapIsometry S) (msDilatedStrategy S).ψ)
      _ κ η (conjTranspose_mul_le_one_mul hX0 hX4)
      (conjTranspose_mul_le_one_neg
        (conjTranspose_mul_le_one_mul hX4 hX0)) ?_ hξ
    have hprod : heteroKron 1 (conjIsometry
          (msBobTwoQubitSwapIsometry S)
          (obsOf (((msDilatedStrategy S).B (.var 0)).postprocess msBitOrZero))) *
        heteroKron 1 (conjIsometry (msBobTwoQubitSwapIsometry S)
          (obsOf (((msDilatedStrategy S).B (.var 4)).postprocess msBitOrZero))) -
        -(heteroKron 1 (conjIsometry (msBobTwoQubitSwapIsometry S)
          (obsOf (((msDilatedStrategy S).B (.var 4)).postprocess msBitOrZero))) *
        heteroKron 1 (conjIsometry (msBobTwoQubitSwapIsometry S)
          (obsOf (((msDilatedStrategy S).B (.var 0)).postprocess msBitOrZero)))) =
        heteroKron (1 : Op ((Fin 2 → ZMod 2) × (msDilatedStrategy S).ιA))
          (conjIsometry (msBobTwoQubitSwapIsometry S)
          (msLocalVarObsB S 0 * msLocalVarObsB S 4 +
            msLocalVarObsB S 4 *
              msLocalVarObsB S 0)) := by
      rw [hY 0, hY 4, heteroKron_mul, heteroKron_mul, one_mul, sub_neg_eq_add,
        ← heteroKron_add_right, conjIsometry_mul,
        conjIsometry_mul, ← hcadd]
    rw [hprod, applyOperatorToState_rightTensor_conjIsometry,
      norm_isometryTensor]
    rw [msJointAnticommutatorB] at hac
    exact hac
  nlinarith [hbound, norm_nonneg (applyOperatorToState
      (heteroKron 1 (conjIsometry (msBobTwoQubitSwapIsometry S)
          (obsOf (((msDilatedStrategy S).B (.var 0)).postprocess msBitOrZero))) *
        heteroKron 1 (conjIsometry (msBobTwoQubitSwapIsometry S)
          (obsOf (((msDilatedStrategy S).B (.var 4)).postprocess msBitOrZero))) -
      -(heteroKron 1 (conjIsometry (msBobTwoQubitSwapIsometry S)
          (obsOf (((msDilatedStrategy S).B (.var 4)).postprocess msBitOrZero))) *
        heteroKron 1 (conjIsometry (msBobTwoQubitSwapIsometry S)
          (obsOf (((msDilatedStrategy S).B (.var 0)).postprocess msBitOrZero)))))
      (idealMsState r))]

/-- `thm:ms-rigidity` in the corrected form adopted on issue #172 (owner
decision B5 on issue #26), imported from Coladangelo--Stark, Theorem 6.9.
Blueprint `ch13_qpbt_test.tex`, paper
`08_classical_and_quantum_low_degree_tests.tex:612-652`.

**Local fix:** The source quantifies over all strategies of value `1 - ε`.
That statement is false; the refutation and the corrected form adopted here
are recorded in `docs/paper-gaps/qpbt_ms-rigidity-symmetric-strategies.tex`.
The source's conclusion forces the two players' variable-0 and variable-4
measurements to agree on the shared state, while
`msGame` samples only constraint-variable pairs and never sends the same
question to both players, and a perfect strategy answering the two orientations
of each edge on independent copies of two EPR pairs, or its symmetric role-flag
version, violates the conclusion at `ε = 0`.  The corrected statement assumes,
in addition to the value, that the two players' bit measurements at the cells
`0` and `4` agree on the state up to `δ` in the squared state-dependent
distance of `def:povm-distance` (`msVariableConsistencyDefect`); the conclusion
is the source's display with `sqrt ε` replaced by `sqrt ε + sqrt δ`, so that
`δ = 0` is the source's display verbatim.  Symmetric projective strategies that
are consistent on their state, the class named in the owner decision, satisfy
the hypothesis with `δ = 0` (`exists_ms_rigidity_of_symmetric_consistent`);
neither symmetry nor projectivity is needed or assumed here.  Both
counterexamples have agreement distance `1` and are excluded.

The paper states the Euclidean estimate at scale `sqrt ε` at lines 624--626
and explains the norm conversion and local basis change at lines 650--652. One
universal constant applies to every strategy and every pair of nonnegative
error parameters.

**The proof.** For `1 <= sqrt eps + sqrt delta` the coarse witness of
`ms_rigidity_coarse_bounds` already satisfies all seven conclusions, through
`exists_ms_rigidity_of_one_le_sqrt_add`.  In the complementary regime the
witness is the tensor of the two players' two-qubit controlled-swap embeddings
composed with the dilation embedding, and the auxiliary state is the residual
state of `MagicSquareRigidity.ms_dilated_state_estimate`, which is the state
conclusion and the step at which `delta` enters, through the cross-player
agreement of the first logical pair.

The bit-measurement conclusions come from the transport of the first logical
pair through the two-qubit controlled swap: the phase observable is transported
exactly and the shift observable up to the anticommutator defect of that pair
(`MagicSquareRigidity.norm_ms_effect_defect_A_X`, `norm_ms_effect_defect_A_Z`
and their counterparts for the second player), and the spectral effects inherit
those estimates.  The anticommutator conclusions come from the approximate
anticommutation of the first pair on the dilated state
(`MagicSquareRigidity.msVarObsA_anticommute`, `msVarObsB_anticommute`), since
products compose under conjugation by an isometry.  Both are then moved from the
dilated state to the ideal state at the cost of twice the state distance, and
from the dilated strategy to the original one by
`MagicSquareRigidity.ms_effect_transfer_A`, `ms_effect_transfer_B`,
`ms_anticommutator_transfer_A`, `ms_anticommutator_transfer_B` and
`ms_state_transfer`. -/
theorem exists_ms_rigidity :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (ε δ : ℝ), 0 ≤ ε → 0 ≤ δ →
      ∀ S : Strategy msGame, 1 - ε ≤ S.value →
        msVariableConsistencyDefect S 0 ≤ δ →
        msVariableConsistencyDefect S 4 ≤ δ →
        ∃ w : MsRigidityWitness S,
          ‖isometryTensor w.φA w.φB S.ψ - idealMsState w.aux‖ ≤
              C * (Real.sqrt ε + Real.sqrt δ) ∧
          msOperatorDistanceA S w 0 .X ≤ C * (Real.sqrt ε + Real.sqrt δ) ∧
          msOperatorDistanceA S w 4 .Z ≤ C * (Real.sqrt ε + Real.sqrt δ) ∧
          msOperatorDistanceB S w 0 .X ≤ C * (Real.sqrt ε + Real.sqrt δ) ∧
          msOperatorDistanceB S w 4 .Z ≤ C * (Real.sqrt ε + Real.sqrt δ) ∧
          msAnticommutatorDistanceA S w ≤ C * (Real.sqrt ε + Real.sqrt δ) ∧
          msAnticommutatorDistanceB S w ≤ C * (Real.sqrt ε + Real.sqrt δ) := by
  classical
  refine ⟨2 * 10 ^ 12, by norm_num, fun ε δ hε hδ S hwin hd0 hd4 => ?_⟩
  by_cases hbig : 1 ≤ Real.sqrt ε + Real.sqrt δ
  · exact exists_ms_rigidity_of_one_le_sqrt_add _ ε δ (by norm_num) hbig S
  push_neg at hbig
  have hse : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  have hsd : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg δ
  have hsqe : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε
  have hεt : ε ≤ Real.sqrt ε + Real.sqrt δ := by nlinarith
  obtain ⟨r, hrnorm, hstate⟩ :=
    ms_dilated_state_estimate S ε δ hε hδ hwin hd0 hd4
  have hξ : ‖isometryTensor (msAliceTwoQubitSwapIsometry S)
      (msBobTwoQubitSwapIsometry S) (msDilatedStrategy S).ψ -
      idealMsState r‖ ≤ 172608 * (Real.sqrt ε + Real.sqrt δ) := hstate
  have hacA := norm_msJointAnticommutatorA_le S ε hwin
  have hacB := norm_msJointAnticommutatorB_le S ε hwin
  have hκt : (624 : ℝ) * Real.sqrt ε ≤ 624 * (Real.sqrt ε + Real.sqrt δ) := by nlinarith
  have htt : (Real.sqrt ε + Real.sqrt δ) ^ 2 ≤ Real.sqrt ε + Real.sqrt δ := by nlinarith
  have hX0 : (0 : ℝ) ≤ 624 * Real.sqrt ε + 2 * (172608 * (Real.sqrt ε + Real.sqrt δ)) := by
    positivity
  have hkey : (624 * Real.sqrt ε + 2 * (172608 * (Real.sqrt ε + Real.sqrt δ))) ^ 2 ≤
      345840 ^ 2 * (Real.sqrt ε + Real.sqrt δ) := by
    have h1 : 624 * Real.sqrt ε + 2 * (172608 * (Real.sqrt ε + Real.sqrt δ)) ≤
        345840 * (Real.sqrt ε + Real.sqrt δ) := by linarith
    have h2 : (624 * Real.sqrt ε + 2 * (172608 * (Real.sqrt ε + Real.sqrt δ))) ^ 2 ≤
        (345840 * (Real.sqrt ε + Real.sqrt δ)) ^ 2 := pow_le_pow_left₀ hX0 h1 2
    nlinarith [h2, htt]
  have hη2 : (172608 * (Real.sqrt ε + Real.sqrt δ)) ^ 2 ≤
      172608 ^ 2 * (Real.sqrt ε + Real.sqrt δ) := by nlinarith [htt]
  have hproj : ∀ (W : PauliKind) (b : ZMod 2),
      idealMagicBitProj W b =
        reflectionEffect (twoQubitPauliObs W) b :=
    fun W b => sum_ite_pauliProj_eq_reflectionEffect W b
  refine ⟨{ ιA'' := (msDilatedStrategy S).ιA
            ιB'' := (msDilatedStrategy S).ιB
            φA := (msAliceTwoQubitSwapIsometry S).comp
              (naimarkEmbedding S.ιA MsAnswer)
            φB := (msBobTwoQubitSwapIsometry S).comp
              (naimarkEmbedding S.ιB MsAnswer)
            aux := r
            aux_norm := hrnorm }, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine le_trans (le_of_eq (ms_state_transfer S (msAliceTwoQubitSwapIsometry S)
      (msBobTwoQubitSwapIsometry S) (idealMsState r))) (le_trans hξ ?_)
    nlinarith
  · refine le_trans (ms_effect_transfer_A S _ _ (idealMsState r)
      (fun b => heteroKron (heteroKron (idealMagicBitProj (.X) b) 1) 1) ε
      (172608 * (Real.sqrt ε + Real.sqrt δ)) hwin 0 hξ) ?_
    have hdil := ms_dilated_operator_distance_A S 0 .X r (624 * Real.sqrt ε)
      (172608 * (Real.sqrt ε + Real.sqrt δ)) hξ (fun b => by
        rw [hproj, dilatedEffect_var_A_eq]
        exact le_trans (norm_ms_effect_defect_A_X S b) hacA)
    refine le_trans (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left hdil (by norm_num : (0:ℝ) ≤ 3)) (le_refl _))
      (le_refl _)) ?_
    linarith [hkey, hη2, hεt]
  · refine le_trans (ms_effect_transfer_A S _ _ (idealMsState r)
      (fun b => heteroKron (heteroKron (idealMagicBitProj (.Z) b) 1) 1) ε
      (172608 * (Real.sqrt ε + Real.sqrt δ)) hwin 4 hξ) ?_
    have hdil := ms_dilated_operator_distance_A S 4 .Z r (624 * Real.sqrt ε)
      (172608 * (Real.sqrt ε + Real.sqrt δ)) hξ (fun b => by
        rw [hproj, dilatedEffect_var_A_eq]
        refine le_trans (norm_ms_effect_defect_A_Z S b) ?_
        positivity)
    refine le_trans (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left hdil (by norm_num : (0:ℝ) ≤ 3)) (le_refl _))
      (le_refl _)) ?_
    linarith [hkey, hη2, hεt]
  · refine le_trans (ms_effect_transfer_B S _ _ (idealMsState r)
      (fun b => heteroKron 1 (heteroKron (idealMagicBitProj (.X) b) 1)) ε
      (172608 * (Real.sqrt ε + Real.sqrt δ)) hwin 0 hξ) ?_
    have hdil := ms_dilated_operator_distance_B S 0 .X r (624 * Real.sqrt ε)
      (172608 * (Real.sqrt ε + Real.sqrt δ)) hξ (fun b => by
        rw [hproj, dilatedEffect_var_B_eq]
        exact le_trans (norm_ms_effect_defect_B_X S b) hacB)
    refine le_trans (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left hdil (by norm_num : (0:ℝ) ≤ 3)) (le_refl _))
      (le_refl _)) ?_
    linarith [hkey, hη2, hεt]
  · refine le_trans (ms_effect_transfer_B S _ _ (idealMsState r)
      (fun b => heteroKron 1 (heteroKron (idealMagicBitProj (.Z) b) 1)) ε
      (172608 * (Real.sqrt ε + Real.sqrt δ)) hwin 4 hξ) ?_
    have hdil := ms_dilated_operator_distance_B S 4 .Z r (624 * Real.sqrt ε)
      (172608 * (Real.sqrt ε + Real.sqrt δ)) hξ (fun b => by
        rw [hproj, dilatedEffect_var_B_eq]
        refine le_trans (norm_ms_effect_defect_B_Z S b) ?_
        positivity)
    refine le_trans (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left hdil (by norm_num : (0:ℝ) ≤ 3)) (le_refl _))
      (le_refl _)) ?_
    linarith [hkey, hη2, hεt]
  · refine le_trans (ms_anticommutator_transfer_A S _ _
      (idealMsState r) ε (172608 * (Real.sqrt ε + Real.sqrt δ)) hwin hξ) ?_
    have hdil := ms_dilated_anticommutator_A S r (624 * Real.sqrt ε)
      (172608 * (Real.sqrt ε + Real.sqrt δ)) hξ hacA
    refine le_trans (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left hdil (by norm_num : (0:ℝ) ≤ 3)) (le_refl _))
      (le_refl _)) ?_
    linarith [hkey, hη2, hεt]
  · refine le_trans (ms_anticommutator_transfer_B S _ _
      (idealMsState r) ε (172608 * (Real.sqrt ε + Real.sqrt δ)) hwin hξ) ?_
    have hdil := ms_dilated_anticommutator_B S r (624 * Real.sqrt ε)
      (172608 * (Real.sqrt ε + Real.sqrt δ)) hξ hacB
    refine le_trans (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left hdil (by norm_num : (0:ℝ) ≤ 3)) (le_refl _))
      (le_refl _)) ?_
    linarith [hkey, hη2, hεt]

/-- `thm:ms-rigidity` on the class fixed by owner decision B5 on issue #26:
the symmetric consistent strategies of the Magic Square game, that is, the
symmetric strategies that are projective and all of whose measurements are
consistent on their state (`def:consistent-strategy`, paper
`06_nonlocal_games_and_mipstar.tex:162-174`, where a consistent strategy is
projective by definition).  Every SPCC strategy (`def:spcc`) is one of these, so
the corollary covers the SPCC class as well.  Their variable measurements have
zero agreement distance, so this is the case `δ = 0` of `exists_ms_rigidity`,
and its conclusion is the source's display verbatim.  Projectivity is assumed
so that the hypothesis is exactly the source's class; the derivation below uses
only consistency.  The witness and the distances are those of the underlying
`Strategy msGame`, which the symmetric presentation `msGameSymm` yields
definitionally (`msGameSymm_toGame`).  Blueprint
`cor:ms-rigidity-symmetric-consistent` in `ch13_qpbt_test.tex`, paper
`08_classical_and_quantum_low_degree_tests.tex:612-652`; its proof specializes
`exists_ms_rigidity` at `δ = 0`. -/
theorem exists_ms_rigidity_of_symmetric_consistent :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (ε : ℝ), 0 ≤ ε →
      ∀ S : SymmetricStrategy msGameSymm, S.toStrategy.IsProjective →
        S.IsConsistent →
        1 - ε ≤ S.toStrategy.value →
        ∃ w : MsRigidityWitness S.toStrategy,
          ‖isometryTensor w.φA w.φB S.toStrategy.ψ - idealMsState w.aux‖ ≤
              C * Real.sqrt ε ∧
          msOperatorDistanceA S.toStrategy w 0 .X ≤ C * Real.sqrt ε ∧
          msOperatorDistanceA S.toStrategy w 4 .Z ≤ C * Real.sqrt ε ∧
          msOperatorDistanceB S.toStrategy w 0 .X ≤ C * Real.sqrt ε ∧
          msOperatorDistanceB S.toStrategy w 4 .Z ≤ C * Real.sqrt ε ∧
          msAnticommutatorDistanceA S.toStrategy w ≤ C * Real.sqrt ε ∧
          msAnticommutatorDistanceB S.toStrategy w ≤ C * Real.sqrt ε := by
  obtain ⟨C, hC, h⟩ := exists_ms_rigidity
  refine ⟨C, hC, fun ε hε S _hproj hS hwin => ?_⟩
  have h0 := msVariableConsistencyDefect_eq_zero_of_isConsistent S hS 0
  have h4 := msVariableConsistencyDefect_eq_zero_of_isConsistent S hS 4
  obtain ⟨w, h1, h2, h3, h4', h5, h6, h7⟩ :=
    h ε 0 hε le_rfl S.toStrategy hwin h0.le h4.le
  rw [Real.sqrt_zero, add_zero] at h1 h2 h3 h4' h5 h6 h7
  exact ⟨w, h1, h2, h3, h4', h5, h6, h7⟩

end

end MIPStarRE.QPBT
