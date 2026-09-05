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

/-!
# Magic Square rigidity

This stable public facade re-exports the elementary symmetry facts, the
value-to-parity relation layer, and the perfect strategy construction while
retaining the rigidity theorem and its supporting definitions.

The rigidity theorem is stated in the corrected form adopted on issue #172: the
source quantifies over all strategies, which is false for the role-symmetric
game (`docs/paper-gaps/qpbt_ms-rigidity-symmetric-strategies.tex`), and the
corrected statement assumes that the two players' `Variable_1` and `Variable_5`
measurements are consistent between the players up to a defect `δ`
(`msVariableConsistencyDefect`, in `Rigidity/Consistency.lean`).  Symmetric
consistent strategies satisfy the hypothesis with `δ = 0`
(`exists_ms_rigidity_of_symmetric_consistent`).

## References

The source statement is `thm:ms-rigidity` in
`blueprint/src/chapter/ch13_qpbt_test.tex`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`.

The variable indices below are zero-based: indices 0 and 4 represent the
paper's first and fifth variables, respectively.
-/

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

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
`ch13_qpbt_test.tex:224-253`, paper
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

/-- `thm:ms-rigidity` in the corrected form adopted on issue #172 (owner
decision B5 on issue #26), imported from Coladangelo--Stark, Theorem 6.9.
Blueprint `ch13_qpbt_test.tex`, paper
`08_classical_and_quantum_low_degree_tests.tex:612-652`; the correction is
recorded in `docs/paper-gaps/qpbt_ms-rigidity-symmetric-strategies.tex`.

**The correction.** The source quantifies over all strategies of value
`1 - ε`.  That statement is false: its conclusion forces the two players'
variable-0 and variable-4 measurements to agree on the shared state, while
`msGame` samples only constraint-variable pairs and never sends the same
question to both players, and a perfect strategy answering the two orientations
of each edge on independent copies of two EPR pairs, or its symmetric role-flag
version, violates the conclusion at `ε = 0`.  The corrected statement assumes,
in addition to the value, that the two players' bit measurements at the cells
`0` and `4` agree on the state up to a consistency defect `δ`
(`msVariableConsistencyDefect`); the conclusion is the source's display with
`sqrt ε` replaced by `sqrt ε + sqrt δ`, so that `δ = 0` is the source's display
verbatim.  Symmetric strategies that are consistent on their state, the class
named in the owner decision, satisfy the hypothesis with `δ = 0`
(`exists_ms_rigidity_of_symmetric_consistent`); symmetry itself is not needed
and not assumed.  Both counterexamples have defect `1` and are excluded.

The paper states the Euclidean estimate at scale `sqrt ε` at lines 624--626
and explains the norm conversion and local basis change at lines 650--652. One
universal constant applies to every strategy and every pair of nonnegative
error parameters.

**Proof obligation.** The `sorry` is the part of the assembly of issue #105
that concerns the regime `sqrt ε + sqrt δ < 1`.  The complementary regime is
proved: `exists_ms_rigidity_of_one_le_sqrt_add` gives all seven conclusions
whenever `1 ≤ sqrt ε + sqrt δ` and `8 ≤ C`, from the coarse witness
`ms_rigidity_coarse_bounds`.

The following inputs to the small-error regime are available and sorry-free.
The first logical pair, at the cells `0` and `4`, approximately anticommutes on
the dilated state for each player (`MagicSquareRigidity.msVarObsA_anticommute`
and `msVarObsB_anticommute`), and the two players agree there through the
consistency hypothesis (`MagicSquareRigidity.msVarObsA_close_msVarObsB`).  The
second logical pair, at the cells `1` and `3`, approximately anticommutes for
each player (`MagicSquareRigidity.msCellObsA_second_pair_anticommute` and
`msVarObsB_second_pair_anticommute`), the two players agree there through the
constraint questions (`MagicSquareRigidity.msCellObsA_close_msVarObsB_second_x`
and `msCellObsA_close_msVarObsB_second_z`), and the two pairs approximately
commute on both sides
(`MagicSquareRigidity.msVarObsA_comm_msCellObsA_of_shared_constraint` and
`msVarObsB_comm_of_shared_constraint`).  The one-qubit controlled-swap
extraction and its intertwining relations are
`MagicSquareRigidity.binarySwapIsometry`, `binarySwap_intertwines_Z` and
`norm_binarySwap_intertwines_X_sub_le`; the two-qubit embeddings themselves are
`MagicSquareRigidity.msAliceTwoQubitSwapIsometry` and
`msBobTwoQubitSwapIsometry`, built from the two logical pairs of each player by
`MagicSquareRigidity.twoBinarySwapIsometry`.  The conclusions are transported
from the dilation to the original strategy by `ms_state_transfer`,
`ms_effect_transfer_A`, `ms_effect_transfer_B`, `ms_anticommutator_transfer_A`
and `ms_anticommutator_transfer_B`.

The joint state estimate for those two embeddings is also proved:
`MagicSquareRigidity.ms_dilated_state_estimate` carries the dilated state to
within a universal multiple of `sqrt ε + sqrt δ` of two EPR pairs tensored with
a unit residual state, and `ms_state_transfer` moves it to the original
strategy.  This is the step at which `δ` enters, through the cross-player
agreement of the first logical pair.

What remains is the bit-measurement estimate on the dilation: that the
two-qubit controlled swap carries each player's variable-0 and variable-4
effects to the marginals of the two-qubit Pauli basis over the first register
coordinate, up to `O(sqrt ε + sqrt δ)` on the transported state.  The one-qubit
intertwining relations are `MagicSquareRigidity.binarySwap_intertwines_Z` and
`norm_binarySwap_intertwines_X_sub_le`, and their two-qubit ingredients --- the
identification of those marginals with the spectral effects of the two-qubit
Pauli observable and the completeness of the residual factors of the second
swap --- are `MagicSquareRigidity.sum_ite_pauliProj_eq_reflectionEffect`,
`sum_twoSwapFactor_conjTranspose_mul` and `sum_rightTensor_twoSwapFactor`.
Their transport through the second controlled swap is the only step of the
argument that is not yet formalized. -/
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
  sorry

/-- `thm:ms-rigidity` on the class fixed by owner decision B5 on issue #26:
symmetric strategies of the Magic Square game that are consistent on their
state (`def:consistent-strategy`, paper
`06_nonlocal_games_and_mipstar.tex:162-174`).  Their variable measurements have
zero consistency defect, so this is the case `δ = 0` of `exists_ms_rigidity`,
and its conclusion is the source's display verbatim.  The witness and the
distances are those of the underlying `Strategy msGame`, which the symmetric
presentation `msGameSymm` yields definitionally (`msGameSymm_toGame`).
Blueprint `ch13_qpbt_test.tex`, paper
`08_classical_and_quantum_low_degree_tests.tex:612-652`; the proof is that of
`exists_ms_rigidity`, whose obligation is issue #105. -/
theorem exists_ms_rigidity_of_symmetric_consistent :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (ε : ℝ), 0 ≤ ε →
      ∀ S : SymmetricStrategy msGameSymm, S.IsConsistent →
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
  refine ⟨C, hC, fun ε hε S hS hwin => ?_⟩
  have h0 := msVariableConsistencyDefect_eq_zero_of_isConsistent S hS 0
  have h4 := msVariableConsistencyDefect_eq_zero_of_isConsistent S hS 4
  obtain ⟨w, h1, h2, h3, h4', h5, h6, h7⟩ :=
    h ε 0 hε le_rfl S.toStrategy hwin h0.le h4.le
  rw [Real.sqrt_zero, add_zero] at h1 h2 h3 h4' h5 h6 h7
  exact ⟨w, h1, h2, h3, h4', h5, h6, h7⟩

end

end MIPStarRE.QPBT
