import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.Transfer
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.AnticommutatorB
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.CellRelations

/-!
# Cross-player agreement of the Magic Square variable measurements

The rigidity theorem `thm:ms-rigidity` is false for arbitrary strategies of the
role-symmetric Magic Square game: its conclusion forces the two players'
`Variable_1` and `Variable_5` measurements to agree on the shared state, and the
game never tests that agreement.  The corrected statement adopted on issue #172
(owner decision B5 on issue #26; the note is
`docs/paper-gaps/qpbt_ms-rigidity-symmetric-strategies.tex`) assumes that
agreement, quantitatively.  The *variable-measurement agreement distance* at a
variable is the summed squared state-dependent distance between Alice's and
Bob's binary variable effects on the shared state, in the `≈_δ` convention of
`def:povm-distance`, and the corrected theorem bounds it at the paper's first
and fifth variables.

That distance is not the consistency defect of `def:consistency`, which is the
off-diagonal outcome weight of a pair of measurements (`consistencyDefect`); it
is the squared state-dependent distance `opFamilyDistSq` of
`def:povm-distance`.  The declaration name `msVariableConsistencyDefect` records
what the distance measures: the failure of the two players' variable
measurements to be consistent with one another.

This file defines that distance on the original, possibly non-projective,
strategy and relates it to the reflections of the projective dilation on which
the self-testing argument operates.

* For a symmetric strategy whose variable measurements are consistent in the
  exact sense of `def:consistent-measurement`, the distance vanishes, so the
  corrected theorem specializes to the symmetric consistent strategies named in
  the owner decision.
* The two players' dilated variable reflections `msVarObsA S j` and
  `msVarObsB S j` are close on the dilated state whenever that distance is
  small.
  The loss is the leakage of the dilated observables out of the ground slice,
  which `Rigidity/Transfer.lean` controls by the cell-consistency masses of a
  strategy of value `1 - ε`.  This is the cross-player input that the
  swap-isometry extraction of issue #105 needs in order to compare the two
  players' extracted qubits.

## References

`thm:ms-rigidity`, blueprint `blueprint/src/chapter/ch13_qpbt_test.tex:224-253`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`.
The consistency notions are `def:consistent-measurement` and `def:povm-distance`,
paper `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:144-174` and
`258-271`.  The variable indices are zero-based, so the paper's first and fifth
variables are the cells `0` and `4`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open MIPStarRE.QPBT.MagicSquareRigidity

noncomputable section

/-! ## The agreement distance of a variable measurement -/

/-- The variable-measurement agreement distance between the two players'
binary measurements at the variable `j` of a Magic Square strategy: the summed
squared state-dependent distance `∑_b ‖(A_b ⊗ 1 - 1 ⊗ B_b) ψ‖²` of
`def:povm-distance` between Alice's and Bob's `Variable_j` effects, relabelled
to a bit by `msBitOrZero`, on the shared state.  The corrected
`thm:ms-rigidity` (blueprint `def:ms-variable-agreement` and
`thm:ms-rigidity` in `ch13_qpbt_test.tex`, correction recorded in
`docs/paper-gaps/qpbt_ms-rigidity-symmetric-strategies.tex`) assumes this
distance to be at most `δ` at the cells `0` and `4`.

The declaration name records what the distance measures, namely the failure of
the two players' variable measurements to be consistent with one another.  The
quantity itself is the squared state-dependent distance `opFamilyDistSq` of
`def:povm-distance`, not the outcome-disagreement weight `consistencyDefect` of
`def:consistency`.

The distance vanishes for a symmetric strategy whose variable measurements are
consistent in the sense of `def:consistent-measurement`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:144-160`; see
`msVariableConsistencyDefect_eq_zero_of_isConsistent`. -/
noncomputable def msVariableConsistencyDefect (S : Strategy msGame) (j : Fin 9) : ℝ :=
  opFamilyDistSq (uniformDistribution Unit)
    (fun _ b => heteroKron (((S.A (.var j)).postprocess msBitOrZero).effect b) 1)
    (fun _ b => heteroKron 1 (((S.B (.var j)).postprocess msBitOrZero).effect b))
    S.ψ

/-- The agreement distance is nonnegative. -/
theorem msVariableConsistencyDefect_nonneg (S : Strategy msGame) (j : Fin 9) :
    0 ≤ msVariableConsistencyDefect S j :=
  opFamilyDistSq_nonneg _ _ _ _

/-- The agreement distance as a sum of two squared state-dependent norms. -/
theorem msVariableConsistencyDefect_eq_sum (S : Strategy msGame) (j : Fin 9) :
    msVariableConsistencyDefect S j =
      ∑ b : ZMod 2, ‖applyOperatorToState
        (heteroKron (((S.A (.var j)).postprocess msBitOrZero).effect b) 1 -
          heteroKron 1 (((S.B (.var j)).postprocess msBitOrZero).effect b)) S.ψ‖ ^ 2 := by
  unfold msVariableConsistencyDefect
  rw [opFamilyDistSq_uniform_unit]

/-! ## Exact consistency -/

/-- Formalization-only: the action on a state is additive over finite sums of
operators. -/
theorem applyOperatorToState_finset_sum {β ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset β) (M : β → Op ι) (ψ : EuclideanSpace ℂ ι) :
    applyOperatorToState (∑ b ∈ s, M b) ψ = ∑ b ∈ s, applyOperatorToState (M b) ψ := by
  unfold applyOperatorToState
  simp only [map_sum, LinearMap.sum_apply]

/-- Formalization-only: equality of the matrix-vector products implies equality
of the corresponding operator actions on the state. -/
theorem applyOperatorToState_eq_of_mulVec_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M N : Op ι} {ψ : EuclideanSpace ℂ ι} (h : M.mulVec ψ = N.mulVec ψ) :
    applyOperatorToState M ψ = applyOperatorToState N ψ := by
  ext p
  have hp := congrFun h p
  simpa [applyOperatorToState, Matrix.toEuclideanLin] using hp

/-- A postprocessed effect of a measurement that is consistent on a state
(`def:consistent-measurement`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:144-160`) acts alike
on the two tensor factors of that state. -/
theorem applyOperatorToState_postprocess_effect_eq_of_isConsistentOn
    {α β ι : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype ι] [DecidableEq ι]
    (M : MIPStarRE.Quantum.Measurement α ι) (ψ : EuclideanSpace ℂ (ι × ι))
    (hM : MIPStarRE.QPBT.Measurement.IsConsistentOn M ψ) (f : α → β) (b : β) :
    applyOperatorToState (heteroKron ((M.postprocess f).effect b) 1) ψ =
      applyOperatorToState (heteroKron 1 ((M.postprocess f).effect b)) ψ := by
  classical
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect,
    MagicSquareRigidity.heteroKron_finset_sum_left,
    MagicSquareRigidity.heteroKron_finset_sum_right, applyOperatorToState_finset_sum,
    applyOperatorToState_finset_sum]
  exact Finset.sum_congr rfl fun a _ => applyOperatorToState_eq_of_mulVec_eq (hM a)

/-- A strategy whose two players' bit effects at variable `j` act alike on the
shared state has zero agreement distance at `j`. -/
theorem msVariableConsistencyDefect_eq_zero_of_forall (T : Strategy msGame) (j : Fin 9)
    (h : ∀ b : ZMod 2,
      applyOperatorToState
          (heteroKron (((T.A (.var j)).postprocess msBitOrZero).effect b) 1) T.ψ =
        applyOperatorToState
          (heteroKron 1 (((T.B (.var j)).postprocess msBitOrZero).effect b)) T.ψ) :
    msVariableConsistencyDefect T j = 0 := by
  rw [msVariableConsistencyDefect_eq_sum]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [applyOperatorToState_sub_op, h b, sub_self, norm_zero]
  simp

/-- A symmetric strategy whose measurement at variable `j` is consistent on its
state has zero agreement distance at `j`: exact consistency in the sense of
`def:consistent-measurement` is the case `δ = 0` of the hypothesis of the
corrected `thm:ms-rigidity`.  Paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:144-174`. -/
theorem msVariableConsistencyDefect_eq_zero_of_isConsistentOn
    (S : SymmetricStrategy msGameSymm) (j : Fin 9)
    (hS : MIPStarRE.QPBT.Measurement.IsConsistentOn (S.M (.var j)) S.ψ) :
    msVariableConsistencyDefect S.toStrategy j = 0 :=
  msVariableConsistencyDefect_eq_zero_of_forall S.toStrategy j fun b =>
    applyOperatorToState_postprocess_effect_eq_of_isConsistentOn (S.M (.var j)) S.ψ hS
      msBitOrZero b

/-- A symmetric strategy all of whose measurements are consistent on its state
has zero agreement distance at every variable.  Together with projectivity this
is a consistent strategy in the sense of `def:consistent-strategy`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:162-174`, the class
named in owner decision B5 on issue #26, to which the corrected
`thm:ms-rigidity` applies with `δ = 0`; projectivity is not needed here. -/
theorem msVariableConsistencyDefect_eq_zero_of_isConsistent
    (S : SymmetricStrategy msGameSymm) (hS : S.IsConsistent) (j : Fin 9) :
    msVariableConsistencyDefect S.toStrategy j = 0 :=
  msVariableConsistencyDefect_eq_zero_of_isConsistentOn S j (hS (.var j))

end

/-! ## Transfer to the dilated reflections -/

namespace MagicSquareRigidity

noncomputable section

/-- Formalization-only: the dilated state is additive over differences of
states. -/
theorem naimarkDilatedState_sub (α : Type) [Fintype α] [DecidableEq α]
    {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (u v : EuclideanSpace ℂ (ιA × ιB)) :
    naimarkDilatedState α (u - v) =
      naimarkDilatedState α u - naimarkDilatedState α v := by
  ext p
  simp only [PiLp.sub_apply, naimarkDilatedState_apply]
  split_ifs <;> simp

/-- Formalization-only: a left-placed inflated operator acts on the dilated
state as the original operator acts on the original state. -/
theorem applyOperatorToState_leftTensor_naimarkInflation (α : Type) [Fintype α]
    [DecidableEq α] {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB]
    [DecidableEq ιB] (M : Op ιA) (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    applyOperatorToState (heteroKron (naimarkInflation (α := α) M) 1)
        (naimarkDilatedState α ψ) =
      naimarkDilatedState α (applyOperatorToState (heteroKron M 1) ψ) := by
  rw [← applyOperatorToState_heteroKron_naimarkInflation]
  conv_lhs => rw [← applyOperatorToState_rightTensor_groundProjection α ψ]
  rw [← applyOperatorToState_mul, heteroKron_mul, Matrix.mul_one, Matrix.one_mul]
  rfl

/-- Formalization-only: a right-placed inflated operator acts on the dilated
state as the original operator acts on the original state. -/
theorem applyOperatorToState_rightTensor_naimarkInflation (α : Type) [Fintype α]
    [DecidableEq α] {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB]
    [DecidableEq ιB] (N : Op ιB) (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    applyOperatorToState (heteroKron 1 (naimarkInflation (α := α) N))
        (naimarkDilatedState α ψ) =
      naimarkDilatedState α (applyOperatorToState (heteroKron 1 N) ψ) := by
  rw [← applyOperatorToState_heteroKron_naimarkInflation]
  conv_lhs => rw [← applyOperatorToState_leftTensor_groundProjection α ψ]
  rw [← applyOperatorToState_mul, heteroKron_mul, Matrix.mul_one, Matrix.one_mul]
  rfl

/-- On the dilated state, the ground compressions of the two players' dilated
variable reflections differ exactly as the original variable observables do on
the original state. -/
theorem norm_compressed_varObs_sub_eq (S : Strategy msGame) (j : Fin 9) :
    ‖applyOperatorToState
        (heteroKron (groundProjection S.ιA MsAnswer * dilatedObsA S (.var j) *
            groundProjection S.ιA MsAnswer) 1 -
          heteroKron 1 (groundProjection S.ιB MsAnswer *
            dilatedObsB S (.var j) msBitOrZero * groundProjection S.ιB MsAnswer))
        (naimarkDilatedState MsAnswer S.ψ)‖ =
      ‖applyOperatorToState
        (heteroKron (obsOf ((S.A (.var j)).postprocess msBitOrZero)) 1 -
          heteroKron 1 (obsOf ((S.B (.var j)).postprocess msBitOrZero))) S.ψ‖ := by
  rw [← naimarkInflation_obs_A, ← naimarkInflation_obs_B, applyOperatorToState_sub_op,
    applyOperatorToState_leftTensor_naimarkInflation,
    applyOperatorToState_rightTensor_naimarkInflation, ← naimarkDilatedState_sub,
    naimarkDilatedState_norm, ← applyOperatorToState_sub_op]

/-- Formalization-only: a sum over the two-element answer alphabet. -/
private theorem sum_univ_zmod_two {M : Type*} [AddCommMonoid M] (f : ZMod 2 → M) :
    ∑ b : ZMod 2, f b = f 0 + f 1 :=
  Fin.sum_univ_two f

/-- The original variable observables of the two players differ on the state by
at most the square root of twice the agreement distance.  This is the
answer-cardinality bound `povm_to_obs` (`lem:povm-to-obs`) for the two-outcome
alphabet, with the unit-modulus weights `1` and `-1` that assemble the two
effects of a binary measurement into its observable. -/
theorem norm_varObs_sub_sq_le_two_mul_defect (S : Strategy msGame) (j : Fin 9) :
    ‖applyOperatorToState
        (heteroKron (obsOf ((S.A (.var j)).postprocess msBitOrZero)) 1 -
          heteroKron 1 (obsOf ((S.B (.var j)).postprocess msBitOrZero))) S.ψ‖ ^ 2 ≤
      2 * msVariableConsistencyDefect S j := by
  classical
  set c : ZMod 2 → ℂ := fun b => if b = 0 then 1 else -1 with hcdef
  have hcnorm : ∀ b : ZMod 2, ‖c b‖ = 1 := by
    intro b
    by_cases hb : b = 0 <;> simp [hcdef, hb]
  have hA : (∑ b : ZMod 2, c b •
      heteroKron (((S.A (.var j)).postprocess msBitOrZero).effect b) (1 : Op S.ιB)) =
      heteroKron (obsOf ((S.A (.var j)).postprocess msBitOrZero)) 1 := by
    rw [sum_univ_zmod_two]
    simp [hcdef, obsOf, heteroKron_sub_left, ← sub_eq_add_neg]
  have hB : (∑ b : ZMod 2, c b •
      heteroKron (1 : Op S.ιA) (((S.B (.var j)).postprocess msBitOrZero).effect b)) =
      heteroKron 1 (obsOf ((S.B (.var j)).postprocess msBitOrZero)) := by
    rw [sum_univ_zmod_two]
    simp [hcdef, obsOf, heteroKron_sub_right, ← sub_eq_add_neg]
  have hkey := povm_to_obs (uniformDistribution Unit)
    (fun (_ : Unit) (b : ZMod 2) =>
      heteroKron (((S.A (.var j)).postprocess msBitOrZero).effect b) (1 : Op S.ιB))
    (fun (_ : Unit) (b : ZMod 2) =>
      heteroKron (1 : Op S.ιA) (((S.B (.var j)).postprocess msBitOrZero).effect b))
    c hcnorm S.ψ
  simp only [opDistSq_uniform_unit, hA, hB] at hkey
  simpa [msVariableConsistencyDefect] using hkey

/-- The leakage of Alice's dilated variable reflection out of the ground slice is
controlled by the value of the strategy. -/
theorem norm_leak_varObs_sq_le_A (S : Strategy msGame) (ε : ℝ) (hwin : 1 - ε ≤ S.value)
    (j : Fin 9) :
    ‖applyOperatorToState (heteroKron ((1 - groundProjection S.ιA MsAnswer) *
        dilatedObsA S (.var j)) 1) (naimarkDilatedState MsAnswer S.ψ)‖ ^ 2 ≤ 144 * ε := by
  obtain ⟨i, k, hik⟩ := every_variable_is_incident j
  have hleak := norm_leak_obs_le_A S i k
  have hsq := sq_add_le_of_sum_sq_le _ _ ε (sum_norm_sq_intertwining_le_reverse S i k)
    (reverse_cell_mismatch_mass_le S ε hwin i k)
  rw [hik] at hleak hsq
  have hpow := pow_le_pow_left₀ (norm_nonneg _) hleak 2
  linarith

/-- The leakage of Bob's dilated variable reflection out of the ground slice is
controlled by the value of the strategy. -/
theorem norm_leak_varObs_sq_le_B (S : Strategy msGame) (ε : ℝ) (hwin : 1 - ε ≤ S.value)
    (j : Fin 9) :
    ‖applyOperatorToState (heteroKron 1 ((1 - groundProjection S.ιB MsAnswer) *
        dilatedObsB S (.var j) msBitOrZero)) (naimarkDilatedState MsAnswer S.ψ)‖ ^ 2 ≤
      144 * ε := by
  obtain ⟨i, k, hik⟩ := every_variable_is_incident j
  have hleak := norm_leak_obs_le_B S i k
  have hsq := sq_add_le_of_sum_sq_le _ _ ε (sum_norm_sq_intertwining_le_forward S i k)
    (forward_cell_mismatch_mass_le S ε hwin i k)
  rw [hik] at hleak hsq
  have hpow := pow_le_pow_left₀ (norm_nonneg _) hleak 2
  linarith

/-- The two players' dilated variable reflections at cell `j` agree on the
dilated state up to the agreement distance of the original variable
measurements and the leakage out of the ground slice: the squared
state-dependent distance is at most `864 ε + 6 δ` for a strategy of value
`1 - ε` whose agreement distance at `j` is at most `δ`.  This is the cross-player agreement
that the hypothesis of the corrected `thm:ms-rigidity` provides to the
swap-isometry extraction (issue #105); blueprint `ch13_qpbt_test.tex:224-253`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`. -/
theorem norm_msVarObsA_sub_msVarObsB_sq_le (S : Strategy msGame) (ε δ : ℝ)
    (hwin : 1 - ε ≤ S.value) (j : Fin 9) (hδ : msVariableConsistencyDefect S j ≤ δ) :
    ‖applyOperatorToState (msVarObsA S j - msVarObsB S j) (msDilatedStrategy S).ψ‖ ^ 2 ≤
      864 * ε + 6 * δ := by
  rw [msDilatedStrategy_psi, msVarObsA_eq_obsOf, msVarObsB_eq_obsOf]
  change ‖applyOperatorToState
      (heteroKron (dilatedObsA S (.var j)) (1 : Op (S.ιB × Option MsAnswer)) -
        heteroKron (1 : Op (S.ιA × Option MsAnswer)) (dilatedObsB S (.var j) msBitOrZero))
      (naimarkDilatedState MsAnswer S.ψ)‖ ^ 2 ≤ 864 * ε + 6 * δ
  have hop : heteroKron (dilatedObsA S (.var j)) (1 : Op (S.ιB × Option MsAnswer)) -
      heteroKron (1 : Op (S.ιA × Option MsAnswer)) (dilatedObsB S (.var j) msBitOrZero) =
      (heteroKron (groundProjection S.ιA MsAnswer * dilatedObsA S (.var j) *
          groundProjection S.ιA MsAnswer) 1 -
        heteroKron 1 (groundProjection S.ιB MsAnswer * dilatedObsB S (.var j) msBitOrZero *
          groundProjection S.ιB MsAnswer)) +
      heteroKron (dilatedObsA S (.var j) - groundProjection S.ιA MsAnswer *
        dilatedObsA S (.var j) * groundProjection S.ιA MsAnswer) 1 -
      heteroKron 1 (dilatedObsB S (.var j) msBitOrZero - groundProjection S.ιB MsAnswer *
        dilatedObsB S (.var j) msBitOrZero * groundProjection S.ιB MsAnswer) := by
    rw [heteroKron_sub_left, heteroKron_sub_right]
    abel
  rw [hop, applyOperatorToState_sub_op, applyOperatorToState_add_op,
    applyOperatorToState_leftTensor_sub_compression,
    applyOperatorToState_rightTensor_sub_compression]
  have hmid := norm_varObs_sub_sq_le_two_mul_defect S j
  rw [← norm_compressed_varObs_sub_eq] at hmid
  have hA := norm_leak_varObs_sq_le_A S ε hwin j
  have hB := norm_leak_varObs_sq_le_B S ε hwin j
  set x := applyOperatorToState
    (heteroKron (groundProjection S.ιA MsAnswer * dilatedObsA S (.var j) *
        groundProjection S.ιA MsAnswer) 1 -
      heteroKron 1 (groundProjection S.ιB MsAnswer * dilatedObsB S (.var j) msBitOrZero *
        groundProjection S.ιB MsAnswer)) (naimarkDilatedState MsAnswer S.ψ) with hx
  set y := applyOperatorToState (heteroKron ((1 - groundProjection S.ιA MsAnswer) *
    dilatedObsA S (.var j)) 1) (naimarkDilatedState MsAnswer S.ψ) with hy
  set z := applyOperatorToState (heteroKron 1 ((1 - groundProjection S.ιB MsAnswer) *
    dilatedObsB S (.var j) msBitOrZero)) (naimarkDilatedState MsAnswer S.ψ) with hz
  have htri : ‖x + y - z‖ ≤ ‖x‖ + ‖y‖ + ‖z‖ := by
    have h1 := norm_sub_le (x + y) z
    have h2 := norm_add_le x y
    linarith
  have hsq : ‖x + y - z‖ ^ 2 ≤ (‖x‖ + ‖y‖ + ‖z‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) htri 2
  nlinarith [hsq, hmid, hA, hB, hδ, sq_nonneg (‖x‖ - ‖y‖), sq_nonneg (‖y‖ - ‖z‖),
    sq_nonneg (‖x‖ - ‖z‖)]

/-- The cross-player agreement of the dilated variable reflections in the
squared-distance convention of `def:povm-distance`. -/
theorem msVarObsA_close_msVarObsB_opDistSq (S : Strategy msGame) (ε δ : ℝ)
    (hwin : 1 - ε ≤ S.value) (j : Fin 9) (hδ : msVariableConsistencyDefect S j ≤ δ) :
    opDistSq (uniformDistribution Unit) (fun _ => msVarObsA S j) (fun _ => msVarObsB S j)
      (msDilatedStrategy S).ψ ≤ 864 * ε + 6 * δ := by
  rw [opDistSq_uniform_unit]
  exact norm_msVarObsA_sub_msVarObsB_sq_le S ε δ hwin j hδ

/-- The cross-player agreement of the dilated variable reflections in the
unsquared convention of the rigidity chain. -/
theorem msVarObsA_close_msVarObsB (S : Strategy msGame) (ε δ : ℝ)
    (hwin : 1 - ε ≤ S.value) (j : Fin 9) (hδ : msVariableConsistencyDefect S j ≤ δ) :
    NormCloseOn (msDilatedStrategy S).ψ (Real.sqrt (864 * ε + 6 * δ))
      (msVarObsA S j) (msVarObsB S j) := by
  change ‖applyOperatorToState (msVarObsA S j - msVarObsB S j) (msDilatedStrategy S).ψ‖ ≤ _
  calc ‖applyOperatorToState (msVarObsA S j - msVarObsB S j) (msDilatedStrategy S).ψ‖
      = Real.sqrt (‖applyOperatorToState (msVarObsA S j - msVarObsB S j)
          (msDilatedStrategy S).ψ‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (864 * ε + 6 * δ) :=
        Real.sqrt_le_sqrt (norm_msVarObsA_sub_msVarObsB_sq_le S ε δ hwin j hδ)

end

end MagicSquareRigidity

end MIPStarRE.QPBT
