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

**Remaining proof.** It remains to combine the one-way Coladangelo--Stark
self-test for the orientation in which Alice holds the constraint --- or,
equivalently, the swap-isometry extraction of `Rigidity/Swap.lean` --- with the
approximate anticommutation of `Rigidity/Anticommutation.lean`, the
cross-player agreement `MagicSquareRigidity.msVarObsA_close_msVarObsB` that the
hypothesis yields in `Rigidity/Consistency.lean`, and the transfer estimates of
`Rigidity/Transfer.lean` and `Rigidity/AnticommutatorB.lean`; issue #105 tracks
this derivation. -/
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
`08_classical_and_quantum_low_degree_tests.tex:612-652`; its proof is that of
`exists_ms_rigidity`, which issue #105 tracks. -/
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
