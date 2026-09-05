import MIPStarRE.QPBT.Algebra.Pauli
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Basic
import MIPStarRE.QPBT.Test.MagicSquareTheorems.PerfectStrategy
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.Relations
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.Dilation
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.Anticommutation
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.Transfer
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.AnticommutatorB
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.Swap

/-!
# Magic Square rigidity

This stable public facade re-exports the elementary symmetry facts, the
value-to-parity relation layer, and the perfect strategy construction while
retaining the imported rigidity theorem and its supporting definitions.

## References

The source statement is `thm:ms-rigidity` in
`blueprint/src/chapter/ch13_qpbt_test.tex:228-250`, from
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

/-- `thm:ms-rigidity`, imported from Coladangelo--Stark, Theorem 6.9.
Blueprint `ch13_qpbt_test.tex:228-250`, paper
`08_classical_and_quantum_low_degree_tests.tex:612-652`.

The paper states the Euclidean estimate at scale `sqrt ε` at lines 624--626
and explains the norm conversion and local basis change at lines 650--652. One
universal constant applies to every strategy and nonnegative error parameter. -/
theorem exists_ms_rigidity :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (ε : ℝ), 0 ≤ ε →
      ∀ S : Strategy msGame, 1 - ε ≤ S.value →
        ∃ w : MsRigidityWitness S,
          ‖isometryTensor w.φA w.φB S.ψ - idealMsState w.aux‖ ≤
              C * Real.sqrt ε ∧
          msOperatorDistanceA S w 0 .X ≤ C * Real.sqrt ε ∧
          msOperatorDistanceA S w 4 .Z ≤ C * Real.sqrt ε ∧
          msOperatorDistanceB S w 0 .X ≤ C * Real.sqrt ε ∧
          msOperatorDistanceB S w 4 .Z ≤ C * Real.sqrt ε ∧
          msAnticommutatorDistanceA S w ≤ C * Real.sqrt ε ∧
          msAnticommutatorDistanceB S w ≤ C * Real.sqrt ε := by
  sorry

end

end MIPStarRE.QPBT
