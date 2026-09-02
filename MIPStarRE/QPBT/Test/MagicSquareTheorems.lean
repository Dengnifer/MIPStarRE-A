import MIPStarRE.QPBT.Algebra.Pauli
import MIPStarRE.QPBT.Games.StrategyClasses
import MIPStarRE.QPBT.Test.MagicSquare

/-!
# Magic Square rigidity and perfect strategies

This file states the imported rigidity theorem and the construction of a
perfect strategy from two anticommuting consistent binary measurements.

## References

The source statements are `thm:ms-rigidity` and `thm:ms-from-ac` in
`blueprint/src/chapter/ch13_qpbt_test.tex:207-263`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-722`.

Magic Square variables are one-based in the paper. Thus Lean's `.var 0` and
`.var 4` denote the paper's first and fifth variables, respectively.
-/

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-- Symmetry of the Magic Square question distribution from `def:ms-game`;
blueprint `ch13_qpbt_test.tex:188-203`, paper
`08_classical_and_quantum_low_degree_tests.tex:512-610`. -/
theorem msQuestionDistribution_symm (x y : MsType) :
    msGame.μ.weight (x, y) = msGame.μ.weight (y, x) := by
  sorry

/-- Symmetry of the Magic Square decision predicate from `def:ms-game`;
blueprint `ch13_qpbt_test.tex:188-203`, paper
`08_classical_and_quantum_low_degree_tests.tex:512-610`. -/
theorem msWinPredicate_symm (x y : MsType) (a b : MsAnswer) :
    msWinPredicate x y a b = msWinPredicate y x b a := by
  sorry

/-- The symmetric-game presentation of the Magic Square game. -/
noncomputable def msGameSymm : SymmetricGame where
  Question := MsType
  Answer := MsAnswer
  μ := msGame.μ
  μ_prob := msGame.μ_prob
  μ_symm := msQuestionDistribution_symm
  decide := msWinPredicate
  decide_symm := msWinPredicate_symm

/-- The symmetric presentation has the Magic Square game as its
underlying game. -/
theorem msGameSymm_toGame : msGameSymm.toGame = msGame := by
  rfl

/-- The observable associated with a binary measurement; formalization-only notation
used in `thm:ms-from-ac`, blueprint `ch13_qpbt_test.tex:234-263`, paper
`08_classical_and_quantum_low_degree_tests.tex:658-722`. -/
def obsOf {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Measurement (ZMod 2) ι) : Op ι :=
  M.effect 0 - M.effect 1

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
      (conjIsometry w.φA ((S.A (.var j)).effect (.bit b))) 1)
    (fun _ b => heteroKron
      (heteroKron (idealMagicBitProj W b) (1 : Op w.ιA'')) 1)
    (idealMsState w.aux)

/-- Bob's bit-measurement distance in `thm:ms-rigidity`. -/
noncomputable def msOperatorDistanceB (S : Strategy msGame)
    (w : MsRigidityWitness S) (j : Fin 9) (W : PauliKind) : ℝ :=
  opFamilyDistSq (uniformDistribution Unit)
    (fun _ b => heteroKron 1
      (conjIsometry w.φB ((S.B (.var j)).effect (.bit b))))
    (fun _ b => heteroKron 1
      (heteroKron (idealMagicBitProj W b) (1 : Op w.ιB'')))
    (idealMsState w.aux)

/-- Alice's anticommutator defect from the consequence in
`thm:ms-rigidity`. -/
noncomputable def msAnticommutatorDistanceA (S : Strategy msGame)
    (w : MsRigidityWitness S) : ℝ :=
  let X := heteroKron
    (conjIsometry w.φA
      ((S.A (.var 0)).effect (.bit 0) - (S.A (.var 0)).effect (.bit 1))) 1
  let Z := heteroKron
    (conjIsometry w.φA
      ((S.A (.var 4)).effect (.bit 0) - (S.A (.var 4)).effect (.bit 1))) 1
  opDistSq (uniformDistribution Unit) (fun _ => X * Z)
    (fun _ => -(Z * X)) (idealMsState w.aux)

/-- Bob's anticommutator defect from the consequence in
`thm:ms-rigidity`. -/
noncomputable def msAnticommutatorDistanceB (S : Strategy msGame)
    (w : MsRigidityWitness S) : ℝ :=
  let X := heteroKron 1
    (conjIsometry w.φB
      ((S.B (.var 0)).effect (.bit 0) - (S.B (.var 0)).effect (.bit 1)))
  let Z := heteroKron 1
    (conjIsometry w.φB
      ((S.B (.var 4)).effect (.bit 0) - (S.B (.var 4)).effect (.bit 1)))
  opDistSq (uniformDistribution Unit) (fun _ => X * Z)
    (fun _ => -(Z * X)) (idealMsState w.aux)

/-- `thm:ms-rigidity`, imported from Coladangelo--Stark, Theorem 6.9.
Blueprint `ch13_qpbt_test.tex:207-231`, paper
`08_classical_and_quantum_low_degree_tests.tex:612-652`.

**Local fix:** The state estimate is stated in Euclidean norm at scale
`sqrt ε`, and the ideal observables use the local basis change described at
paper lines 650--652. The universal constant is quantified before the strategy
and error parameter. This formal boundary is recorded in issue #16. -/
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

/-- The state of the perfect strategy constructed in `thm:ms-from-ac`. -/
noncomputable def msPerfectState (ι : Type*) [Fintype ι] [DecidableEq ι]
    [Nonempty ι] : EuclideanSpace ℂ ((ι × ZMod 2) × (ι × ZMod 2)) :=
  reindexState prodShuffle (vecTensor (eprState ι) (eprState (ZMod 2)))

/-- `thm:ms-from-ac`: any anticommuting pair of projective binary
measurements, consistent on an EPR state, extends to a value-one SPCC Magic
Square strategy. Blueprint `ch13_qpbt_test.tex:234-263`, paper
`08_classical_and_quantum_low_degree_tests.tex:654-722`.

The local index type is arbitrary, finite, and nonempty; no field model or QPBT
parameter is assumed. The equality `hι` records the explicitly constructed
local tensor factor. -/
theorem exists_ms_perfect_strategy_of_anticommuting
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A B : Measurement (ZMod 2) ι)
    (hA : MIPStarRE.QPBT.Measurement.IsProjective A)
    (hB : MIPStarRE.QPBT.Measurement.IsProjective B)
    (hcA : MIPStarRE.QPBT.Measurement.IsConsistentOn A (eprState ι))
    (hcB : MIPStarRE.QPBT.Measurement.IsConsistentOn B (eprState ι))
    (hac : obsOf A * obsOf B = -(obsOf B * obsOf A)) :
    ∃ S : SymmetricStrategy msGameSymm, ∃ hι : S.ι = (ι × ZMod 2),
      S.IsSPCC ∧ S.toStrategy.value = 1 ∧
      reindexState (Equiv.prodCongr (Equiv.cast hι) (Equiv.cast hι)) S.ψ =
        msPerfectState ι ∧
      ∀ b : ZMod 2,
        reindexOp (Equiv.cast hι.symm) ((S.M (.var 0)).effect (.bit b)) =
            heteroKron (A.effect b) (1 : Op (ZMod 2)) ∧
          reindexOp (Equiv.cast hι.symm) ((S.M (.var 4)).effect (.bit b)) =
            heteroKron (B.effect b) (1 : Op (ZMod 2)) := by
  sorry

end

end MIPStarRE.QPBT
