import MIPStarRE.QPBT.Games.StrategyClasses
import MIPStarRE.QPBT.Test.MagicSquare

/-!
# Basic Magic Square symmetry facts

This file proves symmetry of the Magic Square question distribution and
decision predicate, packages the game as a `SymmetricGame`, and defines the
observable associated with a binary measurement.

## References

The game is `def:ms-game` in
`blueprint/src/chapter/ch13_qpbt_test.tex:207-222`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:512-610`.
-/

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-- Symmetry of the Magic Square question distribution from `def:ms-game`;
blueprint `ch13_qpbt_test.tex:207-222`, paper
`08_classical_and_quantum_low_degree_tests.tex:512-610`. -/
theorem msQuestionDistribution_symm (x y : MsType) :
    msGame.μ.weight (x, y) = msGame.μ.weight (y, x) := by
  classical
  simp [msGame, graphDistribution, Sym2.eq_swap]

/-- Symmetry of the Magic Square decision predicate from `def:ms-game`;
blueprint `ch13_qpbt_test.tex:207-222`, paper
`08_classical_and_quantum_low_degree_tests.tex:512-610`. -/
theorem msWinPredicate_symm (x y : MsType) (a b : MsAnswer) :
    msWinPredicate x y a b = msWinPredicate y x b a := by
  cases x <;> cases y <;> cases a <;> cases b <;>
    simp [msWinPredicate, and_comm, eq_comm]

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
used in `thm:ms-from-ac`, blueprint `ch13_qpbt_test.tex:257-267`, paper
`08_classical_and_quantum_low_degree_tests.tex:658-722`. -/
def obsOf {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Measurement (ZMod 2) ι) : Op ι :=
  M.effect 0 - M.effect 1

end

end MIPStarRE.QPBT
