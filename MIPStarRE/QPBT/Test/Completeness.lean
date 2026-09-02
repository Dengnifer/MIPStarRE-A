import MIPStarRE.QPBT.Games.StrategyClasses
import MIPStarRE.QPBT.Test.LowDegreeGameTheorems
import MIPStarRE.QPBT.Test.MagicSquareTheorems
import MIPStarRE.QPBT.Test.PauliBasisTest

/-!
# Completeness of the Pauli basis test

This file packages the landed Pauli basis game as a symmetric game and states
the value-one SPCC completeness theorem.

## References

The source node is `lem:pauli-completeness` in
`blueprint/src/chapter/ch13_qpbt_test.tex:371-382`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1229-1421`.
-/

namespace MIPStarRE.QPBT

noncomputable section

/-- Symmetry of the Pauli question distribution, used to package the landed
game as the symmetric game appearing in `lem:pauli-completeness`. -/
theorem pauliQuestionDistribution_symm (P : AdmissibleParams)
    (x y : PauliQuestion P) :
    (pauliQuestionDistribution P).weight (x, y) =
      (pauliQuestionDistribution P).weight (y, x) := by
  sorry

/-- Symmetry of the Pauli decision predicate, used to package the landed game
as the symmetric game appearing in `lem:pauli-completeness`. -/
theorem pauliWinPredicate_symm (P : AdmissibleParams)
    (x y : PauliQuestion P) (a b : PauliAnswer P) :
    pauliWinPredicate P x y a b = pauliWinPredicate P y x b a := by
  sorry

/-- The symmetric presentation of the Pauli basis test. The field and basis
are those fixed by `P.model`; no additional model is quantified. -/
noncomputable def pauliBasisTestSymm (P : AdmissibleParams) : SymmetricGame where
  Question := PauliQuestion P
  Answer := PauliAnswer P
  μ := pauliQuestionDistribution P
  μ_prob := (pauliBasisTest P).μ_prob
  μ_symm := pauliQuestionDistribution_symm P
  decide := pauliWinPredicate P
  decide_symm := pauliWinPredicate_symm P

/-- The symmetric presentation has the landed Pauli basis test as its
underlying game. -/
theorem pauliBasisTestSymm_toGame (P : AdmissibleParams) :
    (pauliBasisTestSymm P).toGame = pauliBasisTest P := by
  rfl

/-- `lem:pauli-completeness`: every admissible Pauli basis test has a
value-one SPCC strategy. Blueprint `ch13_qpbt_test.tex:371-382`, paper
`08_classical_and_quantum_low_degree_tests.tex:1229-1421`. -/
theorem exists_spcc_value_one (P : AdmissibleParams) :
    ∃ S : SymmetricStrategy (pauliBasisTestSymm P),
      S.IsSPCC ∧ S.toStrategy.value = 1 := by
  sorry

end

end MIPStarRE.QPBT
