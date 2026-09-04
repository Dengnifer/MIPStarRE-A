import MIPStarRE.QPBT.Games.StrategyClasses
import MIPStarRE.QPBT.Games.TypedCondLinear
import MIPStarRE.QPBT.Test.LowDegreeGameTheorems
import MIPStarRE.QPBT.Test.MagicSquareTheorems
import MIPStarRE.QPBT.Test.PauliBasisTest

/-!
# Completeness of the Pauli basis test

This file presents the Pauli basis test as a symmetric game and states its
value-one SPCC completeness theorem.

## References

The source statement is `lem:pauli-completeness` in
`blueprint/src/chapter/ch13_qpbt_test.tex:390-395`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1229-1421`.
-/

namespace MIPStarRE.QPBT

noncomputable section

/-- The Pauli question sampler equals the generalized typed distribution on the
Pauli type graph. This is the distribution-equality obligation supporting
`lem:pauli-question-typed-cl`, blueprint `ch13_qpbt_test.tex:440-448`, paper
`references/qpbt-paper/07_types.tex:84-93`.

**Unfaithful:** The equality asserted in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1115-1120`
is not yet proved and is tracked by issue #180. Elimination: identify the
uniform `PauliEdge` sampler with `graphDistribution` and unfold the common-seed
push-forward in `typedCLDistribution`.
-/
theorem pauliQuestionDistribution_eq_typedCL (P : AdmissibleParams) :
    pauliQuestionDistribution P =
      typedCLDistribution pauliEdges (by
        refine ⟨Sym2.mk (.point .X) (.point .X), ?_⟩
        simp [pauliEdges]) (pauliCL P) (pauliCL P) := by
  sorry

/-- `lem:pauli-question-typed-cl`: the Pauli maps form a common-level typed
conditionally linear family, and their typed distribution is exactly the
question distribution of the Pauli basis test. Blueprint
`ch13_qpbt_test.tex:450-458`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-966,1084-1120`.

**Unfaithful:** This proof currently relies on the open declarations
`isTypedCondLinearFamily_pauliCL` and
`pauliQuestionDistribution_eq_typedCL`, which are not yet proved from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1084-1120`.
This is tracked by issue #180. Elimination: complete those component family and
distribution-equality proofs.
-/
theorem pauliQuestionDistribution_isTypedCL (P : AdmissibleParams) :
    IsTypedCondLinearFamily (PauliScalar P) PauliType 3 (pauliCL P) ∧
      pauliQuestionDistribution P =
        typedCLDistribution pauliEdges (by
          refine ⟨Sym2.mk (.point .X) (.point .X), ?_⟩
          simp [pauliEdges]) (pauliCL P) (pauliCL P) := by
  exact ⟨isTypedCondLinearFamily_pauliCL P,
    pauliQuestionDistribution_eq_typedCL P⟩

/-- Symmetry of the Pauli question distribution in the symmetric game appearing
in `lem:pauli-completeness`. -/
theorem pauliQuestionDistribution_symm (P : AdmissibleParams)
    (x y : PauliQuestion P) :
    (pauliQuestionDistribution P).weight (x, y) =
      (pauliQuestionDistribution P).weight (y, x) := by
  sorry

/-- Symmetry of the Pauli decision predicate in the symmetric game appearing in
`lem:pauli-completeness`. -/
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

/-- The symmetric presentation has the Pauli basis test as its
underlying game. -/
theorem pauliBasisTestSymm_toGame (P : AdmissibleParams) :
    (pauliBasisTestSymm P).toGame = pauliBasisTest P := by
  rfl

/-- `lem:pauli-completeness`: every admissible Pauli basis test has a
value-one SPCC strategy. Blueprint `ch13_qpbt_test.tex:390-395`, paper
`08_classical_and_quantum_low_degree_tests.tex:1229-1421`. -/
theorem exists_spcc_value_one (P : AdmissibleParams) :
    ∃ S : SymmetricStrategy (pauliBasisTestSymm P),
      S.IsSPCC ∧ S.toStrategy.value = 1 := by
  sorry

end

end MIPStarRE.QPBT
