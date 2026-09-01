import MIPStarRE.QPBT.Algebra.Subspaces
import MIPStarRE.QPBT.Algebra.FieldBasis
import MIPStarRE.QPBT.Algebra.LowDegreeCode
import MIPStarRE.QPBT.Algebra.Lines
import MIPStarRE.QPBT.Algebra.Pauli
import MIPStarRE.QPBT.Games.Defs
import MIPStarRE.QPBT.Games.Distance
import MIPStarRE.QPBT.Games.CondLinear
import MIPStarRE.QPBT.Test.LowDegreeGame
import MIPStarRE.QPBT.Test.MagicSquare
import MIPStarRE.QPBT.Test.PauliBasisTest
import MIPStarRE.QPBT.Test.Soundness

-- Mathlib 4.31 header checks require this for this aggregate module.
set_option linter.style.header false

/-!
# Quantum Pauli basis test

This aggregate module re-exports the stage-4.1 statement skeleton for the
quantum Pauli basis test.  The source-facing declarations follow the algebra,
game, test, and soundness chapters of the blueprint and retain proof-level
obligations for later stages.

## References

Blueprint chapters `ch11_qpbt_algebra.tex`, `ch12_qpbt_games.tex`, and
`ch13_qpbt_test.tex`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.
-/
