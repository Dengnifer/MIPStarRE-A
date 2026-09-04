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
import MIPStarRE.QPBT.Test.SoundnessDefs
import MIPStarRE.QPBT.Test.Soundness
import MIPStarRE.QPBT.State
import MIPStarRE.QPBT.Algebra.SubspacesTheorems
import MIPStarRE.QPBT.Algebra.SelfDualBasis
import MIPStarRE.QPBT.Algebra.SelfDualBasisTheorems
import MIPStarRE.QPBT.Algebra.LowDegreeCodeTheorems
import MIPStarRE.QPBT.Algebra.PauliTheorems
import MIPStarRE.QPBT.Games.DistributionAux
import MIPStarRE.QPBT.Games.ErrorFunctions
import MIPStarRE.QPBT.Games.Consistency
import MIPStarRE.QPBT.Games.StrategyClasses
import MIPStarRE.QPBT.Games.DistanceTheorems
import MIPStarRE.QPBT.Games.Sandwich
import MIPStarRE.QPBT.Games.CondLinearTheorems
import MIPStarRE.QPBT.Games.TypedCondLinear
import MIPStarRE.QPBT.Observables.LineDefs
import MIPStarRE.QPBT.Observables.Anticommuting
import MIPStarRE.QPBT.Observables.Setup
import MIPStarRE.QPBT.Observables.Defs
import MIPStarRE.QPBT.Observables.ExpandedDefs
import MIPStarRE.QPBT.Observables.PointConsistency
import MIPStarRE.QPBT.Observables.LineMeasurement
import MIPStarRE.QPBT.Observables.WinImplications
import MIPStarRE.QPBT.Test.LowDegreeGameTheorems
import MIPStarRE.QPBT.Test.MagicSquareTheorems
import MIPStarRE.QPBT.Test.Completeness
import MIPStarRE.QPBT.Test.QubitForm
import MIPStarRE.QPBT.Test.CanonicalParams
import MIPStarRE.QPBT.Combining.Defs
import MIPStarRE.QPBT.Combining.DirectLowDegree
import MIPStarRE.QPBT.Combining.Linearity
import MIPStarRE.QPBT.Combining.Witnesses
import MIPStarRE.QPBT.Combining.Points
import MIPStarRE.QPBT.Combining.Lines
import MIPStarRE.QPBT.Combining.Claims
import MIPStarRE.QPBT.Combining.Apply

-- Mathlib 4.31 header checks require this for this aggregate module.
set_option linter.style.header false

/-!
# Quantum Pauli basis test

This aggregate module provides the QPBT algebraic, game-theoretic, and test
declarations.

## References

Blueprint chapters `ch11_qpbt_algebra.tex`, `ch12_qpbt_games.tex`, and
`ch13_qpbt_test.tex`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.
-/
