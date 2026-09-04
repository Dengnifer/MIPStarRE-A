import MIPStarRE.QPBT.Combining.DirectLowDegree.Soundness
import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Consistency
import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Strategy
import MIPStarRE.QPBT.Combining.DirectLowDegree.GameValue
import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.PassConversion
import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.SeedFiberValue
import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Error

/-!
# The directly indexed low-degree game

The low-degree game used by the Pauli-basis combining argument is needed in
dimension `2 * m + 2`.  The existing conditionally linear game represents a
coordinate index by an equally sized fiber in the scalar field and therefore
requires the dimension to divide the field size.  This file gives the separate
directly indexed variant which samples that index directly.

The geometric line carrier records the sampled coordinate, and line evaluation
uses an `Option` outcome rather than assigning a value when a point does not
determine one.  The game retains the point, axis-line, and diagonal-line answer
formats and the nine ordered type branches of the original low-degree game.

The `Transport` modules relate the direct game to the seed-indexed game and to
the mature low individual degree test interface: `Transport.Correspondence`
identifies coordinates, answers, and the question law of the two QPBT
presentations; `Transport.SeedFiber` dilates a seed-indexed strategy to a
direct strategy by a correlated residue register, and `Transport.SeedFiberValue`
shows that the dilation preserves the value exactly; `Transport.Questions`
reads mature lines as canonical direct questions and rebases direct answers;
`Transport.Strategy` reads one coordinate of a projective direct strategy as a
mature `ProjStrat`, with exact Born-weight formulas for both adapters; and
`Transport.BranchComparison`, `Transport.DiagonalRecursion`, and
`Transport.PassConversion` convert a value bound of the direct game into the
pass hypothesis of the mature low individual degree theorem for every
coordinate strategy.  `GameValue` supplies the rejection calculus relating the
direct value to the mature branch weights.  `Transport.Error` carries the
scalar half of the transport: the auxiliary sampling parameter with which
the mature theorem is applied, bounds on the three terms of its error
function, and the absorption of the resulting simultaneous-measurement
estimate into the error function of `lem:ld-soundness`.
`Transport.Consistency` identifies polynomial outcomes and transports the
three mature consistency conclusions to the direct game.

## References

The underlying game is `def:ld-game` in
`blueprint/src/chapter/ch13_qpbt_test.tex:17-105`, with source origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
The need for the directly indexed repair in Chapter 15 is explained around
`rem:qld-4-7-divisibility` in
`blueprint/src/chapter/ch15_qpbt_combining.tex:1257-1293` and in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.
-/
