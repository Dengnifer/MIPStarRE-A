import MIPStarRE.QPBT.Combining.DirectLowDegree.Soundness
import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Strategy
import MIPStarRE.QPBT.Combining.DirectLowDegree.GameValue

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
direct strategy by a correlated residue register; `Transport.Questions` reads
mature lines as canonical direct questions and rebases direct answers; and
`Transport.Strategy` reads one coordinate of a projective direct strategy as a
mature `ProjStrat`, with exact Born-weight formulas for both adapters.

## References

The underlying game is blueprint
`def:ld-game`, with source origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
The need for the directly indexed repair in Chapter 15 is explained around
blueprint
`rem:qld-4-7-divisibility` and in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.
-/
