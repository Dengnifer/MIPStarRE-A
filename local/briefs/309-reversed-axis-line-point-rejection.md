# Reversed axis-line/point rejection transport

Issue #309 is an auxiliary proof task under #119, stacked on the line-point
transport from #307 and transitively on the axis transport from #305 and the
expanded-state transport from #302. The source context is the strategy
construction in the proof of `lem:qld-4-7` at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`.

The new theorem identifies the rejection probability of the point/axis-line
branch with `completedLinePointDefect` on the `BB'`--`AB''` placements for the
supplied `ExtendedLinesWitness`. Its proof unfolds the finite game
postprocessing, uses zero mass of invalid answer tags, exchanges the two finite
answer sums to align the player order, commutes the opposite placements, and
applies the exact `AB''`--`BB'` state correlation from #302. It does not identify
the Alice and Bob spaces or assume symmetry of the strategy or state.

The Lean statement assumes the existing `CombinedPointsWitness` and
`ExtendedLinesWitness`; it adds no passing premise, producer input, or bridge
hypothesis. Its conclusion is only the exact branch equality. It does not prove
the full passing bound in `lem:qld-4-7`, construct a global measurement, or
discharge the separate extraction-witness frontier tracked by #119.

The proof depends mathematically on the expanded-state correlation from #302
and the forward axis-line/point transport from #305. The diagonal-line/point
transport from #307 records stack and repository provenance; this proof does
not use its theorem. Existing #119 usage and the B8 budget of 13 attempts /
26509 seconds remain unchanged.
