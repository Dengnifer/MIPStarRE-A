# Diagonal-line/point rejection transport

Issue #307 is an auxiliary proof task under #119, stacked on the axis transport
from #305 and transitively on the expanded-state transport from #302. The source
context is the strategy construction in the proof of `lem:qld-4-7` at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`.

The new theorem identifies the rejection probability of the
diagonal-line/point branch with `completedLinePointDefect` for the supplied
`ExtendedLinesWitness`. Its proof unfolds the finite game postprocessing,
preserves completed evaluation as an `Option`, uses zero mass of invalid answer
tags, and applies the exact `AA'`--`BA''` state correlation from #302. Zero
diagonal directions are included; failed evaluation remains `none` and counts
as rejection.

The Lean statement assumes the existing `CombinedPointsWitness` and
`ExtendedLinesWitness`; it adds no passing premise, producer input, or bridge
hypothesis. Its conclusion is only the exact branch equality. It does not prove
the full passing bound in `lem:qld-4-7`, construct a global measurement, or
discharge the separate extraction-witness frontier tracked by #119.

Completion requires per-file Lean validation, a standard-only axiom check, and
the normal publication, canonical CI, independent review, and merge gates.
Existing #119 usage and the B8 budget of 13 attempts / 26509 seconds remain
unchanged.
