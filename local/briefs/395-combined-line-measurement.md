# Issue 395: combined line measurement constructor

Recover the five-declaration X-Z-X paired-line measurement slice supporting
`lem:qld-xz-lines`, sourced from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:942-949`.

The owned Lean changes are limited to a dedicated helper module and its facade
import.  The constructor uses the existing expanded line measurements and
`pastedMeasurement_isMeasurement`; the two support lemmas use the existing
axis-degree vanishing theorem.  No consistency estimate, conditioned sampler,
point-witness hypothesis, zero-direction restriction, or source-theorem closure
is part of this issue.

The integration stack preserves PR #391 at `3ab9f44b`, PR #392 at `2cc44385`,
and the required expanded-line proof head at `b04ced12`.  B8 remains the separate
Bob-side extended-line obstruction for `lem:qld-4-13`.
