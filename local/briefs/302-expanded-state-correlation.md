# Expanded-state correlation transport

Issue #302 is an auxiliary proof task under #119. The existing constructions
from #115 and #244 are prerequisites. The source is `eq:def-psihat` in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:367-372`
and the strategy construction in the proof of `lem:qld-4-7` at 1279-1288.

Regroup the six-register state as the existing two-player `pairState` and one
unused EPR pair. Prove both the `AA'`--`BA''` and `AB''`--`BB'` orientations,
using EPR swap symmetry for the latter. Transport the quadratic form of any
Hermitian operator on each expanded local space across these equalities.
The local operators are not assumed to factor between their two registers.

The entire Lean change belongs to the new standalone module
`MIPStarRE/QPBT/Combining/ExtendedLineGame/StateTransport.lean`. Reuse the
existing general placement reindexing lemmas and Mathlib Kronecker-product
associativity. Preserve every existing definition and source theorem.

Completion requires per-file Lean validation and standard-only axiom checks,
then the normal publication, canonical CI, independent review and merge gates.
No game-passing bound, line-line agreement, global measurement witness, or
paper theorem is claimed. Existing #119 worktrees, its recorded 1927 seconds
and unknown later historical usage, and the B8 budget of 13 attempts / 26509
seconds remain unchanged. This task is not a mathematical-gap correction.
