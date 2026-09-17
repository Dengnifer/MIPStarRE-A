# Completion of mixed line/point rejection bounds

Issue #311 is an auxiliary proof task under #119, stacked on the reversed axis
transport from #309 and transitively on #307, #305, and #302. The source
context is the strategy construction in the proof of `lem:qld-4-7` at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`.

The first theorem identifies the remaining point/diagonal-line rejection
probability with the `BB'`--`AB''` completed diagonal-line/point defect. Its
proof preserves completed evaluation as an `Option`, exchanges the finite
answer sums to align player order, commutes the opposite placements, and uses
the exact second expanded-state correlation. Zero directions remain included,
and failed evaluation remains the `none` outcome and contributes rejection.

The second theorem rewrites all four mixed point/line rejection probabilities
by their exact completed-defect identities and applies the two oriented bounds
from `completedLinePointDefect_sums_le`, obtaining the sum bound
`4 * deltaL`.

Both Lean statements use only the supplied `CombinedPointsWitness` and
`ExtendedLinesWitness`. They add no passing premise, producer input, symmetry,
divisibility condition, or bridge hypothesis. This packet advances the
supplied-witness passing-value route but does not bound the remaining game
branches, construct a global measurement, or complete `lem:qld-4-7`.

Completion requires focused Lean validation, standard-only axiom checks, and
the normal publication, canonical CI, independent review, and merge gates. The
PR remains blocked on #309 while PR310 is pending. Prior issue #309 usage and
the B8 budget of 13 attempts / 26509 seconds remain unchanged.
