# Expanded Spectator Publication Refresh

## Scope

This record concerns PR274 / issue #273. The refresh starts from published
head `b716c50cbfc13d36f34a4ad51a054edc3320761b` and incorporates the coordinator's
final published main pin `5924b3acec0d1ad5fe38b8a93ac5e950e2daa071` by an ordinary
merge. The complete 192-line `Observables/ExpandedSpectator.lean` module is
unchanged, with Git blob `7d9afc63264c3ae68c74dba41fd920b12c416021`. Its import
in `MIPStarRE/QPBT.lean` is retained alongside every incoming main import.
No theorem, definition, hypothesis, proof body, or blueprint completion tag
is changed by this refresh.

## Source and Identities

The source is `eq:def-psihat` in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:367-372` and
the two register partitions at lines 433-450. The corresponding blueprint
definitions are `def:expanded-state` and `def:symmetric-equivalents`.

The expanded state is the original bipartite state tensored with normalized
EPR pairs on `A'A''` and `B'B''`. Operators on `AA'` and `BA''` act trivially
on `B'B''`; after an explicit coordinate permutation, their product is a
tensor product with the identity on that unused pair. Its contribution to
the complex expectation is its squared norm, which is one. The `BB'`,
`AB''` case instead removes `A'A''` and explicitly reverses the original
state coordinates from `AB` to `BA`. The two original player spaces need
not have equal dimension.

These are exact coordinate identities for arbitrary operators. They do not
use positivity, symmetry of the strategy, or an approximate consistency
estimate. The proof uses the existing tensor and reindexing operations,
Mathlib's finite-sum and matrix-reindexing identities, and the proved EPR
normalization. It does not import an unmerged consistency-transfer result.

## Statement Integrity

- Source context: the expanded-state definition and its two register
  partitions, with normalized ancillary EPR pairs.
- Lean assumptions: unchanged `P : AdmissibleParams`,
  `S : ProjectiveSetting P epsilon`, and arbitrary operators on the two
  indicated expanded player spaces; the existing finite-dimensional field
  model and decidability instances are retained.
- Source calculation: an identity-acted normalized ancillary pair contributes
  one, with the explicit player-coordinate reversal in the second partition.
- Lean conclusions: the two state factorizations, the two placed-operator
  product identities, and the two full complex expectation identities are
  unchanged.
- Verdict: faithful Lean-only coordinate identities. No paper-facing
  consistency result is claimed, and no assumption or conclusion is changed.

## Validation

The pending merge-loss guard and whitespace checks pass. Every incoming path
is retained, and the raw telemetry tree equals the pinned main tree. The
source packet contains no proof hole, axiom declaration, prohibited bypass,
or debug command.

The private build artifacts are refreshed from the published complete snapshot
at `a2f52f6d15a1af57740ee73eab913e3747b47792`. Its cache key matches, and its Lean
source, toolchain, and dependency manifest are identical to the final main pin.
The primary cache-consumer script is used with package fetching and full
building disabled; neither the shared cache nor its packages are written.

The targeted build of `MIPStarRE.QPBT.Observables.ExpandedSpectator` and
`MIPStarRE.QPBT` succeeds. Direct `lake env lean` checks of the spectator
module and the QPBT root also succeed. All six public theorem axiom closures
are exactly `[propext, Classical.choice, Quot.sound]`. Blueprint declaration
synchronization succeeds after regenerating its ignored declaration list.

The unchanged module's `open Classical` at line 29 produces an existing style
warning under the Lake target build. It is recorded here without modifying
the preserved source or suppressing the linter. Other imported proof debt is
unchanged by this packet. Historical CI evidence cited by the preceding PR
description belongs to its recorded old head, not to this refreshed head.
Checked publication, fresh exact-head full CI, independent review, and merge
remain separate workflow gates; this publication worker runs no canonical CI
or self-review.
