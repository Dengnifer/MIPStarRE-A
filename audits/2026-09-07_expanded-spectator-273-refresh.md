---
title: "Expanded spectator publication refresh"
date: 2026-09-07
purpose: >
  Records the publication refresh of the expanded-state spectator identities
  for issue #273, the later review repair that folded them onto the existing
  two-player state, and what was checked about their faithfulness to
  `eq:def-psihat`.
status: active
track: qpbt
kind: publication-audit
issue: "#273"
pr: "#274"
---

# Expanded Spectator Publication Refresh

## Scope

This record concerns PR274 / issue #273. The refresh starts from published
head `b716c50cbfc13d36f34a4ad51a054edc3320761b` and incorporates the coordinator's
final published main pin `5924b3acec0d1ad5fe38b8a93ac5e950e2daa071` by an ordinary
merge. At `b716c50c` the packet was the 192-line module
`Observables/ExpandedSpectator.lean` with Git blob
`7d9afc63264c3ae68c74dba41fd920b12c416021`, and that merge carried it over
unchanged. Later heads did change it: first the declaration-scoped
`open Classical` fix recorded under Validation, then the review repair recorded
under Review Repair, which also moved and renamed the module. Its import in
`MIPStarRE/QPBT.lean` is retained alongside every incoming main import. No
theorem, definition, hypothesis, proof body, or blueprint completion tag is
changed by the refresh merge itself.

## Source and Identities

The source is `eq:def-psihat` in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:367-372` and
the two register partitions at lines 433-450. The corresponding blueprint
definitions are `def:expanded-state` and `def:symmetric-equivalents`.

The expanded state is the original bipartite state tensored with normalized
EPR pairs on `A'A''` and `B'B''`. Operators on `AA'` and `BA''` act trivially
on `B'B''`; after an explicit coordinate permutation, their product is a
tensor product with the identity on that unused pair. Its contribution to
the complex expectation is its squared norm, which is one. The `AB''`,
`BB'` case instead removes `A'A''`, and the remaining two-player state is the
same one, because an EPR pair is invariant under exchanging its registers.
The two original player spaces need not have equal dimension.

These are exact coordinate identities for arbitrary operators. They do not
use positivity, Hermiticity, symmetry of the strategy, or an approximate
consistency estimate. The proof uses the existing tensor and reindexing
operations, Mathlib's finite-sum and matrix-reindexing identities, and the
proved EPR normalization. It does not import an unmerged consistency-transfer
result.

## Statement Integrity

- Source context: the expanded-state definition and its two register
  partitions, with normalized ancillary EPR pairs.
- Lean assumptions: unchanged `P : AdmissibleParams`,
  `S : ProjectiveSetting P epsilon`, and arbitrary operators on the two
  indicated expanded player spaces; the existing finite-dimensional field
  model and decidability instances are retained.
- Source calculation: an identity-acted normalized ancillary pair contributes
  one, in each of the two opposite register partitions.
- Lean conclusions: the two inverse state factorizations, the two placed-operator
  product identities, and the two full complex expectation identities.
- Verdict: faithful Lean-only coordinate identities. No paper-facing
  consistency result is claimed, and no assumption or conclusion is weakened.

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

The targeted build of the spectator module and `MIPStarRE.QPBT` succeeds.
Direct `lake env lean` checks of the spectator module and the QPBT root also
succeed. All six public theorem axiom closures are exactly
`[propext, Classical.choice, Quot.sound]`. Blueprint declaration
synchronization succeeds after regenerating its ignored declaration list.

The module's former module-wide `open Classical` produced a
`linter.style.openClassical` warning under the Lake target build. The review
finding at head `44e6526e` is addressed by replacing it with
declaration-scoped `open Classical in` on the two state factorizations, the
only declarations that needed classical decidability. No statement, proof
term, or definition was altered, and the linter is not suppressed. The
targeted build and the direct `lake env lean` check of the module report no
warning. Other imported proof debt is unchanged by this packet. Historical CI
evidence cited by the preceding PR description belongs to its recorded old
head, not to a later head. Checked publication, fresh exact-head full CI,
independent review, and merge remain separate workflow gates; this publication
worker runs no canonical CI or self-review.

## Review Repair

Review 5236205528, at head `c791c8f612de4cff46a9d4b4ed93f9577739a4d8`, found that
the packet redefined declarations already on `main`: the four-register state
`psiHatAlicePair` duplicated `ExtendedLineGame.pairState`
(`MIPStarRE/QPBT/Combining/ExtendedLineGame.lean`), and the shuffle
`aliceSpectatorShuffle` with the factorization
`psiHat_eq_alicePair_tensor_epr` duplicated `aaBaRegrouping` and
`reindexState_aaBaRegrouping_psiHat`
(`MIPStarRE/QPBT/Combining/ExtendedLineGame/StateTransport.lean`).

The repair deletes all four of this packet's own state and permutation
definitions and states the expectation identities over the existing `pairState`
and the existing `aaBaRegrouping` and `abBbRegrouping` equivalences. Because
`Observables` sits below `Combining`, the module moved to
`MIPStarRE/QPBT/Combining/ExtendedLineGame/SpectatorExpectation.lean`, one layer
below its new dependency `StateTransport`, and the root import in
`MIPStarRE/QPBT.lean` moved with it. The second partition now reads `AB''`,
`BB'` in the orientation `stateQForm_pairState_eq_AB''_BB'` already uses on
`main`, instead of the packet's own reversed `BB'`, `AB''` order over a
separately defined `bob`-first state; the private EPR-spectator helper
`inner_reindex_tensor_epr_one`, which has no counterpart on `main`, is kept
unchanged.

The surviving statements are strictly stronger than the transport already on
`main`: they are identities of the full complex expectation for arbitrary
operators, whereas `stateQForm_pairState_eq_AA'_BA''` and
`stateQForm_pairState_eq_AB''_BB'` require Hermitian operators and record only
the real quadratic form. No hypothesis was added, and no conclusion was
weakened, to obtain them.
