---
title: "Issue 523: complete Pauli overlap estimates"
date: 2026-09-14
purpose: >
  Records the dimension-independent Pauli comparison and evaluated consistency
  proofs, their provenance, and the remaining concrete extraction composition.
issue: "#523"
pr: "#544"
---

# Issue 523: complete Pauli overlap estimates

## Scope

This continuation starts from clean commit
`69a0dc0b092c37076dc8ec45a95ddc23ba3608be`. MAIN identifies the original launch
as 08:12:57 UTC, with deadline 08:37:57 UTC. The first local clock check was
08:13:10 UTC. The 25-minute authorization includes validation, audit, and commit;
the timing reminder does not reset that budget. Only the existing issue523 worktree
is writable. No child, full build, CI, review, publication, or claim change
is part of this continuation.

The target `exists_extractionWitness_ofGlobalPairWitness` retains its exact
signature and original proof hole. The earlier state construction, large-error
witnesses, EPR proofs, and issue520 self-consistency are preserved. This audit
supersedes the Required Action in `2026-09-14_issue-523-continuation.md`.

## Source of Truth

The source is `lem:qld-unitary`, particularly lines 1785-1858 of
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`.
The blueprint is `blueprint/src/chapter/ch16_qpbt_extraction.tex`.
The numerical correction and the separate isometry-transfer obligation are
documented in `docs/paper-gaps/qpbt_extraction-transfer.tex`.

## Findings

Every selected sum of effects of a complete measurement is a positive
contraction. Applied to the product measurement, this bounds the entire overlap
operator, without an outcome-cardinality factor. Its expectation changes by at
most twice the norm distance between unit vectors.
`pauli_overlap_transfer` combines this fact with Schwartz--Zippel: the evaluated
overlap on a unit theta is at most the full diagonal overlap on a unit Delta
plus `md/q + 2 * norm(theta - Delta)`.

For a local POVM A with Pauli-register outcomes and normalized
Delta = aux tensor EPR, let E(theta) denote A's evaluated overlap with the
canonical Pauli measurement on the opposite register. The theorem
`pauli_distance_on_ideal_le` bounds the full answer-summed distance between A
and the canonical projectors on its own register by
`2 * (1 - E(theta)) + 2md/q + 4 * norm(theta - Delta)`.
The exact EPR transport is `extracted_epr_actions_eq`. The two auxiliary spaces
are arbitrary and heterogeneous, so the estimate applies to either player by
interchanging them. It is not yet instantiated with the concrete swap expressions.

`evaluated_pauli_tilde_consistency_ofGlobalPairWitness` proves both evaluated
total-Pauli/pulled-apart consistency estimates on `S.psiHat`, at one universal
construction scale. It combines the recovered full point estimates with point
self-consistency and both orientations of the actual game's Pauli-basis check.
It does not invoke any of the five original `Consistency.lean` holes.

`extraction_small_error_absorption` proves that if `0 <= delta <= 1` and
`C >= 18`, both `16 * delta` and `2 * delta + 2md/q + 16 * sqrt(delta)`
are at most `deltaExtract C delta m d q`. This is the scalar estimate needed
after the concrete operator comparison and the previously proved state bound.

## Required Action

Let Q be a total-Pauli measurement extended to its full extraction block and
conjugated by that block's swap; let T be the canonical measurement on the
opposite extracted register. Prove that the evaluated Q/T overlap on the
reindexed swapped state is one minus the corresponding evaluated-Pauli/tildeM
consistency defect on `S.psiHat`. Use `swapUnitary_conj_tildeM`, the exact
encoding/evaluation identity, simultaneous unitary invariance, and the register
placements, for both orientations.

Then instantiate `pauli_distance_on_ideal_le` with Q and the normalized aux
from `exists_extraction_aux_ofGlobalPairWitness`. Rewrite the resulting norm
sum to the exact `ExtractionWitness.pauli_close` field on `S.idealExpState aux`.
Choose C at least the state-construction constant, the evaluated-consistency
constant, and eighteen, before introducing parameters or strategies. Monotonicity
in the construction coefficient gives a common delta. Use the proved scalar
absorption when delta is at most one and the existing complete large-error
constructor otherwise. The target's original `sorry` remains until this
composition is checked.

No counterexample or new mathematical obstruction was found. This is an
uncompleted formal composition, not a hypothesis to add to the target.
The source global-witness construction and downstream isometry transfer remain
separate obligations, and the source route remains not ready.

## Provenance

PR533 object `d2e021ebba69a3c914b52f6b6f7c3165cb56b120` supplies the additional
proofs in `PointConsistency.lean`, `SupportMass.lean`, `TensorConsistency.lean`,
`PairStateConsistencyTransport.lean`, and `NonencodingSupport.lean`.
PR539 object `27f4c8110d0ff41fe834a8bb5b12bab72de44a33` supplies the additional
proofs in `PointConsistencyPrime.lean`. Existing placement proofs are retained.
The four final supplied-point declarations are recovered into
`SuppliedPointConsistency.lean`, preserving their names while importing the
existing `Consistency` module. No source-construction module, divergent public
statement, unrelated branch change, or replacement proof hole is recovered.

## Statement Integrity

Paper assumptions: the projective setting and the global measurement obtained
earlier in the source. Paper conclusion: swap unitaries, a normalized auxiliary
state, state closeness, and both full total-Pauli comparisons.

Lean target assumptions and conclusion: unchanged, including the explicit
supplied global witness, the parameter domain, the quantifier order, and the
nested error scale. Verdict: the existing extra global-witness assumption is
conditional; the full target is still open. No bridge assumption is added.

The general comparison lemma permits any POVM, unit theta, unit auxiliary
state, heterogeneous local spaces, and either Pauli basis. It preserves the
full answer sum and displays the evaluated-overlap deficit and both losses.
Verdict: a proved intermediate estimate with weaker projectivity requirements,
not a completion of the paper theorem. The evaluated-consistency theorem retains
the supplied-witness conditionality and the exact admissible parameter domain.
Blueprint support nodes display these hypotheses and do not mark the source
extraction or global-witness route complete.

## Validation

Focused Lean compilation passed for each recovered and new module; the unchanged
target retains its original proof-hole warning. Twelve fresh axiom queries for
the recovered point estimates, evaluated consistency, contraction and
overlap transfer, full Pauli distance estimate, and scalar absorption
all report only `propext`, `Classical.choice`, and `Quot.sound`.
The target was queried separately and still includes `sorryAx`.
Blueprint web rendering, declaration synchronization, and whitespace checks
passed. The declaration checker resolved all 1,453 blueprint declarations.
Synchronization retains the thirteen existing statement/proof-mark
warnings. The hook installation check and the proof commit's normal hooks passed.
No independent review is claimed; the review-drain hold leaves the independent
gates to MAIN.

The proof commit is `9042eabbb01d680e76682b9c1464f0b44cc155e9`.
This final audit update records the exact launch/deadline reminder and completed
hook evidence, without adding proof work or extending the authorized duration.

## Cost Preservation

The prior native thread `01a09edb-6c0b-7d03-8b93-c0999048791e` ran
07:39:35.369Z-08:08:04.259Z, a total span of 1,708.89 seconds including
its 63-second audit-format finalization. This is the preceding work already
recorded in the state-extraction audit, not an additional amount to count twice.
That audit also preserves historical lower bounds of 7,395 wall seconds,
24,256,025 input tokens (23,113,344 cached), and 139,412 output tokens, plus
unknown historical usage. Native token snapshots are cumulative and are not
additive. This continuation adds elapsed work; MAIN records native telemetry
after terminal completion. No uncertain overlapping costs are summed here.

## Review Use

Check the concrete equality identified under Required Action before treating
the target as discharged. The new estimates resolve the complete-overlap
contraction, collision, EPR comparison, evaluated-consistency, and scalar
steps; they do not yet assemble the six-register witness. Preserve the frozen
proof provenance and cumulative costs when continuing the composition.
