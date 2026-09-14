---
title: "Issue 523: supplied-witness state extraction checkpoint"
date: 2026-09-14
purpose: >
  Records the verified state-extraction and large-error witness constructions,
  their provenance and costs, and the remaining conditional extraction obligation.
issue: "#523"
pr: "#544"
---

# Issue 523: supplied-witness state extraction checkpoint

## Scope

This audit covers `exists_extractionWitness_ofGlobalPairWitness` in
`MIPStarRE/QPBT/Extraction/Unitary.lean` and the supporting constructions
identified below.

Admission: 2026-09-14 07:39:35 UTC; original deadline: 08:04:35 UTC.
The existing worktree was clean at `94a6845ab01a821329d1c9afe1388b9391cdeb6b`.
The primary owner-session ledger, all `opus-*` rows in the live
`watchdog/meta-dispatched.txt` claim ledger, and live processes were checked.
No competing claim on issue 523 or PR 544 was found. Input branches were read
through immutable Git objects. Primary setup ran with `--no-build` and retained
the populated build directory. No other worker's checkout was modified.

## Source of Truth

The source is `lem:qld-unitary`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1666-1860`.
The new state proof addresses lines 1715-1783 using the numerical correction
in `docs/paper-gaps/qpbt_extraction-transfer.tex`.

## Findings

The original `exists_extractionWitness_ofGlobalPairWitness` signature and
proof hole remain unchanged. No new axiom or proof hole is introduced.

`exists_extraction_aux_ofGlobalPairWitness` constructs a normalized auxiliary
vector for the actual swapped state with squared error at most
`16 * deltaConstructPaulis C epsilon deltaG P.m P.d P.q`. The universal C
precedes parameters and strategies. Observable disagreement is transported
through both swaps and into auxiliary/EPR coordinates. A nonzero basis element
permutes the uniform Pauli labels. Jensen's inequality bounds each averaged
displacement; the preserved EPR product identity and contraction estimates
bound projection error. The preserved normalization theorem covers zero
projection without a nonvanishing assumption.

`exists_extractionWitness_ofGlobalPairWitness_of_four_le` constructs every
field of the actual witness at allowed error at least four. Its auxiliary
vector is the original strategy state tensored with EPR on the auxiliary
registers. Both states have norm one. Both measurement families have summed
adjoint-square equal to the identity, bounding the complete answer-summed
distance by four for both players and bases. No dimension factor occurs.
The `_of_one_le_construct` specialization gives the same full witness at the
target's nested scale when C is at least four and construction error at least one.

## Required Action

The remaining construction is the small-error total-Pauli comparison on the
normalized ideal state, paper lines 1785-1858. Combine supplied-witness point
consistency with the game's evaluated Pauli/point consistency, conjugate the
measurements, remove unequal encoding outcomes by Schwartz--Zippel, and
transfer the complete overlap operator between the swapped and ideal states.
Then absorb both estimates into one universal constant at the unchanged nested
error scale. Small-error state-error absorption is also not performed here.
The source global witness and downstream isometry transfer remain separate.

## Provenance

- PR294 `0f8f393891dfbf34eff79e4884c21ebd8863f129`: exact `Observables.lean`
  and required `Quantum/ControlledUnitary.lean`. Both swap holes are discharged
  at unchanged statements; their fresh closures contain only standard axioms.
- Issue520 `df21901ec428ac22ebebb56466ab568fc383c554`: character, pulling,
  collision, and placement support. Its `Consistency.lean` is recovered as
  `ObservableConsistency.lean`. That module and `PullingDefect` import the
  existing `Consistency` instead of the frozen `MeasurementConsistency` split.
  The exact constant remains `48 + 32 * card(PauliEdge)`.
- The same issue520 object supplies the small public tensor-measurement API
  addition in `Games/DistanceTheorems.lean`; all existing proofs are preserved.
- PR539 immutable `27f4c8110d0ff41fe834a8bb5b12bab72de44a33`, published
  `ca866da402947c9ee7e1dd5e935a2782fe0d1602`, and PR533 immutable
  `d2e021ebba69a3c914b52f6b6f7c3165cb56b120` were inspected. Their full point
  estimates are available for the remaining comparison. Only placement and
  convolution support preserved by issue520 is needed here; neither full point
  estimate is copied or reproved. The five original `Consistency.lean` holes
  remain intact. No whole divergent branch was imported.
- All previous issue523/PR544 EPR prerequisites, commits, audits, and costs
  are preserved without resetting or replacing their history.

## Statement integrity

Paper assumptions: admissible projective setting and global measurement
obtained earlier in the source. Conclusion: swap unitaries, normalized
auxiliary state, state closeness, and both total-Pauli comparisons.

Lean target assumptions: unchanged supplied `GlobalPairWitness`,
nonnegative errors, and epsilon at most one. Lean target conclusion:
unchanged witness, quantifier order, placements, and nested error scale.
Verdict: the existing extra global-witness premise remains conditional;
the full target is still open. No bridge or producer premise is added.

Actually proved fields: both unitarity fields for every supplied witness;
auxiliary data, normalization, and state closeness at the linear error bound;
every field including `pauli_close` in the allowed-error-at-least-four case.
The general small-error witness is not constructed. Blueprint entries display
these restrictions. The source joint consistency entry no longer marks its
conditional unfinished declarations as matched; the source joint construction
and unrestricted extraction remain visibly open.

## Validation

Focused Lean checks passed for all recovered/new modules and `Unitary.lean`,
which retains only its original proof-hole warning. Fresh axiom queries for
both swap identities, recovered self-consistency, swapped self-consistency,
projection, auxiliary-state construction, and both restricted constructors
report exactly `propext`, `Classical.choice`, `Quot.sound`. The original target
still additionally reports `sorryAx`. No new checked proof uses another hole.

Blueprint web rendering, declaration synchronization, LaTeX conventions,
whitespace, and focused line checks passed. Synchronization retains 13 existing
statement/proof-mark warnings. Every changed Lean module is below 1000 lines.
No full build, CI, review, publication, worker, or child session was launched.

## Cost Preservation

The preceding audit `2026-09-12_issue-523_epr-projection.md` preserves the known
historical prerequisite/scouting lower bound: 7,395 wall seconds, 24,256,025
input tokens (23,113,344 cached), and 139,412 output tokens, plus explicitly
unknown historical usage. Earlier issue523 sessions and this continuation are
additional costs, not a reset. MAIN records the native rollout on completion;
this checkpoint does not invent missing runtime usage measurements.

The owner authorized a separate documentation-only finalization of at most
three elapsed minutes after the completed proof run. Its first clock check
was 2026-09-14 08:06:43 UTC, at clean head
`7969c00f7c9f17c456e4c32c76c6fca98a14357f`. This additional time and usage must
be included in cumulative telemetry, without resetting the original proof-run
costs. MAIN records the complete native session once after the final terminal
receipt. This correction changes only this audit's metadata and organization;
it adds no proof work or Lean or blueprint edits.

## Review Use

Use this checkpoint to distinguish the verified auxiliary-state construction
and restricted complete witnesses from the still-open full extraction theorem.
Check the frozen-input provenance and stated axiom closures when integrating
the proof content. Resolve the Required Action before treating the conditional
extraction constructor as complete, and preserve the separate source-witness
construction obligation and all cumulative costs.
