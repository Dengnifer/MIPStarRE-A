---
title: "Issue 512: recovery of the established extended-line construction"
date: 2026-09-12
purpose: >
  Records the recovery of the proof of `exists_extendedLinesWitness_established`
  from a saved commit, its statement-integrity comparison with the source
  lemma, the per-module provenance of the recovered declarations, and the
  verification and cost accounting a reviewer needs to check that the recovery
  introduced no new mathematical content.
status: active
track: qpbt
kind: proof-recovery-audit
origin: "issue #512"
issue: "#512"
pr: "#549"
---

# Issue 512: Recovery of the established extended-line construction

The proof of `exists_extendedLinesWitness_established` was recovered from
commit `6e8d67ef8ba22de69a0c166adcdf23ba6e7a33aa`, retained at
`0f4ef05370350f4017439ebd839ef0561f13130f`, onto the isolated issue-512
worktree based at `ae124f8f09ee002444ac5b9711822c0f1daae142`.
The preceding receipt is `prover-512-20260912-01.last.md` in the local
session archive. This is recovery of that proof, not a new mathematical attempt.

This audit is the reader-facing record of that provenance. The Lean module and
theorem docstrings carry only mathematical source and gap references; the
commit-level recovery history of each module is kept here instead.

## Scope

The recovered declarations and the modules holding them:

- `MIPStarRE/QPBT/Combining/Lines/{Sampling,PointComparison,Conditioning,
  Construction}.lean`
- `MIPStarRE/QPBT/Combining/{XEvalDeficit,SubLineXDeficit}.lean`
- `MIPStarRE/QPBT/Combining/ExtendedLines/{Measurement,Overlap,Estimates}.lean`
- the target `exists_extendedLinesWitness_established` in
  `MIPStarRE/QPBT/Combining/Apply.lean`

Each of these modules was recovered from the saved commit named above. The
blueprint counterpart is the formalization-support node
`lem:qld-4-13-established` in `blueprint/src/chapter/ch15_qpbt_combining.tex`;
the paired-line consistency theorem it rests on is recorded in
`lem:combined-line-measurement-consistency` and the supporting nodes beside it.

## Source of Truth

The source is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`,
`lem:qld-xz-lines` (882-961), `lem:qld-4-10` (689-709), and
`lem:qld-4-13` with its first proof route (1020-1034, 1118-1246).
The auxiliary blueprint entry is `lem:qld-4-13-established`. The divergences
between that entry and the printed lemma are governed by
`docs/paper-gaps/qpbt_combined-lines-error-term.tex` and
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.

## Findings

### Construction and provenance

Only declarations needed by the construction were recovered. Existing proofs
of the combined point witness, subline law, Z deficits, polynomial absorption,
projection contraction, and heterogeneous pasting were reused. No file from
another worktree was changed, and the saved branch was neither merged nor copied
wholesale. The recovered material is divided into modules below 1000 lines.

- `Lines/Sampling`, `PointComparison`, `Conditioning`, and `Construction`
  recover the needed declarations from saved `Combining/Lines.lean`. The
  X-Z-X measurement is unchanged. Conditioning is on nonzero X directions;
  its mass is at least one half, and the discarded contribution is restored
  with the bound `1/(2q)` under the original product law.
- The current `combined_line_measurement_consistency` statement is unchanged
  and moved to `Lines/Construction`. The existing witness constructors now
  use its proved value. The current heterogeneous pasting theorem needs only
  the two forward marginal comparisons, so the saved unused second joint
  family and its extra comparison were omitted. Its error function still
  satisfies the same polynomial contract.
- `XEvalDeficit` and `SubLineXDeficit` recover only the opposite-placement
  X estimates needed from saved `EvalDeficit` and `SubLineDeficit`. The saved
  XZ ordered-point estimate is added alongside the existing ZX estimate.
- `ExtendedLines/Measurement`, `Overlap`, and `Estimates` recover the
  conditional law, affine polynomial construction, degree support, and
  two-placement real-part overlap estimates from saved `Apply.lean`.
- The two scalar estimates `rpow_quarter_nonneg` and `sqrt_deficit_bound_le`,
  which the recovered estimates share with the claims module, are stated in
  `Combining/ErrorBounds.lean` with the other formalization-only scalar
  bounds; neither is specific to Claims 17-1 through 17-3.
- The saved established-error construction is inlined into the target.
  Its universal outer constant remains `1`. No narrower helper replaces the
  current `exists_extendedLinesWitness_established_ofPointsWitness`: that
  obligation quantifies arbitrary scalar point errors, whereas the saved
  helper first fixes a polynomially controlled point family. Its signature
  and proof hole are left unchanged.

### Statement integrity

Paper assumptions: an admissible parameter tuple and a projective strategy
passing the Pauli basis test with error epsilon; the preceding construction
supplies the joint point measurements.

Lean assumptions: the existing `AdmissibleParams` and `ProjectiveSetting`
domain. The point witness and its polynomial error are constructed
existentially. No new bridge premise, positivity premise, axiom, or proof
hole is added.

Paper conclusion: two extended-line consistency comparisons, axis degree at
most d, general degree at most md+1, source line-point sampling, field answers,
and the printed error `poly(m^2 * epsilon, md/q)`.

Lean conclusion: the unchanged directly indexed `ExtendedLinesWitness`, both
opposite-placement comparisons on completed answers, the same degree bounds,
and `C * m * poly(epsilon, md/q)` in the corrected additive error convention.

Verdict: exact recovery of the current auxiliary statement. It is not a
formalization of the printed source theorem: the carrier/law transport,
completed-answer comparison, and printed-error issues remain recorded in
`qpbt_ld-dimension-divisibility.tex` and `qpbt_combined-lines-error-term.tex`.
The complex Claim 17-2 obligation is also unchanged; the recovered proof uses
separate real-part estimates with their stated line and point errors.

The declaration header is byte-for-byte equal at the base, saved commit,
and recovered state. Its SHA-256, excluding ` := by`, is
`fd0305b7aa316707f14f917a4974499ece4c6223a67eec4d3f05fd1445c5a02a`.
The witness, parameter, carrier, law, and error definitions were not changed.

## Required Action

No follow-up is required for the recovery itself. The obligations it leaves
open are the pre-existing ones, and they are tracked outside this audit:

- transport of the question carrier and line-point law, in
  `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`;
- conversion of the completed answer comparison to the source summation over
  `a` in `F_q`, including zero-direction singleton lines, in
  `docs/paper-gaps/qpbt_combined-lines-error-term.tex`;
- the printed error form `poly(m^2 * epsilon, md/q)`, whose declaration
  `exists_extendedLinesWitness` remains unproved;
- the unchanged proof hole of
  `exists_extendedLinesWitness_established_ofPointsWitness` and the complex
  Claim 17-2 obligation.

A reader checking this audit should confirm that the source-labelled entries
`lem:qld-xz-lines` and `lem:qld-4-13` still carry no formalization mark, and
that the marks introduced by the recovery sit only on support nodes whose
statements display their restrictions.

## Validation

Focused Lean checks passed for the recovered modules and the target under
the worktree's actual Lean v4.32.0 toolchain. A recursive audit traversed
75,666 type/body dependencies of the target, including 3,310 project
declarations, checking each axiom closure against the allowed set
`propext`, `Classical.choice`, `Quot.sound`. The target and the recovered
line-consistency theorem have exactly that closure, without `sorryAx`.
The audit program and full output are in the session archive as
`issue512-recovered-audit.lean` and `issue512-recovered-audit.log`.
The required locked build and exact-head CI results are recorded by the
primary `local/bin` workflow and in the session's final receipt.

Historical cost remains thirteen attempts and 26,383 recorded seconds.
The preceding verification added approximately 805 seconds, giving
approximately 27,188 seconds before this recovery session. Session
`prover-512-20260912-02` adds its actual recovery and validation cost to
that history; its final elapsed time belongs to the dispatcher receipt.
This recovery does not reset B8 or the historical mathematical-gap budget.
Independent review remains the next session's responsibility.

## Correction after reconciliation with main (2026-09-15)

This note supersedes only the statements above that every recovered module was
needed by the final construction and that `Lines/Sampling.lean` remained part
of its module decomposition. After the recovery branch was reconciled with
main, no module imported `MIPStarRE.QPBT.Combining.Lines.Sampling`, and none of
its declarations was used by the target or its dependency graph.

The three zero-direction declarations in that file had the same public
statements and proofs as the canonical declarations in
`MIPStarRE/QPBT/Combining/Lines/DiscardedMass.lean`:
`dLinePointDist_zero_direction_mass_le`,
`linePointDist_zero_direction_mass_le`, and
`prod_linePointDist_zero_X_direction_mass_le`. The theorem
`avgOver_lineRepMap_resample_parameter` was the same representative-parameter
average, up to bound-variable names, as the canonical theorem
`avgOver_uniform_lineRepMap_resample_parameter` in
`MIPStarRE/QPBT/Combining/Lines/SubLineUniform.lean`.

The remaining theorem, `linePointDist_nondegenerate_mass_ge`, was distinct but
unreferenced. It was not exposed by an imported module, and the active
conditioning argument instead uses `nondegenerateLinePastingMass_bounds` and
`prod_linePointDist_nondegenerate_mass_pos` from the canonical retained-mass
modules. Consequently `Lines/Sampling.lean` was retired in the operator
correction for PR #549. The construction continues to obtain the discarded
mass bound through `Lines/Conditioning.lean`, which imports
`Lines/DiscardedMass.lean`; no theorem used by
`exists_extendedLinesWitness_established` was removed or replaced.
