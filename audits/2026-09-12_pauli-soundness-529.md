---
title: "Pauli soundness: independent transfer estimates"
date: 2026-09-12
purpose: >
  Preserves the historical proof, failure, and cost record for the general
  range-projection and ancilla estimates; a dated continuation distinguishes
  current-main status from the original issue 529 attempt.
issue: "#529"
pr: "#536"
---

# Pauli soundness: independent transfer estimates

The original session record below describes its 2026-09-12 base, not the
current main branch. Its then-open global-pair and pulled-apart constructions
have since been completed. The dated continuation below records the status of
the preserved estimates on main; historical failures and costs are retained.

Session: `prover-529-20260912-01`, started 2026-09-12 at 05:08:36 UTC.
Base: `ae124f8f09ee002444ac5b9711822c0f1daae142`.
Issue: #529. The public `pauli_soundness` statement and its existing proof
hole are preserved. This packet does not prove that theorem.

## Source and obstruction

The statement is `thm:pauli` in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.
Its proof concludes at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1862-1876`.
The source adjoins local EPR states and applies the extraction unitaries.
Conjugation by the resulting isometries inserts their range projections;
the omitted argument is explained in `docs/paper-gaps/qpbt_extraction-transfer.tex`.

At the historical base commit, `Combining/Apply.lean:172` and
`Extraction/Unitary.lean:94` carried proof holes for the global-pair and
extraction constructions. The latter takes the former's output as data; it
does not construct a global witness from strategy success. The then-current
global-pair statement also assumed strictly positive error. Current main
proves the global-pair construction and pulled-apart consistency, including
the zero-error endpoint; extraction and final soundness remain separate.

The source's auxiliary classical game at dimension `2m+2` also requires a
domain comparison: admissibility gives `m | q`, whereas `2m+2 | q` fails
for admissible `m >= 2`. The directly indexed carrier avoids that divisibility
condition, but its comparison with the source route and the combined-lines
error are separate obligations. See `qpbt_ld-dimension-divisibility.tex` and
`qpbt_combined-lines-error-term.tex` in `docs/paper-gaps/`.
These observations do not constitute a counterexample to Pauli soundness.
This session does not reopen the historical mathematical-gap correction lanes.

## Proved estimates

`Test/Soundness/RangeProjection.lean` proves that, for a complete POVM
`N`, an orthogonal projection `Q`, and `Q theta = theta`,

```text
sum_a ||(N_a Q - T_a) Delta||^2
  <= 2 sum_a ||(N_a - T_a) Delta||^2 + 2 ||Delta - theta||^2.
```

No normalization of the vectors or property of `T` is required. The
sum-of-squares bound for complete POVMs controls the second term without a
factor depending on the number of answers. The module also proves the
isometry version and both local bipartite versions from the exact identity
`N_a phi = phi M_a`. This is an explicit hypothesis about arbitrary operators
in an auxiliary theorem, not an extra assumption on `pauli_soundness`.

`Test/Soundness/ErrorBounds.lean` proves
`sqrt (deltaQld a b epsilon m d q) <= deltaQld a (b / 2) epsilon m d q`
for admissible parameters, `a >= 1`, arbitrary real `b`, and `epsilon >= 0`.
This supplies the square-root adjustment in `rem:pauli-robustness-form`.

Neither module invokes `exists_globalPairWitness`, the conditional extraction
theorem, or `pauli_soundness`. The final theorem still needs the concrete
isometry constructions, their exact intertwining identities, the upstream
consistency estimates, and transport from a projective dilation of the
original strategy. The numerical factors from the transfer estimates must
also be absorbed into the universal prefactor.

## Provenance and prior cost

Searches covered all locally saved commits touching `Test/Soundness.lean`,
the histories of the test and extraction modules, and the open PR list read
through the primary checkout's `gh_common.py`. No completed proof of the
target was found. Relevant saved results include:

- PR #253, head `389fdcb65b777cd7065b8ea225d27350c1697dd9`: register transport,
  originally committed as `9b75a5f858141a2900d7c77921366184eeae80d3`.
- PR #383, head `ef1663383e174f05c83a50286fb614d8d957f8dc`: exact swap conjugation.
- `c4f3c9b6c1bf2414f79a729dde23abe58c716ab1`: extraction error absorption,
  already present in main as `deltaExtract_le_deltaQld`.
- `966b9b8cb996406f3977434cee3e113a20a27800`: transport of supplied soundness
  witnesses to qubits; this does not construct a soundness witness.

No divergent branch was copied. The new estimates reuse main's
`DistanceCalculus.sum_norm_mul_apply_le`, `measurement_sum_adjoint_mul_le_one`,
and the matrix-isometry and contraction API in `MagicSquareRigidity.GroundSlice`.

The primary `results/telemetry/sessions.jsonl` records these closely related
prior prover sessions:

| Session | Recorded wall seconds |
| --- | ---: |
| prover-241-20260906-01 | 954 |
| prover-241-20260906-02 | 711 |
| prover-245-20260906-01 | 1820 |
| prover-245-20260906-02 | 742 |
| prover-246-20260906-01 | 1473 |
| prover-246-20260906-02 | 320 |

Their subtotal is 6020 seconds, with 16,501,860 input tokens, 15,693,824 cached
input tokens, and 110,688 output tokens. These are overlapping prerequisite
costs, not a total for the entire soundness development. The related
`prover-121-native-20260907` row has no recorded duration or usage; those
values remain unknown and are not counted as zero. No matching prior #529
session or matching owner-session row was found. This session's dispatcher
record must be added to the subtotal; it does not reset earlier costs.

## Statement integrity

- Paper assumptions: universal constants `a >= 1`, `0 < b < 1`; admissible
  parameters; a strategy of success at least `1 - epsilon`.
- Lean assumptions: the same quantifier order, explicit `epsilon >= 0`,
  finite-dimensional strategy carriers, and the field model fixed by the
  admissible parameters. No projectivity or witness assumption was added.
- Paper conclusion: local isometries, a unit auxiliary state, the norm bound,
  and both Pauli measurement comparisons on the ideal state.
- Lean conclusion: the unchanged `PauliSoundnessWitness`, unsquared state
  norm, and the two finite sums of squared operator norms, all bounded by the
  unchanged `deltaQld` expression.
- Verdict: unchanged statement with the existing faithful finite-dimensional
  and nonnegative-error boundary conditions; the proof remains open.

The five new blueprint support statements display their own hypotheses and
conclusions. They do not certify `thm:pauli` or `lem:qld-unitary`.

## Validation and next gate

Focused Lean checks use the actual pinned toolchain, Lean 4.32.0. The
repository's AGENTS.md toolchain summary still says 4.31.0; no toolchain
configuration was changed. The transfer lemmas compile at the default
heartbeat limit, and their axiom closures are exactly `propext`,
`Classical.choice`, and `Quot.sound`. The target's closure still contains
`sorryAx`. Blueprint rendering and declaration synchronization are checked
separately; exact-head CI and its status are recorded on the PR.

At that time the next gate was independent review after exact-head CI.
Completion of #529 then required both the global-pair and extraction
constructions and their application to the unchanged theorem; the current
status is recorded in the preservation section below.

## Continuation on 2026-09-12

Session `prover-529-20260912-03` resumed the preserved commit
`3a269dd892be695123c19f7efd143cef0cce7979` in the same worktree. The primary
registry records predecessor `prover-529-20260912-01`, thread
`01a09404-79d8-78e2-b21a-1263d768ff97`, as failed after exhausted HTTP 503
retries, with 1903 wall seconds and unknown usage. The independent attempt
`prover-529-20260912-02` also failed, with 48 wall seconds and unknown usage.
Neither unknown usage is zero. Thus the recorded wall subtotal, including
the six prerequisite sessions above, is 7971 seconds before this continuation;
the known token subtotal above remains only a lower bound. The dispatcher
records this continuation separately; no cumulative counter is reset.

The local main and all saved histories of `Test/Soundness.lean` still contain
the target hole. Saved commit `4109e55aecca3e0b7f17e47fcf07d39624a31a9f`
adds EPR projection and normalization results, but retains
`exists_extractionWitness_ofGlobalPairWitness` as an obligation. Its remaining
steps are correlation estimates for the swapped state and the total-Pauli
measurement comparison. No new evidence discharges the global-pair
construction or the documented classical-game domain and error comparisons.
Those approaches were not restarted, and no divergent branch was copied.

`Test/Soundness/Ancilla.lean` now constructs the isometry
`J psi = psi tensor eta`, in the actual extraction register order `(AA')A''`,
and proves `(M tensor I tensor I) J = J M` for every original operator `M`.
It then constructs `phi = U J` from `U.adjoint * U = I` and proves the exact
identity `(U (M tensor I tensor I) U.adjoint) phi = phi M`. This discharges
the algebraic intertwining hypothesis of the preserved range-projection
estimates for these maps. The proofs use the existing coordinate tensor norm
and matrix-isometry API; no closeness, success, global-pair, or extraction
hypothesis is introduced. The new blueprint support entry explicitly states
the unit-ancilla and matrix-isometry conditions.

The public `pauli_soundness` declaration remains byte-for-byte unchanged from
the packet base. Its assumptions, quantifier order, fixed field model, error
functional, and all three conclusions therefore retain the statement-integrity
verdict above. This is an independently proved prerequisite, not a completed
proof of `thm:pauli`. Its new constructions and lemmas have only `propext`,
`Classical.choice`, and `Quot.sound` in their axiom closures; the target still
contains `sorryAx`.

PR #536 already preserves the earlier work. Its first CI run passed the Lean
build and mathematical audits but failed workflow tests within blueprint
synchronization because inherited `MIPSTARRE_HARDNESS_REASON` conflicted with
routine fixture classifications. The continuation clears model, classification,
and review overrides for publication and CI. Exact-head CI is recorded on the
updated PR. The next gate remains independent review, which this author session
does not launch. At that time full soundness still required both upstream
constructions, the zero-error endpoint, concrete state and measurement
transport, Naimark compression to the original strategy, and absorption of
transfer constants. The preservation section below updates this status.

## Preservation on current main (2026-09-17 UTC)

### Scope and source of truth

This addendum describes preservation on `4cebd0a2f22f421e22dd98739ab0e31ce1dbb4f3`,
not a new soundness proof. The source is `thm:pauli` in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`,
the unitary lemma and final isometry passage in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1666-1875`,
and the discrepancy in `docs/paper-gaps/qpbt_extraction-transfer.tex`.

### Findings and required action

The twelve unique declarations in `RangeProjection.lean` and `Ancilla.lean`
(ten public and two private) are independent finite-dimensional estimates and
constructions. Four transfer inequalities each retain the complete-POVM,
projection or isometry, intertwining, and arbitrary-state hypotheses displayed
in their five subordinate chapter-16 nodes. The ancilla constructors require
a unit vector and, for the unitary composition, `Uᴴ * U = 1`.
They do not assume strategy success, prove the source unitary lemma, or
construct a final Pauli soundness witness. The scalar `sqrt_deltaQld_le` is
already in `Combining/RootErrorBounds.lean` and belongs to the chapter-15
support node; neither declaration nor node is duplicated.

Unlike the 2026-09-12 base described above, current main proves
`exists_globalPairWitness` and `exists_pulled_apart_consistency`, including
the zero-error case. The supplied-witness extraction constructor remains
conditional. The source-domain and classical-error restrictions cited above,
the unconditional source extraction, and the concrete final transfer and
soundness proof remain open. Apply the independent estimates to actual swap
unitaries and complete the remaining source obligations without adding
hypotheses to `pauli_soundness`.

### Historical CI and cost

The original PR #536's earlier CI attempt failed in blueprint-sync workflow
fixtures because an inherited hardness-reason environment setting conflicted
with routine classification. The later recorded exact-head manifest for
`b37ebc1faac601a5c2a8405fc4bdbb7f0f1359e7` reports a build-step timeout
acquiring the machine-wide lock (30 seconds), while its blueprint render,
paper-gap, blueprint sync, length, proof-debt, and proof-evasion steps passed.
Neither attempt is current-main validation or independent review. The known
6020-second prerequisite subtotal, later 1903- and 48-second failed attempts
with unknown token usage, and continuation costs above remain cumulative,
not reset by this preservation. This addendum does not infer unknown usage.

### Statement integrity

Paper assumptions: admissible parameters and a successful arbitrary strategy;
the final proof adjoins EPR pairs and uses extraction unitaries. Lean assumptions
on the unchanged `pauli_soundness` theorem: the same success hypothesis,
nonnegative error and finite-dimensional fixed-field boundary conditions;
none of the auxiliary intertwining hypotheses is added to the source theorem.
Paper conclusion: two local isometries, an auxiliary state, and state and both
operator closeness assertions. Lean conclusion: the unchanged witness with
unsquared state norm and both summed squared operator distances at `deltaQld`.
Verdict: the source statement is preserved, with faithful boundary conditions;
its proof is unfinished. The five new nodes are explicitly formalization-only
support, not paper-labelled results, and include their own load-bearing
hypotheses and unchanged constants.

### Validation and review use

The original packet's checks above are historical. Fresh focused checks,
axiom results, and any remaining warnings for this preservation are recorded
in `/tmp/pr536-preservation-20260918-receipt.md`. Full CI, publication and
independent review are deferred to the owner; neither the original PR nor
issue #529 is disposed of by this author-only task. Reviewers should verify
the five support-node statements and standard-axiom closures separately from
the still-open theorem `pauli_soundness`.
