# Pauli soundness: independent transfer estimates

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

At the base commit, `Combining/Apply.lean:172` leaves
`exists_globalPairWitness` unproved, and `Extraction/Unitary.lean:94` leaves
`exists_extractionWitness_ofGlobalPairWitness` unproved. The latter assumes
the former's output; it is not a construction from the success hypothesis.
The current global-pair theorem also assumes strictly positive error, so a
soundness proof must address the endpoint allowed by `pauli_soundness`.

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

The next gate is independent review of these auxiliary estimates after
exact-head CI. Completion of #529 still requires source-faithful global-pair
and extraction constructions and their application to the unchanged theorem.

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
does not launch. Full soundness additionally requires both upstream constructions,
the zero-error endpoint, concrete state and measurement transport, Naimark
compression back to the original strategy, and absorption of transfer constants.
