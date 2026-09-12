# Issue 512: Recovery of the established extended-line construction

The proof of `exists_extendedLinesWitness_established` was recovered from
commit `6e8d67ef8ba22de69a0c166adcdf23ba6e7a33aa`, retained at
`0f4ef05370350f4017439ebd839ef0561f13130f`, onto the isolated issue-512
worktree based at `ae124f8f09ee002444ac5b9711822c0f1daae142`.
The preceding receipt is `prover-512-20260912-01.last.md` in the local
session archive. This is recovery of that proof, not a new mathematical attempt.

## Construction and Provenance

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
  The existing numerical lemmas in `Claims` are exported for reuse.
- The saved established-error construction is inlined into the target.
  Its universal outer constant remains `1`. No narrower helper replaces the
  current `exists_extendedLinesWitness_established_ofPointsWitness`: that
  obligation quantifies arbitrary scalar point errors, whereas the saved
  helper first fixes a polynomially controlled point family. Its signature
  and proof hole are left unchanged.

The source is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`,
`lem:qld-xz-lines` (882-961), `lem:qld-4-10` (689-709), and
`lem:qld-4-13` with its first proof route (1020-1034, 1118-1246).
The auxiliary blueprint entry is `lem:qld-4-13-established`.

## Statement Integrity

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

## Verification and Accounting

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
