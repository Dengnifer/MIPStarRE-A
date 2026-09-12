# Joint law for the second extended-line argument, issue #510

`exists_extendedLinesWitness` remains unproved, with the same signature and
proof body as pinned main `d647a4818ef43092aa66404834b99f2cb292ede8`.
This independent attempt proves the joint distribution comparison needed by
the second argument, for the concrete directly indexed sub-line sampler.
It does not retry the impossible first-route scalar absorption.

## Mathematical result

The source is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`:
the target is `lem:qld-4-13` at lines 1020-1034; the sub-line construction
is at lines 1071-1116; the second argument is at lines 1241-1245. The source
invokes a joint product decomposition not supplied by the separate marginal
properties in its sub-line statement.

For the concrete law `subLineDist`, choose a kind and an extended coordinate
uniformly. The source index of a block is that coordinate within the block,
when applicable, and the first coordinate otherwise. At each fixed kind
and coordinate, the two projected line-point pairs have independent
restricted line-point laws. Averaging these identities proves
`subLineDist_map_joint`. The assertion includes vanishing direction blocks
and singleton lines; it introduces no nondegeneracy assumption.

The general nonnegative-average consequence is
`avgOver_subLineJointProjection_le`, with factor `4m^2`. Applied to the
completed consistency integrand it proves
`subLineDist_consistencyDefect_le_ofLinesWitness`: if a joint line witness
of error `deltaP` is supplied, its defect under the actual joint sub-line
law is at most `4m^2 deltaP`, for every directed opposite placement.
This conditional consequence is recorded separately in the blueprint with
its premise explicit. No field is added to `SubLineWitness` or to a paper
theorem, and no `GlobalPairWitness` is assumed.

## Reuse and provenance

The fixed-coordinate identity `subLineBranchRaw_map_joint` is already on
main in `Combining/Lines/SubLineSource.lean`, recovered in commit
`f4f9c9e7ccc6a010248d82c6b32f49719f00d2c4`. Its exact statement retains
both point blocks jointly, not just either marginal. Its axiom closure
contains only `propext`, `Classical.choice`, and `Quot.sound`. The new proof
reuses it, `subLinePointDist_bind`, and the existing restricted-average API.

The saved-history search used `git log --all` on `Combining/Apply.lean`
and on joint sub-line declarations. It found the previously preserved
existential assembly and established-error constructions, including
`6e8d67ef8ba22de69a0c166adcdf23ba6e7a33aa`. They do not discharge the
unchanged printed-error target; their divergent helper signatures and
existing proof dependencies were not imported. The fixed-coordinate joint
identity was reused rather than reproved. No saved complete mixture
identity was found.

The first attempt's immutable checkpoint is commit
`e31df23c592e0db8c55376cdbfe616c30597f2a1`, PR #530, and
`audits/2026-09-12_issue510-extended-lines-error-obstruction.md` there.
Its final receipt is `prover-510-20260912-01.last.md`. Its theorem about
quarter-power absorption was neither copied nor reproved. This branch is
independent of that PR and does not edit the first attempt's worktree.

## Statement integrity

- Paper assumptions: the surrounding admissible parameters and passing
  projective strategy; point measurements constructed by `lem:qld-4-10`.
- Lean target assumptions: unchanged `AdmissibleParams`, real error, and
  `ProjectiveSetting`, with the point witness supplied existentially.
- Paper conclusion: line POVMs with total degree `md+1`, axis degree `d`,
  and both field-answer consistency relations at `poly(m^2 epsilon, md/q)`.
- Lean conclusion: unchanged `ExtendedLinesWitness`, using the pre-existing
  direct carrier and law, completed `Option` answers, and corrected sum-form
  polynomial error contract.
- Verdict: no target statement change. The new joint law is unconditional
  on strategies but restricted to the specified direct sampler; its
  consistency consequence explicitly assumes a line witness. Neither is
  advertised as a completed proof of `lem:qld-4-13` or of the source's
  seed-indexed sub-line theorem. Existing scope markers remain.

## Validation and remaining prerequisites

Focused Lean checks pass for `Lines/SubLineJoint.lean` without warnings and
for `Apply.lean` with its five existing proof-hole warnings. The new file has
no proof holes, axiom declarations, or proof-integrity bypasses. The hook
installation check, whitespace check, blueprint synchronization after
regenerating the ignored `lean_decls`, and `leanblueprint web` pass.

Freshly compiled-module axiom checks give the standard three axioms for
the new joint identity, average bound, and conditional consistency theorem.
`exists_combinedPointsWitness` also has that closure.
`combined_line_measurement_consistency` and `exists_extendedLinesWitness`
still contain `sorryAx`. The supplied witness is not a proof of its
construction.

The complete blueprint axiom audit also passes, with no proof-level
`leanok` declaration depending on `sorryAx`. A pre-commit check rejected the
conditional helper's link in a theorem-like blueprint entry. Its conditional
name is preserved, and its statement and argument are instead recorded in
an unlinked remark, as required by the existing gates. The unconditional
joint-mixture lemma retains its proof-complete links.

The initial shared-helper full-build attempt waited 120 seconds for the
machine-wide lock and timed out before compilation. Exact-head CI after
publication is the next build gate; its result belongs to the published
commit statuses and final session receipt. No reviewer is launched here.

The mathematical next step remains a consistency estimate at the printed
error scale for constructed witnesses. The now-proved direct comparison
only gives `4m^2 deltaP`; a generic `deltaP = poly(epsilon, md/q)` cannot
absorb that dimension factor into the requested two arguments. Source-game
transport and completed-answer conversion also remain distinct obligations.
This is an obstruction to that derivation, not a counterexample to the target.

## Separate attempt accounting

Session `prover-510-20260912-02` started at `2026-09-12T05:41:19Z`.
This checkpoint was written after `2026-09-12T06:02:37Z`, at least
1,278 additional seconds into this independent attempt. Its authorized
60-minute window ends at `06:41:19Z`; no descendants were launched.

The earlier audit records a nonoverlapping historical lower bound of
27,325 seconds: the 816-second saved-assembly session, the exhausted
ten-attempt B8 episode of 19,931 seconds, and the later 6,578 seconds in
`mathfix-118-20260906-11`, `-12`, and `-13`. These episodes are not reset.
The terminal dispatcher row for attempt 1 records **1,551 seconds**, giving
28,876 seconds before this attempt. This supersedes its receipt's
approximate 28,830-second cumulative figure. At this checkpoint the combined
recorded lower bound is 30,154 seconds, excluding later work in this session
and other historical combining work.

Attempt 1's terminal usage is 10,606,280 input tokens, 10,395,648 cached input
tokens, 33,622 output tokens, and 16,552 reasoning tokens, recorded separately
in `results/telemetry/sessions.jsonl`. Cached input and reasoning are not
additional quantities to sum into input and output. The dispatcher will
record this attempt's final usage and duration under its own session name;
resumed cumulative counters from historical threads must not be summed.
