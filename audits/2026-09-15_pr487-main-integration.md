# PR 487: integration of published main

## Scope and history

This bounded integration repair starts from
`86b1474a337a0a72774a2445f96fdcba3e169cd1` and merges only published main
`bf864c016b3426a690c02f93bea9d40986604195`. The assignment was verified against
SHA-256 `79f6cd784d7618f33d6f0ad93d2b3ffa4a712a2851cb2eebe12cee66dbefaf4c`.
Work began at 2026-09-15T11:07:15Z, with an absolute deadline of 11:51:00Z.
No earlier commit, review, attempt, or accumulated cost is replaced.

The assigned worktree path is a pre-existing symlink to
`/tmp/qpbt-point-self-consistency-completed-20260909`. All edits and generated
validation products remain in that worktree. The primary checkout is read only.

## Mathematical integration

The textual conflict in `Combining/Lines.lean` was resolved by retaining both
import sets, including `PointSelfConsistencyCompleted`, `Construction`, and
`PairStateConsistencyTransport`.

Main's `Lines/PointComparison.lean` and `Lines/Conditioning.lean` independently
declared fourteen results already present in the branch's smaller modules.
Their statements agree. The incoming modules now import those declarations
instead of declaring them again. The two additional completion identities in
`PointComparison` and the two additional discarded-mass results in `Conditioning`
remain unchanged. Every public name remains available through both import routes.
There are no duplicate public declarations in the combining subtree.

The fourteen printed Lean signatures were compared in separate published-main
and merged environments and agree byte for byte. The six declarations in
`PointSelfConsistencyCompleted.lean` are byte-identical to the starting commit.
The earlier placement-API repair in `ExtendedLineGame/PointPointRejection.lean`
is also retained; the removed private implementations are not reintroduced.

## Statement integrity

The primary source is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`:
`eq:qld-q-self-cons` at lines 693-697 and the application of `lem:qld-xz-lines`
at lines 936-963.

- Paper assumptions: the supplied joint projective point measurements satisfy
  self-consistency on uniformly sampled point pairs; the line comparisons use
  the line-point laws and the symmetric opposite-register placements.
- Lean assumptions: the existing admissible parameters, projective setting,
  supplied `CombinedPointsWitness`, and directed opposite-placement relation
  are unchanged. Completeness and projectivity are derived where required.
  No bridge input, positivity premise, or error hypothesis has been added.
- Paper conclusion: joint point self-consistency and the two point-to-line
  comparisons supply the pasting hypotheses for the X-Z-X measurement.
- Lean conclusions: completion preserves the defect, independent line-point
  sampling retains the bound, and conditioning gives the displayed bound
  divided by the positive retained mass. Both answer orders remain available;
  the pasting-compatible order is `(Z,X)`. All fourteen consolidated signatures
  and all six reviewed signatures are unchanged.
- Verdict: exact preservation of the public Lean statements. The completed and
  conditioned estimates remain explicitly identified as formalization-only
  consequences, not substituted for the paper's unconditioned statements.

Main's `exists_globalPairWitness` retains its unrestricted strategy-error
quantifier, including zero error, and has no additional witness premise.
`Combining/Apply.lean` and the extraction construction, consistency, and
observable files are byte-identical to the incoming snapshot. All unfinished
source markers, including the blueprint's `lem:qld-xz-lines` marker, are retained.
The three completed-point blueprint nodes and their five declaration links
each occur once and retain their separate auxiliary status.

## Verification

- The targeted `Lines` module build passed. The targeted `Combining.Apply`,
  `Extraction.Construction`, and `Extraction.Observables` builds also passed.
  No full project build or CI lane was run.
- All six reviewed declarations, `combined_line_measurement_consistency`, and
  `exists_globalPairWitness` depend only on `propext`, `Classical.choice`, and
  `Quot.sound`.
- No proof hole or kernel bypass occurs in the three manually edited Lean
  files or in `PointSelfConsistencyCompleted.lean`.
- The blueprint web build and final synchronization check passed. The ignored
  declaration index was regenerated with the normal hook command. Initial
  synchronization failures concerned that generated index, not tracked statements.
- The pending-index merge-loss guard passed against both best merge bases.
- Multiset comparisons of the historical event, session, owner-session,
  estimate, build, and stage records found no missing lines from either parent.
- `lake env lean` passed for all 87 Lean files differing from either parent.
  Existing source-obligation and linter warnings are retained, not suppressed.
- The normal pre-commit checks passed before checkpointing. They remain enabled
  for the commit, together with the reference-transaction merge-loss guard.
  The final handoff records the committed-object guard result and exact parents.

The first `Lines.lean` check reported the missing incoming
`MIPStarRE.QPBT.Combining.Lines.Construction.olean`. Loading the exact-main
snapshot and rebuilding the affected modules resolved that artifact failure.

The old branch build products are preserved under
`.lake/build.pr487-before-main-20260915`. The exact-main snapshot was copied
through the primary `local/bin/warm-worktree.sh` with `--no-build --skip-packages`;
the shared cache and package store were not modified. Detailed validation logs
and signature checks are preserved under `.lake/pr487-*`.

## Remaining gates

PR 487 remains based on `issue-468-conditioned-point-line-marginals` (open
PR 472, head `cfdebb0ec47e9cc61242862c09b53db85096c12b`). Neither PR is retargeted,
closed, or merged. Approval 5195197720 applies to
`9e4e87949896a47bb177b83442bf75497ae36d07`, not this integration.

MAIN must perform the authorized publication and deterministic exact-head
checks, followed by the required independent gate and normal guarded stack
integration. This session does not publish, run CI or review, write primary
telemetry, post issue comments, or alter daemon markers.
