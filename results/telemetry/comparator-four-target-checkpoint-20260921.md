# Four-target comparator checkpoint, 2026-09-21

MAIN observed the ongoing author at the scheduled 20-minute checkpoint, first
reading live state at 10:32:11 UTC. The sole native delegate remains
`01a0c373-664c-7123-bde2-1786665a2da3`, on space-3, under the existing
10:56:55.140 UTC deadline. This is a checkpoint, not a new assignment or a
renewed budget.

## Established result

The generated challenge at `/tmp/issue662-four-target-20260921` contains
31 files: the root and 30 contributing modules. It declares all four required
targets, with the corrected direct-effect soundness statements:

- `MIPStarRE.QPBT.pauli_soundness`;
- `MIPStarRE.QPBT.pauli_soundness_qubit`;
- `MIPStarRE.QPBT.exists_spcc_value_one`;
- `MIPStarRE.QPBT.exists_ld_soundness`.

The challenge copied into `/home/drx/QPBT-comparator` built successfully at
10:28:45.806 UTC (8686 jobs). The output contains exactly four intended
statement-placeholder warnings in Challenge.lean, at lines 171, 181, 224 and
250. This is elaboration evidence for the independent statement challenge;
it is not comparator acceptance or an axiom audit of the library proofs.

The first failed challenge build required explicit finite-type context in the
generated measurement module. A later failure required the intended namespace
for Distribution in the consistency module. The subsequent successful build
above supersedes those failed builds; their original outputs remain in the
delegate rollout.

## Work still running

At 10:30:28.203 UTC the author started a diagnostic four-target comparison in
the external checkout. At 10:33 UTC its shell PID 566270 and Lake PID 566275
were live; the author's tool session is 96977. Its log is
`/tmp/issue662-space3-diag-four-oldpin.out`. It is rebuilding the solution's
newly required dependencies before comparison.

This run deliberately uses the historical library pin
`a942ecb56fd25933da51286070ddc615609edc76`, the diagnostic comparator copy,
fake landrun, and a temporary configuration with nanoda disabled. Its planned
exports are `/tmp/issue662-space3-challenge4.export` and
`/tmp/issue662-space3-solution4-oldpin.export`. The run can identify mismatches;
it cannot establish acceptance of the repaired current library. No result
from this running comparison is yet recorded as a verdict.

The external checkout remains at committed draft head
`9e879feb96174ee0089a487d8bcebf659ef99a48` with the new challenge and configuration
uncommitted. Its tracked comparator configuration still permits only the three
standard axioms and enables nanoda for official verification; the temporary
diagnostic configuration is distinct.

PR 663 remains published at `a942ecb5`. The author worktree still has committed
head `d9a380b8`, the preserved merge of PR 660 with conflicts resolved locally,
and unpublished generator, context and library changes. Main has not started
canonical CI, claimed a new review, staged a train or inferred official
acceptance from the challenge build.

## Next decision

Use the actual diagnostic result to finish only the necessary library or
generation repairs, then bind verification to the resulting current source.
The official comparator, real landrun and nanoda, a merged-main pin, the C5
record, independent review and all other artifact criteria remain required.
The author retains its existing deadline and all predecessor/K6/K7 charges.

The raw build and process observations are preserved in the native rollout:
`rollout-2026-09-21T19-11-55-01a0c373-664c-7123-bde2-1786665a2da3.jsonl`.
