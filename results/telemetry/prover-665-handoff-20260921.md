# Issue 665 native author handoffs

The first handoff disclosed a consumer regression; the second records its repair within the same assignment.

Implemented and published the source-faithful repair.

**Publication**
- Branch: `issue-665-raw-pauli-effects-20260921`
- Head: `91014a3f91b63f357bbddc6988be65369d28eb75`
- PR: #668, open at exact head
- Published at `03:20:50Z`, within the authorized publication tail
- Primary and issue worktree are clean
- No merge performed

**Repair**
- Added raw prescribed-answer distances in [SoundnessDefs.lean](/home/drx/MIPStarRE-qpbt/.worktrees/issue-665-raw-pauli-effects-20260921/MIPStarRE/QPBT/Test/SoundnessDefs.lean).
- Added [RawOperatorTransfer.lean](/home/drx/MIPStarRE-qpbt/.worktrees/issue-665-raw-pauli-effects-20260921/MIPStarRE/QPBT/Test/Soundness/RawOperatorTransfer.lean), proving:
  - completion differs from raw effects only at zero;
  - fixed-edge malformed-answer mass bounds for both players;
  - completed-to-raw distance estimates for both players;
  - absorption of linear and squared losses into the existential `deltaQld` prefactor.
- Updated `pauli_soundness`, the qubit corollary, and nonvacuity consumers to use raw effects.
- Added the blueprint explanation, gap note/register entry, theorem-index updates, and bibliography entry.
- Regenerated the QPBT comparator fixture and removed only the two now-unused `Measurement.lean` QPBT preludes.

**Verification**
- Focused Lean builds passed for `RawOperatorTransfer`, `Soundness`, `QubitForm`, and `NonVacuity`.
- Axiom checks report only `propext`, `Classical.choice`, and `Quot.sound`.
- No new `sorry`, `axiom`, unsafe cast, or kernel bypass.
- `leanblueprint web` and all 1,862 `checkdecls` entries passed.
- QPBT and unchanged LDT comparator drift checks passed.
- Comparator unit tests passed.
- Normal pre-commit passed all 758 tests; checked pre-push passed.

**Statement Integrity**
Paper and Lean assumptions agree: admissible parameters, `ε ≥ 0`, and value at least `1 - ε`. Both conclusions now compare the direct `.effect (.pauliOutcome u)` effects for Alice and Bob with the ideal projectors. There are no extra premises or weakened conclusions. Verdict: **source-faithful**, with only the existential universal prefactor enlarged.

Remaining work belongs to MAIN: full CI/review and integration with the separately owned four-target comparator expansion. Under the current two-target configuration, the drift guard is green, but directly compiling the generated fixture still omits the completed internal distance declarations; that is the already-separated gate647/PR660 target-expansion work.

---

Corrected PR #668 within the publication tail.

- Updated `challenge_qpbt_footer.lean` to use `rawPauliOperatorDistanceA/B`.
- Regenerated `ChallengeQPBT.lean.expected`.
- Direct `/tmp` challenge type-check passed; only the two intentional challenge `sorry` warnings.
- QPBT and LDT drift guards passed.
- Commit: `325e3e24c7a3b5752f65028d8c567695923248ef`
- Checked-pushed and verified PR #668 at that exact head.
- PR validation report updated.
- Issue worktree is clean.

The primary currently has only concurrent workflow telemetry modifications in `results/telemetry/builds.jsonl` and `results/telemetry/events.md`; I did not edit or revert them.
