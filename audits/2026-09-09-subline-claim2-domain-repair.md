# Claim 17-2 Statement Integrity Audit

Author: native session `01a081c4-16db-7613-88c5-c2f1f5030d2d`.
Issue: #414. This session authored the repair and cannot independently review it.

## Source

The primary source is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`:
`lem:qld-xz-lines`, lines 942-949, defines the X-Z-X measurement, and
`claim:17-2`, lines 1168-1201, bounds removal of its X-point factor.
The active blueprint node is `lem:claim-17-2`.

## Claim 17-2

- Paper assumptions: admissible parameters; a projective strategy passing with error epsilon;
  its expanded measurements and state; the subline distribution; the defined X-Z-X measurement.
- Previous Lean assumptions: the same setting, but arbitrary point and line witnesses with
  independent real errors deltaQ and deltaP. The line witness did not retain the construction.
- Repaired Lean assumptions: `P`, `epsilon`, `ProjectiveSetting P epsilon`, and
  `SubLineWitness P`. The expression uses `S.combinedLineMeasurement` directly.
- Paper conclusion: the two scalar correlations differ by `O(m * sqrt(deltaLine epsilon))`.
- Repaired Lean conclusion: the same existing real-part scalar comparison, placements, averages,
  universal positive constant, factor `m`, and square-root error. Only `lines.T` is replaced by
  the source's concrete measurement.
- Verdict: source construction domain restored. No new bridge, equality, marginal, or producer
  hypothesis; no error weakening. The existing directly indexed subline encoding and real-part
  scalar convention remain explicit formalization boundaries.

The uniform constant-polynomial POVM gives the former assertion a positive difference
`(q-1)/q^2` even at zero strategy error. The verification of all witness fields appears in
`docs/paper-gaps/qpbt_subline-claims-line-marginal.tex`. This is a mathematical counterexample,
not a kernel-certified Lean instance.

## Combined Line Construction

The public statements of `exists_combinedLinesWitness_ofPointsWitness` and
`exists_combinedLinesWitness` are unchanged relative to the published constructor dependency.
Their proofs now instantiate `T := S.combinedLineMeasurement`. Degree support uses the
published constructor lemmas. The source-facing theorem obtains its point family internally.

The new `combined_line_measurement_consistency` is a Lean-only construction obligation.
Its point-error function and polynomial bound precede its line-error function; the supplied
point witness has error `deltaQ epsilon`. Its conclusion is the explicit evaluated consistency
estimate for the concrete sandwich in paper lines 942-961. It introduces no additional
hypothesis to the source-facing theorem and has a separate unfinished blueprint entry.

This obligation retains the existing unfinished consistency part of the combined-line
construction. Its discharge is the source's point-to-line comparison and pasting argument.
The two former witness-existence `sorry` sites are replaced by one named consistency site.
The C2 `sorry` remains. Thus the edited files have two direct holes, compared with three before
the repair. No proof of the underlying pasting estimate is claimed by this rearrangement.

## Scope and Dependencies

The base is published PR #400, `37a2e268bc1ef7434e13c9b8b3daf3c02d18b94e`.
Published PR #398, `19ec21353f4bcaecb59441b81aa08358ab73f933`, is merged with its full
dependency history preserved. Only its import-list conflict was resolved, by retaining both
sets of imports. The merge-loss guard passed.

The combined dependency graph also imported three declarations already present in
`Points/PlacementSupport.lean`: `place_zero`, `pointMeasExpOption_effect_some`, and
`pointMeasExpOption_effect_none`. Their duplicate copies are removed there; the same public
declarations and signatures remain available from the imported `LinePointOverlap.lean`.
This resolves the concrete duplicate-declaration errors in the first focused build.
`ZEvalDeficit.lean` imports the existing `Points.Placement` module instead of the partial
`PlacementSupport` copy, so the combined graph does not load both copies of the placement API.
The declarations used by that consumer have identical signatures in the two published files.

Claims 17-1 and 17-3 and the abstract witness record are unchanged. There are no implemented
callers of C2 to migrate. The later extended-line existence declarations remain outside this
repair. They can use the concrete consistency obligation and explicit witness construction
when their proofs are developed.

The separately owned `combinedLineMeasurement_sum_Z` proof is neither copied nor edited.
The existing issue #405 worktree and its private draft remain intact. No B8 or full-pasting
attempt is part of this change.

## Validation

The targeted build of `MIPStarRE.QPBT.Combining.Claims` and
`MIPStarRE.QPBT.Combining.Lines` passed after the documented import integration repair.
`leanblueprint web`, blueprint/Lean synchronization, the paper-facing proof-debt audit,
paper-gap reference and style checks, the installed-hook check, and whitespace checks passed.
The new mathematical note also compiles with `latexmk`. The existing C2 and named concrete
consistency holes remain explicitly tracked; no proof of either estimate is claimed.
