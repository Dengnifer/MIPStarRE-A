# Issue 360: supplied-witness direct soundness

## Status

Withdrawn after review round 1 of PR 361 (finding F1). The packet now ships
only the arbitrary-strategy transport of issue #346; the supplied-witness
wrapper is deferred, so issue #360 remains open.

## Original goal

Apply arbitrary-strategy directly indexed low-degree soundness to the concrete
strategy determined by a supplied `CombinedPointsWitness` and
`ExtendedLinesWitness`, using the passing-value theorem from issue #348 with
error `3 * (sqrt (deltaQ + deltaL) + m * d / q)`.

## Why the wrapper is withdrawn

`ExtendedLinesWitness` is not a boundary condition. It supplies the line
measurements and their quantitative consistency estimates, that is, the proof
data that paper `lem:qld-4-13` is responsible for producing. In
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1278-1286` the
proof of `lem:qld-4-7` obtains that strategy from `lem:qld-4-13` and only then
applies low-degree soundness, and the blueprint passage
`blueprint/src/chapter/ch15_qpbt_combining.tex:2113-2149` records the
construction and transport obligations that are still open. In Lean the
corresponding construction,
`exists_extendedLinesWitness_established_ofPointsWitness`
(`MIPStarRE/QPBT/Combining/Apply.lean:143-152`), is still an explicit proof
obligation.

A theorem that assumes those witnesses is therefore a newly introduced
conditional helper, not a theorem with faithful boundary hypotheses. The
faithful-formalization policy (`AGENTS.md`, "Do not add a conditional helper
merely to keep a file compiling") admits such a helper only in the narrow
paper-realignment case, which preserves existing proof content; this packet
introduced new content instead. Deriving the witnesses internally is not
available either, because the named construction theorem is itself unproved and
the derived statement would inherit that proof debt.

## What ships in PR 361

`MIPStarRE/QPBT/Combining/DirectLowDegree/AnyStrategySoundness.lean` only:
`exists_direct_ld_soundness_of_k_eq_one_any_strategy`, the generic
arbitrary-strategy transport of directly indexed low-degree soundness through
Naimark dilation and ground-slice compression (issue #346). That theorem takes
an arbitrary strategy and a passing value as its input; it assumes no witness
structure.

## Discharge plan

Reinstate the supplied-witness application only after the extended-line
construction is discharged, and then in the source-faithful form: obtain the
points and lines data internally from the construction theorem instead of
assuming it, so that the resulting statement quantifies over an admissible
parameter tuple and a projective setting alone. The construction obligations
are tracked with `exists_extendedLinesWitness_established_ofPointsWitness` and
the gap notes `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` and
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`.

## Source and statement integrity

- Paper assumptions (`lem:qld-4-7`, first proof paragraph): an admissible
  parameter tuple and a projective setting; the line and point measurements are
  produced inside the proof.
- Lean assumptions of the withdrawn wrapper: the same tuple and setting plus a
  supplied `CombinedPointsWitness` and a supplied `ExtendedLinesWitness`.
- Verdict: extra assumptions (a conditional helper), not faithful boundary
  hypotheses. The wrapper is therefore removed rather than retained.
- The source-labelled blueprint entry `lem:qld-4-7` is unchanged and keeps no
  `\leanok` from this packet.

## Verification

Focused Lean checking of the remaining changed files, aggregate re-export
checking for `MIPStarRE.QPBT` and `MIPStarRE.QPBT.Combining.DirectLowDegree`,
proof-debt and prohibited-construct scans, axiom inspection, hooks, and normal
checked publication.
