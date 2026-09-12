# PR 400: source scope of the subline estimates

This audit repairs the source correspondence at frozen head
`37a2e268bc1ef7434e13c9b8b3daf3c02d18b94e`. The canonical CODE review is
`48c8adbc83d749b0b79fb9faac681534`; the PROSE review is
`8aaa7139221c4975a2082d886b77714d`. The paper source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`,
`lem:qld-sublines`, `claim:17-1`, and `claim:17-3`.

## Statement integrity

- Paper assumptions: the projective setting and joint-point and paired-line
  measurements constructed in the preceding lemmas, averaged over the
  seed-indexed subline law D and a uniform point on its extended line.
- Lean assumptions: the unchanged `ProjectiveSetting`,
  `CombinedPointsWitness`, `CombinedLinesWitness`, and `SubLineWitness`.
  The last record has a directly indexed extended-line marginal and separate
  X and Z point mixture laws; it is explicitly an auxiliary record.
- Paper conclusion for Claim 17-1: a complex absolute difference of the
  joint and ordered overlaps bounded by a universal multiple of sqrt(deltaQ).
- Lean conclusion for Claim 17-1: the absolute difference of their real
  parts on the auxiliary law, with the same asymptotic error. The universal
  constant remains outside all parameter and witness quantifiers.
- Paper conclusion for Claim 17-3: a complex absolute difference of the Z
  overlap from one, of order sqrt(m) times the sum of the three fourth roots.
- Lean conclusion for Claim 17-3: the corresponding real-part estimate on
  the auxiliary law, with unchanged error and quantifier order.
- Verdict: the Lean results are auxiliary results on a different carrier;
  the Claim 17-1 real-part conclusion is weaker than the source conclusion.
  The blueprint now certifies only separate auxiliary entries that state
  these distinctions. The source-labelled statements remain pending.

The missing distribution transport, complex estimate, and Z-overlap reality
are explained in `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`, section
"Scalar estimates on the auxiliary subline law". They are not added as
hypotheses. Neither source statement nor either public Lean contract changes.

## Other review findings

The two duplicate proof bodies now apply the existing completed-pair norm
identity and uniform affine-point identity. The source proof sketch uses
W-adjoint times W, squared distance 4 deltaQ, and error 2 sqrt(deltaQ).
Prefix truncation annihilates preceding blocks and retains later blocks.
The q-element fibers are fibers on ambient-point/parameter pairs; their
canonical representative is fixed in the nonzero-direction case.
The Z-deficit modules describe only their implemented Z estimates.

The Claim 17-2 statement and its one existing `sorry` are unchanged. The
separate issue 414 / PR 454 repair is not imported. No attempt or time budget
for the earlier C1/C3 work or B8 is reset by this documentation repair.

## Validation

The focused Claims target build passed, rebuilding all six changed Lean
modules in its dependency graph. A final direct Claims elaboration passed
with only the unchanged Claim 17-2 proof-hole warning. The public source
header check reports no changes. The proof-integrity scan finds the same
single `sorry` and no prohibited bypasses in the six touched modules.
The first and third scalar theorems and the reused uniform-point identity
depend only on `propext`, `Classical.choice`, and `Quot.sound`.

Blueprint rendering passed after bibliography generation, without error or
warning lines; blueprint declaration synchronization passed, and all 1654
declaration links resolved. The blueprint LaTeX conventions, paper-facing
proof-debt audit, paper-gap style and reference checks, and installed-hook
check passed. The paper-gap note also compiled to PDF, with one inherited
unresolved citation to `gap:qpbt_ld-simultaneous-sandwich` in its unchanged
soundness discussion. Full exact-head CI and independent review belong to
the publication owner after the frozen review consumer is released.
