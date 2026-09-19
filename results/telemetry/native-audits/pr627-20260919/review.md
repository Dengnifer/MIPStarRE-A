# Review - PR 627 @ 05aedbaada3f87723f8177c8444d329c04e0f36a

Fresh independent review of the exact head against published `main`, merge base
`b5f52bcae19a350de0ff9c29d695df8fe82fd420`. The contribution is limited to
the new 208-line completed-point leaf, its aggregate import, and three
formalization-support nodes in chapter 15.

## Findings

- none

## Review

**Source and statement integrity.** Paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:689-697`
provides projective joint point measurements whose copies are self-consistent,
on average over uniform `x,z`, with error `delta_Q`. Paper lines 948-961 use
that estimate as the application of the pasting hypothesis `eq:pasting-2` from
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-523`.

The six new declarations do not claim either source statement. At
`MIPStarRE/QPBT/Combining/Lines/PointSelfConsistencyCompleted.lean:64` and
`:93`, the first two results prove exact identities for coordinatewise
completion and coordinate exchange. At `:111` and `:130`, the next two results
transport the existing joint-point bound to the product of two independent
line-point laws, in X-then-Z and Z-then-X outcome order. At `:161` and `:185`,
the last two restrict that product law to nonzero first-line direction and give
the exact bound `delta_Q / nondegenerateLinePastingMass`.

The Lean hypotheses are the existing `CombinedPointsWitness`, directed
opposite placements, and finite/decidable boundary data. No bridge, residual,
producer, positivity, or conclusion-shaped hypothesis is added. The conclusions
are faithful weaker consequences of `eq:qld-q-self-cons`, with the altered
answer alphabet and question laws displayed explicitly. Verdict: exact
formalization-only transport statements; no weakened source theorem, extra
source assumption, or source-completion claim.

**Proof preservation and indexing.** The declaration region is identical to
the six retained results at PR 487 head `7c3b54bc`; only the final theorem's
docstring was softened to avoid claiming a current consumer. Completion sends
every pair to `(some a, some b)` and gives zero effect to outcomes containing
`none`, so the defect is preserved exactly. The Z-then-X form uses
`Equiv.prodComm` together with `completed_orderedZX_effect`, preserving the
joint outcome order required by the X-Z-X sandwich. The conditioned law maps
unconditioned samples `(s_X,s_Z)` to a question whose `question.2` is `s_X`
and whose `question.1.2` is `s_Z`; therefore
`Q question.2.2 question.1.2.2` reads `(x,z)` in the intended order. The
conditioning theorem divides by precisely the retained first-line
nondegeneracy mass, whose positivity is already proved on `main`.

The old PR 487 review's fourteen already-main declarations are absent from this
patch. Repository search confirms that these six declarations remain leaf
support outside their own module and blueprint links; the module and blueprint
say so directly rather than inventing a consumer.

**Blueprint audit.** The three distinct nodes at
`blueprint/src/chapter/ch15_qpbt_combining.tex:1690`, `:1719`, and `:1758`
separately record exact completion, product-law self-consistency, and
conditioned self-consistency. They display the relevant hypotheses, outcome
ordering, laws, retained mass, and bounds; identify themselves as
formalization-only support; carry statement and proof `leanok`; and cite real
proof dependencies. None marks `lem:qld-xz-lines`, `eq:qld-q-self-cons`, or
`eq:pasting-2` complete.

**Verification and limits.** All nine exact-head `local-ci/*` contexts are
currently successful; the non-partial manifest records 546 seconds, including
the full build, blueprint render, blueprint sync, proof-debt, and proof-evasion
checks. I inspected the manifest and terminal logs, ran `git diff --check`,
scanned the new Lean file for proof holes, bypasses, and debug tactics, and
type-checked it directly. Independent `#print axioms` probes for all six public
declarations returned only `propext`, `Classical.choice`, and `Quot.sound`.
I did not rerun the full build, canonical CI, or the repository-wide
supplemental blueprint axiom audit; the PR records that supplemental audit as
passing, while the six changed declarations were independently probed here.
No source, status, merge, issue, or branch mutation was performed.

VERDICT: APPROVED (code=APPROVED, prose=APPROVED)
