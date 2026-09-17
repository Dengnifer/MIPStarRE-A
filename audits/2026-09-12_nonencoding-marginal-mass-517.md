---
title: "Non-encoding marginal mass (#517)"
date: 2026-09-12
purpose: >
  Records the historical proof and validation of the supplied-witness
  non-encoding marginal mass bound, including its September 18 preservation.
issue: "#517"
pr: "#580"
---

# Non-encoding marginal mass (#517)

## Record and scope

This is the historical issue-517 audit from September 12, 2026, restored on
September 18, 2026 against main `b103158a7d9b1803a1cf2bd0546d5a38f3a3f105`.
The original proof is preserved in PR #543 at `e36fd1aa056782007917b0d6c5e19b85ea28179b`;
the later unpublished documentation correction is `4a57da3448af20d867dde95782c589283a5ecc01`.
The present branch takes only the existing `nonencodingMarginalMass_le` proof,
not any superseded modules, placement helpers, or three historical proof holes.
The September 17 comparison is `/tmp/opus-report-pr543-20260917.md`.

The original PR #543 CI attempt failed: the build could not take the
machine-wide full-build lock within 30 seconds, and blueprint sync failed.
The blueprint render, paper-gap check, file-length check, proof-debt scan,
and proof-evasion check passed. There was no green full build, CI summary,
or independent review for that PR; those failed and absent results are not
renamed as successes in this audit.

## Statement integrity

The primary passage is `lem:qld-construct-the-paulis`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1463-1605`.
Its decoder substitution at lines 1483-1492 is false for arbitrary polynomial
representatives, as explained in `docs/paper-gaps/qpbt_decoding-identity.tex`.
The support estimate is a formalization-only auxiliary for the corrected
calculation `eq:qld-nonencoding-mass`, separately recorded at
`lem:qld-nonencoding-mass-bound`; it is not a named theorem of the paper.

- Paper assumptions: admissible parameters and a projective strategy passing
  with probability at least `1 - epsilon`; the polynomial-pair construction
  of `lem:qld-4-7` supplies projectivity and both point-consistency bounds.
- Lean assumptions: unchanged `AdmissibleParams`, `0 <= epsilon <= 1`,
  `0 <= deltaG`, `ProjectiveSetting P epsilon`, and the explicitly supplied
  `GlobalPairWitness S deltaG`. The original domain includes `1 <= d` and
  `m` dividing `q`, but no new `d < q` hypothesis; zero error is included.
- Paper conclusion: `lem:qld-construct-the-paulis` obtains the two
  point-consistency statements and observable self-consistency for its
  constructed measurements. Its corrected proof separately needs small
  non-encoding marginal mass.
- Lean conclusion: for both player sides and Pauli bases, the actual marginal
  mass is bounded by `C * (deltaG + sqrt epsilon + md/q)`, with the universal
  `C >= 1` preceding all parameters, errors, strategies, and witnesses.
- Verdict: exact original Lean statement and explicitly supplied-witness
  auxiliary blueprint statement. Relative to the source construction, this
  auxiliary has an extra witness premise and does not itself prove the source
  theorem. Main now separately proves `exists_globalPairWitness` and composes
  it into `exists_pulled_apart_consistency`; no source-level dependency edge
  from that proof to this uniform auxiliary has been added.

The definitions `nonencodingMarginalMass` and `deltaConstructPaulis`, every
quantifier and assumption of the theorem, and its error bound are unchanged
from the historical head. Its proof alone closes the tracked local hole.

## Mathematical proof and provenance

The reference measurement returns the encoding of the sum of the strategy's
Pauli answer and an ideal ancillary Pauli answer. It is complete and supported
on encodings. Independent additive convolution with the perfectly correlated
ancillary measurement preserves consistency defects. The consistency triangle
gives `deltaG + C * sqrt epsilon`: `deltaG` remains outside the square root.
Schwartz--Zippel adds `md/q`; positivity and completeness bound the mass on
non-encoding polynomial representatives. Exact register identities transport
that mass to the six-register state, on either player side. This uses neither
strategy symmetry nor the restriction `d < q`.

The following sources of proof content were recorded by the September 12
author; the earlier PR/open-branch descriptions are historical, not current
publication or CI claims:

| Ingredient | Historical origin |
| --- | --- |
| Encoding reference and tensor POVM/postprocessing | `55ae7487`, saved PR #263 head `3a1b6761` |
| Real polynomial collision | `36c07381`, saved head `f266121a` |
| Supported-reference mass comparison | `ff4c92d1`, saved PR #264 head `193723b4` |
| Independent additive convolution | saved head `84c7ec43`, issue #266 |
| Pair-state consistency transport | `7f916eb8`, issue #494 |

The original work was in `Extraction/NonencodingSupport.lean` and the target
proof; its ideal-point perfection input followed from the proved
`sum_tauPointProj_pair_stateQForm_eprState`. The September 18 base already
contains the support declarations. Its `NonencodingSupport.lean` documentation
is retained without changes in this preservation task. The saved PR's three
old point-consistency and observable-consistency `sorry` stubs were subsequently
proved on main under the `*_ofGlobalPairWitness` names and are not restored.

The unpublished September 14 follow-up removed the auxiliary proof-level
blueprint mark because the global witness constructor was then unproved.
On the September 18 base, `exists_globalPairWitness` is proved for zero error
as well, and `exists_pulled_apart_consistency` already composes it with three
separate estimates. That historical retraction therefore cannot be copied
as an assertion of an open constructor today. It also cannot remove the
explicit witness premise from `nonencodingMarginalMass_le`.

## Historical effort and validation

The September 12 author reported focused Lean checks for the target and its
support modules, with only then-existing unrelated holes in `Consistency.lean`.
Its scratch axiom audit reported exactly `propext`, `Classical.choice`, and
`Quot.sound` for the target and key support declarations. That was a focused
check on the old head, not a full-build or current-main certification.

At the September 12 checkpoint, dispatcher wall times for two scout sessions
and three prerequisite prover sessions were 900, 201, 2397 (#258), 1500
(#259), and 701 (#261) seconds: 5699 seconds of known prior effort, not an
episode total. The #258 final report says 36m54s; the dispatcher records
2397 seconds, which is used here. Incomplete zero counters on failed scout
and #259 sessions do not imply zero token usage; the #259 handoff reported
6,477,828 last-observed tokens, mostly cached input. Other available input
and output counters were 3,072,191/20,297 (resumed scout),
8,164,681/40,226 (#258), and 1,980,260/14,401 (#261). Cached input and
reasoning output are not counted twice. The September 14 continuation audit
at unpublished `4a57da34` records the two further prover-session durations
3750 and 831 seconds (a known subtotal of 10280 seconds), without claiming
complete episode-wide time or token accounting. The failed third-attempt
capacity admission is historical and does not indicate a proof failure.

## September 18 preservation checks

On the current base the direct `lake env lean` check of `Consistency.lean`
passes and reports the single unrelated inherited hole in
`marginalPoly_sub_pointMeas_approx_zero`; the restored target itself uses no
`sorry`. Focused module-build, fresh target axiom query, blueprint render and
sync, paper-gap validation, and ordinary commit-hook outcomes are recorded in
`/tmp/pr543-preservation-20260918-receipt.md` after they run. These focused
checks do not constitute full CI or an independent review. Publication and
merge are deliberately deferred.
