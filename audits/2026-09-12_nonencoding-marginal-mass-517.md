# Non-encoding marginal mass

## Result and statement integrity

The theorem `MIPStarRE.QPBT.nonencodingMarginalMass_le` is proved at the
statement in base commit `ae124f8f09ee002444ac5b9711822c0f1daae142`.
The universal constant precedes parameters, errors, strategy, witness, side,
and basis. No assumption, quantifier, error function, or conclusion changes.

The primary source is `lem:qld-construct-the-paulis`, in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1458-1602`.
Its unrestricted decoder substitution is false, as documented in
`docs/paper-gaps/qpbt_decoding-identity.tex`. The precise target is the
blueprint repair `eq:qld-nonencoding-mass` and its separate lemma
`lem:qld-nonencoding-mass-bound`, not a separately printed paper assertion.

- Source assumptions: admissible QPBT parameters, a projective strategy
  passing with probability at least `1 - epsilon`, and the polynomial-pair
  measurement with point consistency supplied by `lem:qld-4-7`.
- Lean assumptions: the original `AdmissibleParams`, `0 <= epsilon <= 1`,
  `0 <= deltaG`, `ProjectiveSetting P epsilon`, and
  `GlobalPairWitness S deltaG`. Finite coordinate and field instances are
  supplied by the existing domain.
- Blueprint conclusion: for either player and basis, the non-encoding mass
  is at most a universal constant times `deltaG + sqrt epsilon + md/q`.
- Lean conclusion: exactly the original `deltaConstructPaulis` bound.
- Verdict: faithful boundary hypotheses for the blueprint repair, with the
  existing explicit supplied-witness premise retained. This theorem does not
  construct the global witness or certify the whole source extraction lemma.

## Proof

The reference measurement returns the encoding of the sum of the strategy's
Pauli answer and an ideal ancillary Pauli answer. It is a complete POVM
supported on encodings. Independent additive convolution with the perfectly
correlated ancillary measurement preserves consistency defects exactly.
The point self-consistency and the two directed Pauli-basis checks therefore
give evaluated marginal/reference inconsistency at most
`deltaG + C * sqrt epsilon`. The global error is outside the square root.

The existing Schwartz-Zippel comparison bounds full polynomial inconsistency
by evaluated inconsistency plus `md/q`. Completeness of the reference and
positivity put the non-encoding marginal mass below full inconsistency.
The two-player expanded state has the same relevant correlations as the
six-register state, with identities on unused registers. This proves both
player cases without strategy symmetry or a degree restriction `d < q`.

## Reused proof content

The saved main and branch history was searched before implementation. The
target was still open. Only needed source files and one tensor API change
were recovered; no divergent branch was merged or modified.

| Content | Provenance |
| --- | --- |
| Encoding reference and public tensor POVM/postprocessing | `55ae7487`, saved PR #263 head `3a1b6761` |
| Real polynomial collision | `36c07381`, saved head `f266121a` |
| Supported-reference mass comparison | `ff4c92d1`, saved PR #264 head `193723b4` |
| Independent additive convolution | saved head `84c7ec43`, issue #266 |
| Pair-state consistency transport | `7f916eb8`, issue #494 |

PR #263 and PR #264 were confirmed open at their cited heads on GitHub during
this session. Their branches and lifecycle records were not modified.
The new work is `Extraction/NonencodingSupport.lean` and the target proof.
The ideal-point perfection input is derived from main's already proved
`sum_tauPointProj_pair_stateQForm_eprState`; the unmerged ideal-point module
is not copied.

## Validation

Focused Lean checks pass for the target and all recovered/new proof modules.
The only warnings in `Consistency.lean` are its four other existing holes.
The new modules contain no proof holes or proof-integrity bypasses.
The target and the key comparison/construction declarations have axiom
closure exactly `propext`, `Classical.choice`, and `Quot.sound`.
The scratch audit is outside the repository at
`~/.cache/mipstarre-dev/issue517-axioms.lean`.

Publication and exact-head CI evidence belong to the PR statuses and manifest;
focused checks alone are not a full-build claim. Independent review is the
next gate after green CI and is not launched by this author session.

## Prior effort and accounting

This is a continuation of the existing support-estimate effort, not a new gap
episode. The scout handoff
`scout-123-nonencoding-mass-20260906-02.last.md` already gave the proof
decomposition and established no mathematical obstruction.

Recorded wall times in `results/telemetry/sessions.jsonl` for the two scout
sessions and the three direct prerequisite prover sessions are respectively
900, 201, 2397 (#258), 1500 (#259), and 701 (#261) seconds: 5699 seconds total.
These are distinct recorded session durations, not the total cost of every
integration/review session. The #258 final report says 36m54s, whereas its
dispatcher row records 2397 seconds; the dispatcher value is used here.

The failed scout and #259 registry rows contain zero token counters that are
incomplete, not evidence of zero consumption. The #259 handoff
`orc-259-20260906-01.last.md` records 6,477,828 last-observed tokens, mostly
cached input, for its 1500-second attempt. The other available input/output
counters are 3,072,191/20,297 (resumed scout), 8,164,681/40,226 (#258), and
1,980,260/14,401 (#261). Cached input and reasoning are not added again, and
these mixed/incomplete observations are not asserted to be an episode total.
Additional tensor, transport, review, and integration costs remain in their
original telemetry. This session's usage is recorded by the dispatcher.
