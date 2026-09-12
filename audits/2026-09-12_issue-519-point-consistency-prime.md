# Alice's pulled-apart measurement and Bob's point measurement

Issue #519; session `prover-519-20260912-01`; base
`ae124f8f09ee002444ac5b9711822c0f1daae142`.

## Mathematical result

For every supplied global polynomial-pair witness, the new theorem
`tildeM_consistencyDefect_le_deltaG_add_nonencoding'` proves

\[
  \operatorname{Defect}(\widetilde M_{\mathrm A},M_{\mathrm B})
  \leq \delta_G + \nu_{\mathrm A,W},
\]

where `nu` is `nonencodingMarginalMass w .alice W`. This estimate has no
unproved dependencies. It does not assume a bound on the non-encoding mass.

The source is the second display of Item 1 of
`lem:qld-construct-the-paulis`, in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1463-1492`.
The source proves the opposite ordering and states that the argument applies
with the registers interchanged. Here the factors on `AA'A''` and `B` are
regrouped as factors on `AA'` and `BA''`, without assuming a symmetric
strategy or identifying the players' Hilbert spaces. The convolution formula
for the expanded point measurement then gives the decoded overlap.

For encoding outcomes the decoded value equals polynomial evaluation. For
the other outcomes, positivity and completeness bound the evaluated overlap
by their marginal mass, while the decoded overlap is nonnegative. The
witness's Alice-side consistency field supplies the averaged evaluated
overlap bound. This is the support restriction required by
`docs/paper-gaps/qpbt_decoding-identity.tex`; the unrestricted decoder identity
used in the printed calculation is false.

The target `tildeM_consistent_pointMeas'` applies this estimate and the
existing `nonencodingMarginalMass_le`. Its universal constant is `C + 1`
when the latter supplies `C`: writing
`T = deltaG + sqrt epsilon + md/q`, positivity gives `deltaG <= T`, so
`deltaG + C*T <= (C+1)*T`.

The target's direct hole is removed, but its axiom closure still contains
`sorryAx` through `nonencodingMarginalMass_le` (#517). This is a reduction
to that existing prerequisite, not certification of the paper theorem.
The source-facing construction of the supplied witness remains separate.

## Statement integrity

- Paper assumptions: the projective setting and the global measurement of
  `lem:qld-4-7`, with its point-consistency estimate.
- Lean assumptions: the unchanged `AdmissibleParams`, real errors with
  `0 <= epsilon <= 1` and `0 <= deltaG`, `ProjectiveSetting P epsilon`,
  supplied `GlobalPairWitness S deltaG`, and either Pauli basis.
- Paper conclusion: Alice's pulled-apart measurement is consistent with
  Bob's point measurement on uniformly random points, at the enlarged error.
- Lean conclusion: the same ordering and averaging distribution, bounded by
  `deltaConstructPaulis C epsilon deltaG P.m P.d P.q` for a universal `C >= 1`.
- Verdict: the assigned public Lean signature is preserved exactly. The
  explicit error contract and the blueprint's documented decoder correction
  are retained. No symmetry, support hypothesis, or new bridge input is added.

No other existing proof body is changed. No blueprint completion marker is
added; the remaining mass estimate and the source-facing witness construction
are not certified by this work.

## Provenance and cumulative costs

The search covered saved Git refs and the history of `Extraction/Consistency`.
No completed proof of the target was found. Commit
`16ddc770ad0ed4511d1e63bea6a3d661997aec6a` (#518) contains the opposite-order
calculation. Its auxiliary `Extraction/PointConsistency.lean` is reused from
Git blob `08d862f0857e16046c0e3126dc494c64c9e31c30`, including the
side-parametric convolution lemma. The only adjustment replaces a terminal
`first` tactic by `ac_rfl` to satisfy the full build's flexible-tactic linter.
The Alice-side extension is isolated in
`Extraction/PointConsistencyPrime.lean`. No other change from that commit is
copied. The averaged proof also reuses `sum_marginalPoly_eval_mul` and
`marginalPoly_pointMeas_consistent_alice` from the existing marginal API.

The owner reports a prior #519 admission attempt that never acquired an
account reservation and is terminal. No completed session row for that
attempt was found in the primary registry at the time of inspection; its
elapsed time and usage are unknown, not zero.

The existing prerequisite records in the primary `sessions.jsonl` give:

| Issue | External sessions | Recorded seconds | Recorded output tokens |
| --- | ---: | ---: | ---: |
| #243, marginal agreement | 4 | 4895 | 52393 |
| #245, register transport | 3 | 3432 | 62189 |
| #258, encoding support | 4 | 4972 | 68870 |
| #261, supported-mass comparison | 4 | 2669 | 68192 |
| Total | 15 | 15968 | 251644 |

These are prerequisite costs, not fifteen prior attempts at this exact goal.
Two further historical native observations for #261 have unknown time and
usage. The #518 proof effort and the current session are additional to the
table; their final dispatcher records were not yet present when inspected.
No historical gap budget is reset. This session started at
`2026-09-12T05:31:23Z`, has a 60-minute bound, and launches no descendants.

## Validation and remaining gates

Focused compilation of the three Lean files passes using the checkout's
actual Lean/Mathlib version, v4.32.0. Both auxiliary modules are warning-free;
`Consistency.lean` reports only its four unchanged direct holes. The integrity
scan finds no new hole, axiom, or kernel bypass. The hook-installation check
and `git diff --check` pass.

Fresh branch-private artifacts were used to print axiom closures. The exact
operator identity, decoded-defect identity, pointwise mass comparison, and
averaged bound each use only `propext`, `Classical.choice`, and `Quot.sound`.
The target additionally uses `sorryAx` through the mass estimate. The audit
file is `~/.cache/mipstarre-dev/sessions/prover-519-20260912-01-checks/Axioms.lean`.

The first exact-head CI run passed the full project build and LDT axiom-audit
build. Its workflow unit suite failed one model-policy fixture because the
session's inherited `MIPSTARRE_HARDNESS_REASON` reached a routine dispatch
fixture. Clearing the dispatch metadata as well as the invoking/review model
settings makes that focused regression pass. The failed CI evidence is
retained; a subsequent exact-head run verifies the linter correction and uses
the fully scrubbed environment. No workflow source or policy is changed.

The unchanged direct holes are `marginalPoly_sub_pointMeas_approx_zero`,
`nonencodingMarginalMass_le`, `tildeM_consistent_pointMeas`, and
`tildeObs_selfConsistent`. Only the mass estimate is used by the new target
proof. Their owning packets remain separate.

Publication and exact-head local CI are the next workflow gates, followed by
independent review. Issue #519 should remain open while #517 leaves its axiom
closure incomplete. The final session report records publication and CI
outcomes; this session does not launch a reviewer or merge the PR.

## Completion after the saved support proof became available

This section supersedes the earlier residual-dependency status. During the
publication checks, the saved commit
`e36fd1aa056782007917b0d6c5e19b85ea28179b` from #517 became available. Its
support proof gives new mathematical evidence beyond the initial reduction.
The necessary source modules were read and recovered, with their original
provenance retained:

- `Extraction/EncodingSupport.lean` and the public tensor-measurement API in
  `Games/DistanceTheorems.lean`, originally from `55ae7487`.
- `Extraction/PolynomialCollision.lean`, originally from `36c07381`.
- `Games/SupportMass.lean`, originally from `ff4c92d1`.
- `Games/DistanceTheorems/TensorConsistency.lean`, originally from `84c7ec43`.
- `Combining/Lines/PairStateConsistencyTransport.lean`, originally from `7f916eb8`.
- `Extraction/NonencodingSupport.lean`, proved in `e36fd1aa`.

The full-build linter found a global `open scoped Classical` in the recovered
`NonencodingSupport.lean`. It is restricted to the two theorem statements
whose filters need classical decidability, using `open Classical in`.

Only these necessary support files and the tensor API change were recovered.
The other packet's `Consistency.lean`, blueprint, audit, and gap-note edits
were not copied. In particular, `nonencodingMarginalMass_le` remains untouched
in this branch; the target no longer uses that declaration.

The reference returns the encoding of the sum of the strategy's Pauli answer
and the ideal ancillary answer. Its evaluated consistency with Alice's
global marginal is at most `deltaG + C * sqrt epsilon`, by the point and
Pauli-basis checks and exact preservation under independent ancillary
convolution. Schwartz-Zippel adds `md/q`, and completeness bounds the marginal
mass outside encodings by that inconsistency. Applying these recovered
lemmas directly proves Alice's mass bound inside the target. Combining it
with the new defect estimate gives

\[
  \operatorname{Defect}(\widetilde M_{\mathrm A},M_{\mathrm B})
  \leq 2\delta_G+C\sqrt\epsilon+md/q
  \leq (C+1)(\delta_G+\sqrt\epsilon+md/q),
\]

using `C >= 1` and nonnegative errors. The public existential constant,
quantifier order, assumptions, distribution, register ordering, and conclusion
are unchanged. A fresh byte comparison of the target signature succeeds.

Focused compilation of every recovered file and the updated target succeeds.
After regenerating the target's branch-private `.olean`, the fresh axiom
audit reports exactly `propext`, `Classical.choice`, and `Quot.sound` for
`tildeM_consistent_pointMeas'`, as well as the four earlier new estimates.
The separate `nonencodingMarginalMass_le` still reports `sorryAx`, confirming
that its unchanged proof hole is outside the target's dependency closure.

The earlier #517 blocking edge records the provenance of the support work,
whose verified content is now included in this branch. The completed target
still assumes the supplied global witness exactly as before; it does not
construct that witness or prove the other items of the extraction lemma.
No blueprint proof-completion tag is added to the combined source lemma.

The #517 session is additional to the prerequisite cost table above, with
its final time and usage retained in the dispatcher record when available.
The full-build and exact-head CI results for the completed target are recorded
in PR #539 and the final session report. Independent review remains the next
gate after green CI.
