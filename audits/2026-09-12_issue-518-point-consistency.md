# Point consistency of the pulled-apart measurement

Issue #518; session `prover-518-20260912-01`; base
`ae124f8f09ee002444ac5b9711822c0f1daae142`.

## Mathematical Result

For a supplied global polynomial-pair witness with point-consistency error
`deltaG`, the theorem
`tildeM_consistencyDefect_le_deltaG_add_nonencoding` proves

\[
  \operatorname{Defect}(M_{\mathrm A},\widetilde M_{\mathrm B})
  \leq \delta_G + \nu_{\mathrm B,W},
\]

where `nu` is `nonencodingMarginalMass w .bob W`. This theorem does not use
the unproved estimate for that mass. Its axiom closure contains only
`propext`, `Classical.choice`, and `Quot.sound`.

The source is Item 1 of `lem:qld-construct-the-paulis`, specifically
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1463-1492`.
The matching blueprint entry is in `ch16_qpbt_extraction.tex`. The correction
to the source's unrestricted decoder identity is already documented in
`docs/paper-gaps/qpbt_decoding-identity.tex` and is retained here.

For a fixed point `u`, expand the definition of the pulled-apart measurement
and regroup its factors on `A`, `BB'`, and `B''`. The convolution formula for
the expanded point measurement identifies the resulting overlap with

\[
  \sum_g \langle\widehat\psi,
    (\widehat S^W_g)_{\mathrm{BB}'}
    (\widehat M^W_{\operatorname{Dec}(g)\cdot\operatorname{ind}_m(u)})
      _{\mathrm{AB}''}\widehat\psi\rangle.
\]

For encoding outcomes, the decoded value equals `g(u)`. For every other
outcome, both overlaps are nonnegative, and the overlap at `g(u)` is at
most the marginal mass of that outcome, by completeness of the expanded
point measurement. Summing gives the loss `nu`. The given witness supplies
the evaluated overlap bound after averaging over `u`.

The auxiliary module `Extraction/PointConsistency.lean` proves the exact
operator identity, its consistency-defect formulation, and this pointwise
comparison. The existing marginal postprocessing lemmas complete the averaged
estimate in `Extraction/Consistency.lean`.

The body of `tildeM_consistent_pointMeas` now applies that estimate and the
existing theorem `nonencodingMarginalMass_le`. If the latter supplies constant
`C`, the target uses `C + 1`: with
`T = deltaG + sqrt epsilon + md/q`, one has `deltaG <= T` and hence
`deltaG + C*T <= (C+1)*T`.

## Statement Integrity

- Paper assumptions: the projective setting and the global measurement
  supplied by `lem:qld-4-7`, with its point-consistency estimate.
- Lean assumptions: the original `AdmissibleParams`,
  `0 <= epsilon <= 1`, `0 <= deltaG`, `ProjectiveSetting P epsilon`, and
  supplied `GlobalPairWitness S deltaG`, for either `PauliKind`.
- Paper conclusion: average consistency of Alice's original point measurement
  with Bob's pulled-apart measurement, after absorbing errors into `deltaS`.
- Lean conclusion: the same register ordering and uniform point distribution,
  bounded by `deltaConstructPaulis C epsilon deltaG P.m P.d P.q` for a
  universal constant. All public quantifiers and the error definition are
  unchanged.
- Verdict: exact preservation of the assigned Lean statement and its existing
  explicit error contract. This is a conditional use of a supplied witness;
  it does not prove the source-facing construction of that witness. The
  non-encoding mass estimate remains an unproved prerequisite.

A byte comparison of the target signature against the base succeeds. No
other existing theorem, definition, or proof body is changed. No blueprint
completion marker is added: the combined source lemma is not certified by
this reduction.

## Provenance and Prior Costs

The search covered all saved Git refs and the complete history of
`Extraction/Consistency.lean`. No completed proof of this target was found.
The reused `sum_marginalPoly_eval_mul` and
`marginalPoly_pointMeas_consistent_bob` originate in
`ba454653ecaa2d92821e9210b15e248c13b9c744` and its subsequent integration.
Their current implementations are reused through the local API.
The saved encoding-support construction at
`55ae74879dbf4452d04fb5c698e9f7636197dcf4` was also inspected; no divergent
branch was copied. The decoder algebra is reused from the current base.

The pre-session registry contains these related prerequisite efforts:

| Issue | External Sessions | Recorded Seconds | Recorded Output Tokens |
| --- | ---: | ---: | ---: |
| #243, marginal agreement | 4 | 4895 | 52393 |
| #245, register transport | 3 | 3432 | 62189 |
| #258, encoding support | 4 | 4972 | 68870 |
| #261, supported-mass comparison | 4 | 2669 | 68192 |
| Total | 15 | 15968 | 251644 |

Two additional historical native observations for #261 have unknown wall time
and usage; they are not counted as zero-cost sessions in the table. These
are prerequisite efforts, not fifteen prior attempts at this exact target.
The current session adds to this history; it does not reset any mathematical
gap budget. Its dispatcher records its actual time and token usage. Its
60-minute bound starts at `2026-09-12T05:00:49Z`. No subagent was launched.

## Validation and Remaining Work

Focused compilation of both changed Lean files passes with Lean/Mathlib
v4.32.0, the versions actually pinned in this checkout. The new module has no
warnings; `Consistency.lean` reports only its four unchanged direct holes.
The proof-integrity scan finds no added hole, axiom, or bypass. Whitespace,
new-module line width, and the worktree hook-installation check pass.

Fresh branch-private artifacts were used for the axiom audit. The three main
auxiliary lemmas and `tildeM_consistencyDefect_le_deltaG_add_nonencoding`
depend only on `propext`, `Classical.choice`, and `Quot.sound`.
`tildeM_consistent_pointMeas` additionally depends on `sorryAx` through
`nonencodingMarginalMass_le`, tracked by #517 and #47. The target's direct
hole is removed, but its axiom closure is not yet free of proof debt.

The four retained direct holes are `marginalPoly_sub_pointMeas_approx_zero`,
`nonencodingMarginalMass_le`, `tildeM_consistent_pointMeas'`, and
`tildeObs_selfConsistent`. Only the mass estimate is used by the target's new
proof. These declarations belong to other packets and are untouched.

Publication, exact-head local CI, and independent review are subsequent
workflow gates. This session does not launch a reviewer or merge the PR.
Issue #518 should remain open while #517 leaves the target's axiom closure
incomplete. The audit script is in the session's private checks directory
under `~/.cache/mipstarre-dev/sessions/`.

### First Published CI Run

PR #533 first tested `16ddc770ad0ed4511d1e63bea6a3d661997aec6a`.
The full build passed. Build-mode linting reported a flexible-tactic warning
in the new register calculation; the subsequent correction makes the same
simplification close its goal. The original file's `open scoped Classical`
warning predates this packet.

The blueprint-sync gate failed in the isolated model-policy dispatch fixture:
the invoking session's `MIPSTARRE_HARDNESS_REASON` was inherited by a routine
dispatch test. The model variables had been unset, but this associated
classification setting had not. The corrected invocation also unsets
`MIPSTARRE_JOB_CLASS` and `MIPSTARRE_HARDNESS_REASON`; no workflow code or
model policy is changed. The failed exact-head evidence remains on GitHub.
The isolated fixture passes with that environment, and the corrected auxiliary
module passes a focused check with `linter.mathlibStandardSet=true`.

## Failover Continuation

Session `prover-518-20260912-03` continues the same assignment. The first
session ended at 05:43:01Z after exhausted HTTP 503 retries; its dispatcher
records 2532 seconds, failure, and unknown token usage. These observations
remain unchanged and are not treated as zero cost. The separate failed
session `prover-518-20260912-02` records another 59 seconds and unknown usage
in the independent-attempt worktree. No descendant is launched here.

The continuation found new mathematical evidence in saved PR #543, commit
`e36fd1aa056782007917b0d6c5e19b85ea28179b`: the encoding-supported reference
comparison and non-encoding mass estimate have proofs without `sorryAx`.
Five necessary modules are recovered byte-for-byte from that commit:
`PairStateConsistencyTransport`, `PolynomialCollision`, `SupportMass`,
`DistanceTheorems.TensorConsistency`, and `NonencodingSupport`. Their earlier
provenance is retained in their documentation and in the #517 audit at that
commit. The encoding measurement and tensor API are already present in the
current base, so no replacement of those files is needed. The corresponding
Alice-side application in commit `6521816f` concerns issue #519 and is not
the target of this packet.

The target now uses the Bob-side reference estimate directly. It bounds the
non-encoding mass by `deltaG + C * sqrt epsilon + md/q`, adds the witness
error using the previously proved defect comparison, and absorbs the result
in `deltaConstructPaulis (C + 1)`. The separately owned declaration
`nonencodingMarginalMass_le` is unchanged and is no longer a dependency of
the target. The original signature, error definition, uniform distribution,
and player ordering remain unchanged. The statement-integrity verdict is
exact preservation of the assigned conditional theorem; construction of the
supplied global witness remains outside this result. No blueprint completion
marker is added for the other assertions of the source lemma.

Focused compilation of all five recovered modules and `Consistency.lean`
passes. A fresh artifact audit reports exactly `propext`, `Classical.choice`,
and `Quot.sound` for `tildeM_consistent_pointMeas` and its defect comparison.
The four unrelated direct holes remain unchanged. The signature matches the
assigned base byte-for-byte; the hook-installation check, whitespace check,
and recovered-module proof-integrity scan pass.

The cumulative active-work limit requires a publication checkpoint: fresh
exact-head full CI and independent review remain the next gates. Earlier
green CI at `3d412206` is historical evidence, not validation of this change.
