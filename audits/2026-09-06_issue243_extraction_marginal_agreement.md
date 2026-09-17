---
title: "Direct marginal agreement in extraction"
date: 2026-09-06
purpose: >
  Record the two given-witness marginal agreement estimates, their source
  restrictions, and the recovery validation of the persisted proof checkpoint.
issue: "#243"
---

# Issue #243: direct marginal agreement in extraction

Date: September 6, 2026. Session: `prover-243-20260906-01`.

## Scope and source

The Lean changes are confined to
`MIPStarRE/QPBT/Extraction/Consistency.lean`. No measurement definition,
witness field, existing theorem statement, import, or shared blueprint file
is changed. The packet proves only the two directed placements supplied by
the existing witness: Alice's marginal on `AA'` against Bob's expanded point
measurement on `BA''`, and Bob's marginal on `BB'` against Alice's expanded
point measurement on `AB''`.

The source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1617-1662`,
especially the agreement calculation at lines 1626–1637. The identity display
is labelled `eq:qld-sg-cons` in the mirror, not `eq:qld-sg-cons1`; the second
display is `eq:qld-sg-cons2`. This is a label clarification, not a change to
the mathematical statement.

The blueprint link is `lem:qld-constructing-the-paulis-helper` in
`blueprint/src/chapter/ch16_qpbt_extraction.tex`. The existing blueprint entry
describes all placements; none of the new restricted results should replace
its link to the full theorem. No blueprint tags are edited in this packet.

## Mathematical argument

Let the field be `PauliScalar P`, and let the question be a uniformly random
point in `Fin P.m → PauliScalar P`. Fix a Pauli basis. Denote the joint
polynomial-pair measurement by \(S\), its selected polynomial marginal by
\(S_g^W\), and its evaluation at a point \(u\) by
\[
Q_{u,a}=\sum_{g:g(u)=a}S_g^W.
\]
Selecting a component and then evaluating is the same finite postprocessing
as `evalAt W u`. This equality uses
`Quantum.Measurement.postprocess_comp`, not an assumption about the marginal.
Consequently the two witness fields `point_consistent_alice` and
`point_consistent_bob` give the stated consistency bound \(\delta_G\) for
the corresponding evaluated marginals.

Write \(Q_{u,a}\) and \(R_{u,a}\) for the placed evaluated marginal and
expanded point effects in either of the two directed placements. Agreement
of complete POVMs gives
\[
\mathbb E_u\sum_a\|(Q_{u,a}-R_{u,a})\widehat\psi\|^2
\leq 2\delta_G.
\]
The implementation uses `opFamilyDistSq_le_two_mul_consistencyDefect`, the
explicit-constant form of `fact:agreement` in
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-311`.

The evaluated joint measurement is projective by the existing theorem
`SandwichProduct.postprocess_isProjective`, applied directly to
`w.Smeas` and `w.projective`. The proof does not call or reimplement
`GlobalPairWitness.marginalPoly_isProjective`, which belongs to issue #240.
Projective absorption, implemented by
`opDistSq_sum_sub_mul_le_of_projective`, then gives
\[
\begin{aligned}
\|(I-\sum_a Q_{u,a}R_{u,a})\widehat\psi\|^2
&=\|\sum_a Q_{u,a}(Q_{u,a}-R_{u,a})\widehat\psi\|^2\\
&\leq\sum_a\|(Q_{u,a}-R_{u,a})\widehat\psi\|^2.
\end{aligned}
\]
This is `lem:cool-closeness-fact` in the same paper mirror, lines 364–380.
Finally, finite regrouping identifies \(\sum_a Q_{u,a}R_{u,a}\) with
\(\sum_g S_g^W R_{u,g(u)}\). Thus each direct identity estimate has bound
\(2\delta_G\), before any game-error or Schwartz–Zippel enlargement.
It is bounded by `deltaConstructPaulis 2 epsilon deltaG P.m P.d P.q`, since
the two additional terms in that expression are nonnegative.

The private placement support expresses the existing entrywise `S.place` as
tensoring with the identity followed by a finite coordinate equivalence. It
retains positivity, completeness, and projectivity. These are exact operator
identities; they assert no invariance of `psiHat` under moving an operator
between registers. In particular, they are not issue #115 transfer theorems.

## Declarations and prospective blueprint links

All eight public declarations support
`lem:qld-constructing-the-paulis-helper`; the last two formalize only its
explicitly restricted direct-placement instances.

- `GlobalPairWitness.marginalPoly_postprocess_eval`: evaluation/postprocessing identity.
- `sum_marginalPoly_eval_mul`: regrouping of the agreement sum.
- `marginalPoly_pointMeas_consistent_alice`: direct consistency with bound `deltaG`.
- `marginalPoly_pointMeas_consistent_bob`: reverse-player consistency with bound `deltaG`.
- `marginalPoly_pointMeas_approx_alice`: field-answer distance at most `2 * deltaG`.
- `marginalPoly_pointMeas_approx_bob`: reverse-player field-answer distance at most `2 * deltaG`.
- `sum_marginalPoly_pointMeas_approx_id_alice`: direct identity estimate at most `2 * deltaG`.
- `sum_marginalPoly_pointMeas_approx_id_bob`: reverse-player identity estimate at most `2 * deltaG`.

## Statement-integrity audit

- **Paper assumptions:** the standing admissible finite-field setting, a
  projective global polynomial-pair measurement, and its two point-consistency
  relations on the expanded state, as supplied by `lem:qld-4-7`.
- **Lean assumptions:** `P : AdmissibleParams`,
  `S : ProjectiveSetting P epsilon`, an existing
  `w : GlobalPairWitness S deltaG`, and `W : PauliKind`. No witness producer,
  extra consistency premise, transfer premise, or projectivity premise is added.
- **Paper conclusion:** the direct agreement sum resolves the identity on
  average, with a universally enlarged error; the coarse-grained comparison
  is also used in the proof of the annihilation estimate.
- **Lean conclusion:** the same two directed comparisons, with explicit
  squared-distance bound `2 * deltaG`. The new lemmas do not quantify over
  all directed opposite placements and do not assert same-side annihilation.
- **Verdict:** exact direct-placement restrictions, with explicit constants
  and faithful finite-dimensional encoding. They are not replacements for
  the unrestricted source theorem. The extra sign/range hypotheses of the
  full extraction scale are unnecessary for these stronger local estimates.

The signatures and retained proof bodies of all six pre-existing theorems
were compared textually with the initial `HEAD`: all are unchanged. The
A1–A6 check finds no conclusion-shaped input, altered measurement definition,
fallback branch, default witness, new axiom, or external-statement assumption.
The construction of a `GlobalPairWitness` is neither asserted nor used.

## Remaining obligations

All six original `sorry` occurrences remain; no new one is introduced.

| Declaration | Remaining argument and tracking |
| --- | --- |
| `sum_marginalPoly_pointMeas_approx_id` | Combine the new direct lemmas with the still-missing `BA''` versus `AA'` and `AB''` versus `BB'` register-transfer estimates, then choose a common constant. Existing tracker #47; placement-transfer work #115. No separate paper-gap note is currently cited by this declaration. |
| `marginalPoly_sub_pointMeas_approx_zero` | Use the proved field-answer comparisons, projective contraction, `expPoint_self_cons`, and the orthogonal fiber calculation to obtain the same-side annihilation estimates. Source lines 1637–1662; #47 and #115. The marginal projectivity declaration remains owned by #240. |
| `nonencodingMarginalMass_le` | Prove the non-encoding support estimate from point consistency and Schwartz–Zippel. Target is this named theorem; #47 and `docs/paper-gaps/qpbt_decoding-identity.tex`. |
| `tildeM_consistent_pointMeas` | Complete the first pulling-consistency calculation using `nonencodingMarginalMass_le` and the marginal absorption estimates. #47 and `docs/paper-gaps/qpbt_decoding-identity.tex`. |
| `tildeM_consistent_pointMeas'` | Complete the reverse-player pulling-consistency calculation using the same source-faithful support and absorption theorems. #47; the same decoding gap note applies. |
| `tildeObs_selfConsistent` | Complete the two measurement-consistency estimates and the final trace postprocessing to observables. Existing tracker #47; no separate paper-gap note is currently cited by this declaration. |

## Validation and cache provenance

The edited file passes `lake env lean MIPStarRE/QPBT/Extraction/Consistency.lean`
with only the six pre-existing proof-obligation warnings. The proof-hole scan
reports exactly six `sorry` occurrences and no axiom declaration. The
forbidden-token scan, the 100-character Lean line-length check, and
`git diff --check` pass.

The initial copied cache is older than the checked-out measurement sources:
it lacks `ProjectiveSetting.pointMeas_isProjective`,
`averageOperatorOverDistribution_smul_const`, `posSemidef_pauliProj`, and
`sum_pauliProj_eq_one`, despite their presence in the source. Its inherited
`pointMeasExp` has `sorryAx` in its axiom closure. This is not used as evidence
that the new declarations have an axiom-free closure.

Fresh validation uses a private copy of the project artifacts under
`~/.cache/mipstarre-dev/prover-243-20260906-01/lib`, with targeted recompilation
of the required current source modules. No shared package, hot-main artifact,
or worktree cache is modified. Logs and the axiom queries are in the same
session-private directory. The final fresh-artifact results are recorded below.

A full `lake build` is not run: this packet requests targeted checks, changes
no imports, and must not run the shared workflow. No CI, review, PR, merge,
main refresh, or additional agent session is initiated.

## Recovery validation: September 6, 2026

Session `orc-243-20260906-01` began at 11:53:27 +08:00 and recovered this
uncommitted checkpoint without changing the persisted Lean file. Its Git blob
is `289e86c6e04c4c80e8149aec5a851beda1af972e`; its SHA-256 is
`71ba183b2610ee06be0acd038e04561316c37e0c82bc5ce381720cd144963682`.
The preceding report is preserved; this dated supplement supplies the final
validation evidence that its prospective last paragraph did not contain.
The original brief is `local/briefs/243-extraction-marginal-agreement.md` in
the primary checkout. No PR number is known to this session, so the metadata
does not invent one.

### Targeted validation and dependency closure

The ordinary command
`lake env lean MIPStarRE/QPBT/Extraction/Consistency.lean` exits successfully,
with the six pre-existing proof-obligation warnings. The source scan finds
`sorry` only at lines 412, 443, 491, 522, 549, and 574, and no axiom
declaration. The six pre-existing theorem statements and proof bodies are
textually identical to those at base commit
`a61ee557b33a2d8a4721e92b08b6d06dcb69ed57`. The prohibited-token scan,
100-character Lean line-length check, and `git diff --check` also pass.

Because an ordinary type-check does not establish the freshness of imported
artifacts, the recovery makes a separate copy-on-write copy of the prior
session's private artifacts. In that copy it recompiles these current sources,
in dependency order:

- `MIPStarRE/LDT/Basic/DistributionAvg.lean`
- `MIPStarRE/QPBT/Algebra/Pauli.lean`
- `MIPStarRE/QPBT/Observables/Defs.lean`
- `MIPStarRE/QPBT/Observables/ExpandedDefs.lean`
- `MIPStarRE/QPBT/Combining/Witnesses.lean`
- `MIPStarRE/QPBT/Extraction/Defs.lean`
- `MIPStarRE/QPBT/Extraction/Observables.lean`
- `MIPStarRE/QPBT/Extraction/Consistency.lean`

This run completes successfully from 11:58:14 to 11:59:56 +08:00. It uses
`lake env` with the recovery-private `lib` directory prepended to `LEAN_PATH`,
and `lean -o` writes each artifact only there. The log records each source's
SHA-256. Other imported artifacts are reused; this is targeted validation,
not a full source rebuild or a claim that the whole repository has no holes.

The eight new public declarations listed above each have exactly the axiom
closure `[propext, Classical.choice, Quot.sound]`. Sixteen further axiom
queries, including `GlobalPairWitness`, `GlobalPairWitness.marginalPoly`,
`ProjectiveSetting.pointMeasExp`, the postprocessing and agreement lemmas,
and `ProjectiveSetting.psiHat`, have the same closure. Thus there is no
`sorryAx`, additional axiom, or unfinished transfer/projectivity theorem in
these new proofs' transitive axiom dependencies. This is a standard-axiom
closure, not an assertion that no axioms are used. The retained holes in
`Extraction/Defs.lean` and `Extraction/Observables.lean` still produce warnings
when those modules are compiled, but do not enter the eight new declarations.

Runtime evidence is preserved under
`~/.cache/mipstarre-dev/orc-243-20260906-01/`:
`default-typecheck.log`, `fresh-validation.log`, `Axioms.lean`, and
`DependencyAxioms.lean`. The predecessor's directory and captures are not
overwritten. No full build, cache refresh, publication, CI, independent review,
merge, or additional agent session is run. The installed normal Git hooks are
checked; the local commit is subject to those hooks without bypasses.

### Statement integrity and remaining scope

The source comparisons are `eq:qld-s-point-con-alice` and
`eq:qld-s-point-con-bob` of `lem:qld-4-7`, followed by `eq:qld-sg-cons` in
`lem:qld-constructing-the-paulis-helper`. Lean assumes an already supplied
`GlobalPairWitness S deltaG`, rather than proving its existence. Its two
point-consistency fields give precisely the two directed placements proved
here. The conclusion is the corresponding identity approximation, with
explicit squared-distance bound `2 * deltaG`. Verdict: faithful
finite-dimensional, given-witness direct-placement restrictions, not the full
source theorem and not a witness-construction result. No measurement or game
definition, source statement, or blueprint link is changed.

All six obligations in the preceding table remain. In particular, the
four-placement identity theorem and the same-side annihilation theorem are
not proved. No new source correction is proposed, no further proof attempt
on issue #118 is made, and its exhausted obligation is not reassigned to
issue #243. Owner decisions B7 and B8 remain pending. Future independent
review should first compare the two placement conclusions with the witness
fields and consult the fresh-artifact axiom results, not infer completion
from the unrestricted blueprint entry's existing `\leanok` tag.

### Time and usage evidence

The predecessor `prover-243-20260906-01` ran from 10:34:20 to 11:19:20 +08:00
on September 6, 2026 (ending at 03:19:20 UTC), then exited with timeout code
124 after 2700 seconds. The primary checkout's
`results/telemetry/sessions.jsonl`, line 733, records that failure with zero
usage fields and no completed turn. Those fields are not measured zero-token
work and are not rewritten here.

The predecessor's saved rollout has a last token-count event at
03:19:11.950 UTC: 8,047,278 input tokens, including 7,886,336 cached input
tokens; 42,659 output tokens, including 20,242 reasoning output tokens;
8,089,937 total tokens. These are the last observed cumulative counters, not
terminal usage. Their source is
`~/.codex/sessions/2026/09/06/rollout-2026-09-06T10-34-20-01a07491-1640-71e1-a4e1-7b36907863c9.jsonl`.

The recovery runs in the existing primary-account session, configured for
`gpt-6-astra` with effort `max` and a 900-second session timeout. Configuration
is not independent verification of the server's effort. Its live rollout
contains cumulative token-count events; terminal time and usage are available
only after the dispatcher finishes the session. No timeout or budget setting
is changed, and no new session is used to extend either proof attempt.
