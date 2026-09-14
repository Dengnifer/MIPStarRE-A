---
title: "Point consistency and the global measurement construction"
date: 2026-09-12
purpose: >
  Record the final supplied-witness proof and the source-facing construction
  obligation after the statement-faithfulness repair for issue 519.
issue: "#519"
pr: "#539"
---

# Point Consistency and the Global Measurement Construction

## Scope

This audit describes the repair of review `5194106099` at published head
`08ffce99c3076bbfe0783363a5202d23298552ab`. It covers
`Extraction/Consistency.lean`, the supplied-witness documentation in
`Extraction/NonencodingSupport.lean`, the paired source node in
`blueprint/src/chapter/ch16_qpbt_extraction.tex`, its declaration list, and
`docs/paper-gaps/qpbt_decoding-identity.tex`. The only incident-ledger deletion
is the empty PR532 heading immediately preceding the PR531 incident.

The mathematical proof retained from issue #519 is Alice's pulled-apart
measurement versus Bob's original point measurement. The witness constructor
and the other source components are not proved by this repair.

## Source of Truth

The primary source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`:

- `lem:qld-4-7`, lines 1267-1274, constructs the global projective
  polynomial-pair measurements, with universal error constants.
- `lem:qld-construct-the-paulis`, lines 1463-1480, asserts both
  point-consistency conclusions and observable self-consistency for the
  measurements constructed from that same pair.
- Lines 1483-1492 give the point-consistency calculation and its symmetric
  counterpart. The decoder substitution needs the correction explained in
  `docs/paper-gaps/qpbt_decoding-identity.tex`.
- The setting at lines 197-199 includes zero error. The current constructor
  `exists_globalPairWitness` assumes strictly positive error and is unfinished.

The blueprint source node is `lem:qld-construct-the-paulis`. The separate
Lean-only node is `lem:qld-construct-the-paulis-given-global-pair`.
The conventions are `AGENTS.md`, `docs/formalization-patterns.md`,
`docs/paper-gaps/proof-gap-protocol.tex`, and
`audits/2026-04-29_audit-document-format.md`.

## Findings

**F1: conditional proof and source construction.** The proved result is now
`tildeM_consistent_pointMeas'_ofGlobalPairWitness`. Its signature and proof
are preserved apart from the conditional name. For a supplied witness it
proves, with universal `C >= 1`,

\[
 \operatorname{Defect}(\widetilde M_{\mathrm A},M_{\mathrm B})
 \leq 2\delta_G+C\sqrt\epsilon+md/q
 \leq (C+1)(\delta_G+\sqrt\epsilon+md/q).
\]

The proof uses the exact register regrouping and decoded-overlap calculation
from `PointConsistencyPrime.lean`. For encoding outcomes the decoded value
equals polynomial evaluation. Positivity and completeness control the other
outcomes by their marginal mass. The encoding-supported reference gives
evaluated consistency at `deltaG + C * sqrt epsilon`; Schwartz-Zippel adds
`md/q`. The theorem invokes these estimates directly. It does **not** use
`nonencodingMarginalMass_le` or `exists_globalPairWitness` in its proof.

The paired first orientation and observable estimate have also been renamed
`tildeM_consistent_pointMeas_ofGlobalPairWitness` and
`tildeObs_selfConsistent_ofGlobalPairWitness`. Their existing holes remain.
All three carry the required `**Unfaithful:**` explanation of the supplied
witness and belong only to the conditional blueprint entry, without a
completion marker. In particular, the unproved Alice-point/Bob-pulled
component is not advertised as the source theorem.

The source-facing `exists_pulled_apart_consistency` quantifies universal
`a`, `b`, and `C` before all parameters and strategies. It outputs one
`GlobalPairWitness` at `deltaQld a b epsilon m d q`, and both point
estimates and observable self-consistency hold for that same witness with
one common construction constant. This is the joint source construction,
not a separate existential measurement for each basis or conclusion.
Its tracked `sorry` preserves the nonnegative-error domain. Using the
existing constructor directly would restrict the statement to positive
error. The repair does not make that restriction or attempt its discharge.

**F2: supplied-witness auxiliary.** The docstring of
`global_marginal_encoding_consistency` now explicitly records its
`GlobalPairWitness` premise and use of both point-consistency fields. It
does not claim to construct the witness. Its proof is unchanged.

**F3: final-state audit.** This document replaces the superseded account in
which the target called the unfinished mass estimate. That was an earlier
implementation, not the dependency structure at the published review head
or after this repair. Historical source provenance and cumulative costs
remain recorded below; they are not evidence of source-theorem completion.

**F4: incident attribution.** Only the orphaned empty PR532 heading is
removed. The PR531 and actual PR532 incident bodies and all session records
are preserved.

### Statement Integrity

| Comparison | Paper | Final Lean statement |
| --- | --- | --- |
| Assumptions | Admissible parameters; projective passing strategy in the expanded setting | `AdmissibleParams`, `ProjectiveSetting P epsilon`, `0 <= epsilon <= 1` |
| Construction | Global pair obtained from `lem:qld-4-7` with universal constants | Witness is an output at `deltaQld`; `a`, `b`, `C` precede the strategy |
| Conclusions | Both point consistencies and observable self-consistency for that pair | Same pair, placements, bases, and uniform question distributions for all three |
| Error | Source absorbs the construction losses into its enlarged error | Common `deltaConstructPaulis C epsilon deltaG m d q`, as documented in the blueprint and gap note |

Verdict: the source-facing obligation has faithful boundary hypotheses in
the blueprint's probability-error domain and the documented corrected error
scale. It has no supplied witness or other bridge premise. It is an open
proof obligation, not a proved source theorem. The three supplied-witness
statements have **extra assumptions** relative to the source construction
and are explicitly conditional. The vacuous basis-index quantifier on the
point estimates is omitted; the observable estimate retains it.

## Required Action

The statement repair is complete; the following mathematical obligations
remain open and are not discharged by the conditional proof:

| Declaration | Remaining obligation |
| --- | --- |
| `exists_pulled_apart_consistency` | New realignment hole, issue #519: construct a common global pair, including zero error, and assemble all three estimates. |
| `exists_globalPairWitness` | Existing hole in `Combining/Apply.lean`: the source construction of `lem:qld-4-7`; extend its domain to zero error for the source-facing composition. |
| `tildeM_consistent_pointMeas_ofGlobalPairWitness` | Retained hole: Alice-point/Bob-pulled calculation using the opposite marginal reference and mass comparison. |
| `tildeObs_selfConsistent_ofGlobalPairWitness` | Retained hole: the pulling argument at lines 1495-1605 and trace postprocessing. |
| `marginalPoly_sub_pointMeas_approx_zero` | Unchanged hole: same-side projection-contraction and point self-consistency at lines 1637-1662. |
| `nonencodingMarginalMass_le` | Unchanged hole: assemble the general two-sided mass estimate from reference consistency and Schwartz-Zippel. It is not a dependency of the proved conditional target. |

The four retained holes in `Consistency.lean` remain tracked by issue #47
and their existing source citations. The source obligation's docstring and
the gap note name the construction and conditional theorems that discharge
its new hole. No new axiom, generic assumption structure, or kernel bypass
is introduced. The constructor is not edited in this repair.

## Validation

The primary `worktree-setup.sh --no-build` and hook verification passed.
The actual toolchain in this checkout is Lean/Mathlib v4.32.0.
Focused checks of both edited Lean files pass; `Consistency.lean` reports
the four retained holes and the one documented realignment hole.
After regenerating the two edited modules' branch-private artifacts,
fresh axiom queries report only `propext`, `Classical.choice`, and
`Quot.sound` for `tildeM_consistent_pointMeas'_ofGlobalPairWitness`,
`global_marginal_encoding_consistency`,
`mass_outside_encoding_le_evaluated_defect`, and
`tildeM_consistencyDefect_le_deltaG_add_nonencoding'`.
The source obligation, the opposite conditional orientation, observable
self-consistency, `nonencodingMarginalMass_le`, and
`exists_globalPairWitness` additionally report `sorryAx`.
The query and output are in the worktree's ignored
`.lake/issue519-checks/Axioms.lean` and `axioms.log`.

`blueprint_lean_sync.py --update-lean-decls --ci` passes and regenerates the
ignored declaration list. Its warnings concern other source nodes with
statement-only completion markers. The paper-gap style check,
`git diff --check`, and the 100-character Lean line check pass.
`leanblueprint web` completes with bibliography warnings. The cached
declaration checker, invoked as
`lake env .lake/build/bin/checkdecls blueprint/lean_decls`, resolves all
1681 references in the list generated by that web build.
No full build, CI, independent review, or publication is performed by this
repair delegate; those gates remain with MAIN.

## Historical Provenance and Costs

The original session was `prover-519-20260912-01`, starting at
`2026-09-12T05:31:23Z` from `ae124f8f09ee002444ac5b9711822c0f1daae142`.
The opposite-order calculation came from commit
`16ddc770ad0ed4511d1e63bea6a3d661997aec6a` (#518), with
`PointConsistency.lean` recovered from blob
`08d862f0857e16046c0e3126dc494c64c9e31c30`. Its terminal `first` tactic
was replaced by `ac_rfl` for linter compatibility. The Alice-side extension
is in `PointConsistencyPrime.lean`.

Support content recovered from `e36fd1aa056782007917b0d6c5e19b85ea28179b`
(#517) includes `EncodingSupport.lean` and the tensor measurement API
(`55ae7487`), `PolynomialCollision.lean` (`36c07381`), `SupportMass.lean`
(`ff4c92d1`), `TensorConsistency.lean` (`84c7ec43`),
`PairStateConsistencyTransport.lean` (`7f916eb8`), and
`NonencodingSupport.lean` (`e36fd1aa`). The other packet's target,
blueprint, audit, and gap-note edits were not copied. The final conditional
proof already used this support content at the published review head.

The original audit recorded these prerequisite costs from the registry:

| Issue | External sessions | Recorded seconds | Recorded output tokens |
| --- | ---: | ---: | ---: |
| #243, marginal agreement | 4 | 4895 | 52393 |
| #245, register transport | 3 | 3432 | 62189 |
| #258, encoding support | 4 | 4972 | 68870 |
| #261, supported-mass comparison | 4 | 2669 | 68192 |
| Total | 15 | 15968 | 251644 |

These are prerequisite costs, not fifteen attempts at this target. Two
historical native observations for #261 have unknown time and usage. The
owner-reported prior #519 admission attempt acquired no reservation; its
elapsed time and usage were unknown, not zero. The #517 and #518 efforts,
the original #519 session, and this bounded repair are additional costs.
No prior budget or session record is reset. MAIN owns completion accounting.

The original premature publication and inherited-hardness CI incidents
remain in `results/telemetry/events.md`. They are historical workflow
records, not validation of this repair.

## Review Use

Check the conditional signature and axiom closure independently of the
source obligation. A kernel-checked theorem with an explicit global witness
does not prove that the witness exists. Confirm that the source node has no
`leanok`, that it requires the same constructed pair for all three
conclusions, and that the zero-error case has not disappeared. Future
proof work should discharge the named obligations before claiming source
completion; preserving only the already-proved conditional estimate is
insufficient.
