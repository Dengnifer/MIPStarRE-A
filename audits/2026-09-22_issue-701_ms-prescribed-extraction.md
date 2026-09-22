---
title: Prescribed Magic Square extraction and separate agreement errors
date: 2026-09-22
status: pending-independent-review
track: paper2001qpbt
kind: statement-integrity-audit
issue: "#701, continuing #105, #172, and #688"
base: e3f224b90fb98d615c0210cdb3de7862f9d42819
session: mathfix-701-20260922-01
---

# Prescribed Magic Square Extraction

The two admitted construction targets are proved. A stronger theorem supplies
all seven prescribed-answer quantities with agreement entering only Alice's
two squared measurement distances. The original unrestricted assertion is
still false and remains unasserted. This evidence is for main's independent
review and adoption decision; the register remains pending.

## Source Defect

The printed theorem is `thm:ms-rigidity`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:620-652`.
For every arbitrary finite-dimensional tensor-product strategy of value
exactly `1-epsilon`, with a unit state, it asserts one pair of local
isometries and a unit auxiliary vector satisfying seven estimates: Euclidean
state distance, four answer-summed squared measurement distances, and two
squared anticommutator distances, all bounded by one universal multiple of
`sqrt(epsilon)`. The bit effects are the prescribed answers themselves.
The source's final state convention is ill-typed for transported operators;
the retained proposition explicitly reads those operators on the ideal state.

The independent-copy example wins perfectly in each orientation while
the players' bare-variable observables act on unrelated entangled copies.
Their correlations at both distinguished variables are zero, whereas exact
simultaneous extraction forces one. Anticorrelated role flags give the same
counterexample within symmetric projective strategies. Their same-player
anticommutators vanish. These constructions and every historical record in
`audits/2026-09-22_issue-688_ms-adoption.md` and the gap note are preserved.

The cited one-way LCS result is
`references/cs-paper/self-testing.tex:669-724`, instantiated at
`references/cs-paper/specific-games.tex:111-135`. It compares the constraint
player's constraint-read operators and the variable player's operators; it
does not compare the unused bare-variable family of the constraint player.

## Corrected Statements

Write `Delta_j` for the original-state completed-variable agreement
distance, `s` for the Euclidean state distance, and `dA_j,dB_j,aA,aB`
for prescribed-effect and prescribed-anticommutator squared distances on
the ideal state. Indices `0,4` in Lean correspond to paper variables `1,5`.

| Quantity | Bound from value at least `1-epsilon` |
| --- | --- |
| State `s` | `155904*sqrt(epsilon)` |
| Bob's two `dB_j` | `5*10^12*epsilon` |
| Alice's two `dA_j` | `15*10^12*epsilon + 6*Delta_j` |
| Both `aA,aB` | `4*10^12*epsilon` |

One witness satisfies all seven bounds. No agreement hypothesis occurs in
this separate-error statement: the actual defects appear in its conclusion.
The theorem `exists_ms_prescribed_rigidity_separate_errors` proves it.

The theorem `exists_ms_rigidity_prescribed_answers` has precisely the
existing robust theorem's value and two completed-agreement hypotheses.
It supplies all seven prescribed quantities at the common scale
`2*10^13*(sqrt(epsilon)+sqrt(delta))`, for all nonnegative parameters.

The completed one-way theorem `exists_ms_one_way_rigidity_with_constraints`
supplies the same state rate, Bob's completed-variable squared bounds
`2*10^12*epsilon`, and Alice's completed constraint-read squared bounds
`7*10^12*epsilon`, without a variable-agreement premise.
The separate prescribed-variable theorem uses the very same construction.
The constraint-read effects are explicitly completed by assigning malformed
single-bit answers to zero; they are not advertised as prescribed triple
submeasurements. Reversing player names gives the other orientation, allowing
a different witness. No theorem asserts simultaneous exact extraction of
both players' bare-variable families without agreement.

| Comparison | Paper | New Lean | Verdict |
| --- | --- | --- | --- |
| Strategy domain | Arbitrary finite spaces and POVMs, unit state | Same `Strategy msGame` | Faithful coordinate encoding |
| Winning assumption | Value equals `1-epsilon` | Value at least `1-epsilon` | Monotone strengthening, no extra proof input |
| Seven quantities | State norm; six squared operator distances | Same witness shape and prescribed quantities | Preserved |
| Uniform corrected theorem | No agreement hypothesis | Two explicit completed-variable agreement bounds | Restricted correction, separately labelled |
| Separate-error theorem | All bounds at `sqrt(epsilon)` | Value-only state/Bob/anticommutators; Alice has linear defect | Explicit changed guarantee on original strategy domain |
| Constraint comparisons | One-way cited self-test | Completed constraint reads, explicitly labelled | One-way scope and completion convention displayed |
| Existing public definitions/theorems | Inherited statements | No changes | Preserved, including #692's distinction |

## Correctness

Alice's first logical pair is read from cells 0 and 4 of row constraints
0 and 1; the second pair is read from cells 1 and 3 of those rows.
Bob uses the four corresponding variable observables. All cross-player
comparisons are sampled incidences, with norm bound `12*sqrt(epsilon)`.
Transferring Bob's first anticommutator gives Alice's bound
`(24+624+24)*sqrt(epsilon)=672*sqrt(epsilon)`. The inter-pair commutators
transfer with constant `24+96+24=144`. The established second-pair,
joint-swap and residual-normalization APIs give `2*116*672=155904`.

Bob's effect Gram identities remain valid with Alice's different isometry.
Compression and state transfer retain squared order `epsilon`, without
replacing it by `sqrt(epsilon)`. The ideal Pauli effects act equally on
the two EPR halves. Inserting the extracted actual state gives the proved
general comparison
`dA_j <= 24*s^2 + 3*Delta_j + 3*dB_j` for completed effects.
The tested forward-incidence squared distance is at most `72*epsilon`,
so the same comparison proves the constraint-read estimates.

For the wrong-form effect `R`, positivity, `R<=I`, and the existing
rejection estimate give `||R psi||^2 <= 36*epsilon`.
On the ideal state its squared action is at most `72*epsilon+2*s^2`.
Removing it at bit zero yields
`d_prescribed <= 2*d_completed + 144*epsilon + 4*s^2`.

Products use actual opposite-player constraint transfer.
`norm_product_via_opposite_le` writes
`R Z = R (Z-D) + D R`, where `D` is a contractive constraint
observable on the opposite register and hence commutes with `R`.
Thus `||R Z psi|| <= 18*sqrt(epsilon)`; the two errors on the right of
a product have bound `12*sqrt(epsilon)` each. The four-term
anticommutator perturbation costs `60*sqrt(epsilon)`.
The inherited completed bound `1183680*epsilon` gives norm at most
`1088*sqrt(epsilon)`, so the prescribed norm is at most
`1148*sqrt(epsilon)`. Its norm on any vector is at most eight times that
vector's norm. Transport therefore gives
`(1148*sqrt(epsilon)+8*s)^2` on the ideal state.

For the uniform corollary, use `epsilon_0=min(epsilon,1)`.
Nonnegative strategy value supplies the capped winning hypothesis;
`epsilon_0<=sqrt(epsilon)`. The complete two-outcome agreement distance
is at most eight, so `Delta_j<=delta` implies `Delta_j<=8*sqrt(delta)`
for every nonnegative `delta`. This handles large errors without a
well-formedness assumption or an unproved product certificate.

Adversarial cases checked in ordinary mathematics:

- Independent copies and their role-flag symmetrization have zero value error
  and nonzero agreement. They satisfy the separate-error theorem with
  nonvanishing Alice error and do not contradict it.
- Rotation about either distinguished Pauli axis isolates one agreement
  defect while preserving the other at zero and winning perfectly.
- At `epsilon=delta=0`, wrong-form effects annihilate the state and both
  players' prescribed comparisons and anticommutators are exact.
- Arbitrary malformed answers at nonzero error are included in the 36-times
  rejection bounds; no answer is removed from the verifier.
- Large `epsilon` or `delta` is covered by the proved cap argument.
  Zero-dimensional local spaces cannot support a unit strategy state.

No finite experiment is offered as a universal proof.

## Minimality

The rotations in the gap note give `Delta_1=1-cos(theta), Delta_5=0`
or the opposite pair, at perfect value. For any witness whose state and
Bob comparisons are exact, the ideal EPR actions identify Alice's error
vector with the transported cross-player difference. Consequently
`dA_j=Delta_j`, also for prescribed effects because malformed mass is
zero. A uniform `o(Delta_j)` bound is impossible with those value-only
exact conclusions. Linear dependence is sufficient and necessary in this
precise sense; no square root of agreement is needed in any conclusion.

There is also a sharp agreement order for the printed rates. For every fixed
nonnegative `L`, the conditions `Delta_j <= L*sqrt(epsilon)` suffice for
all seven bounds at `2*10^13*(1+L)*sqrt(epsilon)`, by the separate-error
theorem at `min(epsilon,1)`. Conversely, reverse wrong-form transfer gives
`d_completed <= 2*d_prescribed + 144*epsilon + 4*s^2`. Combining it with
the predecessor's reverse agreement estimate gives
`Delta_j <= 48*s^2 + 6*dA_prescribed + 6*dB_prescribed + 864*epsilon`.
The printed rates therefore force `Delta_j=O(sqrt(epsilon))` as epsilon
tends to zero. This order is necessary and sufficient up to universal
constants. An `O(epsilon)` agreement requirement is unnecessarily strong
for the printed squared-distance convention. This optimality comparison is
proved in ordinary mathematics; no separate Lean optimality theorem is claimed.

Removing either zero-error agreement condition while retaining the source's
simultaneous four-variable conclusion is false. Symmetry does not help.
A uniform agreement term in the state, Bob measurements, or anticommutators
is unnecessary by the construction. Adding same-cell edges would change the
game and is neither needed nor performed.

Optimal numerical constants and joint optimality of every value exponent
are not established. Main has not adopted a source correction or terminal
status. The optional averaged-agreement construction for the QPBT-induced
strategies also remains unassembled; the actual source consumer does not
need it.

## Sufficiency

The complete source use inventory in the #688 audit remains applicable.
A fresh literal search finds only the declaration and chapter 14 line 339
as occurrences of `thm:ms-rigidity`. The source use needs Bob's
original-state anticommutator, and its interchanged version needs Alice's.
Both prescribed original-state bounds are now also proved from value.
Their squared bounds are `O(epsilon)`, which supplies the printed
`O(sqrt(epsilon))` small-error use, with the constant norm cap handling
the complementary range. Averaging and the point-observable transfers
preserve the same downstream statement.

The full mathematical sequel is unchanged: chapter 14 lines 462-521
(`lem:qld-comm-cons`); 681-879 (combined points, including delayed proofs);
882-1034 (combined lines); 1035-1249 (sublines and claims 17-1/2/3);
1267-1411 (global polynomial pair); 1416-1860 (Pauli construction and swap);
1862-1877 and chapter 8 lines 1429-1491 (soundness and qubit form);
chapter 8 lines 1503-1563 (parameters and error bound); chapter 9 lines
1947-1981 and its uses at 1984, 1989 and 2275 (introspection).
Completeness via `thm:ms-from-ac` and low-degree soundness are independent.
The NEEXP same-cell game at secondary source lines 100-116 is not substituted.

The old explicit blueprint closure of `thm:ms-rigidity` still has just
that theorem and `cor:ms-rigidity-symmetric-consistent`. The twelve
`lem:ms-rigidity-support-*` nodes are proof inputs, not applications of
its conclusion. Their unchanged mathematical descriptions are covered by
the #688 inventory. The four new statement nodes are the prescribed
distance definition, one-way lemma, separate-error lemma and uniform
prescribed corollary, each with its actual scope displayed.

A fresh reverse-reachability computation using
`blueprint_citations.build_label_index` and `_active_lines`, over each
statement and attached proof span, gives 85 labels in the closure
of `lem:qld-ms-anticommutator-original-state`. This is the 81 statement
nodes listed in the predecessor audit, two equation labels inside their
spans, and the two new dependent prescribed statements. Here is the
complete current label set:

```text
cor:ms-rigidity-prescribed-answers
cor:pauli-binary
def:introparams
def:s-w-marginals
def:tilde-m-measurement
def:tilde-w-observables
def:v-swap-unitary
eq:qld-qxz-close-to-point
eq:qld-qxz-close-to-point-2
lem:claim-17-1
lem:claim-17-1-re-direct
lem:claim-17-2
lem:claim-17-3
lem:claim-17-3-re-direct
lem:combined-line-measurement-consistency
lem:combined-lines-given-points
lem:combined-points-unrestricted-error
lem:delta-bound
lem:direct-passing-value
lem:expanded-point-field-commutation
lem:ms-prescribed-separate-errors
lem:paired-subline-overlap-estimates
lem:pauli-extraction-state-distance-support
lem:pauli-extraction-state-error-form-support
lem:pauli-supplied-extraction-error-form-support
lem:qld-4-10
lem:qld-4-10-same-placement
lem:qld-4-12
lem:qld-4-13
lem:qld-4-13-established
lem:qld-4-13-established-given-points
lem:qld-4-7
lem:qld-combined-point-x-marginal-distance
lem:qld-combined-point-z-marginal-distance
lem:qld-comm-cons
lem:qld-completed-point-self-consistency
lem:qld-conditioned-completed-point-self-consistency
lem:qld-construct-the-paulis
lem:qld-construct-the-paulis-given-global-pair
lem:qld-constructing-the-paulis-helper
lem:qld-evaluated-pauli-given-global-pair
lem:qld-extraction-error-form
lem:qld-first-route-overlap-components
lem:qld-large-error-extraction-given-global-pair
lem:qld-line-conditioning-restoration
lem:qld-line-point-marginal-identities
lem:qld-ms-anticommutator-original-state
lem:qld-nonencoding-mass-bound
lem:qld-opposite-ordered-products
lem:qld-paired-line-restored-defect
lem:qld-point-line-marginal-bounds
lem:qld-point-self-consistency-defect
lem:qld-sandwich-consistency-defect
lem:qld-sandwich-orthonormalization
lem:qld-sandwich-povm
lem:qld-state-extraction-given-global-pair
lem:qld-supplied-scalar-point-measurement
lem:qld-unitary
lem:qld-unitary-given-global-pair
lem:qld-win-implications-obs
lem:qld-x-point-overlap-deficit
lem:qld-xz-lines
lem:qld-xz-lines-restricted
lem:s-w-marginals-projective
lem:subline-joint-overlap
lem:tilde-m-projective
lem:tildew-product-form
lem:v-swap-conjugation
thm:pauli
thm:pauli-arbitrary-strategy-isometry-support
thm:pauli-arbitrary-strategy-raw-isometry-support
thm:pauli-concrete-isometry-transfer-support
thm:pauli-extraction-alice-distance-support
thm:pauli-extraction-bob-distance-support
thm:pauli-extraction-isometry-construction-support
thm:pauli-extraction-transferred-range-support
thm:pauli-projective-setting-isometry-support
thm:qld-completed-pair-actual-error
thm:qld-direct-line-real-overlap
thm:qld-rounded-polynomial-ordered
thm:qld-rounded-scalar-linearity
thm:qld-rounded-separated-mass
thm:qld-rounded-wrong-variable-mass
thm:qld-supplied-direct-polynomial-consistency
thm:qld-supplied-scalar-polynomial-consistency
```

The Lean source consumers remain
`Observables/WinImplications/AnticommutingObs.lean`,
`TwistedCommutation.lean`, `InterchangedCommutation.lean`,
`Observables/WinImplications.lean`, `ExpandedCommutation.lean`,
combined points/lines, `exists_globalPairWitness`, and the extraction
chain to `pauli_soundness` and `pauli_soundness_qubit`.
No existing caller invokes the new corrected extraction theorem.
The only added import consumer is `MIPStarRE/QPBT.lean`, hence the root.
All newly affected downstream support modules are explicitly re-elaborated.
Other paper-gap rows are not certified by this relative sufficiency argument.

## Lean Evidence

There are 46 new mathematical declarations in eight support files and a
ninth Lean file containing six executable axiom checks. No existing theorem
signature, mathematical definition, game, paper mirror, or unrelated proof
is edited. The facade change is one import.

Every new support file passed `lake env lean`, in dependency order.
Importable products were emitted with `-o` solely into this worktree's
private `.lake/build`. The focused `PrescribedAudit.lean` checks the
one-way constraint theorem, agreement transfer, both original prescribed
anticommutators and both seven-bound theorems. Each axiom set is exactly
`propext, Classical.choice, Quot.sound`. The existing 13-headline
`Test/AxiomAudit.lean` also passes. The original facade, winning
implications, QPBT umbrella and repository root are checked separately.

The note style check and its 20-page PDF build pass; the final PDF log has
no undefined references/citations. `leanblueprint web` exits zero; its
fresh-checkout bibliography file is absent, producing bibliography warnings.
The static blueprint convention check uses `--root blueprint/src`.
Declaration sync is regenerated after the web build, which rewrites the
generated declaration list. The inherited four orphan tags and two missing
proof marks are reported, not changed.

The initial umbrella check needed the parent's unbuilt `PrintedClaim.olean`;
checking that unchanged source into the private build directory resolved it.
An initial convention-check invocation used the repository root and therefore
reported paper-mirror cleveref commands; rerunning on the documented blueprint
source root passed. An intermediate sync check saw the web-generated expanded
list; regeneration after web resolves that artifact-ordering issue.
These are recorded failed diagnostics, not unreported successful checks.

No full `lake build` was run. Full CI, independent review and publication
are main's remaining gates. The receipt records the final declaration-check,
sync, hook and commit results.

## Budget And Operator Record

This is one expressly admitted Astra `mathfix` construction session with
a 3600-second wall cap, starting `2026-09-22T22:04:25+09:00`, under
`/tmp/main-ms-prescribed-packet-20260922.md`. The deadline is
`2026-09-22T23:04:25+09:00`. No extension is inferred.

All predecessor work and costs are retained. The #688 audit lists 21 owner
registry rows for #105/#172: 17 numeric duration fields total 40594 seconds
and four durations are unknown. That is a field subtotal, not a deduplicated
budget. Original anchors remain `2026-09-04T12:04:10Z`,
`2026-09-04T15:24:39Z`, and the Fable mathematical attempt at
`2026-09-04T22:38Z` with 3562 recorded seconds. The original proof commits,
negative attempts, PR192/217 reviews and repairs remain untouched.

The current later registry rows retain:
`orc-688-20260922-01` 2067 seconds,
`orc-688-20260922-02` 915 seconds,
`reviewer-pr692-20260922-02` 415 seconds,
`reviewer-pr692-20260922-01` 418 seconds, and
`blueprint-688-20260922-01` 632 seconds.
Their subtotal is 4447 seconds; with the earlier numeric fields this is
45041 seconds, still not a complete or deduplicated aggregate.
All additional/unknown historical costs remain chargeable. A globally
deduplicated cumulative attempt count and elapsed total are unavailable;
this tranche does not reset them. The dispatcher's final duration and usage
are authoritative for this session.

The primary duplicate checker found no existing declarations for
`exists_ms_one_way_rigidity`, `exists_ms_rigidity_prescribed_answers`,
or `exists_ms_prescribed_rigidity_separate_errors` on `github/main`.
These names, their constraint/agreement variants, and the support declarations
are owned by this isolated assignment. No shared declaration-registry or
runtime mutation was made under the worktree-only/no-collaboration restriction;
main can reconcile registry entries before publication.

Suggested one-line #27 record, not posted:
"Issue #701 proves prescribed Magic Square extraction with value-only state,
Bob and anticommutator errors and linear Alice agreement errors; adoption
remains pending full CI and independent review."

Main owns any event/design-decision entries, adoption, publication and review.
There is no owner-permission blocker and no #500 action. No subagent,
collaboration tool, direct Codex, proxy, alternate credential, cache write,
hook skip, push or merge was used.
