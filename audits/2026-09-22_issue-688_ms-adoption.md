---
title: Magic Square rigidity adoption evidence
date: 2026-09-22
status: pending-adoption
track: paper2001qpbt
kind: statement-integrity-audit
issue: "#688, continuing #105 and #172"
base: 7a5aba592bf1b944c168b1a3ff8e3dcc5f13f3e8
session: orc-688-20260922-01
---

# Magic Square Rigidity Adoption Evidence

The unrestricted printed extraction assertion remains false. This change
retains it as `PrintedMagicSquareRigidityClaim`, including its prescribed
answers, and supplies the missing comparison with the proved robust theorem.
It does **not** certify a terminal correction. The anticommutation assertion
actually used in soundness is already proved from winning probability alone;
neither its proof nor its consumers need the extra agreement hypothesis.

The assignment is the 3600-second evidence tranche admitted at the base above
in `/tmp/main-ms-adoption-packet-20260922.md`. There is no extension or restart
of the historical mathematical budget. Only the Magic Square gap note, this
audit, and the new retention module are changed. Main owns publication, full
CI, independent review, and any adoption decision.

## Statement Comparison

The primary source is
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:620-652`,
`thm:ms-rigidity`. The game is specified at lines 512-578. The cited theorem
uses the one-way LCS convention in
`references/cs-paper/self-testing.tex:669-724`, with its Magic Square instance
in `references/cs-paper/specific-games.tex:111-135`.

| Form | Hypotheses | Conclusion | Verdict |
| --- | --- | --- | --- |
| Printed theorem | Arbitrary finite-dimensional tensor-product strategy, unit state, value exactly `1-epsilon` | One pair of local isometries, two EPR pairs, unit auxiliary state; Euclidean state bound and four squared bit-effect bounds, plus two squared anticommutator bounds, all at `O(sqrt(epsilon))` | Refuted, including within symmetric projective strategies |
| `exists_ms_rigidity` | Arbitrary `Strategy msGame`, nonnegative `epsilon,delta`, value at least `1-epsilon`, completed-bit agreement defects at cells 0 and 4 at most `delta` | Same witness shape, seven bounds at `2*10^12*(sqrt(epsilon)+sqrt(delta))`, using completed bit effects | Proved; extra agreement assumptions and enlarged error, with an additional answer-representation comparison |
| `exists_ms_rigidity_of_symmetric_consistent` | Symmetric projective strategy consistent at every question, winning bound | Seven completed-bit bounds at `C*sqrt(epsilon)` | Proved scope restriction; not the unrestricted source theorem |
| `WinImplications.msVarObs_anticommutator_le`, `msVarObsA_anticommutator_le` | Arbitrary strategy, nonnegative `epsilon`, winning bound | Each player's original-state completed-variable anticommutator has squared norm at most `1183680*epsilon` | Proved source-faithful auxiliary for the actual soundness use; prescribed-answer transfer is explained in the note |
| `PrintedMagicSquareRigidityClaim` | Exactly the printed value hypothesis over the existing arbitrary-strategy domain | All seven source bounds, directly on `MsAnswer.bit b` effects and their differences | Unasserted `Prop`; no agreement, symmetry, projectivity, or zero-error restriction |

One common constant at least one faithfully encodes the finitely many universal
big-O constants. The new definition keeps the printed equality rather than
quietly substituting a lower bound. The proved lower-bound formulation is not
the obstruction: success probabilities lie in `[0,1]` and all errors are
monotone, so an exact-value theorem would imply the lower-bound version by
using the actual loss.

There are two explicit representation boundaries. Local spaces use finite
coordinate types, and the anticommutator is read on the ideal extracted state,
as are the preceding four source estimates. The last generic convention in
the source instead names the original state; the transported operators cannot
act on that space. The new docstring identifies this typing correction. It
does not describe literal equality with that ill-typed sentence.

The existing `msOperatorDistanceA/B` and `msAnticommutatorDistanceA/B` cannot
be reused to retain the prescribed-answer claim: they call `msBitOrZero`,
which adds every triple answer to bit zero. The new definition writes the
prescribed effects explicitly. Wrong-form answers remain in the original
strategy and its acceptance probability; no answer or game is deleted.

## Counterexamples and Minimality

The original negative evidence is preserved in
`audits/2026-09-04_magic-square-rigidity-orientation-obstruction.md` and in
sections 4-6 of the gap note. On two independent perfect copies, Alice's
constraint/Bob's variable orientation uses copy 1 and the reversed orientation
uses copy 2. Both orientations win with probability one. The two players'
distinguished variable observables act on independent maximally mixed
registers, so their correlations are zero and both agreement defects are one.
Exact joint extraction and the four ideal-variable comparisons would force
both correlations to equal one. Anticorrelated role flags make the strategy
symmetric without altering the contradiction. Same-player anticommutation is
exact throughout these examples.

The new rotation calculation in the gap note also separates the two agreement
conditions. On the canonical EPR state, leave Alice's constraints and Bob's
variables fixed, rotate Alice's variable solution by
`exp(-i theta Z/2)` on the first qubit, and rotate Bob's constraint solution by
the conjugate unitary. Both orientations still win perfectly, while
`Delta_1 = 1-cos(theta)` and `Delta_5 = 0`. Rotation about `X` gives the
opposite example. Thus neither condition can be omitted at zero error.

Necessity of agreement does not prove necessity of the uniform error function.
With extracted actual state `Psi'`, ideal state `Theta`, state distance `s`,
and squared effect distances `d_A,j,d_B,j`, the note proves

```text
Delta_j <= 24*s^2 + 3*d_A,j + 3*d_B,j
d_A,j   <= 24*s^2 + 3*Delta_j + 3*d_B,j.
```

The constants follow by inserting `Psi'`, using equality of the two ideal
Pauli effects on `Theta`, and applying the three-term squared triangle
inequality in the direct sum of the two outcome spaces. Each difference of
the transported contractions has norm at most two. These statements concern
complete binary effects; the prescribed-answer comparison is separate below.

The printed bounds therefore force agreement of order `sqrt(epsilon)` by this
calculation, not order `epsilon`. A one-way extraction with state bound
`O(sqrt(epsilon))` and Bob's squared effect bound `O(sqrt(epsilon))` would
give Alice's squared effect bound `O(sqrt(epsilon)+Delta_j)`. The state and
Bob's bounds would not depend on `delta`. At zero error, the rotation example
already realizes state and Bob errors zero and Alice error `Delta_j` with the
identity isometries. No globally sharp exponent is claimed by that example.

The proved uniform `sqrt(epsilon)+sqrt(delta)` bound is sufficient, but its
minimality is not established. It recovers the printed rate through
`delta=O(epsilon)`, which is not a hypothesis of the printed standalone game.
At zero error it recovers the printed conclusion only on the proper subclass
with both defects zero. Quantifying `delta` freely does not fix this: choosing
`delta=1` covers the independent-copy example only with a nonzero error at
perfect winning probability. This is a weaker guarantee than the source's.

## Every Source Use

A literal label search through all of `references/` finds exactly one
invocation of `thm:ms-rigidity`, at chapter 14 line 339, besides its declaration.
The introductory prose at chapter 8 lines 612-618 announces its use for
soundness but does not make another mathematical application. The following
inventory follows both the named references and the delayed proofs, which a
search confined to the next `proof` environment would miss.

In this table, chapter 8 is
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex`, chapter
14 is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`, and
chapter 9 is `references/qpbt-paper/09_introspection_games.tex`.

| Source location | Use and sufficient replacement |
| --- | --- |
| Chapter 8, 512-618, 620-652 | Both orientations of the same constraint-variable game; one-way cited self-testing does not constrain the other player's bare-variable family. Preserve the full printed assertion unasserted. |
| Chapter 14, 160-172, 197-265 | General strategy and projective dilation; items 1, 6, 7 provide consistency, induced Magic Square value, and point-variable comparisons. `M` denotes both measurement families for notation, not symmetry. The final clause supplies the reversed orientation. |
| Chapter 14, 267-362, especially 326-350 | `len:qld-win-implications-obs`, `eq:qld-implication-ms-anticomm`: only Bob's original-state anticommutation is used. Its Alice counterpart supplies the interchanged conclusion. The value-only bound gives `O(epsilon)` after averaging and hence the requested `O(sqrt(epsilon))` for small error. Product transfer yields the point relation. |
| Chapter 14, 462-521 | `lem:qld-comm-cons`: multiply the point observables by ideal Pauli observables, whose exact phase cancels the tested phase. No joint Magic Square extraction witness is used. |
| Chapter 14, 681-879 | `lem:qld-4-10`, including its delayed proof beginning at 729: the same expanded commutation bound supplies sandwich consistency, rounding, and approximate linearity. The independent linearity theorem is an input, not a use of Magic Square extraction. |
| Chapter 14, 882-967, 993-1034 | `lem:qld-xz-lines`, `lem:qld-4-12`, `lem:qld-4-13`: combined measurements use the preceding point contract and the separate line contract. Their incoming Magic Square-derived error and both placements are unchanged. |
| Chapter 14, 1035-1249 | Restricted lines, `lem:qld-sublines`, and the delayed proof of `lem:qld-4-13`, including `claim:17-1`, `claim:17-2`, `claim:17-3`: no further use of extraction or agreement. Their separate sampling and error obstructions are not discharged by this audit. |
| Chapter 14, 1267-1411 | `lem:qld-4-7`: global polynomial pair and point consistency use the combined measurements, with the same incoming bounds. |
| Chapter 14, 1416-1860 | `lem:qld-construct-the-paulis`, `lem:qld-constructing-the-paulis-helper`, `lem:qld-unitary`: spectral marginals, pulling consistency, EPR extraction, and swap conjugation use the global pair and expanded consistency. None requests an `MsRigidityWitness`. |
| Chapter 14, 1862-1877; chapter 8, 1429-1491 | The delayed proof of `thm:pauli-appendix`, hence `thm:pauli`, and `cor:pauli-binary`: unchanged extraction inputs and final error family. The intervening chapter 8 prose at 1447, 1450, 1460 explains this same transition. |
| Chapter 8, 1503-1563 | `def:introparams`, `lem:delta-bound`: use only the unchanged universal constants and final error formula. The related complexity construction uses these parameters, not Magic Square rigidity. |
| Chapter 9, 1947-1981 | `lem:intro-pauli-strat`: uses `cor:pauli-binary` and `lem:delta-bound` to replace the tested strategy by one with Pauli measurements. Its later uses at 1984, 1989, 2275 have exactly that unchanged contract; there is no added agreement premise. The other `lem:delta-bound` references at 202 and 1083 use the same scalar bound. |

This is a substitution argument for the contribution of this one gap to the
entire sequel. It does not claim that every other source assertion in that
sequel is true: the line, divisibility, scalar-error, and other register rows
retain their own status and obligations.

The adjacent construction `thm:ms-from-ac` is independent. Its uses at chapter
8 lines 952, 1351, 1366, 1381, 1409, 1417 concern honest strategies and
completeness. It constructs a consistent perfect Magic Square strategy from
given anticommuting observables; it is not rigidity of an arbitrary strategy.

The secondary mirror,
`references/neexp-paper/07_a_self_test_for_the_pauli_basis.tex:94-116`, refers
to the binary self-test used by NV and explicitly adds same-cell consistency
questions in its oracularized variant. It has no reference to the primary
`thm:ms-rigidity`. Those added questions would exclude the independent-copy
example, but replacing `msEdges` by that graph would change the primary game.
No such substitution is authorized or performed.

## Agreement in the Soundness Application

The robust extraction route is also mathematically sufficient for the sole
source use. Let `P_A,P_B` be the trace-postprocessed point measurements and
`V_A,V_B` the corresponding completed variable measurements at a tuple. On the
conditional anticommuting distribution, compare

```text
V_A  --  P_B  --  P_A  --  V_B.
```

The first comparison uses item 7 with factors interchanged, the last uses
item 7 as stated, and the middle uses item 1 after conditioning and projective
coarse-graining. The squared three-term triangle inequality bounds the
average variable defect by three times the sum of those averaged squared
distances. Conditioning costs a universal factor: the formal tuple law has
the uniform positive bound proved at `fact:omega-anticomm-prob`. The point
question type also has fixed positive probability. For projective
measurements the squared effect distance is twice the disagreement mass;
coarse-graining deletes nonnegative disagreement terms. This is not a claim
of distance monotonicity for arbitrary POVMs.

The swapped estimate is transported back by the tensor permutation, an
isometry, with both operators exchanged as well. For either bit, the
observable/effect conversion contributes the factor two from
`A_b=(I+(-1)^b O_A)/2`. Thus both defects have conditional mean `O(epsilon)`.
Taking `delta_omega=Delta_1+Delta_5` and applying finite Jensen to both square
roots preserves `O(sqrt(epsilon))` after averaging. This construction requires
no symmetry of the strategy.

The named assembled mean-defect theorem is **not** asserted to exist in Lean.
Its exact optional target is a universal bound on
`avgOver (anticommTupleDist P) (fun omega =>
msVariableConsistencyDefect (S.msStrategyAt omega) j)` for `j=0,4` by
`C*epsilon`, for every `ProjectiveSetting P epsilon` with `epsilon>=0`.
The existing direct consumer needs neither this construction nor an extraction
witness. Its proof uses `win_magic_square`, `win_ms_cons` and their reversed
forms, the two value-only anticommutator bounds, and product transfer.

## Blueprint and Lean Consumers

At the base commit, the transitive **explicit `uses` graph** of
`thm:ms-rigidity` contains only that theorem and
`cor:ms-rigidity-symmetric-consistent`. The latter's explicit hypotheses give
zero defects, so it remains justified by specialization. All twelve support
nodes with prefix `lem:ms-rigidity-support-` describe constructions *used to
prove* rigidity. Their prose references back to it do not create proof
dependencies in the opposite direction. Agreement definitions, support
lemmas, and `rem:ms-rigidity-strategy-class` state the same correction and
counterexamples; they do not remove its hypotheses.

There are two narrative integration fixes in `ch13_qpbt_test.tex`: the opening
summary calls rigidity imported, and the paragraph following `thm:pauli`
states that the argument uses corrected extraction. The actual proof of
`lem:qld-win-implications-obs` in chapter 14 invokes
`lem:qld-ms-anticommutator-original-state` instead. Main should align those
two paragraphs and add a separate retention remark for the new `Prop`. No
blueprint file is edited by this assignment.

The explicit descendant closure of that original-state lemma has **81 nodes**:
4 in chapter 13, 3 in chapter 14, 45 in chapter 15, and 29 in chapter 16. The
complete inventory is below, including supplied-input and unasserted nodes.
Keeping their incoming point commutation statement unchanged is sufficient
with respect to Magic Square; their existing restrictions are not newly
certified. Labels may be resolved at any revision with
`python3 scripts/blueprint_citations.py resolve LABEL`.

```text
ch13_qpbt_test.tex (4)
thm:pauli
cor:pauli-binary
def:introparams
lem:delta-bound

ch14_qpbt_observables.tex (3)
lem:qld-ms-anticommutator-original-state
lem:qld-win-implications-obs
lem:qld-comm-cons

ch15_qpbt_combining.tex (45)
lem:expanded-point-field-commutation
lem:qld-sandwich-povm
lem:qld-sandwich-consistency-defect
lem:qld-sandwich-orthonormalization
lem:qld-4-10
lem:qld-combined-point-x-marginal-distance
lem:qld-combined-point-z-marginal-distance
lem:combined-points-unrestricted-error
lem:qld-xz-lines
lem:qld-line-point-marginal-identities
lem:qld-point-self-consistency-defect
lem:qld-completed-point-self-consistency
lem:qld-conditioned-completed-point-self-consistency
lem:qld-point-line-marginal-bounds
lem:qld-line-conditioning-restoration
lem:qld-paired-line-restored-defect
lem:combined-line-measurement-consistency
lem:qld-4-12
lem:qld-4-13
lem:qld-xz-lines-restricted
lem:qld-4-10-same-placement
lem:claim-17-1-re-direct
lem:claim-17-3-re-direct
lem:qld-x-point-overlap-deficit
lem:qld-first-route-overlap-components
lem:claim-17-1
lem:claim-17-2
lem:claim-17-3
lem:combined-lines-given-points
lem:paired-subline-overlap-estimates
lem:subline-joint-overlap
lem:qld-4-13-established-given-points
lem:qld-4-13-established
lem:qld-4-7
lem:qld-opposite-ordered-products
thm:qld-supplied-direct-polynomial-consistency
thm:qld-supplied-scalar-polynomial-consistency
thm:qld-rounded-polynomial-ordered
thm:qld-rounded-scalar-linearity
thm:qld-rounded-wrong-variable-mass
thm:qld-rounded-separated-mass
lem:direct-passing-value
lem:qld-supplied-scalar-point-measurement
thm:qld-completed-pair-actual-error
thm:qld-direct-line-real-overlap

ch16_qpbt_extraction.tex (29)
def:s-w-marginals
lem:s-w-marginals-projective
def:tilde-m-measurement
lem:tilde-m-projective
def:tilde-w-observables
lem:tildew-product-form
lem:qld-construct-the-paulis
lem:qld-construct-the-paulis-given-global-pair
lem:qld-nonencoding-mass-bound
lem:qld-constructing-the-paulis-helper
def:v-swap-unitary
lem:v-swap-conjugation
lem:qld-unitary
lem:qld-state-extraction-given-global-pair
lem:qld-evaluated-pauli-given-global-pair
lem:qld-large-error-extraction-given-global-pair
lem:qld-unitary-given-global-pair
lem:qld-extraction-error-form
thm:pauli-extraction-isometry-construction-support
lem:pauli-extraction-state-distance-support
thm:pauli-extraction-alice-distance-support
thm:pauli-extraction-bob-distance-support
thm:pauli-extraction-transferred-range-support
thm:pauli-concrete-isometry-transfer-support
lem:pauli-extraction-state-error-form-support
lem:pauli-supplied-extraction-error-form-support
thm:pauli-projective-setting-isometry-support
thm:pauli-arbitrary-strategy-isometry-support
thm:pauli-arbitrary-strategy-raw-isometry-support
```

The inventory was computed with the repository's
`blueprint_citations.build_label_index` and `_active_lines`, collecting
`uses` arguments over each statement and adjacent proof span, then iterating
reverse reachability. It includes all chapter files, not only the registered
QPBT chapters. Prose references were inspected separately, including the
twelve support back-references, the strategy-class remark, and both chapter
13 summaries. The source's delayed proofs were inspected manually.

The concrete Lean chain is
`WinImplications/AnticommutingObs.lean` (both original-state estimates and
tuple specialization), `TwistedCommutation.lean` and
`InterchangedCommutation.lean` (both player orientations), the public
`WinImplications.lean` results, `ExpandedCommutation.lean`, combined point and
line witnesses, `exists_globalPairWitness`, pulling consistency and state
extraction, and `pauli_soundness`/`pauli_soundness_qubit`. A text search finds
no invocation of `exists_ms_rigidity` outside its own module's
symmetric-consistent specialization. Shared elementary swap/EPR lemmas used
elsewhere are constructions, not uses of that corrected theorem.

A traversal of the **checked** Lean environment confirms the distinction. It
visits each constant's type and its theorem/definition/opaque value, as well as
inductive constructors; the test fails if `exists_ms_rigidity` is encountered.
The positive detections of the two original-state lemmas check that proof
bodies, rather than just public theorem types, were traversed.

| Root in `MIPStarRE.QPBT` | Corrected extraction in closure | Alice original-state lemma | Bob original-state lemma |
| --- | --- | --- | --- |
| `pointObs_twisted_commutation` | no | no | yes |
| `pointObs_twisted_commutation_interchanged` | no | yes | no |
| `exists_combinedPointsWitness` | no | yes | yes |
| `exists_globalPairWitness` | no | yes | yes |
| `pauli_soundness` | no | yes | yes |
| `pauli_soundness_qubit` | no | yes | yes |
| `exists_spcc_value_one` | no | no | no |
| `exists_ld_soundness` | no | no | no |

Reproduce the traversal with `lake env lean --stdin`, importing
`MIPStarRE.QPBT.Test.MagicSquareTheorems`,
`MIPStarRE.QPBT.Observables.WinImplications`,
`MIPStarRE.QPBT.Test.QubitForm`,
`MIPStarRE.QPBT.Test.LowDegreeGameTheorems`, and
`MIPStarRE.QPBT.Test.Completeness`, and starting at each table root. Use
`env.checked.get.find?`, `Expr.getUsedConstants`, a visited `NameSet`, and the
`ConstantInfo.thmInfo`, `defnInfo`, `opaqueInfo` values explicitly. The initial
diagnostic using `env.find?` failed to see the positive controls and was
discarded; its all-negative output is not evidence. The corrected traversal
produced the table above. An earlier attempt to import the unbuilt
`Test.AxiomAudit.olean` also failed; the existing audit was instead checked as
a source file and the focused traversal imported its actual theorem modules.

## Construction Targets and Verdict

The prescribed-answer transfer is not definitional. If `R_j` is the triple
mass operator, the existing `alice_variable_wrong_form_mass_le` and Bob
counterpart give expectation at most `36*epsilon`. Positivity and `R_j<=I`
give action norm at most `6*sqrt(epsilon)`, or `6*sqrt(epsilon)+s` after
moving to the ideal state. Thus the raw bit distance is bounded by
`2*d_completed + 2*(6*sqrt(epsilon)+s)^2`. Products require a further
opposite-player constraint transport; a bound on `R_j psi` alone does not
bound `R_j O_k psi`. The gap note supplies this calculation explicitly.

Two useful unasserted construction targets remain:

1. `exists_ms_rigidity_prescribed_answers` (proposed name): from the existing
   value and two completed-agreement bounds, construct all seven
   prescribed-answer estimates at `C'*(sqrt(epsilon)+sqrt(delta))`. No
   well-formed-answer or product-transfer hypothesis may be added. This
   changes neither the game nor the hypotheses of existing declarations.
2. `exists_ms_one_way_rigidity` (proposed name): from value alone, construct
   state extraction and Bob's variable comparisons at the printed rate,
   together with Alice's corresponding constraint-read comparisons. Reversing
   roles gives the other orientation, potentially with different witnesses.
   The agreement-transfer calculation can then transfer the required
   variable comparisons without weakening every bound uniformly. This target
   is not itself the unrestricted printed four-variable theorem.

No proposed target is introduced as a hypothesis or declared with a proof
hole. The first would complete the representation comparison; the second
would give evidence for a closer robustness statement. Neither refutes the
independent-copy obstruction or authorizes alteration of the source game.

| Adoption condition | Evidence and remaining limit |
| --- | --- |
| Correctness | Existing corrected theorem and symmetric specialization are proved, with standard axioms. The note gives both counterexamples, the two single-defect tests, the orientation conditioning, dilation, swap, and agreement argument. This proves correctness of the completed-bit robust statement, not the printed claim. |
| Sufficiency | Every direct source use, its full sequel, and all 81 explicit blueprint descendants receive the same value-only anticommutation input. The alternative average-agreement derivation is mathematical, not an invented Lean dependency. |
| Minimality | Not certified. The extra agreement is necessary at zero error, but the source domain is still restricted when retaining its vanishing error. Necessity of uniform `sqrt(delta)` losses does not follow; state/one-way estimates can be separated. The completed-bit representation also needs its prescribed-answer transfer. |
| Lean convergence | The new unasserted definition and existing corrected/consumer interfaces type-check in focused checks. Existing headline and intermediate axiom audits pass. Full CI and independent review of this head are main's remaining gates. |

**Verdict:** retain `pending`. The exit criterion of issue #688 is met by
reviewable retention evidence and exact unresolved targets, not by pretending
all four adoption conditions hold. B5 remains a historical scoped decision;
it is not a certificate under `local/protocols/completion.md` C3. No terminal
cell, completion criterion, game, root import, or blueprint chapter changes.

## Predecessor Costs

The following are the existing records in
`results/telemetry/owner-sessions.jsonl` at the base. They are neither
deduplicated nor rewritten. Row numbers identify evidence, not new charges.

| Row | Recorded session | Issue | Recorded seconds |
| --- | --- | --- | ---: |
| 81 | `claude-prover-105-20260904T1204Z` | 105 | unknown, killed |
| 86 | `claude-prover-105` | 105 | 982 |
| 92 | `claude-prover-172-20260904T1524Z` | 172 | unknown, ended-unrecorded |
| 97 | `claude-prover-172` | 172 | 3253 |
| 111 | `fable-mathfix-172-20260904T2238Z` | 172 | 3562 |
| 119 | `claude-prover-105-20260904T2329Z` | 105 | unknown, killed |
| 121 | `opus-repair-pr192-r1-20260905T0110Z` | 172 | 4392 |
| 124 | `claude-prover-105` | 105 | 7319 |
| 125 | `opus-prover-105-s2-20260905T0140Z` | 105 | unknown, killed |
| 135 | `opus-fix-pr192-build-20260905T0616Z` | 172 | 253 |
| 138 | `opus-prover-105-s4-20260905T0619Z` | 105 | 1524 |
| 144 | `opus-reviewer-pr192-r2-20260905T0640Z` | 172 | 1304 |
| 146 | `opus-prover-105-s5-20260905T0652Z` | 105 | 5102 |
| 150 | `opus-fix-pr192-round2-20260905T0714Z` | 172 | 1142 |
| 158 | `opus-reviewer-pr192-r3-20260905T0802Z` | 172 | 1185 |
| 166 | `opus-merge-105-20260905T0908Z` | 105 | 2304 |
| 174 | `opus-reviewer-pr217-r1-20260905T1001Z` | 105 | 1598 |
| 179 | `opus-fix-pr217-round1-20260905T1042Z` | 105 | 2131 |
| 187 | `opus-reviewer-pr217-r2-20260905T1030Z` | 105 | 2450 |
| 193 | `opus-fix-pr217-round2-20260905T1052Z` | 105 | 775 |
| 197 | `opus-reviewer-pr217-r3-20260905T1130Z` | 105 | 1318 |

The sum of the seventeen recorded `wall_s` fields is 40594 seconds. This is
**not** a deduplicated elapsed-time total: several start records overlap later
receipts, four rows lack a duration, and some timestamp spans differ from
recorded active durations. All original timestamps and token/tool counts
remain in their rows. The original starts are `2026-09-04T12:04:10Z` for
#105, `2026-09-04T15:24:39Z` for #172, and `2026-09-04T22:38Z` for the
recorded Fable mathematical-gap attempt. The new Astra tranche resets none
of them and does not replace Fable's recorded 3562 seconds with its larger
wall-clock span.

The historical halted audit, partial proof work and final proof commits
`d4c565e`, `116f62c`, `ce9b82b`, `5a46cb0`, and the reviews/repairs of PRs
192 and 217 remain evidence. `sessions.jsonl` at the base contains no rows
with issue 105, 172, or 688; this is not evidence of zero cost. The current
dispatcher records this session on completion. A separate malformed JSON row
751 in `owner-sessions.jsonl`, beginning with `opus-review-pr650-20260917-01`,
prevented a whole-file JSONL read; line-by-line parsing preserved and reported
the defect without editing it. Main receives this telemetry issue in the
receipt.

## Validation

The checkout's actual `lean-toolchain` is `leanprover/lean4:v4.32.0`; the older
version quoted in `AGENTS.md` was not used to alter it. The worktree was clean
at the admitted SHA, `origin/main` resolved, and
`scripts/install_git_hooks.sh --check` passed. The primary duplicate checker
found no existing `MIPStarRE.QPBT.PrintedMagicSquareRigidityClaim` on
`github/main`.

Focused validation:

- `lake env lean MIPStarRE/QPBT/Test/MagicSquareTheorems/PrintedClaim.lean`
  passes with no warnings; the file has no proof holes or axioms.
- `lake env lean MIPStarRE/QPBT/Test/MagicSquareTheorems.lean` passes with its
  pre-existing `push_neg` deprecation warning at line 655.
- `lake env lean MIPStarRE/QPBT/Observables/WinImplications.lean` passes.
- `lake env lean MIPStarRE/QPBT/Test/AxiomAudit.lean` passes all thirteen
  standard-axiom checks, including all four headlines and the global-pair and
  extraction constructions.
- A focused `Lean.collectAxioms` check also gives exactly
  `propext, Classical.choice, Quot.sound` for the corrected Magic Square
  theorem, its symmetric specialization, and both original-state
  anticommutator lemmas.
- The changed gap note passes `scripts/check_paper_gap_note_style.py --ci`
  and its focused `make build/qpbt_ms-rigidity-symmetric-strategies.pdf` build.
  The final log has no undefined references or citations. Inherited long
  declaration names still produce layout warnings.

These are focused elaborations using worktree build artifacts, not a full
rebuild of every consumer. No full `lake build`, cache publication, review,
GitHub publication, or merge was run in this session. The final receipt records
the commit, normal-hook result, and exact integration patch for main.
