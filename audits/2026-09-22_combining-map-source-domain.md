# Combining Map: Projection Domain and Evaluation

Issue #695, starting at `023a0c59539cc22be4c23298d7ebed73eee9cc39`.
The affine construction is proved. The source definition `def:combine-map`
remains unmarked because the current coefficient carrier is not the carrier
of polynomial functions on geometric lines. No definition, game, sampling
law, existing theorem statement, or source completion criterion is changed.

## Source and Domain

The combining formula is `eq:combine-lines` in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`.
For an extended line `ell(u,v)` and containing lines `ell_X`, `ell_Z`, the
source assumes that every point of the extended line projects into the two
containing lines. For polynomial functions `f`, `g` of degree at most `md`
on those lines, it defines a polynomial function on the extended line by
the affine-weighted sum of the two evaluations, of degree at most `md+1`.

The source explicitly allows zero directions in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:106-124`.
Its polynomial convention is the reduced polynomial-function convention at
`references/qpbt-paper/04_preliminaries.tex:835-845`. The univariate answer
format at `08_classical_and_quantum_low_degree_tests.tex:347-391` must also
be compared with this convention. The current blueprint explains the
different coefficient interpretation in `rem:deg-line-representatives`.

The relevant existing gap notes are
`docs/paper-gaps/qpbt_subline-claims-line-marginal.tex` and
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`. The latter's separate
extended-dimension sampling obstruction is not used to prove, or to evade,
any result here.

## Proved Declarations

All declarations below are in the namespace `MIPStarRE.QPBT` and the new
module `MIPStarRE/QPBT/Combining/LinePolynomial.lean`.

| Declaration | Mathematical content |
| --- | --- |
| `exists_affine_parameters_of_linePoints_subset` | Line inclusion implies `u = u' + a v'` and `v = b v'`. |
| `exists_isCombineLineCompatible_of_projection_mem` | The two source projection inclusions imply affine compatibility. |
| `exists_combineLinePoly_of_projection_mem` | Constructed compatible parameters give the coefficient formula and degree bound `c+1`, for every pair of degree-`c` coefficient lists. |
| `evaluatesTo_zero_direction_iff` | On a singleton line, evaluation to `a` means that every parameter evaluates to `a`. |
| `not_evaluatesTo_parameter_on_zero_direction` | At every bound `c >= 1`, the coefficient answer `T` has no value on a zero-direction line. |

For the first result, inclusion supplies parameters `a` and `s` for `u`
and `u+v`. Subtracting the two point identities gives `v = (s-a)v'`.
Applying this result to each projection and using the existing
`isCombineLineCompatible_of_blocks` proves compatibility. There is no
division by a direction coordinate: constant projections, zero containing
directions, and a zero extended direction are all included. The same
parameters work for every polynomial answer. The existing
`combineLinePoly_spec` and `combineLinePolynomial_natDegree_le` then give
the coefficient formula and its bound; no subline estimates are reproved.

## The Obstruction

Consider the singleton containing lines `ell_X = ell_Z = {0}`, the extended
line with base `(0,0,1,0)` and zero direction, and coefficient answers
`f(T)=T`, `g(T)=0`. Projection inclusion holds. Every choice of affine
parameters is compatible with the zero source directions. Choosing
`a_X=b_X=0` gives the combined polynomial zero, while `a_X=1`, `b_X=0`
gives the combined polynomial one. Choosing `a_X=0`, `b_X=1` instead gives
the parameter polynomial `T`, which does not evaluate at the singleton
extended point under the existing universal evaluation relation.

The new obstruction theorem certifies the reason: a value for `T` at the
singleton would have to equal both its value zero at parameter zero and
its value one at parameter one. A checked scratch example constructs an
actual `LineDesc.diagonal` with zero base and direction, so the obstruction
is not conditional on an impossible line description. This works over
every scalar field admitted by `LdParams`; for example the source case
`(q,m,d)=(8,1,1)` also has a defined extended-dimensional seed law.

This is **not** a counterexample to the source identity for genuine
functions on lines. The answer `T` is not such a function on a singleton.
It refutes a total, evaluation-preserving identification of the current
coefficient answer carrier with that source domain. Selecting parameter
zero or requiring nonzero directions would change the assertion under
consideration. Assuming that all answers evaluate would move the missing
condition into a new premise.

There is an independent representative issue even for nonzero directions.
Over a finite field of size `q`, the nonzero formal polynomial `T^q-T`
induces the zero function. Its nonzeroness and zero evaluation are checked
using Mathlib's `FiniteField.X_pow_card_sub_X_ne_zero` and
`FiniteField.pow_card`. Thus a correct descent condition is constancy on
parameter fibers as a function, not formal degree zero. The current
`DegPoly` and global `Poly` carriers distinguish representatives. The new
results neither quotient those carriers nor restrict their degree bounds.

## Statement Integrity

| Item | Assumptions | Conclusion | Verdict |
| --- | --- | --- | --- |
| Source geometric step | Every extended-line point projects into each containing line. | Compatible affine parameters exist. | Exact geometric domain; Lean proves it over any field. |
| Lean parameter formula | The same inclusions; arbitrary bounded coefficient lists. | Constructed compatibility, affine-weighted parameter evaluation, degree at most `c+1`. | Proved auxiliary; relative to the full source claim, a weakened conclusion because geometric evaluation and carrier correspondence are absent. |
| Full source definition | Polynomial functions on the two containing geometric lines, including singleton lines. | A well-defined polynomial function on the extended line satisfying the pointwise identity. | Still unmatched by the current coefficient construction. |

No compatibility, line witness, evaluation identity, or nonzero-direction
assumption is added to the source hypothesis list. No existing public Lean
signature changes. The three new auxiliary blueprint nodes are fully marked;
`def:combine-map` retains its statement and `\notready` status. The two
evaluation lemmas are proved statements about the existing carrier, not
conditional replacements for the source definition.

## Affected Consumers and Separate Proposal

A carrier correction needs a separately scoped decision by Main under
`local/protocols/issues-prs.md` section 6. The proposed mathematical domain
is functions on the geometric line whose parameter pullbacks have bounded
polynomial representatives. Representatives must be compared by their
functions, and the singleton condition is constancy of the parameter
function. On that domain, prove that the combining operation is independent
of affine choices and representatives and preserves the required degree.

That construction alone does not transport arbitrary coefficient-indexed
measurements to the source carrier. Non-descending answers such as `T`
must be accounted for in a measurement and game comparison. The new
obstruction forbids simply identifying them with geometric functions.
This proposal is not adopted or implemented in this assignment.

| Consumer | Required comparison before adopting a carrier correction |
| --- | --- |
| `Algebra/Coefficients.lean`, `Observables/LineDefs.lean` | Compare coefficient representatives, `DegPoly`, `EvaluatesTo`, and `evalOpt` with geometric polynomial functions. |
| `Test/LowDegreeGame.lean`, `Test/PauliBasisTest.lean` | Preserve or explicitly compare answer equality and the universally quantified line-point acceptance relation. |
| `Observables/LineMeasurement/Expanded.lean`, `Evaluation.lean` | Transport coefficient-indexed line measurements and completed evaluation classes, including undefined mass. |
| `Combining/Lines/SubLineExtended.lean`, `SubLineConstruct.lean` | Preserve `isCombineLineCompatible_of_blocks`, inherited compatibility, and `subLineTripleOf_compatibility`; their geometry is already valid. |
| `Combining/Witnesses.lean` | Preserve `SubLineWitness.incidence` and `compatibility`; any removal of redundant stored data is separate work. |
| `Combining/ExtendedLines/Measurement.lean` | Compare `affineData`, `combinedPolynomial`, `extendedMeasurement`, the evaluated and optional formulas, and axis degree support. |
| `Combining/DirectLowDegree/Game.lean`, `ExtendedLineGame/ParameterCompletion.lean` | Preserve or compare `DirectDegPoly`, `DirectEvaluatesTo`, `directEvalOpt`, and parameter-to-completed-evaluation relations. |
| `Combining/ExtendedLines/Overlap.lean`, `Estimates.lean`, `Apply.lean` | Transport evaluated overlap and consistency to the source's field-valued statement before claiming `lem:qld-4-13`. |

All paths in the table are relative to `MIPStarRE/QPBT/`. In the paper and
blueprint, this affects the line half of `def:combine-map`, the combined
line construction in `lem:qld-4-13` (paper lines 1128-1132), and its use in
`lem:qld-4-7`. Earlier `lem:qld-comm-line-cons` and `lem:qld-xz-lines` also
use the line-function interpretation. The global combining polynomial and
`lem:qld-4-12` are preserved; they must not be conflated with the singleton
line issue. The dimension and error-rate obligations remain separate.

## Prior Work and Budget

The single additional assignment is bounded by 3600 seconds, starting at
`2026-09-22T20:16:43+09:00`. There is no automatic continuation. The original
#118 anchor remains `2026-09-05T19:24:00Z`, with the recorded ten-attempt,
19931-second historical baseline. The thirteen `mathfix-118` rows in
`results/telemetry/sessions.jsonl` sum to 26509 seconds. They overlap the
baseline; these amounts must not be added together.

The owner ledger retains the earlier #117 and #118 construction sessions,
including the Fable work and incomplete or killed records. The ordinary
ledger retains later #117/#119 work, #414's failed 3880-second repair,
#474's 2328- and 2565-second passes, #480's 4446- and 4599-second proof
sessions, and #512's construction and integration history. Issue #405 and
PR #478 remain linked in the subline note; no missing duration is invented.
The five later records totaling 14637 seconds in
`audits/2026-09-18_issue515-combined-line-consistency-history.md` are an
identified subtotal, overlapping the named #414 record above. They are not
another amount to add blindly. The #689 author and blueprint sessions are
separate later records of 1684 and 1071 seconds. None of these costs or their
review histories is reset, erased, or charged a second time here.

## Validation

Each new declaration passed `lake env lean` before its milestone commit,
with normal hooks. The focused scratch harness reports only `propext`,
`Classical.choice`, and `Quot.sound`; the two geometric lemmas do not use
`Classical.choice`. It also checks an actual singleton line and the
finite-field representative example. No proof hole or axiom is introduced.

Focused `lake env lean` checks pass for `Combining/Defs.lean`, the new module,
`Combining/Lines/SubLineConstruct.lean`,
`Combining/ExtendedLines/Measurement.lean`, and the QPBT umbrella. The root
module was also checked while producing worktree-local object files for the
declaration checker. `lake exe checkdecls blueprint/lean_decls` resolves all
1881 generated entries. The `sorry|axiom` scan of the changed Lean files and
the additional proof-integrity token scan have no matches.

Bibliography generation, `leanblueprint web`, blueprint LaTeX checks, sync,
and changed-declaration blueprint coverage pass. After rendering, the web
tool's generated declaration list caused a sync check to report 254 stale
entries. Regenerating the canonical list with
`blueprint_lean_sync.py --update-lean-decls` resolved this generated-artifact
discrepancy. The four orphan marks and two missing proof marks reported in
unchanged chapters are warnings, not new marks from this change. The source
statement checker reports no changed public headers. Whitespace checks pass.

The exact final command results and commits are recorded in
`/tmp/main-fullspeed-combine-map-20260922-result.md`. No full `lake build`
was run: Main retains full CI, publication, and independent review under the
assignment. No shared build cache was written. This audit makes no approval
claim.
