# Printed QPBT Error Contracts

Issue #674 under #667; session `orc-674-20260922-01`.
Source snapshot: `554c270f37d1a8eaebb2231de3883f478bc4076e`.
This is retention and adoption evidence, not a new mathematical correction attempt.
The earlier #16/#196/#201 costs and admission limits are unchanged.

## Retained Domains

`MIPStarRE/QPBT/Games/ErrorFunctions.lean` now retains:

- `PrintedPolynomialBound`: for a finite tuple of positive real inputs, one
  constant `C > 0` bounds `f x` by `C * (product x)^C`. This is exactly the
  scalar shorthand at `references/qpbt-paper/04_preliminaries.tex:26-29`.
  It adds no nonnegativity hypothesis on the function and no bound at zero.
- `PrintedSquareRootPolynomialClaim`: its one-variable specialization to
  `Real.sqrt`, the explicit choices at chapter 14:508-520 and 649-676.
  This records the scalar claim only; it is not a replacement for either
  operator lemma's quantifiers or conclusions.

`MIPStarRE/QPBT/Games/Sandwich.lean` now retains `PrintedPastingClaim`:

| Component | Retained content and source |
| --- | --- |
| Quantifier order | One two-variable error function, with the printed product bound, before all measurement data and error parameters; chapter 6 `lem:pasting`, `eq:def-deltap` |
| Hidden constants | For each common positive input big-O constant, a positive output constant uniform in all data and errors; `def:consistency`, chapter 6:233-250 |
| Questions and state | Arbitrary finite alphabets, probability distribution on `((X x Y1) x Y2)`, arbitrary common finite local matrix space, normalized bipartite vector |
| Codewords | Finite collections of actual functions `Yi -> Ri`, not arbitrary labels whose evaluations can identify different codewords |
| Measurements | `G1` a POVM, `G2` projective, joint `A` projective, the same `A` available on both registers |
| Collision domain | Distinct second codewords; conditional probability given `(x,y1)` only when its marginal mass is positive |
| First comparison | Alice's first marginal of `A` against Bob's evaluated `G1`, `eq:pasting-1` |
| Second comparison | Alice's second marginal of `A` against Bob's evaluated `G2`, `eq:pasting-1` |
| Third comparison | Alice's joint `A` against Bob's joint `A`, `eq:pasting-2` |
| Output | Alice's joint `A` against Bob's evaluated `G2 G1 G2`, `eq:pasting-2a`, `eq:pasting-3` |
| Scalar domain | Product bound only for strictly positive inputs; comparisons for nonnegative errors, with no extra bound imposed on the axes |

This is the full input/output assertion in the repository's finite-matrix
domain, not an assertion about all separable infinite-dimensional spaces.
The source's otherwise undefined zero-mass conditioning is restricted to its
well-formed domain. These boundaries are explicit, not implicit proof assumptions.
The output big-O constant is kept separate: absorbing it into the same constant
that is also the exponent would be an unjustified change of the printed contract.

All three declarations are **unasserted Prop definitions**. No proof assumes
them. Their type-checks do not prove them. Neither pre-existing corrected
predicate nor any pre-existing theorem statement or proof is edited.

## Source and Consumer Inventory

In this table, C14 means
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`; B12--B16 are
the corresponding active blueprint chapters under `blueprint/src/chapter/`.
Lean paths are relative to `MIPStarRE/QPBT/`.

| Source / blueprint consumer | Lean consumer | Quantitative conclusion and boundary |
| --- | --- | --- |
| C14 `lem:qld-comm-cons` (463-520); B14 same label | `Observables/PointConsistency.lean`: `deltaAnticom_isPolyErr`, `exists_expandedPointConclusions` | Concrete square root with independent constants, zero at zero; not the printed coupled contract |
| C14 `lem:qld-comm-line-cons` (523-678); B14 same label | `Observables/LineMeasurement.lean`: `deltaLine_isPolyErr`, `exists_expandedLineConclusions` | Square-root envelope for the three directed conclusions, zero at zero |
| C14 `lem:qld-4-10` (689-881), including local shorthand at 730 and 742; B15 same label | `Combining/Points.lean`: `exists_combinedPointsWitness` | An `IsPolyErr` point-error function is chosen before settings and witnesses; roots, projective rounding and sums use independent constants |
| Chapter 6 `lem:pasting` (504-525); B12 same label and `lem:pasting-forward-comparisons` | `Games/Sandwich.lean`: `exists_pasting_error`; `Pasting/Heterogeneous.lean`: `exists_pasting_error_of_marginal_consistency` | Three printed inputs retained publicly; proof needs only two forward comparisons and constructs the Schmidt mirror; additive bound `(3C+19)(eta^(1/4)+delta^(1/8))` |
| B12 `lem:pasting-of-register-exchange` | `exists_pasting_error_of_register_exchange` | Separate conditional theorem with a fourth comparison; not used by the one-sided theorem or concrete line constructor |
| C14 `lem:qld-xz-lines` (882-964), pasting call at 955-960; B15 same label, B12 `lem:pasting-heterogeneous` | `Combining/Lines/Construction.lean`: `exists_pasting_error_heterogeneous`; `Combining/Lines.lean`: both witness constructors | Substitutes collision `md/q` and a controlled point/line consistency error; uses opposite finite spaces without symmetry assumption |
| Same line call and nondegenerate conditioning; B15 `thm:qld-conditioned-polynomial-bound` | `Combining/ErrorBounds.lean`: `exists_conditioned_polynomial_bound` | Bounds `min(1, mu*f(rho,(8p(eps)+c(eps+sqrt(eps)))/mu)+rho)` with `1/2 <= mu <= 1`; the exceptional mass is added, not multiplied |
| C14 restricted-line laws and Claims 17-1--17-3 before `lem:qld-4-13`; B15 `lem:restricted-line-mixture-bounds`, the three claim nodes | `Combining/Lines/Restricted.lean`, `Combining/ExtendedLines/Estimates.lean`, `Combining/ErrorBounds.lean` | Roots of the point and line errors, with explicit dimension losses; directed comparisons and actual sampling laws remain relevant |
| C14 `lem:qld-4-13` (1020-1034) and its two proof routes; B15 source, established, and supplied-point nodes | `Combining/Apply.lean`: `PrintedExtendedLinesWitnessClaim`, `exists_extendedLinesWitness_established`, its `_ofPointsWitness` companion | Established outer `C*m*poly(eps,md/q)` only. Printed `poly(m^2*eps,md/q)` and source question/law/answer identifications remain open |
| C14 `lem:qld-sublines` and use in the second extended-line route; B15 source-defects remark | `Combining/Lines/SubLineJoint.lean`, `Combining/ErrorObstruction.lean` | Directly indexed joint identities and the first-route scalar obstruction are not the missing source-law premise or a refutation of the existential printed theorem |
| C14 `lem:qld-4-7` (1267-1274) and proof; B15 same label and scalar support nodes | `Combining/Apply.lean`: `exists_globalPairWitness`; `DirectPassingErrorBounds.lean`, `ActualErrorBounds.lean`, `PassingError.lean` | Actual passing, rounding and completion errors absorbed into `a(md)^a(eps^b+q^(-b)+2^(-bmd))`; no absorption into the missing printed extended-line rate |
| C14 `lem:qld-construct-the-paulis`, its helper (1611 onward); B16 corresponding pulling-apart and marginal nodes | `Extraction/Construction.lean`, `Consistency.lean`, `PullingMeasurement.lean`, `PointConsistency.lean`, `EncodingSupport.lean` and their support modules | The global-pair witness controls the same projective marginals; separate `sqrt(eps)` and `md/q` terms are absorbed in the explicit global error |
| C14 `lem:qld-unitary` (1670-1859), `thm:pauli-appendix` (1862-1876); B16 extraction nodes and detached proof of B13 `thm:pauli` | `Extraction/SourceUnitary.lean`: `exists_extractionWitness_fourth_root_rate`; `Test/Soundness.lean`: `pauli_soundness`; soundness transport and scalar-absorption modules | Fourth roots and universal constants give explicit final robustness; its finite-parameter tails can remain positive at strategy error zero |
| B13 `cor:pauli-binary`, `def:introparams`, `lem:delta-bound` | `Test/QubitForm.lean`, `Test/CanonicalParams.lean` | Downstream robustness specialization, not evidence for the refuted intermediate contract |
| NEEXP Fact 4.35 induction, quantum preliminaries:1031-1051; answer reduction:540-558 | No QPBT Lean proof of that answer-reduction theorem | Iterated one-sided pasting preserves the ordered three-measurement sandwich; separate collision contributions yield additive estimates, not proof of a literal product claim |

The QPBT source has one direct application of `lem:pasting`, in C14's paired
line construction. To match the displayed `T = M_X M_Z M_X`, take `G1=M_Z`,
`G2=M_X` and exchange answer coordinates. Both line families are projective;
the same collision estimate applies after exchanging their roles. The marginal
comparisons and joint self-consistency come from the earlier point construction,
not from a register-exchange assumption on the generic pasting lemma.

The supplied-point line and extended-line constructors are conditional on a
point-error function satisfying `IsPolyErr`. They are not unrestricted
constructions at an arbitrary supplied scalar point error. The existential
constructors supply that controlled family first. This quantifier distinction
must survive an adoption audit.

`PrintedExtendedLinesWitnessClaim` is not an already-retained literal product
claim: its docstring explicitly says that it uses `IsPolyErr2` in the additive
sense and a directly indexed, completed-answer replacement carrier. It cannot
discharge either missing artifact audited here, or the independent rate/law gaps.

## Global Notation Outside QPBT

The complete primary-mirror `\\poly` search separates error estimates from
complexity and size estimates; macros `polymeas`, `polylog` are not this predicate.
Besides chapter 14 and `lem:pasting`, explicit small-error uses occur at
`09_introspection_games.tex:2537-2550` (composition of its soundness error) and
`10_oracularization.tex:298-313` (`thm:oracle-soundness`). The former actually
writes `C*(delta')^(1/C)`, another independent exponent/prefactor choice, not
the coupled printed formula. Neither result has an affected QPBT Lean consumer
whose compilation certifies the full corresponding theorem. They are not
declared justified by this evidence packet.

The remaining global-notation uses are size/runtime estimates in primary
chapters 3, 4, 6, 7, 8, 9, 10, 11, 12 and 13. They are outside the error
predicates' scope and are left unchanged. On size domains bounded below by one,
enlarging a coupled constant is a different operation from enlarging it for
small errors. A blanket global product-to-sum replacement is not warranted.
The finite-arity printed predicate retains the global scalar definition without
asserting any of those complexity claims. Full-paper sufficiency is therefore
not inferred from the QPBT build.

## Four Adoption Conditions

| Condition | Square-root row | Pasting row |
| --- | --- | --- |
| Correctness | Concrete independent-constant square-root witnesses are proved on nonnegative inputs; the coupled printed square-root claim is false | One-sided additive theorem is proved by the mirror argument; the documented example satisfies that bound and refutes the product contract even with fixed big-O constants |
| Full consumer sufficiency | Established QPBT route supported, but not every literal source assertion or global notation use | Established line, global-pair and extraction route supported; printed extended-line rate and source-law obligations remain open |
| Minimality / source semantics | Not met as a literal equivalence: separates coupled constants, admits excluded positive-domain functions, and separately imposes a zero boundary | Fails unchanged C3: product-to-sum loses vanishing in either independent error at fixed positive value of the other |
| Lean convergence | New definitions type-check; focused consumer validation recorded below; full CI delegated to main | Same, with independent review still required; compilation is not a proof of the retained proposition |

The obstruction is exact. At fixed `delta=rho` in `(0,1)`, the example's input
defects are `rho,0,0`, and its output defect is `rho`, for every `eta>0`.
For fixed positive `cOut,C`, `cOut*C*(eta*rho)^C` tends to zero. No faithful
proof on this domain can recover that bound from the additive one. The example
does not depend on imposing a bound at `eta=0`, state symmetry, or a missing
fourth comparison. A product with independent positive exponents would fail
for the same reason.

Both rows stay **pending**. A terminal adoption cannot be manufactured by
retaining these definitions, proving the corrected estimates, or compiling the
headline theorems. Main must assess this obstruction under unchanged rules;
changing the stated project goal would require the separate owner authority
specified in those rules. This packet changes neither the goal nor its gates.

## Initial Verification

- Duplicate guard against `github/main`: all three new declaration names,
  `duplicates: []`, `queried: 3`, exit 0.
- `/home/drx/MIPStarRE-qpbt/scripts/install_git_hooks.sh --check`: passed.
- `lake env lean -o .lake/build/lib/lean/MIPStarRE/QPBT/Games/ErrorFunctions.olean
  MIPStarRE/QPBT/Games/ErrorFunctions.lean`: exit 0, no diagnostics.
- Corresponding single-file check and branch-local olean output for
  `MIPStarRE/QPBT/Games/Sandwich.lean`: exit 0, no diagnostics.
- `rg -n 'sorry|axiom|admit|native_decide|unsafeCast|unsafeCoerce|ofReduceBool|ofReduceNat|lcProof'`
  on the two edited Lean files: no matches (exit 1).
- `python3 scripts/check_paper_gap_note_style.py --changed-files` on the two
  edited notes with `--ci`: passed, two notes.
- `git diff --check`: passed.

No full build or independent review has been run by this author session.
Additional validation and publication receipts are appended below as obtained.
