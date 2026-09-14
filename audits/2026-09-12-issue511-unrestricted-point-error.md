# Issue 511: unrestricted point error in extended-line consistency

Session: `prover-511-20260912-01`, started at 2026-09-12T04:54:47Z.
Base: `ae124f8f09ee002444ac5b9711822c0f1daae142`.
Target: `MIPStarRE.QPBT.exists_extendedLinesWitness_established_ofPointsWitness`
in `MIPStarRE/QPBT/Combining/Apply.lean`.

## Result

The target is not discharged. Its unrestricted scalar point error is a
mathematical obstruction, already identified for the paired-line construction
in issue #118 and repaired there by issue #389. This packet extends the
existing counterexample to the exact extended-line conclusion. The public
statement, proof body, imports, witness fields, and blueprint links remain
unchanged. No Lean proof, additional hypothesis, or replacement theorem is
introduced.

The mathematical account is in
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`, subsection
"Unrestricted point witnesses in the extended-line assertion". For
`m = d = 1`, deterministic joint answers `(x^2, 0)` are admissible as a
supplied point witness at a sufficiently large scalar error. On the X-axis
component of the directly indexed four-dimensional law, a degree-one line
polynomial agrees with the combined answer `alpha * x^2` at at most two
points when `alpha` is nonzero. Every extended-line witness would therefore
have consistency defect at least

\[
  \frac18(1-1/q)(1-2/q),
\]

whereas `C * deltaCombine 0 (1/q)` tends to zero. Admissible field sizes
`q = 2^(2*k+1)` are unbounded, and `m = d = 1` satisfies the public domain.
The argument uses the source's perfect strategy, not an assumption that the
formal completeness obligation is already proved.

## Source and interface audit

The source is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`:
`lem:qld-4-13` at 1020--1034, its conditional averaging construction at
1118--1132, and Claim 17-1 at 1140--1173. The source constructs its joint
point family in `lem:qld-4-10` at 689--709 and then its combined field-valued
family in `lem:qld-4-12` at 993--1018. The first proof route retains the
point-error contribution; it does not allow arbitrary supplied point errors
to be omitted from the conclusion.

The perfect projective strategy used in the mathematical counterexample is
`lem:pauli-completeness` in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1229-1421`.
Its formal counterpart `exists_spcc_value_one` remains admitted. This report
does not use that admission to manufacture a formal contradiction.

The corresponding blueprint entry is `lem:qld-4-13-established` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`. It links the existential-point
declaration `exists_extendedLinesWitness_established`, not the unrestricted
helper. It has no `\leanok` certification, and none is added.

| Item | Source argument | Current target |
| --- | --- | --- |
| Strategy | Admissible parameters, projective strategy of value at least `1-epsilon` | Same, via `ProjectiveSetting` |
| Point family | Constructed with `deltaQ(epsilon) = poly(epsilon)` | Every `CombinedPointsWitness S deltaQ`, for every real `deltaQ` |
| Quantitative choice | The line error absorbs the constructed point error | Universal `C` and `deltaCombine` are chosen before unrestricted `deltaQ` |
| Line conclusion | Two evaluated consistency bounds, degree `md+1`, degree `d` on axes | Same degree requirements; directly indexed questions and completed answers |
| Error | Printed `poly(m^2*epsilon,md/q)`; first route gives `m*poly(epsilon,md/q)` | `C*m*deltaCombine(epsilon,md/q)`, independent of the supplied point error |

Verdict: the helper strengthens the quantification over point witnesses
beyond the source construction. The established first-route error does not
justify that strengthening. Its direct indexing and completed answers remain
separate documented deviations. The weaker numerical error alone is not the
obstruction exhibited here.

## Existing proof content and provenance

The search covered `git log --all` for `Apply.lean`, including saved issue
#118 and #119 histories, and the existing paper-gap notes and session reports.
No proof at the current unrestricted signature was found.

- `f6a340c8dc3c12566d9312215c578939efeb8b4a` changed both internal
  extended-line helper signatures to fix a function `deltaQ : Real -> Real`
  and `IsPolyErr deltaQ` before selecting the output error. This is an
  explicit signature change, not an implementation of the current target.
- `6e8d67ef8ba22de69a0c166adcdf23ba6e7a33aa` contains a proof of the
  established helper at that restricted signature. It constructs conditional
  extended-line POVMs, axis-degree support, and both consistency fields,
  using `subline_joint_overlap_near_one_at` and
  `exists_combining_polynomial_bound`. The saved attempt-11 report records
  validation of that work. This session inspected its source, but did not
  rebuild or certify the divergent dependency chain.
- `0f4ef05370350f4017439ebd839ef0561f13130f` preserves that work and adds
  global-pair scalar absorption. It does not supply the unrestricted proof.
- `3ab9f44bcd4457782a63685fda5642006bf78510`, on the current main history,
  repaired the paired-line helper's point-error domain and added the existing
  mathematical counterexample to the paper-gap note. Its changes do not
  repair the corresponding declarations in `Apply.lean`.

The historical dossier is available at
`0f4ef05370350f4017439ebd839ef0561f13130f:audits/2026-09-06-issue118-point-error-dependency.md`.
Its source construction and later conditioning repairs require reconciliation
before reuse. Copying the saved branch or importing its theorem under the
current name would conceal the changed quantifiers and is not justified.

## Validation and limits

- `lake env lean MIPStarRE/QPBT/Combining/Apply.lean` succeeds with the five
  existing admission warnings.
- `rg -n 'sorry|axiom' MIPStarRE/QPBT/Combining/Apply.lean` reports the five
  existing `sorry` lines: 62, 90, 122, 152, and 177.
- A private axiom audit prints the target's current unrestricted signature
  and reports `[propext, sorryAx, Classical.choice, Quot.sound]` for both
  the target and `exists_spcc_value_one`.
- `scripts/install_git_hooks.sh --check` succeeds with
  `core.hooksPath=.githooks`.
- `texra-blueprint --root . paper-gaps check` succeeds: 40 referenced slugs
  resolve. Existing missing-verdict-marker warnings remain.
- `latexmk -pdf -interaction=nonstopmode -halt-on-error` compiles the updated
  note to 11 pages with resolved citations. Its four overfull-box warnings
  concern unchanged text before the new subsection. Output is under
  `~/.cache/mipstarre-dev/sessions/prover-511-20260912-01-pdf/`.
- `git diff --check` succeeds.

The private audit input is
`~/.cache/mipstarre-dev/sessions/prover-511-20260912-01-axioms.lean`.
It is not a project source file. No full build is needed for this documentation
change. Publication and exact-head CI evidence are recorded in the PR and the
session's final report.

The root-count step uses the usual theorem that a nonzero polynomial has at
most its degree many roots; the existing Mathlib API is
`Polynomial.card_roots'` in `Mathlib/Algebra/Polynomial/Roots.lean`.
No duplicate version is added. This report supplies a mathematical
counterexample, not a kernel-checked negation of the existential Lean
statement. Formalizing the perfect strategy and integrating the lower bound
would be additional work, not grounds for claiming that the target is proved.

## Prior costs and next gate

This is a continuation of the documented gap, not a new zero-cost attempt.
The thirteen `mathfix-118-20260906-*` records in
`results/telemetry/sessions.jsonl` total **26,509 seconds** (7h 21m 49s).
This includes the failed eighth attempt's 2,700 seconds. The three earlier
`prover-119-20260906-*` records add **1,927 seconds** (32m 7s).
Their combined recorded duration is **28,436 seconds** (7h 53m 56s), before
this packet. This is a scoped subtotal, not the entire project's cost:
operator, reviewer, scout, and later packet sessions are not included.
Some records resume the same thread and expose cumulative token counters;
their token values are not summed. Missing or failed capture is not evidence
of zero token use. The dispatcher's final record supplies this packet's
additional wall time and usage; the 60-minute limit remains in force.

At the pre-publication checkpoint, 2026-09-12T05:02:27Z, this packet had used
460 seconds since dispatch. Adding that interval to the prior scoped subtotal
gives 28,896 seconds (8h 1m 36s). This is an in-progress lower bound; the final
dispatcher duration supersedes the packet interval, rather than being added
to it a second time.

The next gate is independent mathematical review of this obstruction and a
separately scoped decision about the invalid helper interface. A subsequent
proof of the existential-point declaration must construct its own controlled
point witness, prove the current unconditioned paired-line consistency
obligation, and retain the resulting errors while constructing extended
lines. The saved first-route proof is potential reusable content under that
domain, not a proof of the present unrestricted assertion. No source theorem
is refuted, no `GlobalPairWitness` is supplied, and no global-pair or final
Pauli-test construction is certified by this packet.
