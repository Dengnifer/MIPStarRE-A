# Paper-gap notes

Every statement in this formalization that departs from the source paper it
cites is justified here. A *paper-gap note* is a standalone LaTeX document that
quotes the printed statement, says precisely what is wrong with it or what
cannot be reconstructed from the printed proof, and states the corrected form
the formalization uses instead. The notes are the reviewer-facing evidence
behind the per-statement table in
[`qpbt-gap-register.md`](qpbt-gap-register.md), which is the repository's
summary of every deviation from the source papers.

Nothing here is a to-do list. A note exists because a correction was already
made; reading one should let a reviewer check that correction against the paper
without opening any Lean file.

## Building the notes

```sh
make -C docs/paper-gaps          # compile every note into docs/paper-gaps/build/
make -C docs/paper-gaps check    # compile, then fail on any LaTeX error or
                                 # unresolved reference, citation or label
make -C docs/paper-gaps pages    # page count per note
make -C docs/paper-gaps clean    # remove docs/paper-gaps/build/
```

Requirements: `latexmk`, `pdflatex` and `bibtex` from any current TeX
distribution, plus the `amsmath`, `amssymb`, `braket`, `hyperref` and `xurl`
packages. No project-specific tool is needed — that is the point of the
Makefile. `build/` is ignored by the repository `.gitignore` and **no PDF is
committed**; the artifact packaging step builds the PDFs at release time.

`make check` is the standalone gate. The repository's own CI additionally runs
`texra-blueprint --root . paper-gaps check` (the `paper-gaps` step of
`local/bin/ci.sh`), which validates cross-note slugs and registered source keys
using the project's blueprint tool. The two are complementary: CI checks that
the notes refer to each other and to the papers consistently, `make check`
checks that they typeset.

### Writing a new note

Start from [`template.tex`](template.tex) and follow [`policy.tex`](policy.tex),
which is the style guide for this directory: notation matches the cited source
via [`command.tex`](command.tex), and Lean identifiers, file paths and issue
numbers appear in footnotes only. A new note also gets a row in
[`qpbt-gap-register.md`](qpbt-gap-register.md).

## The notes

`command.tex` is a macro file shared by every note and is not compiled on its
own; `references.bib` is the shared bibliography. Everything else below is a
document. "Paper locator" is the source passage the note examines, as the note
itself cites it.

### Quantum Pauli basis test (20 notes)

Source: `references/qpbt-paper/` (arXiv:2001.04383).

| Note | Title | Paper locator | Status |
|---|---|---|---|
| [`qpbt_anticommuting-probability.tex`](qpbt_anticommuting-probability.tex) | The Probability of Anticommuting Pauli Tuples | `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`, lines 64--93 | QPBT; row in [`qpbt-gap-register.md`](qpbt-gap-register.md) |
| [`qpbt_characteristic-two-pauli-scope.tex`](qpbt_characteristic-two-pauli-scope.tex) | Prime-Characteristic and Binary Pauli Observables | `references/qpbt-paper/04_preliminaries.tex`, lines 1056--1161 | QPBT; row in [`qpbt-gap-register.md`](qpbt-gap-register.md) |
| [`qpbt_combined-lines-error-term.tex`](qpbt_combined-lines-error-term.tex) | The Error Term of the Combined-Lines Consistency Lemma | `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`, lines 1020--1034 | QPBT; row in [`qpbt-gap-register.md`](qpbt-gap-register.md) |
| [`qpbt_combined-points-field-valued.tex`](qpbt_combined-points-field-valued.tex) | A Field-Valued Construction of the Combined Point Measurements | `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`, lines 689--709 | QPBT; **no register row yet** (see Open items) |
| [`qpbt_cross-basis-phase.tex`](qpbt_cross-basis-phase.tex) | The Cross-Basis Phase in the Extracted Pauli Observables | `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex` | QPBT; row in [`qpbt-gap-register.md`](qpbt-gap-register.md) |
| [`qpbt_decoding-identity.tex`](qpbt_decoding-identity.tex) | The Decoding Identity in the Pauli Extraction Argument | `references/qpbt-paper/04_preliminaries.tex`, lines 917--924 | QPBT; row in [`qpbt-gap-register.md`](qpbt-gap-register.md) |
| [`qpbt_delta-bound-exponent-comparison.tex`](qpbt_delta-bound-exponent-comparison.tex) | The Exponent Comparison in the Canonical Pauli Basis Test Bound | `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex`, lines 1503--1514 | QPBT; row in [`qpbt-gap-register.md`](qpbt-gap-register.md) |
| [`qpbt_extraction-transfer.tex`](qpbt_extraction-transfer.tex) | Triangle Estimates and Isometry Transfer in Pauli Extraction | `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`, lines 1743--1750 | QPBT; row in [`qpbt-gap-register.md`](qpbt-gap-register.md) |
| [`qpbt_ld-dimension-divisibility.tex`](qpbt_ld-dimension-divisibility.tex) | Dimension Divisibility in the Classical Test Instantiation of the Pauli Basis Analysis | `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`, lines 1267--1288 | QPBT; row in [`qpbt-gap-register.md`](qpbt-gap-register.md) |
| [`qpbt_ld-sandwich-indexing.tex`](qpbt_ld-sandwich-indexing.tex) | Index Pairing in the Low-Degree Sandwich | `references/neexp-paper/05_quantum_preliminaries.tex` | QPBT; row in [`qpbt-gap-register.md`](qpbt-gap-register.md) |
| [`qpbt_ld-simultaneous-sandwich.tex`](qpbt_ld-simultaneous-sandwich.tex) | Simultaneous Polynomial Measurements Are Not Obtained Coordinatewise | `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex`, lines 455--458 | QPBT; row in [`qpbt-gap-register.md`](qpbt-gap-register.md) |
| [`qpbt_linearity-distance-normalization.tex`](qpbt_linearity-distance-normalization.tex) | Distance Normalization in the Quantum Linearity Theorem | `references/nv-paper/fullpaper.tex`, lines 866--912 | QPBT; row in [`qpbt-gap-register.md`](qpbt-gap-register.md) |
| [`qpbt_linearity-theorem-quotation.tex`](qpbt_linearity-theorem-quotation.tex) | Quantum Linearity and a Direct Combined-Point Construction | `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex` | QPBT; row in [`qpbt-gap-register.md`](qpbt-gap-register.md) |
| [`qpbt_ms-rigidity-symmetric-strategies.tex`](qpbt_ms-rigidity-symmetric-strategies.tex) | The Strategy Class in the Rigidity of the Magic Square Game | `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex`, lines 74--92 | QPBT; row in [`qpbt-gap-register.md`](qpbt-gap-register.md) |
| [`qpbt_pasting-product-error.tex`](qpbt_pasting-product-error.tex) | The Product-Form Error in the Two-Measurement Pasting Lemma | `references/qpbt-paper/04_preliminaries.tex`, lines 19--29 | QPBT; row in [`qpbt-gap-register.md`](qpbt-gap-register.md) |
| [`qpbt_pauli-binary-factor-index.tex`](qpbt_pauli-binary-factor-index.tex) | The Binary Factor Index in the Qudit-to-Qubit Isomorphism | `references/qpbt-paper/04_preliminaries.tex`, lines 1172--1198 | QPBT; row in [`qpbt-gap-register.md`](qpbt-gap-register.md) |
| [`qpbt_polynomial-error-square-root.tex`](qpbt_polynomial-error-square-root.tex) | Polynomial Error Notation and Square-Root Bounds | `references/qpbt-paper/04_preliminaries.tex` | QPBT; row in [`qpbt-gap-register.md`](qpbt-gap-register.md) |
| [`qpbt_subline-claims-line-marginal.tex`](qpbt_subline-claims-line-marginal.tex) | The Constructed Measurement in Subline Claim 17-2 | `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex` | QPBT; **no register row yet** (see Open items) |
| [`qpbt_symmetrization-attainment.tex`](qpbt_symmetrization-attainment.tex) | Attainment in the Symmetrization Lemma | `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex`, lines 94--99 | QPBT; row in [`qpbt-gap-register.md`](qpbt-gap-register.md) |
| [`qpbt_win-implications-corrections.tex`](qpbt_win-implications-corrections.tex) | Corrections to the Pauli-Test Winning Implications | `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex` | QPBT; row in [`qpbt-gap-register.md`](qpbt-gap-register.md) |

### Low individual degree test (25 notes)

Source: `references/ldt-paper/` (arXiv:2009.12982), with imports from
`references/neexp-paper/` and `references/nv-paper/`.

| Note | Title | Paper locator | Status |
|---|---|---|---|
| [`issue-1032-orthonormalization-constant.tex`](issue-1032-orthonormalization-constant.tex) | The Constant in the Completion-Route Orthonormalization Theorem | `references/ldt-paper/orthonormalization.tex` | LDT track (arXiv:2009.12982); no QPBT register row |
| [`issue-1093-submeasurement-triangle-total-overlap.tex`](issue-1093-submeasurement-triangle-total-overlap.tex) | Issue 1093: The Total-Overlap Term in Projective Point-Consistency Transport | `references/ldt-paper/self_improvement.tex`, lines 719--726 | LDT track (arXiv:2009.12982); no QPBT register row |
| [`issue-1099-line169-triangle-sub-loss.tex`](issue-1099-line169-triangle-sub-loss.tex) | Issue 1099: The Line-169 Replacement Step in the Main-Induction Projectivization Chain | `references/ldt-paper/inductive_step.tex`, lines 150--180 | LDT track (arXiv:2009.12982); no QPBT register row |
| [`issue-1099-sharper-local-fix.tex`](issue-1099-sharper-local-fix.tex) | Issue 1099: The Sharper Local Repair for the Line-169 Transport Step | `references/ldt-paper/inductive_step.tex`, lines 130--185 | LDT track (arXiv:2009.12982); no QPBT register row |
| [`issue-1100-projective-non-measurement-endpoints.tex`](issue-1100-projective-non-measurement-endpoints.tex) | Issue 1100: Endpoint Branches in the Proof of lem:projective-non-measurement | `references/ldt-paper/orthonormalization.tex`, lines 414--531 | LDT track (arXiv:2009.12982); no QPBT register row |
| [`issue-1228-orthonormalization-svd-usage.tex`](issue-1228-orthonormalization-svd-usage.tex) | Issue 1228: The SVD Step in Orthonormalization | `references/ldt-paper/orthonormalization.tex`, lines 774--845 | LDT track (arXiv:2009.12982); no QPBT register row |
| [`issue-1230-self-improvement-sdp-usage.tex`](issue-1230-self-improvement-sdp-usage.tex) | Issue 1230: How the Self-Improvement SDP Is Used | `references/ldt-paper/self_improvement.tex`, lines 62--88 | LDT track (arXiv:2009.12982); no QPBT register row |
| [`issue-1622-ld-pasting-degree-zero.tex`](issue-1622-ld-pasting-degree-zero.tex) | Issue 1622: The Degree-Zero Branch of Low-Degree Pasting | `references/ldt-paper/ld-pasting.tex`, lines 12--55 | LDT track (arXiv:2009.12982); no QPBT register row |
| [`issue-196-sdp-weakening.tex`](issue-196-sdp-weakening.tex) | Issue 196: The SDP Primal Constraint Is a Submeasurement Constraint | `references/ldt-paper/self_improvement.tex`, lines 64--74 | LDT track (arXiv:2009.12982); no QPBT register row |
| [`issue-2338-ch3-same-space-specializations.tex`](issue-2338-ch3-same-space-specializations.tex) | Chapter 3 Same-Space Specializations of Two-Space Paper Propositions | `references/ldt-paper/preliminaries.tex` | LDT track (arXiv:2009.12982); no QPBT register row |
| [`issue-422-main-formal-zero-k-boundary.tex`](issue-422-main-formal-zero-k-boundary.tex) | The Zero-Sampling Boundary in the Main Formal Theorem | `references/ldt-paper/test_definition.tex`, lines 180--202 | LDT track (arXiv:2009.12982); no QPBT register row |
| [`issue-458-foundation-layer.tex`](issue-458-foundation-layer.tex) | Foundation-layer formalization design: finite fields, distributions, and a zero family | `references/ldt-paper/preliminaries.tex`, lines 17--19 | LDT track (arXiv:2009.12982); no QPBT register row |
| [`issue-713-scalar-tensor-decision.tex`](issue-713-scalar-tensor-decision.tex) | Why the full-slice $ABAB$ transport carries an extra $2\sqrt{\zeta}$ | `references/ldt-paper/commutativity-G.tex`, lines 332--401 | LDT track (arXiv:2009.12982); no QPBT register row |
| [`issue-760-scalar-chain-alignment.tex`](issue-760-scalar-chain-alignment.tex) | The evaluated-slice commutativity estimate for the processed-$G$ measurements | `references/ldt-paper/commutativity-G.tex`, lines 16--47 | LDT track (arXiv:2009.12982); no QPBT register row |
| [`issue-904-zeta2-completion.tex`](issue-904-zeta2-completion.tex) | Issue 904: The Missing Completion Term in the Definition of zeta2 | `references/ldt-paper/inductive_step.tex`, lines 135--149 | LDT track (arXiv:2009.12982); no QPBT register row |
| [`issue-906-main-formal-k-bound.tex`](issue-906-main-formal-k-bound.tex) | The Large-k Side Condition in the Main Induction | `references/ldt-paper/inductive_step.tex` | LDT track (arXiv:2009.12982); no QPBT register row |
| [`issue-930-com-main-dimension-typo.tex`](issue-930-com-main-dimension-typo.tex) | The ambient dimension in the commutativity theorem for $G$ | `references/ldt-paper/commutativity-G.tex`, lines 228--257 | LDT track (arXiv:2009.12982); no QPBT register row |
| [`issue-930-distinct-tuple-support.tex`](issue-930-distinct-tuple-support.tex) | The Support of the Distinct-Tuple Distribution | `references/ldt-paper/ld-pasting.tex`, lines 167--213 | LDT track (arXiv:2009.12982); no QPBT register row |
| [`issue-930-main-induction-successor-coefficient.tex`](issue-930-main-induction-successor-coefficient.tex) | The First Successor-Step Error Absorption in the Main Induction | `references/ldt-paper/inductive_step.tex`, lines 584--620 | LDT track (arXiv:2009.12982); no QPBT register row |
| [`issue-930-pasting-from-H-to-G-error.tex`](issue-930-pasting-from-H-to-G-error.tex) | The Accumulated Error in the Pasting From-H-to-G Lemma | `references/ldt-paper/ld-pasting.tex`, lines 1294--1308 | LDT track (arXiv:2009.12982); no QPBT register row |
| [`issue-930-self-improvement-missing-nu-consistency.tex`](issue-930-self-improvement-missing-nu-consistency.tex) | Resolved Missing $\nu$-Consistency Hypothesis in the Self-Improvement Theorem | `references/ldt-paper/self_improvement.tex`, lines 635--671 | LDT track (arXiv:2009.12982); no QPBT register row |
| [`issue-933-quantumstate-normalization.tex`](issue-933-quantumstate-normalization.tex) | Issue 933: Normalization of Quantum States in the LDT Formalization | `references/ldt-paper/preliminaries.tex`, lines 255--268 | LDT track (arXiv:2009.12982); no QPBT register row |
| [`issue-polynomial-function-divergence.tex`](issue-polynomial-function-divergence.tex) | The polynomial definition: functions with a representative, not function types | `references/ldt-paper/introduction.tex` | LDT track (arXiv:2009.12982); no QPBT register row |
| [`naimark-dilation.tex`](naimark-dilation.tex) | Naimark dilation: projective-submeasurement form and the full bipartite assembly | `references/ldt-paper/orthonormalization.tex`, lines 36--115 | LDT track (arXiv:2009.12982); no QPBT register row |
| [`truncation-combinatorics-f-nonneg.tex`](truncation-combinatorics-f-nonneg.tex) | The Nonnegativity Hypothesis in the Small-Overlaps Bound | `references/ldt-paper/orthonormalization.tex`, lines 606--612 | LDT track (arXiv:2009.12982); no QPBT register row |

### Infrastructure (3 documents)

| Note | Title | Paper locator | Status |
|---|---|---|---|
| [`policy.tex`](policy.tex) | Documenting Possible Gaps, Counterexamples, and Formalization Deviations | -- | Infrastructure (style guide / model note / protocol), not a gap note |
| [`proof-gap-protocol.tex`](proof-gap-protocol.tex) | Proof-Gap Protocol for Source-Faithful Formalization | -- | Infrastructure (style guide / model note / protocol), not a gap note |
| [`template.tex`](template.tex) | Model Note: Comparing a Cited Argument with a Formal Statement | `references/ldt-paper/FILE.tex` | Infrastructure (style guide / model note / protocol), not a gap note |

## Open items

These need a content decision and were deliberately left alone by the build
packet, which changed no mathematics:

- `qpbt_combined-points-field-valued.tex` and
  `qpbt_subline-claims-line-marginal.tex` have no row in
  [`qpbt-gap-register.md`](qpbt-gap-register.md). The register's own closing
  paragraph asks every packet that adds a note to add a row; these two were
  added without one. Someone who knows the correction status of both should
  fill in the register's five columns.
- `texra-blueprint --root . paper-gaps check` reports that most notes lack a
  `\gapnote{kind}{status}` verdict marker. That is advisory today, but the
  marker is what would let the register table be generated from the notes
  instead of maintained beside them.

## See also

- [`qpbt-gap-register.md`](qpbt-gap-register.md) — one row per QPBT note:
  source statement, blueprint label, correction status, Lean status, issues.
- [`policy.tex`](policy.tex) — when a gap is documented, and in what form.
- [`proof-gap-protocol.tex`](proof-gap-protocol.tex) — what the formalization
  does when a printed statement is kept but its printed proof is blocked.
