# Independent Review - PR 626 @ cafe0b5727f50714a2842acf5628f367c2b3a949

reviewer_session: native-sol-space-3-independent
base: main (`04f79c5071d020fc4578b9ae11808eff2daa575b` merge base)
ci_status: supplied exact-head canonical CI success

Archive normalization: trailing Markdown whitespace removed. Original artifact SHA256:
`1f304eb957ee66616d66298366e1967e81acc84c633f9bf76a398b46e2b7cbd0`.

## Findings

- [x] `MIPStarRE/QPBT/Combining/ExtendedLineGame/SuppliedDirectSoundness.lean:47` - No correctness or statement-preservation defect found. The theorem derives the game-passing premise internally at lines 100-120, retains the two original expanded carriers and all three original `deltaLd` defects, and does not assert projectivity or a paired measurement.
- [x] `MIPStarRE/QPBT/Combining/ExtendedLineGame/SuppliedScalarPolynomialConsistency.lean:46` - No correctness or statement-preservation defect found. The proof takes the unique `Fin 1` coordinate marginal, applies consistency data processing to the two point comparisons and the mutual polynomial comparison, and uses the exact supplied-point identity at lines 149-156 and 188-195.
- [x] `blueprint/src/chapter/ch15_qpbt_combining.tex:4377` and `blueprint/src/chapter/ch15_qpbt_combining.tex:4414` - The new nodes are distinct formalization-only auxiliary theorems. They state the supplied-witness restrictions and explicitly disclaim construction, projectivity, polynomial separation, and the source paired-polynomial conclusion. They do not replace or inherit the source label `lem:qld-4-7` at line 4195.

No unresolved findings.

## Statement Integrity Audit

Paper `lem:qld-4-7`, `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1289`, constructs for each player a projective measurement whose outcomes are polynomial pairs `(g_X,g_Z)` and proves the two basis-indexed point-consistency conclusions. Its statement does not assume supplied combined-point or extended-line witnesses.

The direct Lean auxiliary assumes admissible parameters, a `ProjectiveSetting`, a supplied `CombinedPointsWitness`, and a supplied `ExtendedLinesWitness`. It concludes the existence of two complete polynomial-tuple POVMs on the original expanded player spaces with two point-polynomial defects and one mutual polynomial defect. The scalar auxiliary has the same assumptions and quantifier order, and concludes the corresponding ordinary scalar-polynomial marginals and the same three bounds. Neither conclusion supplies projectivity, polynomial separation, or a single paired-polynomial measurement.

Verdict on source fidelity: both Lean declarations have extra supplied-witness assumptions and weaker/different conclusions relative to the paper lemma, so neither is the source theorem. That boundary is accurately represented: the names end in `_of_supplied_witnesses`, the docstrings and blueprint call them formalization-only conditional auxiliaries, and the source-labelled node remains separate. The unresolved source work remains tracked by issues #527, #598, and #524.

Historical interface audit: against tuple head `462953fc0dcc468e945082cd787acf76917b2474` and scalar head `e6ff96075f48b084e5377f76d5eeb50337a45fc6`, the public binders, witness types, quantifier order, expanded spaces, and three bounds are preserved. The scalar theorem receives the intended mathematical rename. Replacing `3 * (Real.sqrt (deltaQ + deltaL) + m*d/q)` by `directPassingErrorEnvelope (deltaQ + deltaL) (m*d/q)` is definitional equality by `PassingError.lean:24-25`.

## Proof Review

The direct proof applies arbitrary-strategy `k = 1` soundness, proves positivity of `m*d/q` from admissibility, and supplies `strategy_value_ge_directPassingErrorEnvelope lines`; there is no caller-supplied passing hypothesis. The scalar proof is the preserved historical proof: evaluation commutes with coordinate marginalization, `consistencyDefect_postprocess_le` provides all three monotonicity steps, and `point_values_measurement_eq_suppliedQ` identifies the scalar point readout exactly. I found no A1-A6 proof-evasion pattern, fallback witness, hidden projectivity claim, or private-helper duplication introduced by this diff.

## Validation Limits

- Read the cited paper passage before the Lean diff and inspected all five changed files.
- Compared both theorem implementations against the two requested historical commits.
- Ran focused `lake env lean` checks for both new Lean modules; both passed.
- Ran `git diff --check`, a changed-file prohibited-construct scan, line-length checks, and blueprint-label resolution; these passed.
- Inspected the exact-head CI manifest and relevant proof-evasion, proof-debt, blueprint-sync, and build logs. The advisory duplicate-helper candidates are outside the changed files.
- Did not rerun the full build, canonical CI, blueprint render, or the separate 1,763-declaration axiom audit, per the review constraints. The supplied evidence reports all canonical contexts successful and the supplemental audit at 0 failures.

VERDICT: APPROVED (code=APPROVED, prose=APPROVED)
