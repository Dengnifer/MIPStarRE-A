# Subline Scalar Statement Integrity

This is the bounded paper-realignment pass for issue #474 and PR #478.
No B8 proof attempt, historical-budget reset, or new direct hole is introduced.

## Source and Formal Statements

The source is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`,
Claims `claim:17-1` (1140-1166), `claim:17-2` (1168-1201), and
`claim:17-3` (1204-1239). The source assumes the projective strategy, its
constructed measurements, and the subline law D. Claim 17-2 specifically uses
the X-Z-X measurement of lines 942-949. The conclusions compare complex
expectations in modulus, with errors of order sqrt(deltaQ),
m sqrt(deltaLine), and sqrt(m)(deltaP^(1/4)+deltaQ^(1/4)+epsilon^(1/4)).

The retained proved Lean estimates `subline_replace_by_ordered_product_re_direct`
and `subline_Z_term_near_one_re_direct` use the existing joint-point and
joint-line witness properties and the directly indexed `SubLineWitness` law.
They compare real parts, with universal constant 2. Relative to the source,
the verdict is **weakened conclusion**, together with a changed distribution
domain. They are now explicitly formalization-only auxiliaries, with separate
blueprint entries. Their statements and useful proofs are preserved.

`subline_remove_X_factor_direct` retains the projective strategy and concrete
X-Z-X measurement, but uses the directly indexed law. Its conclusion is now
the complex modulus of the two weighted expectations, at the original error
scale. Scalar verdict: **exact**; distribution verdict: a documented auxiliary
domain, not a faithful encoding of the source law. No bridge, deficit, equality,
or transport assumption is added.

The existing source-shaped blueprint statements `lem:claim-17-1`,
`lem:claim-17-2`, and `lem:claim-17-3` remain unchanged and uncertified. Their
unsupported Lean links are removed. No exact source-law Lean obligation was
found in the current branch or main; the existing blueprint obligations are
reused instead of inventing another carrier or adding duplicate proof holes.
No statement asserts that the directly indexed distribution is the source law.

The combined-point theorem and restricted-law declarations have unchanged
statements. Their blueprint proof/status synchronization records the existing
field-valued sandwich proof and the proved normalization/inflation results.
For the combined-point theorem: paper and Lean assume a projective winning
strategy and conclude a polynomially controlled projective joint family with
both ordered-product comparisons and symmetric equivalents. Verdict: **exact**.

## Retained Holes and Discharge Targets

1. `Claims.lean`: `subline_remove_X_factor_direct`, formerly the real-part
   `subline_remove_X_factor` hole. Apply complex weighted Cauchy--Schwarz,
   then `exists_concreteXPointOverlap_deficit_le`; that theorem already uses
   the concrete X marginal. Tracked by issues #414/#474 and
   `docs/paper-gaps/qpbt_subline-claims-line-marginal.tex`.
2. `Lines.lean`: `combined_line_measurement_consistency`, unchanged. Prove
   consistency of the unconditioned concrete X-Z-X measurement under the
   original product law using source lines 900-961. Tracked by issues #18/#414
   and `docs/paper-gaps/qpbt_combined-lines-error-term.tex`. A conditioned
   construction does not discharge this without a proved transfer back.

The source-distribution transport and complex Claim 17-1 remain named blueprint
obligations, without additional Lean holes. Their gap citations are
`qpbt_ld-dimension-divisibility.tex` and `qpbt_subline-claims-line-marginal.tex`.
B8/#118 remains at its historical 13 attempts and 26,509 working seconds.

## Review Disposition

F1/F4/F5/F6: separate scalar and distribution domains, remove unsupported
certification, restore the pending complex scalar estimate, and use W-adjoint W
with squared-distance constant 4. F2: reuse placement support and existing
completion/product-average lemmas. F3: describe the actual unconditioned target.
F7/F8/F9/F10: synchronize nearby proof/status links and add explicitly scoped
X-deficit support entries. F11: replace implementation-history prose.

The changes add no assumptions or witnesses and introduce no proof-evasion
pattern from A1-A6. All preserved branch commits and historical proofs remain.
