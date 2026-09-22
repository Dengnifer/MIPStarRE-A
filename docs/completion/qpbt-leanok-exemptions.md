# QPBT blueprint exemptions

No permanent exemption is granted by the source-adoption audit of issue #667
at source snapshot `e947a49e14080b46642be21ce551d911032a05f4`.
The table intentionally has no data rows.

| Blueprint label | Reason |
|---|---|

The following are unresolved matches, not exemptions. Their continued absence
of a formalization mark must keep C4 failing. Construction targets and the
row-by-row adoption evidence are in the
[gap register](../paper-gaps/qpbt-gap-register.md#source-adoption-audit-2026-09-22).

1. `lem:qld-xz-lines`: the complete unconditioned line construction is proved,
   but its witness states consistency on completed evaluations. The source
   uses field-valued evaluations, including its unresolved zero-direction
   convention. See [the subline note](../paper-gaps/qpbt_subline-claims-line-marginal.tex).
2. `def:combine-map`: global polynomial combination and the coefficient formula
   are proved; `combineLinePoly_spec` assumes explicit affine compatibility.
   Derive it from the source line-projection domain and justify evaluations on
   degenerate lines (`14_analysis_of_the_pauli_basis_test.tex:970-989`).
3. `lem:qld-4-13`: `PrintedExtendedLinesWitnessClaim` is unasserted and uses
   the directly indexed carrier and completed evaluations. Its error form is
   not established by the proved `C m poly(epsilon,md/q)` auxiliary. See
   [the error note](../paper-gaps/qpbt_combined-lines-error-term.tex) and
   [the dimension note](../paper-gaps/qpbt_ld-dimension-divisibility.tex).

`lem:canonical-complement` is now marked at both statement and proof level.
`isCompl_span_rows_canonicalComplement` derives an RREF presentation and its
correspondence with the intrinsic complement from the independent input rows,
then proves the source complement conclusion using the pivot-coordinate
decomposition. No RREF, correspondence, or complement hypothesis is assumed.
This resolves the former canonical-complement lemma row.

`def:canonical-complement` is now marked as well. The deterministic stored-matrix
program `gaussianElimination` supplies the construction in
`04_preliminaries.tex:303-333`. Its independent-row correctness theorem derives
RREF, row-span preservation, and equality of the computed nonpivot indices
with `canonicalComplement`. Its counter is bounded by `n*(m+n+2*m*n)` under
unit-cost field division, multiplication, subtraction, and equality tests.
The arbitrary-field result requires executable operations and decidable
equality; it is an arithmetic-operation bound for materialized input, not a
machine-instruction, allocation, or bit-complexity claim. The predecessor
cardinality, independence, basis-independence, and register-subspace results
remain linked. This discharges the former algorithmic obligation without an
exemption; see the [integration audit](../../audits/2026-09-22_issue-690-canonical-integration.md).
Full CI, independent review, and merge of this adoption remain with main.

`def:generalized-pauli` is marked, and `lem:pauli-observable-expansion` is
marked at both statement and proof level. The general-prime eigenvectors,
projectors, and both Fourier identities are formalized, closing their former
unresolved rows. See
[the scope note](../paper-gaps/qpbt_characteristic-two-pauli-scope.tex).

The four CL definition nodes audited in chapter 12 now carry marks for their
faithful recursive predicates and shared-seed sampling laws. No theorem or
definition was weakened to obtain those marks, and no proof-level mark was added.
