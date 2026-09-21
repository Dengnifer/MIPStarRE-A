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

1. `def:canonical-complement`: `canonicalComplement` uses prefix ranks;
   the source uses the nonpivot columns of reduced row echelon form
   (`04_preliminaries.tex:303-320`). The equality of these presentations and
   the algorithmic assertion are not formalized.
2. `lem:canonical-complement`: `isCompl_registerSubmodule_canonicalComplement`
   proves complementarity for the prefix-rank definition. The same
   presentation comparison is needed for the source node
   (`04_preliminaries.tex:342-373`). A different proof strategy alone would
   not justify withholding a mark; the remaining issue is the represented object.
3. `def:generalized-pauli`: general-prime matrices exist, but the linked
   eigenvectors and projectors require characteristic two. See
   [the scope note](../paper-gaps/qpbt_characteristic-two-pauli-scope.tex).
4. `lem:pauli-observable-expansion`: the two linked Fourier identities have
   only the characteristic-two domain, whereas the source equations are
   general-prime. The same scope note records the missing constructions.
5. `lem:qld-xz-lines`: the complete unconditioned line construction is proved,
   but its witness states consistency on completed evaluations. The source
   uses field-valued evaluations, including its unresolved zero-direction
   convention. See [the subline note](../paper-gaps/qpbt_subline-claims-line-marginal.tex).
6. `def:combine-map`: global polynomial combination and the coefficient formula
   are proved; `combineLinePoly_spec` assumes explicit affine compatibility.
   Derive it from the source line-projection domain and justify evaluations on
   degenerate lines (`14_analysis_of_the_pauli_basis_test.tex:970-989`).
7. `lem:qld-4-13`: `PrintedExtendedLinesWitnessClaim` is unasserted and uses
   the directly indexed carrier and completed evaluations. Its error form is
   not established by the proved `C m poly(epsilon,md/q)` auxiliary. See
   [the error note](../paper-gaps/qpbt_combined-lines-error-term.tex) and
   [the dimension note](../paper-gaps/qpbt_ld-dimension-divisibility.tex).

The four CL definition nodes audited in chapter 12 now carry marks for their
faithful recursive predicates and shared-seed sampling laws. No theorem or
definition was weakened to obtain those marks, and no proof-level mark was added.
