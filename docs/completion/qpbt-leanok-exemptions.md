# QPBT blueprint exemptions

The source-adoption audit of issue #667 granted no permanent exemption at
source snapshot `e947a49e14080b46642be21ce551d911032a05f4`.
The entry below is separately authorized by the owner's 2026-09-22
"document, don't prove" instruction for issue #710 and its PR #716
documentation repair. It records an unmarked source comparison; it is not
a proof certificate or a change to the registered Lean theorem.

| Blueprint label | Reason |
|---|---|
| `lem:ld-soundness` | The source display uses the original prescribed point-answer effects. The linked `exists_ld_soundness` proves the three bounds with point POVMs completed by `ldPointValuesOrZero`, adding all wrong-form answer effects at the zero tuple. The hypotheses do not force that remainder to vanish. Positivity gives the prescribed-effect bounds from the completed bounds with the same error, but this implication is not stated by the linked Lean declaration. Only `lem:ld-soundness-formalized`, which explicitly states the completed POVMs, retains statement and proof marks. The source entry and its printed tensor-code proof remain unmarked; the game correspondence and valid-parameter error absorption also remain unverified (#527). The [dimension note](../paper-gaps/qpbt_ld-dimension-divisibility.tex), `rem:ld-soundness-provider`, and [DEVIATIONS c2](../DEVIATIONS.md#c2-dimension-divisibility-in-the-classical-test-instantiation) explain the comparison. This documentary exemption under #710 does not assert a kernel proof, alter the theorem, or exempt any other node. |

The following are unresolved matches, not exemptions. Their continued absence
of a formalization mark must keep C4 failing. Construction targets and the
row-by-row adoption evidence are in the
[gap register](../paper-gaps/qpbt-gap-register.md#source-adoption-audit-2026-09-22).

1. `def:canonical-complement`: `canonicalComplement` uses prefix ranks;
   the source uses the nonpivot columns of reduced row echelon form
   (`04_preliminaries.tex:303-340`). Their equality, basis independence,
   cardinality, independence of the selected vectors, and the register-subspace
   case are proved. The remaining obligation is a deterministic executable
   Gaussian-elimination construction, with correctness and a polynomial bound
   on field operations and zero tests. Abstract RREF existence and an executable
   decomposition given an RREF matrix do not establish that claim. This
   obligation remains open until issue #690 receives CI, independent review,
   and merge. See the
   [canonical-complement audit](../../audits/2026-09-22_issue-676-canonical-completion.md).
2. `lem:qld-xz-lines`: the complete unconditioned line construction is proved,
   but its witness states consistency on completed evaluations. The source
   uses field-valued evaluations, including its unresolved zero-direction
   convention. See [the subline note](../paper-gaps/qpbt_subline-claims-line-marginal.tex).
3. `def:combine-map`: global polynomial combination and the coefficient formula
   are proved. Issue #695 derives affine compatibility from projection inclusion,
   including constant projections and zero directions, and proves the parameter
   formula and degree bound in `exists_combineLinePoly_of_projection_mem`.
   Field-valued evaluation on the full coefficient carrier is still unavailable:
   `not_evaluatesTo_parameter_on_zero_direction` proves that the answer `T`
   has no value on a singleton line. The source uses functions on lines, so
   carrier correspondence and representative independence remain required
   (`14_analysis_of_the_pauli_basis_test.tex:970-989`). See
   [the focused audit](../../audits/2026-09-22_combining-map-source-domain.md).
4. `lem:qld-4-13`: `PrintedExtendedLinesWitnessClaim` is unasserted and uses
   the directly indexed carrier and completed evaluations. Its error form is
   not established by the proved `C m poly(epsilon,md/q)` auxiliary. See
   [the error note](../paper-gaps/qpbt_combined-lines-error-term.tex) and
   [the dimension note](../paper-gaps/qpbt_ld-dimension-divisibility.tex).

`lem:canonical-complement` is now marked at both statement and proof level.
`isCompl_span_rows_canonicalComplement` derives an RREF presentation and its
correspondence with the intrinsic complement from the independent input rows,
then proves the source complement conclusion using the pivot-coordinate
decomposition. No RREF, correspondence, or complement hypothesis is assumed.
This resolves the former canonical-complement lemma row without exempting the
definition's remaining algorithmic assertion.

`def:generalized-pauli` is marked, and `lem:pauli-observable-expansion` is
marked at both statement and proof level. The general-prime eigenvectors,
projectors, and both Fourier identities are formalized, closing their former
unresolved rows. See
[the scope note](../paper-gaps/qpbt_characteristic-two-pauli-scope.tex).

The four CL definition nodes audited in chapter 12 now carry marks for their
faithful recursive predicates and shared-seed sampling laws. No theorem or
definition was weakened to obtain those marks, and no proof-level mark was added.
