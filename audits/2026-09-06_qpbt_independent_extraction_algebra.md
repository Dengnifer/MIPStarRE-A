# Independent extraction algebra: issue #240

## Scope and source

Starting revision: `a61ee557b33a2d8a4721e92b08b6d06dcb69ed57`.

The changes concern five declarations in
`MIPStarRE/QPBT/Extraction/Observables.lean`:

- `GlobalPairWitness.marginalPoly_isProjective`;
- `tildeObs_eq_heteroKron`;
- `tildeObs_isHermitian`;
- `tildeObs_mul_self`;
- `tildeObs_twisted_commutation`.

The source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1421-1456`,
especially `eq:tilde_M`, `eq:def-tildewj`, and the displayed product calculation.
The corresponding blueprint entries are `def:s-w-marginals`,
`lem:s-w-marginals-projective`, and `lem:tildew-product-form`, including
`eq:tildew-twisted-commutation`. The proof of `lem:tildew-product-form` now has
its proof-level `\leanok` tag. Its existing declaration links are unchanged.
The dot-product-projector node is unchanged.

## Mathematical argument

Write \(\chi_c(a)=(-1)^{\operatorname{tr}(ca)}\). For any scalar offset \(b\),
the defining coarse-graining and the Pauli Fourier expansion give
\[
  \sum_a \chi_c(a)\tau^W_{b-a}(u)
  =\sum_h\chi_c(b-h\mathbin{\cdot}u)\tau^W_h
  =\chi_c(b)\tau^W(cu).
\]
The first equality reindexes by the bijection \(a\mapsto b-a\), then sums the
fibers of \(h\mapsto h\mathbin{\cdot}u\). The second uses additivity of the
binary trace, invariance of the sign under negation in characteristic two,
and `tauObservable_eq_sum_pauliProj`. This calculation does not use
projectivity of the dot-product effects.

Apply this identity for each polynomial outcome and then sum the fibers of
`PauliKind.selectPoly`. Bilinearity of `heteroKron` gives the product form in
the paper. Finite postprocessing preserves projectivity of the polynomial
marginal by `SandwichProduct.postprocess_isProjective`.

The first tensor factor is a sign-weighted sum of the mutually orthogonal
joint projectors. Hermiticity follows from real coefficients and Hermiticity
of the effects; for the Pauli factor the same argument uses its Fourier
expansion and the adjoint identity for a rank-one outer product. For the
involution and commutation calculations, the proof reuses
`MagicSquareRigidity.signObs_mul_self` and `MagicSquareRigidity.signObs_comm`.
The private identity `phaseSign_eq_complex_bitSign` identifies their real
sign convention with the complex character. No alternative spectral-sum
infrastructure is introduced.

The generalized Pauli relation leaves precisely the phase
\[
  (-1)^{\operatorname{tr}(e_j e_{j'}(u\mathbin{\cdot}v))}.
\]
The incorrect omission of this phase in the source when \(j\ne j'\) is
already documented in `docs/paper-gaps/qpbt_cross-basis-phase.tex` and issue
#19. This change proves the existing corrected statement; it changes neither
the phase nor the domain of register vectors. The discrepancy note's old
sentence saying the proof is open is outside this packet's write scope.

## Statement-integrity audit

**Paper assumptions.** The joint polynomial-pair measurement of
`lem:qld-4-7` is given and projective. The field has characteristic two, the
binary basis is fixed, and the assertions concern either player, either
Pauli basis, arbitrary register vectors, and arbitrary binary-basis indices.
This is a local calculation after the measurement is supplied, not its
construction theorem.

**Lean assumptions.** The existing parameters `P`, `epsilon`, `delta`,
`S : ProjectiveSetting P epsilon`, and `w : GlobalPairWitness S delta` are
unchanged, as are the player, basis, vector, and index arguments. No new
boundary condition or proof-obligation argument is added. Although the
witness type also contains consistency estimates, none of these proofs uses
those fields.

| Declaration | Paper conclusion | Lean conclusion | Verdict |
| --- | --- | --- | --- |
| `marginalPoly_isProjective` | Each single-basis marginal is projective. | `Measurement.IsProjective` of the same finite marginal. | Exact. |
| `tildeObs_eq_heteroKron` | The displayed product form. | The joint sign-weighted sum tensor the generalized Pauli observable. | Exact. |
| `tildeObs_isHermitian` | Each pulled-apart observable is Hermitian. | `Matrix.IsHermitian` of that observable. | Exact. |
| `tildeObs_mul_self` | Each pulled-apart observable squares to the identity. | Its matrix square equals `1`. | Exact. |
| `tildeObs_twisted_commutation` | The printed cross-index dichotomy is false in general; the documented correction retains the full trace phase. | The pre-existing full-phase identity, for all indices and vectors. | Exact to the corrected blueprint; the existing local correction is retained. |

The source-header comparison reports no changed public headers. Definitions,
quantifier order, error parameters, and conclusions are preserved. The
changes introduce no conclusion-shaped assumption, replacement definition,
default witness, axiom, or proof bypass.

## Verification and independence

`lake env lean MIPStarRE/QPBT/Extraction/Observables.lean` passes, with only
the six warnings for unchanged open declarations listed below. The source
scan finds exactly six `sorry` occurrences, down from eleven, and no `axiom`
declaration or other forbidden proof-integrity token. The edited Lean file
has no lines exceeding 100 characters.

For all five completed declarations, `#print axioms` reports exactly
`[propext, Classical.choice, Quot.sound]`. The same check passes for the
postprocessing, Fourier, Pauli-square, Pauli-commutation, and spectral-sum
lemmas used by these proofs.

A traversal of project-local proof-body dependencies confirms that the
product-form proof uses only `GlobalPairWitness.Smeas` and the definition of
`marginalPoly`. The other four proofs use only the supplied measurement and
its `projective` field. In particular, none depends on
`exists_globalPairWitness`, either point-consistency field,
`tauDotProj_isProj`, `sum_tauDotProj_eq_one`, `tildeM_isProj`, or
`sum_tildeM_eq_one`.

The copied cache omitted some already-merged supporting declarations.
Therefore a private overlay recompiles the unchanged sources
`LDT/Basic/DistributionAvg`, `QPBT/Algebra/Pauli`, `QPBT/Algebra/Decoding`,
`QPBT/Observables/Defs`, `QPBT/Observables/ExpandedDefs`,
`QPBT/Combining/Witnesses`, and `QPBT/Extraction/Defs`, followed by the edited
file. All these single-file checks pass. The axiom and dependency checks use
the newly compiled edited module in this overlay, not its original cached
object. No shared cache is modified or published.

The `leanblueprint web` command also passes, with bibliography warnings,
through a private-root invocation of its installed CLI. The LaTeX convention
check passes. The repository-wide blueprint-index check still reports 1,387
missing entries in `blueprint/lean_decls`; that index is unchanged. It finds
no missing Lean declarations. Adding the completed product proof's tag
reduces the count of headers lacking proof tags from 19 to 18. This packet
does not repair the unrelated index omissions.

Full `lake build`, local CI, independent review, publication, and merge are
not run in this proof session. The targeted checks validate these proofs
with unchanged public signatures; the normal integration gates remain required.
Logs, the overlay, and the rendered blueprint are private artifacts under
`~/.cache/mipstarre-dev/prover-240-20260906-01/`.

## Remaining obligations

The following six `sorry` sites in the edited file are unchanged. Their
existing docstrings track them under issue #47 and cite the source passages
listed here; no additional mathematical discrepancy is asserted.

| Open declaration | Expected discharge | Source passage |
| --- | --- | --- |
| `tildeM_isProj` | Orthogonality of the now-projective polynomial marginal and a proof of `tauDotProj_isProj`. | Lines 1425–1435, `eq:tilde_M`. |
| `sum_tildeM_eq_one` | A proof of `sum_tauDotProj_eq_one`, finite reindexing, and completeness of the marginal. | Lines 1425–1435, `eq:tilde_M`. |
| `swapUnitary_mul_conjTranspose` | Joint-projector orthogonality and Pauli involution identities. | Lines 1687–1699. |
| `conjTranspose_mul_swapUnitary` | The reverse orthogonal-projector calculation. | Lines 1687–1699. |
| `swapUnitary_conj_tildeObs` | The now-proved product form, diagonal projector reduction, and Pauli commutation. | Lines 1701–1713. |
| `swapUnitary_conj_tildeM` | Expansion of dot-product effects and Pauli conjugation of their rank-one summands. | Lines 1701–1713. |

`exists_globalPairWitness` in `QPBT/Combining/Apply.lean` remains open, as do
the subsequent extraction and consistency obligations. Its source-import
obligations are recorded in `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.
This packet supplies only the independent algebraic facts: it does not
discharge the integration gates of #119, #120, or #121, and does not establish
the final soundness or extraction theorem.
