# The separated polynomial image: statement integrity

Issue #284 concerns the algebraic combining map in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-983`
and the separated locus used at lines 1327-1374, immediately before
`eq:qld-g-non-separable` and in `eq:qld-sgg-completeness`.
The corresponding blueprint locations are `def:combine-map` and the proof of
`lem:qld-4-7`. The new module is
`MIPStarRE/QPBT/Combining/CombinedPolynomialImage.lean`, imported by the
existing QPBT aggregate so the ordinary library build checks it.

For polynomials in two disjoint blocks of `m` point coordinates, write

\[
  C(f,g)(x,z,\alpha,\beta)=\alpha f(x)+\beta g(z).
\]

The paper first restricts to polynomials homogeneous linear in `alpha, beta`
and then identifies the separated locus by requiring that their two
coefficients depend only on `x` and `z`, respectively. The construction below
isolates this algebraic identification. It does not prove that a polynomial
measurement assigns large mass to this locus.

## Separation and reconstruction

- Paper assumptions: a polynomial in the homogeneous linear locus has the
  form `alpha * g_1(x,z) + beta * g_2(x,z)`. Separation means that `g_1` depends
  only on `x` and `g_2` only on `z`.
- Lean assumptions: `K` is a commutative semiring and `m` is a natural number.
  `IsSeparatedCombined p` requires every coefficient in `alpha, beta` outside
  the two standard basis exponent vectors to vanish. The variable set of
  each remaining coefficient is contained in the image of its respective
  point-block inclusion. No pair of polynomials, image-membership assertion,
  inverse property, or decoder-correctness hypothesis is assumed.
- Paper conclusion: the separated locus consists of the polynomials
  `C(f,g)`, with `f` in the `x` variables and `g` in the `z` variables.
- Lean conclusion: `isSeparatedCombined_iff_exists_combinePoly` characterizes
  this image. `recoverCombinedPoly` specializes the two combining variables
  to a standard basis vector and sets the other point block to zero.
  `recoverCombinedPoly_combinePoly` recovers each component, and
  `combinePoly_recoverCombinedPoly` reconstructs every separated polynomial.
  `combinePoly_injective` proves uniqueness for actual polynomial pairs.
- Verdict: exact algebraic encoding of separation and reconstruction. The
  extension from a finite field to a commutative semiring is proved, rather
  than assumed; no nontriviality or positive-dimension restriction is needed.
  These are formalization-only auxiliary statements, not separately labelled
  theorems from the source.

The reconstruction uses the proved coefficient criterion
`combinePolyTuple_combinedCoef_iff`. Variable-set containment is converted
into a polynomial in the corresponding block using Mathlib's theorem
`MvPolynomial.exists_rename_eq_of_vars_subset_range`: substitute zero for
variables outside that block, then rename the remaining variables back.
Containment ensures that this substitution leaves each monomial unchanged.
Mathlib's `killCompl_rename_app` identifies the result with the explicitly
defined specialization. Thus the existence theorem does not replace the
requested recovery map with a chosen inverse.

## Individual degrees and the bounded image

- Paper assumptions: `f,g` belong to `ideg_(d,m)`, and the admissible degree
  parameter bounds the two fresh linear coordinates. A separated polynomial
  under consideration belongs to `ideg_(d,2m+2)`.
- Lean assumptions: `polyFunc n K d` is the existing space of actual
  multivariate polynomials with every individual degree at most `d`.
  Recovery of bounded components assumes `p` belongs to this space and is
  separated. The equivalence between bounded pairs and the bounded separated
  locus additionally assumes `1 <= d`.
- Paper conclusion: `C(f,g)` has individual degree at most `d`, and the
  separated image can be indexed by pairs in `ideg_(d,m)` as in
  `eq:qld-sgg-completeness`.
- Lean conclusion: `recoverCombinedPoly_mem_polyFunc` obtains the component
  bounds from the degree of `p`; it remains valid for `d = 0`.
  `combinePoly_mem_polyFunc_iff` proves both directions of the degree
  characterization for `1 <= d`. `existsUnique_bounded_combinePoly` proves
  unique bounded reconstruction, including for `d = 0`.
  `combinedPolynomialImageEquiv` gives the two-sided equivalence between
  actual bounded pairs and `SeparatedCombinedPoly m K d` for `1 <= d`.
- Verdict: faithful boundary hypothesis. Over a nontrivial semiring,
  `C(1,0) = alpha` has degree one in `alpha`, so a forward map on all
  degree-zero pairs cannot take values in the degree-zero locus. No such
  restriction is required to recover the components of a polynomial already
  known to lie in that locus.

The reverse degree bound uses `combinedCoef_mem_polyFunc` and preservation of
individual degree under an injective renaming. The forward direction uses
the proved `combinePolyTuple_mem_polyFunc` after embedding the two separate
point blocks. It does not use the admitted `combinePoly_mem_polyFunc` in
`Combining/Defs.lean`.

## Scope and proof integrity

No existing theorem statement, game definition, blueprint claim, or proof
hole is changed. In particular, `PolynomialImageBounds`, `BlockSpecialization`,
and `Defs.lean` are untouched. The new module makes no assertion about bad
mass, the quantitative correlation estimates, or the existence of a global
polynomial-pair measurement. Issue #283's nonconstant-block specialization
estimate and the quantitative mathematical-gap work remain separate.

On 2026-09-06, the following checks passed:

- `lake env lean MIPStarRE/QPBT/Combining/CombinedPolynomialImage.lean` completed
  without diagnostics.
- The new module has no matches for proof holes, explicit axiom declarations,
  forbidden kernel bypasses, placeholder tactics, or debug commands.
- `#print axioms` was run on every one of the sixteen public declarations
  listed below. Their closures are subsets of `propext`, `Classical.choice`,
  and `Quot.sound`; none contains `sorryAx` or a project axiom.
- `scripts/install_git_hooks.sh --check` passed for the issue worktree.

The axiom audit covers the following declarations in `MIPStarRE.QPBT`:

```text
combinedBlockVar
combinedBlockVar_injective
combinePoly_eq_combinePolyTuple
IsSeparatedCombined
recoverCombinedPoly
recoverCombinedPoly_combinePoly
combinePoly_injective
isSeparatedCombined_combinePoly
rename_recoverCombinedPoly
combinePoly_recoverCombinedPoly
isSeparatedCombined_iff_exists_combinePoly
recoverCombinedPoly_mem_polyFunc
combinePoly_mem_polyFunc_iff
existsUnique_bounded_combinePoly
SeparatedCombinedPoly
combinedPolynomialImageEquiv
```

Publication CI and independent review must bind to the eventual pull-request
head. The targeted checks above are not a full-project build or a review
receipt.
