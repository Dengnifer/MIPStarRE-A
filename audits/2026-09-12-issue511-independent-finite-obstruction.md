# Issue 511: independent finite POVM obstruction

Session `prover-511-20260912-02`, dispatched at 2026-09-12T05:41:30Z.
Pinned base: `d647a4818ef43092aa66404834b99f2cb292ede8`.

## Result and Limits

The target `exists_extendedLinesWitness_established_ofPointsWitness` is not
discharged. Its public signature and existing proof hole are unchanged.
The independent contribution is `Combining/QuadraticPointObstruction.lean`:

- Deterministic joint answers `(x_0^2, 0)` give a projective point witness at
  some scalar error for every projective setting. Their completed combined
  answer is exactly `some (alpha * x_0^2)`.
- A finite POVM supported on polynomials of degree at most one has the
  repository's actual `consistencyDefect` at least `1 - 2/card K` against
  `alpha*x^2`, for every nonzero `alpha` and every unit state.
- The same estimate holds on the completed answer alphabet.
- The POVM may depend arbitrarily on `alpha`. Averaging that coefficient
  uniformly gives `(1 - 1/card K)*(1 - 2/card K)`.
- `eight_element_affine_povm_obstruction` specializes to the canonical Pauli
  field at the explicit admissible tuple `(q,m,d) = (8,1,1)`, with bound
  `21/32` and actual finite coefficient-vector outcomes.

These are closed finite counterexample calculations, not a formal negation of
the full construction theorem. The formal transport of this average to the
four-dimensional direct line law, with X-axis mass `1/8`, remains open here.
The bound `21/256` for that contribution is therefore still a mathematical
consequence described in the gap note, not the conclusion of a Lean theorem.
A fixed field of size eight alone does not refute the existential choice of
universal constants. The full contradiction uses the general field-size bound,
unbounded admissible sizes, and a perfect strategy for each size. The formal
perfect-strategy construction is also still admitted. No completeness
admission or `GlobalPairWitness` is used by these new lemmas.

## Source and Statement Audit

Read the source before implementation:
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`,
`lem:qld-4-13` at 1020-1034, construction at 1118-1132, and `claim:17-1`
at 1140-1173; the preceding constructed points are in `lem:qld-4-10` and
`lem:qld-4-12`. Read blueprint `lem:qld-4-13-established` and
`rem:qld-4-13-source-defects`. The new lemmas are counterexample support,
not paper-labelled theorems, so no blueprint completion marker is added.

Paper assumptions: an admissible projective strategy and the preceding
constructed points with polynomially controlled error. Lean assumptions:
the same strategy domain, followed by every real point error and every point
witness at that error. Paper conclusion: two field-answer line consistency
estimates, degree `md+1`, and degree `d` on axes. Lean conclusion: the existing
directly indexed, completed-answer witness with error
`C*m*deltaCombine(epsilon,md/q)`, independent of the supplied point error.
Verdict: the unrestricted point quantifier is an unsupported strengthening.
The target signature, constants, quantifier order and proof body are preserved;
its docstring now identifies the deviation and precise formal limits.

## Provenance

The first attempt's immutable report is
`~/.cache/mipstarre-dev/sessions/prover-511-20260912-01.last.md`;
its published head is `23022fa0b23c4b152afc6c655affe5ad734a1b45` (PR #525).
That attempt supplied prose, not the POVM formalization proved here.
The first attempt's worktree was not edited.

All-ref history of `Apply.lean` was inspected. The saved construction at
`6e8d67ef8ba22de69a0c166adcdf23ba6e7a33aa` has a different signature,
fixing a polynomial point-error function. It is not reused or certified here.
No proof at the assigned unrestricted signature was found.

The broader search found the newer issue #509 commit
`506aa56a06188948a53b7ecc3bbd5cfbc851eae5`. Its complete 86-line
`PointErrorObstruction.lean` is reused byte-for-byte (blob
`63bdb0fa5429163793ceb6914fa43ae3b36b27c2`), without its other changes.
The new quadratic witness uses its
`CombinedPointsWitness.exists_error_of_projective`; the independent duplicate
of that fact was removed. Its coefficient-level scalar lemma is retained in
the unchanged imported module. Both saved lemmas were typechecked and their
axiom closures verified, rather than relying on the saved receipt.
The new root-count application is stated for arbitrary finite fields and
polynomials, as needed for the generic POVM bounds.

## Validation

Both auxiliary modules pass focused Lean checking. The new generic POVM,
completed-answer, uniform-coefficient, eight-element and witness theorems, and
both reused lemmas, have axiom closure exactly `propext`, `Classical.choice`,
and `Quot.sound`. The target still includes `sorryAx`.
The runtime audit is
`~/.cache/mipstarre-dev/sessions/prover-511-20260912-02-axioms.lean`.
The hook installation check passes. Publication and exact-head CI results
belong to the PR and final session receipt; they are not assumed here.

## Accumulated Costs and Next Gate

The first attempt recorded 28,436 seconds for the thirteen relevant issue #118
attempts and three issue #119 attempts. Its final dispatcher duration is
828 seconds, superseding the 798-second checkpoint quoted in its final
message. This gives 29,264 seconds before this independent attempt.
The reused issue #509 proof packet adds 2,869 seconds, making the known scoped
prover subtotal 32,133 seconds. PR #525's separately recorded review took
414 seconds; it is not included in that prover subtotal. Other operator,
reviewer and unrelated packet costs are excluded, not treated as zero.

At 2026-09-12T06:23:11Z this attempt had used 2,501 seconds, making the
scoped prover total 34,634 seconds at that checkpoint. This attempt's final
dispatcher duration replaces that interval, rather than being added twice.
Token counters from resumed historical threads are not summed. This session's
usage remains separately recorded by dispatch, and the 60-minute limit is
not reset by proof reuse or publication.

Next gate: independent review of the published finite obstruction, followed
by a separately scoped decision on the invalid interface. For a full formal
refutation, transport the POVM bound into the direct line law and close the
perfect-strategy construction without admissions. For the source existence
theorem, construct controlled points internally and retain their error in
the line estimates. No reviewer or descendant was launched by this session.
