# PR 432: published-main integration

## Scope and history

This bounded semantic integration started at 2026-09-15T12:11:13Z, with the
absolute deadline 12:39:00Z. Its first parent is
`a558b5005be91cd7a4fed7bbb9f48a7f2ecb4421`; its sole incoming snapshot is
published main `bf864c016b3426a690c02f93bea9d40986604195`.
The worktree was clean, uniquely registered on `issue-429-affine-evaluation`,
and had no other matching worker process or worktree-lock marker before the
ordinary `git merge --no-commit`. The merge base is
`d8bb9efb9760348c9bb9c85019549bcbda593df9`.

The primary checkout's `local/bin/gh_common.py` confirmed open issue 429 and
open PR 432 at the assigned public head. The stack base remains
`issue-388-combined-point-producer`, public SHA
`8c401506a3a84c5f7f612ae67c2e5af36a6f0ffa`. Review 5195360928, submitted on
2026-09-14, approved `f0f80420da4471c63c66d124fb32468ad1b63486`; it does not
approve this integration or its first parent. The earlier review and repair
history remains in the first-parent ancestry. No proof-attempt budget or
accumulated repair/review cost is restarted or replaced.

The PR 487 integration report was read as context only. No commit or file from
that branch was imported. No PR 472 worktree or report was accessed.

## Mathematical reconciliation

The ordinary merge had no textual conflicts. Its automatic result contained two
copies of `DistanceCalculus.stateQForm_conjTranspose_mul_mul` in
`Games/DistanceTheorems/Support.lean`. A focused Lean check reproduced the
duplicate-declaration error. The full signatures and proof terms of the two
copies are byte-identical. One declaration remains in the same shared module,
through the existing imports, and its documentation retains the overlap-gap
and sandwich applications described by the two histories. No public name or
distinct proof content is lost.

The affine-evaluation file is byte-identical on both parents. More generally,
all 637 incoming Lean modules retain identical non-comment code. Thus all
issue 429 mathematics is already present on the specified published main;
this repair introduces no new mathematical assertion or proof. The unique
review-repair prose consists of the two blueprint entries
`lem:expanded-point-field-commutation` and `lem:affine-line-evaluation`, and
the dependency of `lem:qld-4-10` on the former. Both complete entry/proof
blocks are preserved exactly from the first parent.

The `hard/source_semantic` scope is preservation of affine orientation,
nondegeneracy, and the distinction between source and auxiliary constructions
across the two histories, not a renewed construction attempt.

Main's proved `combined_line_measurement_consistency` has exactly the signature
of the older obligation. The automatic merge preserves its proof in
`Lines/Construction.lean` and the import in `Lines.lean`; it does not restore
the older unfinished declaration. `Combining/Apply.lean`, including the
fully proved global-pair theorem, is byte-identical to published main.
All incoming blueprint labels and open source markers remain. In particular,
the source-labelled combined-line statement remains `\notready`; proved
auxiliary results have not been substituted for open source assertions.

The only manually edited tracked paths are
`MIPStarRE/QPBT/Games/DistanceTheorems/Support.lean` and this receipt.
The blueprint additions were retained by the ordinary merge. The incoming
replacement of `qpbt_combined-points-direct.tex` by
`qpbt_combined-points-field-valued.tex` is main's earlier consolidation at
`7030a55c`, not a manual deletion made by this repair.

## Statement integrity

The primary sources were read before the Lean declarations:
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:274-287`
and `14_analysis_of_the_pauli_basis_test.tex:931-963`. The former defines the
equal mixture of axis and diagonal line-point distributions; the latter uses
independent X/Z samples, the ordered X-Z-X line measurement, and polynomial
collision bounds in the pasting argument.

- Affine evaluation: the source argument evaluates a coefficient polynomial
  at the parameter of a point on a nondegenerate line. Lean assumes an
  arbitrary `LdParams`, natural degree bound, line description with
  `line.direction != 0`, coefficient polynomial, and scalar parameter. Its
  unchanged conclusion says that `evalOpt` at the point $u_0+t v$ is
  `some (evalCoefficient poly param)`, where `param` represents $t$. The
  orientation is base plus parameter times direction, not its negative.
  Verdict: the same faithful auxiliary encoding, with the necessary
  nondegeneracy condition and no extra proof premise.
- Uniform collision: the consumer retains distinct coefficient polynomials,
  the same nonzero direction, the uniform affine parameter, and the bound
  `degree / card(field)`. Verdict: exact preservation.
- Quadratic-form identity: both Lean histories quantify an arbitrary finite
  decidable index type, state vector, and two operators, and conclude equality
  of the conjugated quadratic form with evaluation in the transformed vector.
  No positivity, projectivity, or normalization hypothesis is present or added.
  Verdict: identical auxiliary theorem and identical proof.
- Field-valued commutation: the retained blueprint entry matches the existing
  universal `C >= 1`, all admissible parameters and projective settings, every
  placement, and the `C * sqrt(error)` bound without a field-size factor.
  It explicitly distinguishes the field-valued auxiliary consequence from
  the source's binary-refinement assertion at paper lines 466-505.
- Line and global-pair constructions: all quantifier orders, directed
  placements, error functions, witness conclusions, and source/auxiliary
  distinctions are exactly those on published main. The global-pair theorem
  quantifies every strategy error, including zero, and has no supplied-witness
  premise. The older positive-error restriction is not reinstated. Verdict:
  exact preservation of main's strengthened domain, without changing any open
  source claim.

## Verification

The private diagnostic files and logs are under `.lake/pr432-*`.
The old private products remain in `.lake/build.pr432-before-main-20260915`.
The primary `local/bin/warm-worktree.sh` copied the exact-main snapshot using
`--no-build --skip-packages`; no shared cache or package store was changed.

- The focused `Support.lean` check passes after consolidation.
- The blueprint web build passes. Initial synchronization reported exactly
  236 stale entries in the generated `blueprint/lean_decls`; regeneration with
  the normal synchronization command resolves them, and final synchronization
  passes. No tracked mathematical statement was changed for this check.
- The pending-index merge-loss guard passes. Multiset comparisons of event,
  session, owner-session, build, estimate, stage, and decision records preserve
  every line, with its multiplicity, from both parents.
- The targeted builds of `Combining.Lines`, `Combining.Apply`,
  `Extraction.PauliTransport`, `Extraction.Construction`, and
  `Extraction.Observables` pass, including their affected imports. No full
  project build was run.
- The six compiled signatures and axiom closures in `pr432-signatures.lean`
  agree byte for byte between the exact published-main snapshot and the
  integration. They are affine evaluation, uniform affine collision,
  quadratic-form conjugation, field-valued point commutation, constructed-line
  consistency, and global-pair existence. All six use only `propext`,
  `Classical.choice`, and `Quot.sound`. A zero-error specialization of
  global-pair existence compiles in both environments.
- All 1,623 blueprint declarations resolve with the primary
  `scripts/Checkdecls.lean` run through `lake env lean --run`. The prebuilt
  `checkdecls` executable was absent. The first interpreted attempt encountered
  `Combining/Points/WitnessMarginals.olean` during the targeted rebuild;
  rerunning after that build passed. Neither artifact issue was treated as a
  successful check.
- The primary normal pre-commit checks pass, and installed hooks pass
  `--check`. They remain enabled for the eventual merge commit.
- The manually edited Lean file, affine-evaluation file, uniform collision
  consumer, and constructed-line consistency file contain no proof holes or
  kernel bypasses. The three existing `sorry` sites in `Combining/Apply.lean`
  remain exactly as on published main; none is in the axiom closure of
  `exists_globalPairWitness`. No new proof hole or axiom was introduced.
- All 77 changed Lean files and additional direct consumers pass the final
  sequential Lean check. The installed reference-transaction hook checks the
  merge object during commit; the final handoff also records a separate
  committed-object merge-loss check and the exact parents.

## Remaining gates

This is an unpublished local integration, not a new proof attempt or a review.
MAIN owns publication, exact-head deterministic CI, independent review, and
the guarded stack integration. The PR base and issue dependencies are unchanged.
No descendant or external model session, full project build, CI lane, review
lane, primary-file edit, manual telemetry edit, or GitHub write was performed.
