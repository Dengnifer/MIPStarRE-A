# Seed-indexed simultaneous low-degree soundness

Issue #527, session `prover-527-20260912-01`, starting from
`ae124f8f09ee002444ac5b9711822c0f1daae142`.

## Result and construction

`MIPStarRE.QPBT.exists_ld_soundness` is proved for every simultaneity
parameter, with its public signature unchanged. Its axiom closure consists of
`propext`, `Classical.choice`, and `Quot.sound`.

The correlated seed dilation preserves projectivity and game value. Apply
`exists_direct_ld_soundness` to that dilation and compress its polynomial
measurements to the original Hilbert spaces. The two point/polynomial
consistency bounds are unchanged by compression. For the global relation,
the point-agreement branch and the consistency triangle inequality give
agreement of evaluated polynomial tuples. Distinct tuples differ in some
coordinate, so their collision probability is at most `md/q`, independently
of the number of coordinates. The resulting global error is

`E + 2 sqrt(9 epsilon + E) + md/q`, where `E = deltaLd a b epsilon q m d k`.

For `epsilon <= 1`, both `epsilon` and `md/q` are bounded by `E`. When also
`E <= 1`, the displayed expression is at most `10 sqrt(E)`. The new scalar
lemma absorbs this into `deltaLd (10*a) (b/2) epsilon q m d k`. In the other
regimes the unit bound on consistency defects suffices. No global
double-compression identity or coordinatewise measurement construction is used.

The sampling and measurement declarations formerly preceding the theorem
are moved, without changes to their statements or proofs, to
`Test/LowDegreeGameMeasurements.lean`. Three imports use that definitions
module to avoid a cycle through the existing direct soundness proof.

## Source-statement audit

- Paper assumptions: admissible `(q,m,d,k)`, positive error, and a projective
  strategy of value at least `1-epsilon`; source
  `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`.
- Lean assumptions: the same data, with positivity and dimension divisibility
  encoded by `LdParams`, finite matrix carriers, and total point-answer
  postprocessing that folds answers of the wrong form into the zero tuple.
- Paper conclusion: two uniform point/polynomial consistency relations and
  one global polynomial-tuple relation, all bounded by the displayed
  `deltaLd` with universal `a >= 1` and `0 < b <= 1`.
- Lean conclusion: those same three relations with the same quantifier order
  and error function. A textual comparison against the starting commit
  confirms that the entire theorem signature is unchanged.
- Verdict: faithful boundary encoding, with no added assumptions or changed
  conclusion. The proof follows the combining reduction cited from
  `references/neexp-paper/05_quantum_preliminaries.tex:1409-1503`, through
  the established direct game and the low individual degree theorem.

The two unverified assertions in the printed tensor-code proof, documented
in `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`, are not used. The
present result does not settle those assertions or the separate downstream
polynomial-pair construction. The counterexample to the coordinatewise
measurement construction remains valid.

## Reused proofs and prior work

The search covered all saved Git refs and the target's file history. No
completed proof of the current target was found. Reused results include:

- `5c40a3b8`: seed-indexed soundness for one coordinate, including the
  correlated compression and global recovery argument.
- `14aad87d`: direct simultaneous polynomial measurements for general `k`.
- `e1d8eaa2`: absorption of the general-`k` direct error into `deltaLd`.
- `8d593835`: reconciliation of these proofs and the seed-indexed transport.

The starting telemetry snapshot has six distinct prover records for the
relevant issues #134, #135, and #210 (none tagged #135):
`prover-134-20260904-01`, `prover-134-20260905-01` through `-04`, and
`prover-210-20260906-01`. Their recorded wall times total 13,231 seconds
(3 hours, 40 minutes, 31 seconds). This is a lower bound on prior relevant
work, not a fresh budget or a claim to include owner sessions and reviews.
Token counters on resumed historical sessions may overlap, so they are not
summed as independent usage. This session's usage is recorded separately by
the dispatcher; no descendants were launched.

## Validation

- The 36 affected dependency modules were freshly type-checked, in import
  order, into the private worktree build directory.
- Focused checks passed for the target, the scalar lemmas, the moved
  definitions, and the existing one-coordinate seed theorem.
- The target and new helper axiom closures contain only the three standard
  axioms listed above. No new proof holes or axioms were introduced.
- `leanblueprint web` passed, with missing-bibliography warnings from the
  initial absence of `web.bbl`; paper-gap checks passed with existing
  missing-verdict-marker warnings.
- The initial declaration-list check found 235 stale entries in the generated
  list supplied with the fresh worktree. Regeneration removed those entries
  and the synchronization check passed. The list is gitignored, so this
  changes no tracked declaration list, Lean declaration, or blueprint statement.
- Git hooks are installed and `git diff --check` passes.

Exact-head CI and independent review remain the publication gates; this
author session does not perform its own review or merge.
