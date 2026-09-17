# Projective rounding through question-dependent postprocessing

Issue #278; session `prover-278-20260906-01`.

## Source and scope

The orthonormalization lemma `lem:ortho` in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:135-145`
rounds one member of a consistent pair of complete POVMs to a projective
measurement on its original local space. The proved explicit form,
`projective_rounding_with_explicit_constant`, bounds the squared
state-dependent distance by `220 * Real.rpow delta (1 / 4)`.

The application motivating this auxiliary is the proof of `lem:qld-4-7`
at lines 1278-1288 of the same mirror. After the soundness measurements have
been compressed to the original spaces, their projectivity need not survive.
The new module
`MIPStarRE/QPBT/Games/DistanceTheorems/RoundingTransport.lean`
constructs projective roundings of the compressed complete POVMs and
transports their consistency through arbitrary question-dependent outcome
maps. It does not construct the global polynomial-pair measurement.

The active blueprint entries are `lem:ortho`, `lem:ortho-explicit-constant`,
and `lem:qld-4-7`. No blueprint tag or existing public signature is changed.
In particular, `lem:qld-4-7` remains open.

## Quantitative derivation

Let the unit vector psi belong to H_A tensor H_B, with no identification of
the two finite-dimensional spaces. Let A and B be complete POVMs on a common
finite outcome set, and suppose their cross-player consistency defect is
at most delta, where delta is nonnegative. Write

\[
 r = 220\delta^{1/4}.
\]

The existing rounding theorem supplies a complete projective measurement P_A
on H_A whose squared distance from A, with both measurements placed on the
left tensor factor, is at most r. By
`DistanceCalculus.overlap_gap_le_of_opFamilyDistSq`, their diagonal overlaps
with B differ by at most sqrt(r). Completeness, unit-state normalization,
and probability normalization identify consistency defect with one minus
diagonal overlap. Consequently,

\[
 \operatorname{Cons}(P_A,B)\leq\delta+\sqrt r.
\]

For each question x, apply `consistencyDefect_postprocess_le` to the
constant families over the singleton question type with outcome map f_x.
Averaging the resulting inequalities gives the new public lemma
`consistencyDefect_postprocess_question_le`. This step needs neither a unit
state nor probability normalization. For a probability distribution mu,
it gives

\[
 \operatorname{Cons}_{\mu}(P_A^{f_x},B^{f_x})\leq\delta+\sqrt r,
 \qquad
 \operatorname{Cons}_{\mu}(A^{f_x},B^{f_x})\leq\delta.
\]

Suppose N_B is any complete measurement family on H_B satisfying
Cons_mu(A^{f_x}, N_B^x) <= eta. Instantiate
`consistencyDefect_trans_le` with the four families
P_A^{f_x}, B^{f_x}, A^{f_x}, N_B^x. The result is exactly

\[
 \operatorname{Cons}_{\mu}(P_A^{f_x},N_B^x)
 \leq \delta+\sqrt{220\delta^{1/4}}+2\sqrt{\delta+\eta}.
\]

Thus the proposed constants are derived from proved APIs. There is no factor
depending on the number of original or postprocessed outcomes, or on either
local dimension. In particular, the argument never postprocesses a squared
operator-distance estimate.

For the opposite orientation, `Equiv.prodComm` explicitly exchanges the
coordinates of the state. Mathlib's `Matrix.submatrix_mulVec_equiv` intertwines
the Kronecker-product actions, and `LinearIsometryEquiv.piLpCongrLeft`
preserves the inner product. These identities prove
`consistencyDefect_prodComm` and `opFamilyDistSq_left_prodComm`.
Applying the Alice-side construction to the exchanged state and the pair
(B,A) produces P_B on H_B, then these identities return both estimates to
the original state. This uses no invariance of psi under exchange and no
equality of local dimensions.

The public theorem
`projective_rounding_preserves_postprocessed_consistency` returns P_A and P_B
together, their projectivity, and their same-space squared-distance bounds.
Both roundings are chosen before the finite question and target-outcome
types, distribution, maps, comparison families, and comparison errors are
quantified. Its two transport conclusions are separately conditional on
the corresponding original comparison bound. They can therefore be used
with different maps, distributions, and comparison errors for the two sides.

For the later scalar estimates, the displayed error at eta = delta and
0 <= delta <= 1 is at most

\[
 (1+\sqrt{220}+2\sqrt 2)\delta^{1/8}.
\]

Indeed, sqrt(delta^{1/4}) = delta^{1/8}, and on this interval both delta and
sqrt(delta) are at most delta^{1/8}. This last scalar comparison is an
observation for the future consumer, not an additional Lean declaration in
this change; the exact two-error estimate above is the proved API.

## Statement integrity

- Paper assumptions: `lem:ortho` has a unit bipartite state, finite local
  spaces, complete POVMs on the same outcomes, and consistency error
  0 <= delta <= 1. The cited consistency triangle assumes three consistency
  inequalities; data processing uses a common outcome map on both players.
- Lean assumptions: finite coordinate and outcome types with decidable
  equality; the same unit state and complete POVMs; delta >= 0 and the
  original cross-player defect bound. Each transport instance additionally
  specifies a probability distribution, arbitrary maps f_x, and the original
  comparison bound against the unrounded POVM. These are the domain data of
  the derived auxiliary, not new assumptions on `lem:qld-4-7`.
- Range and normalization: the existing explicit rounding theorem already
  handles all delta >= 0, so delta <= 1 is unnecessary here. The comparison
  error eta needs no independent range assumption; its nonnegativity follows
  from the assumed bound on a cross-player defect. Unit-state and probability
  normalization are explicit. Nonempty local and outcome spaces follow from
  the unit state and completeness, so no additional nonemptiness assumptions
  appear in the public signatures.
- Paper conclusion: `lem:ortho` constructs a same-space projective rounding
  with O(delta^{1/4}) squared distance. `lem:qld-4-7` ultimately constructs
  projective polynomial-pair measurements with the two point consistencies.
- Lean conclusion: two complete projective roundings on the original spaces,
  squared distances at most 220 delta^{1/4}, and both universally quantified
  postprocessed consistency estimates with the exact displayed constants.
- Verdict: **exact derived auxiliary, with faithful boundary hypotheses**.
  It is not advertised as a proof of the global-witness theorem. No conclusion
  is moved into a hypothesis, and no bridge or external statement is assumed.

## Verification

The pinned toolchain is Lean v4.32.0. Both the initial check of
`ProjectiveRounding.lean` and the new module's single-file check succeeded.
The new module was also compiled with an explicit output olean in its private
worktree build directory, and imported by a separate Lean process for the
transitive axiom audit.

`rg -n 'sorry|axiom'` on the new module produced no matches (exit 1).
All six public declarations have exactly the axiom closure
`[propext, Classical.choice, Quot.sound]`, as reported by `#print axioms`
through `lake env lean --stdin`. No debugging commands remain in the module.
The 100-character line-length scan found no violations.

The same-space rounding and transport proofs are complete. No new or retained
proof hole belongs to this module. Whitespace checks of both new files reported
no errors.

## Future consumer

After compression has produced complete POVMs C_A and C_B with their original
polynomial-label consistency bound, instantiate the paired theorem with these
POVMs. Instantiate its outcome maps with polynomial evaluation and its
comparison families with the opposite-player point measurements. The maps may
depend on the question and basis. The two returned projective measurements
remain on the original heterogeneous spaces.

The subsequent polynomial-image mass estimate, projective restriction and
completion, and absorption of the error into the universal scalar envelope
still belong to the construction of
`MIPStarRE.QPBT.exists_globalPairWitness` in `Combining/Apply.lean`.
The existing source-import obligations there cite
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`. Neither that theorem nor
the compression packet is edited or used as a dependency here.

## Publication handoff

Normal hook installation was attempted. It could not lock
`/home/drx/MIPStarRE-qpbt/.git/config` because that filesystem is read-only
inside the session sandbox. The subsequent
`scripts/install_git_hooks.sh --check` succeeded: the normal `.githooks`
configuration is already installed and the hooks are executable.

Staging the two new files with `git add` failed with exit 128 because Git
could not create
`/home/drx/MIPStarRE-qpbt/.git/worktrees/issue-278-rounding-transport/index.lock`
on the read-only filesystem. Both files are retained, uncommitted, in the
current branch worktree. No alternative Git directory, index, permission,
account, or execution route was used.

Consequently there is no new commit to publish or to bind exact-head CI to.
No checked push, PR creation, or CI publication was attempted. A full build
was not run: the required machine-wide lock is in the runtime cache outside
the writable sandbox roots. No unlocked build was used. The single-file
compilation and transitive axiom evidence above are the validated checkpoint.

The operator should commit these two files with the normal hooks, publish
through the primary checkout's `local/bin/pr_open.py` (which uses
`checked-push.sh`), and run exact-head `local/bin/ci.sh` before arranging the
independent review. Suggested commit and PR title:
`feat(QPBT/Games): Add projective rounding transport`.
The permission refusals should be recorded in the operator's telemetry ledger.

This session does not extend or reset B8: its supplied anchor remains
`2026-09-05T19:24:00Z`, with twelve mathfix attempts and 24,242 seconds.
