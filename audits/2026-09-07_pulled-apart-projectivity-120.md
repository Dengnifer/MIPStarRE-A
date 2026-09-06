---
title: "Projectivity and completeness of pulled-apart measurements"
date: 2026-09-07
purpose: >
  Records the source comparison, exact proofs, and validation for the two
  pulled-apart measurement obligations of issue120.
issue: "#120"
---

# Pulled-apart measurements

## Scope

This change proves `MIPStarRE.QPBT.tildeM_isProj` and
`MIPStarRE.QPBT.sum_tildeM_eq_one` in
`MIPStarRE/QPBT/Extraction/Observables.lean`. It preserves both public signatures,
all definitions, and all imports. The corresponding proof environment of
blueprint `lem:tilde-m-projective` is now complete.

The branch `issue-120-pulled-apart-projectivity` begins at published PR250 head
`87f034b52345609797b453b7c09012f91a165431` and incorporates published PR248 head
`5838982641c65b543decfa65e1691671a037db93` by merge
`13e5b6deaf39f819300be826dbea2080a2cdbff2`. These are explicit mathematical stack
dependencies: PR250 supplies dot-product projectivity and completeness, while
PR248 supplies the projectivity of polynomial marginals. Neither original
branch is changed by this issue120 proof packet. The canonical merge-loss guard
passes for the stack merge.

## Source of Truth

The paper source is Equation `eq:tilde_M` and the assertion of projectivity
immediately following it in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1416-1438`.
The relevant blueprint nodes are `def:s-w-marginals`,
`def:tau-dot-product-projector`, `def:tilde-m-measurement`, and
`lem:tilde-m-projective` in chapter 16.

Fix the Pauli kind $W$, register vector $u$, scalar outcome $a$, and a supplied
global polynomial-pair measurement. Write $A_g$ for its $W$ marginal and put
$c_g=\operatorname{Dec}(g)\cdot u$. The pulled-apart effect is exactly

\[
  \widetilde M_a^{W,u}=\sum_g A_g\otimes\tau^W_{c_g-a}(u).
\]

Each summand is a projection. For distinct polynomial outcomes $g,h$, the
projectivity of the marginal measurement gives $A_gA_h=0$, so the corresponding
tensor summands multiply to zero. Squaring the finite sum consequently leaves
only its diagonal terms. Taking adjoints preserves each summand, proving that
the sum is a self-adjoint idempotent.

For completeness, the map $a\mapsto c_g-a$ is a bijection of the scalar field.
Hence its Pauli factor sums to the identity for every $g$. Interchanging the
two finite sums reduces completeness to $\sum_g A_g=I$.

## Findings

The proof follows the paper's orthogonal-sum argument and requires no
additional assumptions. Orthogonality of the polynomial marginals is enough;
the proof does not use `tauDotProj_mul_eq_zero_of_ne` or repeat any Pauli basis
calculation. It uses the existing `isProj_kronecker` and
`mul_eq_zero_of_isProj_family` lemmas for the tensor-product and marginal
orthogonality facts, respectively. The outcome change of variables is Mathlib's
`Equiv.subLeft`, and tensor products commute with finite sums by the existing
`DistanceCalculus.heteroKron_finset_sum_left/right` API.

The given `GlobalPairWitness` is used only through its measurement and
projectivity fields. Its consistency bounds and existence construction are
not used. This result does not construct a global witness or discharge issue119.

### Statement integrity

- Paper assumptions: fixed admissible parameters, a Pauli kind $W$, a vector
  $u\in\mathbb F_q^M$, and the given projective polynomial-pair measurement;
  projectivity also fixes $a\in\mathbb F_q$.
- Lean assumptions: unchanged `P`, `epsilon`, `delta`, `S`,
  `w : GlobalPairWitness S delta`, `side`, `W`, `u`, and, for projectivity, `a`.
  The fixed field model supplies the finite-field instances; the player side
  retains the heterogeneous local spaces. No assumption is added.
- Paper conclusion: every pulled-apart effect is a projection, and summing its
  scalar outcomes gives the identity.
- Lean conclusion: `IsProj (tildeM w side W u a)` and
  `sum a, tildeM w side W u a = 1`, respectively, with the existing finite-sum
  notation in the declaration.
- Verdict: faithful boundary hypotheses for the given-measurement algebra.
  Public headers are unchanged. No conclusion or error parameter is weakened.

## Validation

- `lake env lean MIPStarRE/QPBT/Extraction/Defs.lean` passes.
- `lake env lean MIPStarRE/QPBT/Extraction/Observables.lean` passes with only its
  four existing swap-conjugation proof-hole warnings, reduced from six.
- Direct consumers `Extraction/Consistency.lean` and `MIPStarRE/QPBT.lean`
  type-check. The former retains its six existing proof-hole warnings.
- After emitting fresh worktree-private `Defs.olean` and `Observables.olean`,
  the axiom closures of all five issue120 targets, `isProj_kronecker`, and
  `mul_eq_zero_of_isProj_family` are exactly
  `[propext, Classical.choice, Quot.sound]`; none depends on `sorryAx`.
- Source-header comparison against `13e5b6d` reports no changed public headers.
  The hole and bypass scan finds only the four retained swap-conjugation holes;
  no new axiom, bypass, or debug command is present in the edited source.
- `leanblueprint web` passes with the existing missing-bibliography warnings.
  Blueprint LaTeX conventions and blueprint/Lean synchronization pass;
  `lake exe checkdecls blueprint/lean_decls` resolves all 1,398 declarations.
- `git diff --check` passes. The generated declaration list is ignored and is
  not part of the committed change.

## Required Action

The two target proofs are complete, but checked publication, exact-head full
CI, and independent review remain separate gates. Publication is held while
the main integration boundary is frozen. Issue119's construction and the four
remaining swap-conjugation obligations are unchanged. The two unmerged stack
dependencies retain their own review and merge requirements.

## Review Use

Check the exact polynomial marginal used for orthogonality and the direction of
the scalar reindexing. Compare both theorem headers with the stack baseline and
the paper passage above. The standard axiom-closure checks establish proof
independence from the remaining imported obligations; compilation of an import
containing proof holes alone would not establish that fact.
