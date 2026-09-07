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

## Publication Refresh, 2026-09-07

This section supersedes the publication status in Required Action above; the
earlier construction and validation record is retained unchanged. PR293's
published head `dc0ccdc91adf0b5d2b48308e9a20994677f17102` is refreshed by an
ordinary merge of published main
`a4b2a792a888027ff457ca2d0bca347e4df28892`. PR250 / #239 and PR248 / #240 are
now merged, with merge commits `98350244e0d3af7e9afb2e1e583acfef327cf03e` and
`ae63048fbf2b699b3794afdd412bcabb71e7445e`, respectively.

The merge preserves the complete `Extraction/Observables.lean` source and
chapter 16 blueprint from the preceding published PR293 head. It incorporates
the reviewed implementation of `tauDotProj_mul_eq_zero_of_ne` from main,
which uses the existing projective-measurement orthogonality API. Every public
extraction header is unchanged against both the preceding PR293 head and the
new main base. The given-measurement statement-integrity verdict above is
unchanged: the supplied projective polynomial-pair measurement yields
projective, complete pulled-apart effects, without additional assumptions.

Fresh private compilation of `Extraction/Defs.lean` and
`Extraction/Observables.lean` succeeds. Direct checks of
`Extraction/Consistency.lean` and `MIPStarRE/QPBT.lean` also succeed. The only
warnings in these files are the same four swap-conjugation and six consistency
proof obligations. All five issue120 targets, together with
`tauDotProj_mul_eq_zero_of_ne`, `isProj_kronecker`, and
`mul_eq_zero_of_isProj_family`, retain exactly the standard axiom closure
`[propext, Classical.choice, Quot.sound]`.

The canonical pending-merge loss guard succeeds, including all three best
merge bases. Incoming paths and raw telemetry records are preserved. The
ignored generated declaration list initially lacks eight references introduced
by main and is regenerated by the standard blueprint synchronization command.

Issue #119 remains open and is retained as a native dependency of #120. The
four other recorded prerequisites, #63, #114, #239, and #240, are closed. This
refresh does not construct `GlobalPairWitness`, prove its source existence
theorem, or discharge any swap-conjugation or consistency obligation. PR293
remains on merge hold for #119. Exact-head full CI and independent review are
separate required gates, owned by the integration workflow rather than this
publication session.
