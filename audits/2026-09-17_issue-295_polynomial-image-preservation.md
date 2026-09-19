---
title: "Preservation of five ordered polynomial-image bounds"
date: 2026-09-17
purpose: >
  Compare the five completed auxiliary bounds in PR #296 with the current
  polynomial-image module and record their mathematical and provenance limits.
issue: "#295"
status: partial
---

# Scope

This port was first prepared at main
`7de8fe0b5cfd81abf9de2a4f4737b126c8ceb43c` and is republished on
2026-09-19 against main `2eb5f770c452f54aba0e0e725e97ccbc9c615a67`, where
`MIPStarRE/QPBT/Combining/PolynomialImageBounds.lean` is byte-identical to
the earlier base (no drift). At that base the polynomial-image module
contained the pointwise norm comparison and the projective outcome-mass
identity, but not the five declarations restored here from PR #296 at
`2c8f147643d151d8616864cf49817dc6422a9a86`.
The adjacent fiber and retained-point bounds have different hypotheses and
conclusions; they do not assert these five uniform exceptional averages or
the reversed ordered-indicator identity. This port leaves those later
bounds, the existing private helpers, and the factored mass inequality intact.

The blueprint chapter, unlike the Lean module, moved substantially between
the two bases. The five auxiliary entries are nonetheless inserted at the same
anchor as before, after the fiber-norm comparison proof and before the
partial-coefficient-polynomial definition, and every blueprint label they
reference still exists on the new base.

# Source of Truth

In `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1289-1326`,
`eq:qld-g-42` and `eq:qld-g-43` use the two orders of the point-measurement
products. The expansion following them identifies the diagonal sandwich
when the second scalar coefficient is nonzero. At the exceptional value
zero, the paper pays probability $1/q$ for the discrepancy in
`eq:qld-g-prime`. The polynomial-image concentration later in that passage
also needs separate correlation estimates, coefficient-polynomial bounds,
and the corresponding calculation in reverse order. These five Lean results
isolate only the exceptional averaging and order exchange, not that whole
concentration argument or `lem:qld-4-7`.

# Findings

For a finite field $F$ and complete projective $X,Z$, the ordered operator
$T_{\alpha,\beta,a}=\sum_{\alpha b+\beta c=a}X_bZ_c$ has diagonal sandwich
$H_{\alpha,\beta,a}=\sum_{\alpha b+\beta c=a}Z_cX_bZ_c$. The existing
pointwise comparison bounds the difference between the squared ordered-image
norm and the sandwich quadratic form by $1_{\beta=0}\|\psi\|^2$.
The preserved estimates give:

- `avg_abs_orderedIndicator_norm_sq_sub_diagonal_le`: a uniform average
  over $\beta\in F$ for arbitrary $a(\beta)$, bounded by
  $|F|^{-1}\|\psi\|^2$.
- `avg_sum_abs_orderedIndicator_norm_sq_sub_diagonal_le`: the same average
  summed over any finite family of actual vectors $\psi_g$, with bound
  $|F|^{-1}\sum_g\|\psi_g\|^2$ and no factor $|\Gamma|$.
- `avg_sum_abs_projective_orderedIndicator_le`: for complete projective
  $S$, substitute $\psi_g=S_g\psi$ to obtain $|F|^{-1}\|\psi\|^2$.
- `avg_uniform_sum_abs_projective_orderedIndicator_le`: for finite nonempty
  $T$, average the preceding estimate uniformly over the entire product
  $T\times(F\times F)$, retaining the same error and arbitrary answers
  $a(g,t,\alpha,\beta)$.
- `orderedIndicator_reverse`: the reversed sum $\sum Z_cX_b$ equals the
  ordered indicator of $(Z,X)$ at swapped coefficients $(\beta,\alpha)$;
  this is an operator equality, not a commutation claim.

The five statements and their proof content come from the old PR without
additional premises, stronger inequalities, assumed collisions, or a new
construction. Their blueprint entries are explicitly auxiliary and use
the existing indicator, pointwise comparison, and projective-mass entries;
they do not take ownership of already linked declarations. The ordered
products need not be projectors, so the two inherited occurrences of
"ordered projector" in this module were corrected.

Historical evidence, **not fresh validation on this base**: the preserved
source SHA-256 was
`871109bd97b6d50354dbf89f2d828cf4c4a9c2877a88b2aa4a654f764df42762`;
the attempt-13 21-declaration axiom receipt at
`/tmp/issue118-attempt13-axioms-and-placements.log` had SHA-256
`1c4c69600ff7268aa218d07f4c7624dfb5b43475aec8dc7d3f3226767591872a`.
The prior public-API recovery replaced issue-118-only
`Combining.Points.Consistency` norm identities by
`MagicSquareRigidity.norm_applyOperatorToState_sq` and
`DistanceCalculus.stateQForm_one` from public imports. The current module
retains those APIs; this port does not depend on the private artifact.
The original issue-118 sources, worktree, receipts, and audits are unchanged.

# Statement Integrity

- Paper assumptions: complete projective point measurements, uniform
  field-valued scalar coefficients, polynomial-outcome projectors, and
  vectors obtained by applying those projectors to the expanded state.
  The reversed correlation uses the opposite operator order.
- Lean assumptions: a finite field and finite-dimensional vector space,
  complete projective $X,Z$ for the bounds, complete projective $S$ for the
  final two averages, arbitrary answer functions and vectors, and a finite
  nonempty base type for the full product average. The order-reversal
  identity requires only complete $X,Z$, not projectivity. Finiteness and
  decidability instances represent the indicated finite domains.
- Paper conclusion: the diagonal norm expansion has exceptional error
  of order $1/q$ at the zero coefficient; both ordered correlations are
  subsequently used in the polynomial-image concentration calculation.
- Lean conclusion: the first four auxiliary theorems bound only the
  exceptional norm discrepancy by $|F|^{-1}$ times the actual squared
  vector mass, successively averaged and summed. The fifth proves only
  the equality of reversed ordered sums under exchanged indices.
- Verdict: faithful auxiliary calculations, more general in their choice
  of finite base type and answer functions; **not** the paper's full
  approximate correlation, concentration theorem, or polynomial-pair
  witness. No unproved correlation input is hidden in their hypotheses.

# Required Action

Issue #295 requires **21 public declarations**, not merely five missing
bounds: ten other declarations in the current module remain private by
main's existing API decision. Even after this port, the full 21-public
criterion and its 21-closure axiom query are unresolved. Review that API
requirement separately; do not re-expose the ten helpers merely to count
them. The projective polynomial-pair construction and any gaps of issue
#118 remain separate. B8 stays at 13 attempts and 26509 working seconds;
this preservation is no new B8 attempt and does not reset or extend it.
The source-labelled blueprint status of `lem:qld-4-7` is not altered here.

# Validation

Fresh validation on the refreshed base
`2eb5f770c452f54aba0e0e725e97ccbc9c615a67` (2026-09-19):
`lake env lean MIPStarRE/QPBT/Combining/PolynomialImageBounds.lean` exits 0
with no errors, and `lake build MIPStarRE.QPBT.Combining.PolynomialImageBounds`
completes. From a probe file outside the worktree, each of the five new public
declarations reports exactly `propext`, `Classical.choice`, and `Quot.sound`;
no `sorryAx` occurs. No proof hole, axiom declaration, or forbidden kernel
bypass appears in the touched Lean module. `local/bin/dup_check.py check`
finds no duplicate of the five names on `github/main`, under both the fully
qualified and the short name. The commit hooks and the repository CI entry
point run the blueprint checks on this change; their outcome is recorded in
the pull request, not inferred from the historical PR review.

# Review Use

Check that each new theorem has the same hypotheses, uniform averaging
domain, unnormalized state-vector bound, and product order as the preserved
PR statement. Check proof-level dependencies of the five auxiliary blueprint
entries and keep their status distinct from the source lemma. Historical
axiom evidence does not replace fresh closure checks for the five new public
declarations; neither check resolves the outstanding 21-public criterion.
