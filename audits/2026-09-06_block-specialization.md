---
title: "Block specialization: statement-integrity audit"
date: 2026-09-06
purpose: >
  Record the statement-integrity check for the uniform block-specialization
  auxiliary extracted from the proof of the global polynomial-pair lemma, so
  that later readers and reviewers can confirm its hypotheses, conclusion and
  boundary cases against the source passage.
issue: "#283"
pr: "#288"
status: active
track: qpbt
kind: statement-integrity-audit
---

# Block specialization: statement-integrity audit

## Scope

The only Lean addition is `MIPStarRE/QPBT/Combining/BlockSpecialization.lean`,
together with its import line in `MIPStarRE/QPBT.lean` and the subordinate
blueprint node `lem:qpbt-block-specialization` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`.

The five public declarations audited here are
`totalDegree_combinedCoef_le_totalDegree`,
`totalDegree_combinedRestrict_le_totalDegree`,
`exists_nonzero_combinedCoef_of_depends_on_block`,
`exists_block_specialization_exceptional_coefficient` and
`block_specialization_weighted_avg_le`.

The global polynomial-pair theorem, its hypotheses, and the blueprint claims
about it are unchanged. This file proves an auxiliary used in its
specialization argument; it does not assert completion of `lem:qld-4-7`.

## Source of Truth

`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1344-1363`,
between `eq:qld-g-2` and `eq:qld-g-prime-xpt-bound`. The surrounding blueprint
entry is `lem:qld-4-7` in `blueprint/src/chapter/ch15_qpbt_combining.tex`. The
source performs the specialization argument inside that proof and states no
named lemma for it, so every declaration listed above is a formalization-only
auxiliary.

### Mathematical statement

Let K be a finite field of cardinality q and let p(z,x) have total degree at
most D, where z ranges over K^m and x ranges over K^k. Assume p does not belong
to the polynomial ring in z alone. There is a nonzero exponent vector mu and
a nonzero coefficient polynomial c_mu(z) such that

- c_mu has total degree at most D;
- Pr_z[c_mu(z) = 0] is at most D/q;
- for every z with c_mu(z) nonzero, simultaneously for every b in K,
  Pr_x[p(z,x) = b] is at most D/q.

For any nonnegative real weights w(z,b) with sum_b w(z,b) = M at every z,
the resulting conclusion is

    E_z sum_b Pr_x[p(z,x) = b] w(z,b) <= (2D/q) M.

The paper takes weights given by expectations of complete measurement
operators and uses D = (2m+2)d. Its separate preceding term M/q then gives
(2(2m+2)d+1)M/q. The scalar auxiliary establishes the 2D/q term itself.

### Proof and existing API

The existing `combinedCoefAlgHom` reads p as a polynomial in x with
polynomial coefficients in z. If every coefficient at a nonzero exponent
were zero, this rereading would be constant in x. Applying its existing
inverse `combinedCoefInv` would express p as a polynomial in z alone,
contradicting the dependence hypothesis. This constructs c_mu.

Splitting each monomial exponent into its two coordinate blocks shows that
coefficient extraction and specialization do not increase total degree.
The proofs use `combinedCoef_eq_sum`, `eval_combinedCoef`, and
`exists_mem_support_of_combinedCoef_ne_zero` with Mathlib's support and
total-degree inequalities.

Schwartz--Zippel applies first to c_mu and zero. For c_mu(z) nonzero,
the same positive-degree coefficient distinguishes p(z,.) from every
constant polynomial b, so Schwartz--Zippel applies again, uniformly in b.
The local `schwartzZippel_totalDegree` theorem reduces these applications
to Mathlib's `MvPolynomial.schwartz_zippel_totalDegree`.

Each answer probability is at most 1_bad(z) + D/q. Nonnegativity permits
multiplication by w(z,b), and the fixed mass identity gives
M(Pr_z[bad] + D/q) after summation and averaging. This proves 2DM/q.
The same exceptional set is used for all answers; no sum of exceptional
probabilities over the answer alphabet occurs.

## Findings

### Assumptions and boundary cases

Paper assumptions: a polynomial depending nontrivially on the averaged
block, a total-degree bound, uniform sampling of the two field-coordinate
blocks, and nonnegative answer weights of constant total mass.

Lean assumptions: `Field K`, `Fintype K`, `DecidableEq K`, natural block
sizes m and k and degree bound D, `p.totalDegree <= D`, and
`forall r, p != MvPolynomial.rename (combinedPointVar m k) r`.
For the weighted theorem, `w` is any function of z and b with pointwise
nonnegativity and sum M at each z. These are actual polynomial and scalar
hypotheses, with no supplied collision estimate or construction obligation.
The existing API places z first and x second; this only fixes coordinate
order in the notation p(z,x). The two coordinate blocks are `Fin m` and
`Fin k`, so the blueprint node states the polynomial coordinate-free, on
K^m times K^k, rather than with one-indexed displayed variables.

Field cardinality positivity follows from the field instances. No positivity
assumption on m, k, D, or M is added. Parameter spaces remain nonempty when
m is zero. Dependence itself excludes k = 0 and, with the degree bound,
D = 0. Nonnegativity of M follows from the weights, including when M = 0.
The weights need not be independent of z.

No hypothesis D < q or bound on individual degrees is used. In particular,
a nonconstant polynomial can induce a constant function when D >= q, as
with x^q - x. The proof requires polynomial nonconstancy only. The numerical
Schwartz--Zippel bound remains valid in this case; it does not infer function
nonconstancy from a nonzero coefficient. Thus the paper's description of
good parameters as giving nonconstant functions is not needed for the
claimed numerical estimate at large degrees.

Paper conclusion: the second term in `eq:qld-g-2` has the indicated
2D/q times mass bound. Lean conclusion: precisely the scalar inequality
above, together with the coefficient and uniform exceptional-set statement.
Verdict: faithful boundary hypotheses for this auxiliary. No extra
assumptions, weakened conclusion, or change to the final source theorem.

### Relation to the existing individual-degree API

The existing `totalDegree_combinedCoef_le` and
`totalDegree_combinedRestrict_le` assume membership in `polyFunc` and
conclude the bounds m*d and k*d. The two new inequalities assume nothing
beyond the polynomial itself and conclude `p.totalDegree`, so they are not
duplicates of the existing API. None of the five public declarations of this
file exists on main under any other name.

## Required Action

No migration or cleanup remains for this auxiliary. Two obligations belong to
later work and are not claimed here:

- Integration of `block_specialization_weighted_avg_le` into the global
  polynomial-pair argument. The Lean proof of `exists_globalPairWitness` does
  not call it, so the blueprint records no dependency edge from the proof of
  `lem:qld-4-7` to `lem:qpbt-block-specialization`; the edge should be added
  only when that proof actually invokes the auxiliary.
- The unchanged `notready` status and the recorded source defects of
  `lem:qld-4-7` itself.

## Validation

- `lake env lean MIPStarRE/QPBT/Combining/BlockSpecialization.lean` passed
  without errors or warnings.
- `rg -n "sorry|axiom"` on the file returned no matches. The extended scan
  for forbidden proof-integrity tokens and debugging commands also returned
  no matches. All lines are at most 100 characters.
- `Lean.collectAxioms` was checked for all five new public theorems:
  the two total-degree inequalities, the nonzero-coefficient existence
  theorem, the exceptional-coefficient theorem, and the weighted theorem.
  Each closure contains only `propext`, `Classical.choice`, and `Quot.sound`.
  The executable assertion is in runtime storage at
  `~/.cache/mipstarre-dev/prover-283-20260906-01/BlockSpecializationAxioms.lean`.
- Anti-patterns A1--A6 were checked: no assumed probability estimate,
  default coefficient, exceptional-set input, outcome-cardinality loss,
  or external statement assumption is present.
- Hooks were installed and their installation check passed. Full-project
  validation is assigned to exact-head local CI after publication; another
  build held the machine-wide lock during this file-level audit.

There are no remaining proof holes or internal proof obligations in this
auxiliary. Integration into the global polynomial-pair argument and
independent review belong to subsequent work.

### 2026-09-14 revalidation on main

The branch was merged with `github/main` at `cebf210d` (merge commit
`91e27366`). The merge was clean and changed nothing in this auxiliary: the
whole difference between the merged branch and main is this file, the Lean
file, the blueprint entry and one import line. The existing API this file uses
(`combinedCoefAlgHom`, `combinedCoefInv`, `combinedCoef_eq_sum`,
`eval_combinedCoef`, `exists_mem_support_of_combinedCoef_ne_zero`,
`combinedRestrict`, `schwartzZippel_totalDegree`,
`polynomialAgreement_avg_eq_agreementProbability`) is unchanged on main.

Revalidation on the merged tree:

- `lake env lean MIPStarRE/QPBT/Combining/BlockSpecialization.lean` passed
  with no errors and no warnings.
- `scripts/blueprint_lean_sync.py --ci` reports blueprint and Lean in sync,
  and its reverse coverage check reports no changed declaration missing a
  blueprint entry.
- `check_statement_paper_origin.py`, `audit_new_proof_obligation_metadata.py`,
  `audit_paper_facing_proof_debt.py`,
  `audit_conclusion_shaped_hypotheses.py`, `audit_unfaithful_markers.py`,
  `audit_lean_axiom_declarations.py`, `check_source_statement_changes.py`,
  `check_oversized_lean_files.py` and `check_blueprint_latex.py` all pass.
- The whole-project build and `lake exe checkdecls blueprint/lean_decls`
  belong to the lane CI at the exact head; the worktree does not carry a
  complete set of compiled modules.

### 2026-09-17 revalidation after the second merge with main

The branch was merged with `github/main` again. The blueprint chapter
conflicted in two places, both resolved in favour of main's content: the new
definitions and theorems main added after the strategy paragraph are kept
verbatim, and main's rewritten proof of `lem:qld-4-7` is kept verbatim, which
withdraws the dependency edge this branch had added to it. The subordinate
node `lem:qpbt-block-specialization` is placed immediately before
`lem:qld-4-7` and is otherwise unchanged in mathematical content.

## Review Use

Reviewers of later PRs that touch the specialization step should read this
audit before changing any of the five declarations or the blueprint node. The
node is subordinate formalization support, not a named statement of the
source; its title and first sentence must keep saying so. A PR that integrates
the weighted estimate into the global polynomial-pair proof should add the
dependency edge from that proof at the same time, and should update the
Required Action section above.
