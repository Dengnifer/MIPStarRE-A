# Combining scalar estimates: statement integrity

Issue #275 publishes three formalization-only scalar estimates from checkpoint
`0f4ef05370350f4017439ebd839ef0561f13130f`, on base
`928328ff4d45e5fdc2844b120329a2c241a3a58a`. The declaration statements, proof
bodies, and declaration-local heartbeat setting are preserved exactly in
`MIPStarRE/QPBT/Combining/ErrorBounds.lean`. The module imports existing error
definitions and Mathlib inequalities, and the QPBT import file includes it.

The source is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`.
The three auxiliary blueprint nodes are
`thm:qld-conditioned-polynomial-bound`,
`thm:qld-combining-polynomial-bound`, and
`thm:qld-global-pair-error-bound`. No source-labelled measurement theorem is
certified by these nodes.

## Error conventions

A one-variable polynomial error is a function bounded between zero and
`A * x^r` on the nonnegative half-line, for fixed `A >= 1` and `r > 0`.
A two-variable polynomial error is bounded between zero and
`B * (x^s + y^t)` on the nonnegative quadrant, for fixed `B >= 1` and
`s,t > 0`. These are the existing predicates `IsPolyErr` and `IsPolyErr₂`.
Their differences from the paper's literal shorthand are documented in
`docs/paper-gaps/qpbt_polynomial-error-square-root.tex` and
`docs/paper-gaps/qpbt_pasting-product-error.tex`.

## Conditioning

- Paper assumptions: the pasting application in `lem:qld-xz-lines`,
  lines 950-963, uses polynomial point and marginal errors and collision
  error `md/q`. The scalar auxiliary quantifies separately over a mass in
  `[1/2,1]`; it does not derive this mass bound from a line distribution.
  Division by such a mass costs at most a factor of two.
- Lean assumptions: a fixed one-variable polynomial error `p`, a fixed
  two-variable polynomial error `f`, and a fixed constant `c >= 1`.
  The inequality ranges over `error, ratio >= 0` and `1/2 <= mass <= 1`.
- Paper conclusion: polynomial consistency error for the paired-line POVM.
- Lean conclusion: one two-variable polynomial error, chosen before the
  three scalar arguments, bounds
  `min 1 (mass * f ratio ((8*p error + c*(error + sqrt error))/mass) + ratio)`.
- Verdict: exact match to the auxiliary blueprint inequality. This is the
  scalar part of the corrected pasting estimate; it proves no POVM existence,
  retained-mass bound, or symmetry statement.

## Combining

- Paper assumptions: `lem:qld-4-13`, lines 1020-1034, uses the point and
  paired-line measurements. Its first proof route is at lines 1134-1246.
- Lean assumptions: fixed polynomial errors `p` and `f`, and `c >= 0`.
  The inequality ranges over `error, ratio >= 0` and real `dimension >= 1`.
- Paper conclusion: extended-line POVMs with printed error
  `poly(m^2 * error, md/q)`.
- Lean conclusion: a two-variable polynomial error `g` bounds the capped
  expression containing the half and quarter powers, with the explicit factor
  `dimension * g error ratio` on the right.
- Verdict: exact match to the auxiliary blueprint inequality. Relative to
  the printed error claim this retains the dimension factor and therefore
  supplies a weaker error form. The discrepancy is documented in
  `docs/paper-gaps/qpbt_combined-lines-error-term.tex`; no source-labelled
  theorem statement or proof status changes.

## Global polynomial-pair error

- Paper assumptions: `lem:qld-4-7` applies classical low-degree soundness at
  dimension `2m+2` in lines 1278-1288, with admissible Pauli-test parameters.
  The numerical substitution at line 1402 uses
  `O(deltaLd + sqrt(deltaQ) + md/q)`.
- Lean assumptions: fixed polynomial errors `p` and `g`; nonnegative combining
  and final scale constants; a soundness prefactor at least one; and a
  soundness exponent in `(0,1]`. The inequality ranges over admissible
  parameters and nonnegative error.
- Paper conclusion: global polynomial-pair projective measurements with
  error `a' * (md)^a' * (error^b' + q^(-b') + 2^(-b'*md))`.
- Lean conclusion: universal `a' > 1` and `0 < b' < 1` bound the capped scalar
  sum by exactly that error function. The low-degree input is
  `combineConstant * m * g error (md/q) + error`; the final summands are
  `sqrt(p error)` and `md/q`.
- Verdict: exact match to the auxiliary blueprint inequality and the numerical
  absorption used in the paper, with the displayed positive slack. It does
  not invoke low-degree soundness, transport a game, or construct a measurement.
  The admissible-parameter facts used in the proof are already on main.

## Proof integrity and scope

All three proofs derive their majorants from the given polynomial bounds by
Mathlib real-power inequalities. Their minimum with one is part of the stated
scalar inequality; no default quantum measurement is used. The new module
contains no proof holes, new axioms, conditional construction inputs, or
redeclared Mathlib facts. All three extracted declaration texts were compared
with the checkpoint and found identical.

The distinct extraction estimate of issue #241 is absent from this change.
The measurement constructions and stronger printed-error obligation of issue
#118 remain separate. This publication is not a mathematical repair attempt
and changes none of the twelve recorded attempts or their 24242-second total.

## Validation

- `lake env lean MIPStarRE/QPBT/Combining/ErrorBounds.lean` and
  `lake env lean MIPStarRE/QPBT.lean` pass without diagnostics.
- The hole and forbidden-token scans of the new module have no matches.
- Each of the three declarations depends only on `propext`,
  `Classical.choice`, and `Quot.sound`.
- The full `lake build`, run through the primary `warm-worktree.sh`
  with the machine-wide lock and a 14400-second lock wait, passes (9139 jobs).
- `blueprint_lean_sync.py --update-lean-decls` and
  `lake exe checkdecls blueprint/lean_decls` pass; all 1398 links resolve.
- `blueprint_leanok_axioms.py --ci` passes, including the three new
  proof-level entries. Existing statement-only proof-debt warnings remain.
- `leanblueprint web` passes. The generated bibliography is supplied by
  `texra-blueprint bbl`.

Publication CI and independent review bind to the eventual commit SHA and
are recorded on the issue-linked pull request, rather than inferred from
these prepublication checks.

## 2026-09-06: declaration naming correction

PR #276 review 5124737599, finding F1, requires the theorem name
`exists_global_pair_error_bound`. This replaces the checkpoint spelling
`exists_globalPair_error_bound` and updates the corresponding blueprint link.
The exact-text comparisons above record the initial extraction, before this
correction. After the correction, the three declaration texts agree with the
checkpoint after only this identifier substitution; their hypotheses,
conclusions, proof bodies, and declaration-local heartbeat setting are unchanged.
The statement-integrity verdicts above therefore continue to apply.
