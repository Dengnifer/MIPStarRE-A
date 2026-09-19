---
title: "Issue 524: statement correction for the printed attainment form"
date: 2026-09-19
purpose: >
  Statement-integrity audit for the removal of the `sorry` in
  `exists_symmetric_projective_strategy` by a documented statement correction.
  Records what was asserted before, what is asserted now, and what is no longer
  asserted by anything.
issue: "#524"
---

# Issue 524: statement correction for the printed attainment form

Owner decision of 2026-09-19: "i want zero sorry". This audit records the
statement-integrity reasoning for the change that removes the last `sorry` in
`MIPStarRE/QPBT/Games/StrategyClasses.lean`.

## What the source prints

`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:94-99`,
`lem:symmetric-strat`: if a symmetric game has `val*(G) = 1 - eps` for some
`eps >= 0`, then some symmetric projective strategy `S` has
`val*(G, S) >= 1 - eps`.

## Why the printed form is not asserted

Two independent obstructions, both already documented in
`docs/paper-gaps/qpbt_symmetrization-attainment.tex` and neither introduced by
this change.

1. **Attainment.** The proof at lines 101-132 fixes `eps' > eps`, draws a
   strategy above the strict lower bound `1 - eps'` from the supremum defining
   `Game.value`, and symmetrizes it value-preservingly. It never reaches the
   bound. `Game.value` is a supremum over unbounded finite dimension and need
   not be attained.
2. **Formal domain.** `SymmetricGame` permits an empty answer alphabet. Such a
   game has no strategy at all, while `Game.value` is the totalized supremum of
   the empty set, hence zero. At `eps = 1` both printed hypotheses hold and the
   conclusion has no witness. This was checked on 2026-09-12 and recorded in
   `audits/2026-09-12_issue-524-symmetrization-obstruction.md`; it is now a
   library theorem.

The previous arrangement carried the printed sentence as a Lean theorem with an
open proof. That asserted, as a public declaration, a statement that is false on
part of its own domain. Replacing it by an unasserted record plus a proved
refutation is strictly more honest, not less.

## What changed

- `MIPStarRE/QPBT/Games/StrategyClasses.lean`
  - removed: `theorem exists_symmetric_projective_strategy` (term-level
    `sorry`). Nothing in the repository depended on it; an all-tree grep before
    the change found it only in its own definition, in docstrings, in the
    blueprint node, and in audit and register prose.
  - added: `def PrintedSymmetricProjectiveAttainmentClaim (G : SymmetricGame)
    (ε : ℝ) : Prop`, the printed sentence with its two hypotheses as
    antecedents. It is a definition, not a theorem: nothing asserts it.
  - added: `SymmetrizationObstruction.emptyAnswerGame`,
    `SymmetrizationObstruction.no_strategy`,
    `SymmetrizationObstruction.value_eq_zero` — the 2026-09-12 counterexample,
    moved into the library unchanged, 33 Lean lines.
  - added: `theorem not_forall_printedSymmetricProjectiveAttainmentClaim`,
    refuting the universally quantified printed claim.
- `MIPStarRE/QPBT/Games/Symmetrization.lean`: docstrings only. The three
  theorems and their proofs are byte-identical to main.
- `blueprint/src/chapter/ch12_qpbt_games.tex`
  - `lem:symmetric-strat` now states the corrected form (the approximate form,
    nonempty answer alphabet displayed), tags
    `exists_symmetric_projective_strategy_approx` and
    `exists_symmetric_projective_strategy_of_lt_value`, and carries statement-
    and proof-level `leanok`. Its proof is the source argument with the
    supremum step spelled out.
  - `rem:symmetric-strat-limit` states the printed sentence in full and names
    both obstructions.
  - new `lem:symmetric-strat-printed-claim`: the formalization-only node for
    the Lean Prop and its refutation.
  - `lem:symmetric-strat-approx` is folded into `lem:symmetric-strat` and
    removed; it was referenced only from the two nodes rewritten here.
  - `lem:symmetric-strat-given-strategy` is untouched.
- `docs/paper-gaps/qpbt_symmetrization-attainment.tex`: new section "Statement
  correction (2026-09-19)", two forward pointers in the superseded sections,
  and a rewritten conclusion. The source analysis and the counterexample
  sections are untouched.
- `docs/paper-gaps/qpbt-gap-register.md`: the symmetrization row now reads
  "Statement corrected, zero sorry".

## What is still open

Attainment for symmetric games with a nonempty answer alphabet. The refutation
above settles only the unrestricted claim over the current Lean domain. Nothing
in this change claims otherwise, and `rem:symmetric-strat-limit`, the gap note
and the register row all say so.

## Validation

- `lake env lean MIPStarRE/QPBT/Games/StrategyClasses.lean`: succeeds, no
  warning on the changed region; the two pre-existing linter warnings at lines
  553 and 678 are unchanged.
- `lake env lean MIPStarRE/QPBT/Games/Symmetrization.lean`: succeeds.
- `lake build MIPStarRE.QPBT.Games.Symmetrization`: succeeds.
- `#print axioms` from a probe file outside the worktree: all four new
  declarations and the four pre-existing symmetrization theorems depend only on
  `propext`, `Classical.choice` and `Quot.sound`. No `sorryAx` anywhere in the
  family.
- `results/telemetry/owner-tools/estimate.sh --count-sorry-sites` on
  `MIPStarRE/QPBT/Games/StrategyClasses.lean`: 0.
- `scripts/blueprint_leanok_axioms.py --ci`: PASS, 1803 declarations, 0
  failures; no proof-level `leanok` declaration depends on `sorryAx`.
- `scripts/blueprint_lean_sync.py --root . --ci`: in sync.
- `lake exe checkdecls blueprint/lean_decls`: all 1824 declarations resolve.
- `scripts/check_blueprint_latex.py`, `check_paper_gap_note_style.py --ci`,
  `check_statement_paper_origin.py`, `audit_unfaithful_markers.py --ci`,
  `audit_lean_axiom_declarations.py --ci`: pass.
- `scripts/check_source_statement_changes.py --base github/main`: "no changed
  public headers for source-labelled Lean declarations". No hook override was
  set and none was needed: the removed declaration is absent from the new tree,
  and the headers of the three retained symmetrization theorems are unchanged.
- `local/bin/dup_check.py check --name ...` on all four new names: no duplicate
  on `github/main`.
- No `sorry`, `admit`, `axiom`, or `native_decide` is added. The one remaining
  `sorry` under `MIPStarRE/QPBT` is `Combining/Apply.lean:96`, a different gap
  tracked separately.
