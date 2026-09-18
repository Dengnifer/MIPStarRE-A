---
title: "Approximate symmetrization: paper versus Lean"
date: 2026-09-18
purpose: >
  Records the paper-versus-Lean comparison behind the scoped realignment of
  the symmetrization lemma: what the source proof establishes, what the
  printed statement additionally asserts, and which Lean declaration now
  carries which form.
issue: "#524"
pr: "#601"
---

# Issue #524: approximate symmetrization realignment

Published as PR 601 on branch
`issue-524-approximate-symmetrization-20260918`.

## Scope

This packet does **not** prove
`MIPStarRE.QPBT.exists_symmetric_projective_strategy`. That declaration keeps
its printed statement, keeps its proof hole, and keeps its `**Unfaithful:**`
marker. The packet adds the approximate form that the source proof actually
establishes, as a separate proved declaration against a new
formalization-only blueprint node, and records the realignment in the gap
note and the gap register.

The packet also does not re-audit the empty-answer refutation. That evidence
is the separate documentation packet for #524, PR 540 (branch
`issue-524-proof-exists-symmetric-projective-strategy`, based on
`ae124f8f`), whose completed bounded metadata fix and review history are
preserved. The present branch is based on current `github/main`, which does
not contain PR 540's note edits; the edits here are additive and land in
different parts of the gap note (a new section before the conclusion), so
both can stand. The nonempty-answer hypothesis introduced below is exactly
the boundary condition that PR 540's counterexample exposes, and this packet
adopts that finding rather than re-deriving it.

## The immutable source text

`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex`:

- lines 94-99, statement `lem:symmetric-strat`: let
  `G = (X, A, mu, D)` be a symmetric game such that `val*(G) = 1 - eps` for
  some `eps >= 0`; then there exists a symmetric and projective strategy
  `S = (psi, M)` such that `val*(G, S) >= 1 - eps`.
- lines 101-132, the proof: "By definition for any `eps' > eps` there exists
  a strategy `S' = (psi', A, B)` such that `val*(G, S') >= 1 - eps'`." Naimark
  dilation makes `S'` projective on `C^d (x) C^d`; the permutation-invariant
  state `psi` and the block-diagonal measurements
  `M^x_a = |0><0| (x) A^x_a + |1><1| (x) B^x_a` are formed; symmetry of `D`
  gives `val*(G, S) = val*(G, S')`.

The proof therefore establishes, for a *given* strategy, a value-preserving
symmetrization, and, through the supremum, the approximate form at every
`eps' > eps`. It never produces a single strategy at `eps' = eps`. The gap
note `docs/paper-gaps/qpbt_symmetrization-attainment.tex` names the three
forms (attainment, approximate, given-strategy) and records that both source
uses of the lemma --- `10_oracularization.tex:317-321` and
`11_answer_reduction.tex:2322-2332` --- consume only the second or third.

## Hypotheses and conclusion, side by side

| | Source `lem:symmetric-strat` | Source proof (approximate form) | New Lean `exists_symmetric_projective_strategy_approx` |
| --- | --- | --- | --- |
| Game | symmetric game on finite alphabets, the answer alphabet a nonempty finite set | same | `G : SymmetricGame` plus `hA : Nonempty G.Answer` |
| Error | `eps >= 0` | `eps >= 0` and a chosen `eps' > eps` | `(_heps : 0 <= eps)` and `(hlt : eps < eps')` |
| Value hypothesis | `val*(G) = 1 - eps` | same | `h : G.toGame.value = 1 - eps` |
| Conclusion | a symmetric projective strategy of value `>= 1 - eps` | a symmetric projective strategy of value `>= 1 - eps'` | `exists S : SymmetricStrategy G, S.toStrategy.IsProjective and 1 - eps' <= S.toStrategy.value` |

Verdict on the new declaration: hypotheses and conclusion match the second
column exactly, with one side condition added and one binder unused.

- **Added side condition.** `Nonempty G.Answer` is the source's standing
  assumption that `A` is a nonempty finite answer alphabet. It is not a
  bridge hypothesis and carries no unproved step of the argument; it is the
  kind of boundary hypothesis that `AGENTS.md` classifies as a faithful
  encoding ("nonemptiness of a finite type"). It is load-bearing only in the
  Lean domain, where `Game.AnswerA` may be empty: then no strategy exists,
  `Game.value` is the totalized supremum of the empty set, and the conclusion
  is false. The hypothesis is displayed in the statement, in both docstrings,
  in the new blueprint node, and in the gap note.
- **Unused binder.** `_heps : 0 <= eps` is kept for recognizability against
  the printed statement; the approximate form does not need it, so it is
  named with a leading underscore rather than dropped or masked by a linter
  option. Dropping a hypothesis would strengthen the theorem, so keeping it
  is the conservative choice.

## Where the approximate form comes from, step by step

`exists_symmetric_projective_strategy_of_lt_value` is the slack form and does
the work; `exists_symmetric_projective_strategy_approx` is its restatement in
the source's `eps'` shape.

1. `Strategy.value_le_one` --- every strategy value is at most one. Proved
   from the existing `rejectionMass_eq_one_sub_value` together with
   nonnegativity of the rejected mass (`avgOver_nonneg`,
   `outcomeWeight_nonneg`).
2. `bddAbove_range_strategy_value` --- the set of strategy values is bounded
   above, so the `sSup` in `Game.value` is a least upper bound rather than a
   totalization artifact. `Strategy.value_le_game_value` is the companion
   upper-bound direction.
3. `nonempty_strategy_of_nonempty_answer` --- a game with nonempty answer
   alphabets has a strategy: the one-dimensional strategy whose local space
   is `Unit`, whose state is `EuclideanSpace.single` and whose measurements
   are the deterministic POVM at a fixed answer. This is the only new
   construction in the packet and it is private-facing apart from the
   theorem.
4. `exists_strategy_lt_value` --- the supremum property: with a strategy in
   hand, every real strictly below `Game.value` is strictly beaten by some
   strategy (`exists_lt_of_lt_csSup`). This is the source's "by definition
   for any `eps' > eps` there exists a strategy" at
   `06_nonlocal_games_and_mipstar.tex:101-102`.
5. The composition: choose `S0` above `Game.value - delta`, then apply the
   already proved `exists_symmetric_projective_strategy_of_strategy` --- the
   Naimark dilation plus symmetrization of the source proof, value-preserving
   --- to obtain a symmetric projective `S` with
   `S.toStrategy.value = S0.value`.

No compactness, limit, or attainment argument appears anywhere in the chain,
which is why the printed statement is untouched.

## What stays open

The attainment assertion --- that a single symmetric projective strategy
reaches `1 - eps = val*(G)` --- is still an open source gap. `Game.value` is
a supremum over finite-dimensional strategies of unbounded dimension, the
dilated dimension may grow as `eps'` decreases to `eps`, and no compactness
across dimensions is available; the source itself recalls that the set of
finite-dimensional quantum correlations is not closed. The blueprint node
`lem:symmetric-strat` accordingly keeps its printed statement and carries no
proof-level `leanok`, and the Lean declaration keeps its proof hole. No
downstream Lean or source consumer needs the attainment form.

## Blueprint and record choices

Of the two options in the disposition, this packet keeps the printed exact
statement as a proof-hole-carrying declaration and adds the approximate form
beside it. That is the lower-churn option and the one the repository's
proof-gap protocol already prescribes: the printed statement is not known to
be false for games with a nonempty answer alphabet, only its proof is
blocked, so `AGENTS.md` requires the source-labelled node to stay as printed
without `leanok` and the scope-restricted result to be stated as a separate
node whose restriction is displayed. Replacing the printed node with the
approximate one would have silently retired a source statement that the
project still tracks, and would have contradicted the register's existing
"source statement kept as printed" entry.

The new declarations live in a new module,
`MIPStarRE/QPBT/Games/Symmetrization.lean`, rather than at the end of
`MIPStarRE/QPBT/Games/StrategyClasses.lean`: appending them there would have
pushed that file past the repository's 1000-line guard. The new module is
imported from `MIPStarRE/QPBT.lean` next to `StrategyClasses`.

Changes to the record:

- `blueprint/src/chapter/ch12_qpbt_games.tex`: new node
  `lem:symmetric-strat-approx` with `\leanok` on statement and proof, placed
  after `rem:symmetric-strat-limit`; one sentence added to the proof of
  `lem:symmetric-strat` naming the new node and repeating that the exact form
  is an open source gap. `lem:symmetric-strat` itself is unchanged and still
  has no proof-level `leanok`.
- `docs/paper-gaps/qpbt_symmetrization-attainment.tex`: a new section
  "Realignment of the Lean statements (2026-09-18)" before the conclusion,
  and one sentence in the conclusion. The obstruction sections are untouched.
- `docs/paper-gaps/qpbt-gap-register.md`: the symmetrization row lists the
  new node and records the realignment, with no completeness claim for the
  printed theorem.

## Validation

- `lake env lean MIPStarRE/QPBT/Games/StrategyClasses.lean`: succeeds; the
  only warning is the pre-existing "declaration uses `sorry`" on
  `exists_symmetric_projective_strategy`.
- `lake env lean MIPStarRE/QPBT/Games/Symmetrization.lean`: succeeds with no
  warning.
- `lake build MIPStarRE.QPBT.Games.Symmetrization`: succeeds.
- `#print axioms` from a probe file outside the worktree: the six new
  declarations depend only on `propext`, `Classical.choice` and `Quot.sound`.
  `exists_symmetric_projective_strategy` still depends on `sorryAx`, as
  before.
- No `sorry`, `admit`, `axiom`, or `native_decide` is added; the one existing
  proof hole is neither moved nor removed.
- `local/bin/dup_check.py check` reports no duplicate on `github/main` for
  any of the added names.
