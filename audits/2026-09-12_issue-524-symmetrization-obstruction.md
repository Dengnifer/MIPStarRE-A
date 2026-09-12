# Issue 524: obstruction to exact symmetrization

The requested theorem cannot be proved at its current signature. In addition
to the documented attainment gap, its Lean domain admits a symmetric game
with no answers and no strategies. Its game value is zero, so the hypotheses
hold at error one and the conclusion fails. This note preserves a checked
counterexample; it does not propose a replacement theorem.

The audited base is `ae124f8f09ee002444ac5b9711822c0f1daae142`. Session
`prover-524-20260912-01` preserves every Lean declaration and blueprint tag.
The mathematical explanation is in
`docs/paper-gaps/qpbt_symmetrization-attainment.tex`, section
"An additional obstruction in the formal domain".

## Source and prior work

The source is `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex`:
definitions at lines 10-57 and 74-92, statement `lem:symmetric-strat` at
94-99, and proof at 101-130. The corresponding blueprint entries are
`lem:symmetric-strat`, `rem:symmetric-strat-limit`, and
`lem:symmetric-strat-given-strategy` in `ch12_qpbt_games.tex`.

The proof fixes an error strictly larger than the error defining the game
value, chooses a strategy above that strict lower bound, and preserves its
value through dilation and symmetrization. It does not extract an optimal
strategy from a family whose dimensions may grow without bound. No new
compactness argument was attempted in this packet.

An all-ref history search, including the saved branch and remote refs, found
the existing construction in commit
`7c4145458d506bb03fa0311840cbb85df70bf6f9`
(`feat(QPBT/Games): prove transformations and rounding`). Its
declaration is `MIPStarRE.QPBT.exists_symmetric_projective_strategy_of_strategy`.
Commit `ca4ac693b6ae98e420f7e6600517bacec7efe8d3` explicitly retained the
attainment obligation after review. The gap was also audited in
`11415a8753bd25cd709db10c949456353a0f1e47` and
`2a5ca9397c81e6f3de5f1eb96b626a1293feb355`. No completed proof of the target
was found. The target, definitions, and gap note at local main
`d647a4818ef43092aa66404834b99f2cb292ede8` match the audited base.

The earlier work is not a fresh budget:

- Issue 98 has three prover dispatch records, all on the same resumed thread:
  `prover-98-20260904-01`, `-02`, and `-03`, with 1,943, 7,107, and 969
  recorded wall seconds, totaling 10,019 seconds. These sessions also proved
  the value stability and projective rounding results, so this total cannot
  be attributed solely to the attainment gap.
- The last issue-98 record reports 70,606,980 input tokens, including
  68,905,856 cached input, and 260,735 output tokens, with 111,167 reasoning
  tokens reported separately. Earlier nonzero records are cumulative on the
  same thread and are not added again; the first record's zero usage is not
  evidence of zero cost.
- Six PR-158 reviewer records total 5,031 wall seconds. Thus the recorded
  issue-98 prover and PR-158 review work totals 15,050 session-wall seconds,
  with concurrent reviews counted individually, not as elapsed calendar time.
- The broader paper-gap audit has at least two recorded continuations,
  `blueprint-173-20260904-02` and `prover-173-20260905-01`, totaling 2,939
  wall seconds. Its time and cumulative token records cover multiple gaps
  and are not attributed to this target.
- The packet's initial reservation attempt is terminal without an acquired
  account reservation, as recorded in the dispatch instructions. No completed
  issue-524 telemetry row was available when this audit was written; its
  duration and token cost are unknown, not zero. The dispatcher records this
  session separately, without resetting the earlier episode.

## Checked counterexample

Take one question and an empty answer alphabet. The uniform distribution on
the singleton question pair is symmetric; the decision predicate on the
empty answer domain is unique. A unit bipartite state forces each local
coordinate type to be nonempty. Completeness of an empty POVM on such a space
would equate the zero matrix with the identity, which is impossible.

The set of strategy values is consequently empty. Mathlib assigns the real
conditional supremum of the empty set the value zero. This is a convention
for a total operation, not a least-upper-bound theorem for an empty subset
of the reals. Therefore `Game.value = 1 - 1`, while no symmetric projective
strategy exists. This refutes the exact Lean domain; it does not establish
nonattainment for games with nonempty answer alphabets.

The following complete verification was checked with Lean 4.31.0 against the
audited worktree. It deliberately never invokes the target theorem.

```lean
import MIPStarRE.QPBT.Games.StrategyClasses

/-! # Empty-answer obstruction to the exact symmetrization statement

This is a verification artifact for issue #524, not a corrected paper theorem.
The source assertion is `lem:symmetric-strat` in
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:94-99`.
-/

namespace MIPStarRE.QPBT.SymmetrizationObstruction

open MIPStarRE.LDT

/-- A symmetric game with one question and no answers. -/
noncomputable def emptyAnswerGame : SymmetricGame where
  Question := Unit
  Answer := Empty
  μ := uniformDistribution (Unit × Unit)
  μ_prob := uniformDistribution_isProbability (Unit × Unit)
  μ_symm := by intros; rfl
  decide := fun _ _ a _ => nomatch a
  decide_symm := by intro _ _ a; exact isEmptyElim a

/-- A unit state and a complete measurement rule out an empty answer alphabet. -/
theorem no_strategy : IsEmpty (Strategy emptyAnswerGame.toGame) := by
  refine ⟨fun S => ?_⟩
  have hι := nonempty_of_unit_vector S.ψ S.ψ_norm
  letI : Nonempty S.ιA := hι.map Prod.fst
  have ha : Nonempty Empty := measurement_outcome_nonempty (S.A ())
  exact isEmptyElim (Classical.choice ha)

/-- The real conditional supremum of the empty set of strategy values is zero. -/
theorem value_eq_zero : emptyAnswerGame.toGame.value = 0 := by
  letI := no_strategy
  simp [Game.value, Set.range_eq_empty, Real.sSup_empty]

/-- The exact hypotheses at error one hold, but the conclusion has no witness. -/
theorem counterexample :
    (0 : ℝ) ≤ 1 ∧ emptyAnswerGame.toGame.value = 1 - 1 ∧
      ¬ (∃ S : SymmetricStrategy emptyAnswerGame,
        S.toStrategy.IsProjective ∧ 1 - (1 : ℝ) ≤ S.toStrategy.value) := by
  refine ⟨by norm_num, by simpa using value_eq_zero, ?_⟩
  rintro ⟨S, _, _⟩
  exact no_strategy.false S.toStrategy

#print axioms no_strategy
#print axioms value_eq_zero
#print axioms counterexample
#print axioms MIPStarRE.QPBT.exists_symmetric_projective_strategy
#print axioms MIPStarRE.QPBT.exists_symmetric_projective_strategy_of_strategy

end MIPStarRE.QPBT.SymmetrizationObstruction
```

The verification uses existing local lemmas and Mathlib's
`Set.range_eq_empty` and `Real.sSup_empty`. The three counterexample
declarations and the given-strategy symmetrization theorem depend only on
`propext`, `Classical.choice`, and `Quot.sound`. The requested theorem also
depends on `sorryAx`. Importing its module does not place it in the
counterexample's proof dependency closure.

## Statement integrity and next gate

| Component | Paper | Current Lean |
| --- | --- | --- |
| Game | Symmetric game on finite question and answer alphabets | `SymmetricGame`, with finite shared alphabets and probability/symmetry fields; no nonemptiness field for answers |
| Error | Real `eps >= 0` | `(eps : Real)` and `0 <= eps` |
| Value hypothesis | Tensor-product value equals `1 - eps` | `G.toGame.value = 1 - eps`, defined by real conditional supremum |
| Conclusion | A symmetric projective strategy with value at least `1 - eps` | The same existential statement, with finite local coordinate types |

Verdict: the conclusion and numerical hypotheses are unchanged and match the
printed statement. The formal domain has a missing nonemptiness boundary
condition, exposed by the totalized empty supremum. The printed definition
does not specify this empty-supremum convention. Excluding empty answers
would address this counterexample but would not prove the independent
attainment assertion for nonempty games.

The target has no Lean consumers outside its declaration and documentation;
the source-labelled blueprint entry has no proof-level `leanok`. The paper
uses in `10_oracularization.tex:317-321` and
`11_answer_reduction.tex:2322-2332` need a given strategy or a strict lower
bound, as detailed in the gap note. No downstream proof requires the exact
attainment form.

Validation: the complete counterexample passes `lake env lean` with no
warnings; focused checking of `StrategyClasses.lean` succeeds with its one
existing target warning. The hook installation check passes. This packet
adds no Lean declaration, proof hole, hypothesis, or blueprint completion
claim. The next mathematical gate is an independently reviewed domain and
attainment statement correction, or genuinely new evidence for attainment
on an explicitly justified domain. Repeating tactics on the unchanged
signature cannot discharge it.
