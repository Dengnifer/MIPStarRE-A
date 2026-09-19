import MIPStarRE.QPBT.Games.StrategyClasses

/-!
# The approximate form of the symmetrization lemma

The source proof of blueprint `lem:symmetric-strat`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:101-132`, chooses for
every `ε' > ε` a strategy of value at least `1 - ε'` from the supremum
defining `Game.value` and symmetrizes it.  This file formalizes exactly that
passage, on top of the value-preserving construction
`exists_symmetric_projective_strategy_of_strategy` proved in
`MIPStarRE.QPBT.Games.StrategyClasses`.

## Main results

* `exists_symmetric_projective_strategy_approx` — blueprint
  `lem:symmetric-strat`, the corrected statement of that node: the approximate
  form in the source's own shape.
* `exists_symmetric_projective_strategy_of_lt_value` — the same statement in
  slack form.

The exact-attainment assertion printed as `lem:symmetric-strat` is **not**
proved here or anywhere in this development, and is asserted nowhere. It is
recorded verbatim, unasserted, as the proposition
`PrintedSymmetricProjectiveAttainmentClaim` in
`MIPStarRE.QPBT.Games.StrategyClasses`, where its universally quantified form
is also refuted on the current Lean domain by
`not_forall_printedSymmetricProjectiveAttainmentClaim`. The analysis is in
`docs/paper-gaps/qpbt_symmetrization-attainment.tex` and issue `#524`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.LDT MIPStarRE.Quantum

namespace MIPStarRE.QPBT

noncomputable section

/-- The set of strategy values of a game is bounded above by one, so the
supremum in `Game.value` is a genuine least upper bound.  Formalization-only
support for blueprint `def:tensor-product-value`. -/
theorem bddAbove_range_strategy_value (G : Game) :
    BddAbove (Set.range fun S : Strategy G => S.value) :=
  ⟨1, by
    rintro _ ⟨S, rfl⟩
    exact S.value_le_one⟩

/-- No strategy beats the game value.  Formalization-only support for
blueprint `def:tensor-product-value`. -/
theorem Strategy.value_le_game_value {G : Game} (S : Strategy G) :
    S.value ≤ G.value :=
  le_csSup (bddAbove_range_strategy_value G) ⟨S, rfl⟩

/-- The deterministic POVM concentrated at a single answer.  Formalization-only
support for blueprint `def:povm-conventions`. -/
private def pointMeasurement {α d : Type*} [Fintype α] [DecidableEq α]
    [Fintype d] [DecidableEq d] (a₀ : α) :
    MIPStarRE.Quantum.Measurement α d :=
  MIPStarRE.Quantum.Measurement.ofSumEqOne (fun a => if a = a₀ then 1 else 0)
    (fun a => by
      split_ifs
      · exact Matrix.nonneg_iff_posSemidef.mpr Matrix.PosSemidef.one
      · exact le_rfl)
    (by simp)

/-- A game with nonempty answer alphabets has at least one strategy: the
one-dimensional strategy that answers deterministically.  This is the
boundary condition separating the source domain, where the answer alphabet is
a nonempty finite set, from the Lean domain, where `Game.AnswerA` may be
empty and the supremum defining `Game.value` is then the totalized supremum of
the empty set.  See `docs/paper-gaps/qpbt_symmetrization-attainment.tex`. -/
theorem nonempty_strategy_of_nonempty_answer (G : Game)
    (hA : Nonempty G.AnswerA) (hB : Nonempty G.AnswerB) :
    Nonempty (Strategy G) :=
  ⟨{ ιA := Unit
     ιB := Unit
     ψ := EuclideanSpace.single ((), ()) (1 : ℂ)
     ψ_norm := by simp
     A := fun _ => pointMeasurement hA.some
     B := fun _ => pointMeasurement hB.some }⟩

/-- The supremum property of `Game.value`: every real strictly below the game
value is strictly beaten by some strategy.  This is the step the source proof
states as "by definition for any `ε' > ε` there exists a strategy",
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:101-102`. -/
theorem exists_strategy_lt_value {G : Game} (hS : Nonempty (Strategy G))
    {c : ℝ} (hc : c < G.value) : ∃ S : Strategy G, c < S.value := by
  haveI := hS
  have hc' : c < sSup (Set.range fun S : Strategy G => S.value) := hc
  obtain ⟨v, hv, hlt⟩ := exists_lt_of_lt_csSup (Set.range_nonempty _) hc'
  obtain ⟨S, rfl⟩ := hv
  exact ⟨S, hlt⟩

/-- Approximate symmetrization in slack form, blueprint
`lem:symmetric-strat` in its corrected statement, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:101-132`: for every
positive slack `δ` a symmetric projective strategy comes within `δ` of the
game value.  The proof is the source argument verbatim -- choose a strategy
above the strict lower bound `Game.value - δ`, then apply the value-preserving
construction `exists_symmetric_projective_strategy_of_strategy`.

The hypothesis `Nonempty G.Answer` is the source's standing assumption that
the answer alphabet is a nonempty finite set; it is load-bearing in the Lean
domain, where an empty answer alphabet admits no strategy at all while
`Game.value` is still defined, so the conclusion is then false.  No attainment
claim is made at `δ = 0`: the printed attainment form is recorded unasserted as
`PrintedSymmetricProjectiveAttainmentClaim` and analyzed in
`docs/paper-gaps/qpbt_symmetrization-attainment.tex`. -/
theorem exists_symmetric_projective_strategy_of_lt_value (G : SymmetricGame)
    (hA : Nonempty G.Answer) (δ : ℝ) (hδ : 0 < δ) :
    ∃ S : SymmetricStrategy G, S.toStrategy.IsProjective ∧
      G.toGame.value - δ ≤ S.toStrategy.value := by
  have hS : Nonempty (Strategy G.toGame) :=
    nonempty_strategy_of_nonempty_answer G.toGame hA hA
  obtain ⟨S₀, hS₀⟩ :=
    exists_strategy_lt_value hS (c := G.toGame.value - δ) (by linarith)
  obtain ⟨S, hproj, hvalue, -⟩ :=
    exists_symmetric_projective_strategy_of_strategy G (1 - S₀.value) S₀
      (by linarith)
  refine ⟨S, hproj, ?_⟩
  rw [hvalue]
  linarith

/-- Approximate symmetrization in the source's own shape, blueprint
`lem:symmetric-strat` in its corrected statement, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:94-132`: if
`val*(G) = 1 - ε` then for every `ε' > ε` there is a symmetric projective
strategy of value at least `1 - ε'`.  This is what the source proof of
`lem:symmetric-strat` establishes, and it is the official formalization of
that node.  The printed conclusion at `ε' = ε` additionally asserts that the
supremum defining `Game.value` is attained; it is asserted nowhere here and is
recorded unasserted as `PrintedSymmetricProjectiveAttainmentClaim`, analyzed in
`docs/paper-gaps/qpbt_symmetrization-attainment.tex`.

As in `exists_symmetric_projective_strategy_of_lt_value`, `Nonempty G.Answer`
is the source's nonempty answer alphabet, made explicit because the Lean
domain admits an empty one. -/
theorem exists_symmetric_projective_strategy_approx (G : SymmetricGame)
    (hA : Nonempty G.Answer) (ε ε' : ℝ) (_hε : 0 ≤ ε)
    (h : G.toGame.value = 1 - ε) (hlt : ε < ε') :
    ∃ S : SymmetricStrategy G, S.toStrategy.IsProjective ∧
      1 - ε' ≤ S.toStrategy.value := by
  obtain ⟨S, hproj, hvalue⟩ :=
    exists_symmetric_projective_strategy_of_lt_value G hA (ε' - ε)
      (by linarith)
  refine ⟨S, hproj, ?_⟩
  rw [h] at hvalue
  linarith

end

end MIPStarRE.QPBT
