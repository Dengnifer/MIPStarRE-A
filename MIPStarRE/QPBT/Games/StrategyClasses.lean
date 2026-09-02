import MIPStarRE.QPBT.Games.Defs

/-!
# Strategy classes

This file records structural predicates on finite tensor-product strategies.

## References

`Strategy.IsProjective` formalizes `def:projective-strategy-general` in
`blueprint/src/chapter/ch12_qpbt_games.tex`, with paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex`.
-/

namespace MIPStarRE.QPBT

/-- A strategy is projective when every measurement used by either player is
projective.  This predicate is distinct from the LDT `ProjStrat` carrier. -/
def Strategy.IsProjective {G : Game} (S : Strategy G) : Prop :=
  (∀ x, MIPStarRE.QPBT.Measurement.IsProjective (S.A x)) ∧
    (∀ y, MIPStarRE.QPBT.Measurement.IsProjective (S.B y))

end MIPStarRE.QPBT
