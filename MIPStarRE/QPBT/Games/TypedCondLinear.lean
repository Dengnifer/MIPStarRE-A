import MIPStarRE.QPBT.Games.CondLinearTheorems
import MIPStarRE.QPBT.Games.DistributionAux

/-! # Typed conditionally linear distributions

Typed question distributions first sample an ordered edge of the type graph and
then sample the corresponding pair of conditionally linear images of one common
uniform seed.

## References

These are `def:typed-cl-functions` and `def:typed-cl-distributions` in
`blueprint/src/chapter/ch12_qpbt_games.tex:1355-1404`, with paper origin
`references/qpbt-paper/07_types.tex:57-94`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

/-- A typed family whose member at every type is `ell`-level conditionally
linear. This is `def:typed-cl-functions`, blueprint
`ch12_qpbt_games.tex:1355-1360`, paper
`references/qpbt-paper/07_types.tex:57-63`. -/
def IsTypedCondLinearFamily (K T : Type*) [Field K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ell : ℕ) (L : T → (ι → K) → (ι → K)) : Prop :=
  ∀ t, IsCondLinear ell (L t)

/-- The typed CL distribution: sample a type pair from the graph distribution,
then bind it to the CL distribution selected by those two types. This is
`def:typed-cl-distributions`, blueprint `ch12_qpbt_games.tex:1400-1404`, paper
`references/qpbt-paper/07_types.tex:84-94`. -/
noncomputable def typedCLDistribution {K T ι : Type*}
    [Field K] [Fintype K] [DecidableEq K]
    [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
    (E : Finset (Sym2 T)) (hE : E.Nonempty)
    (L R : T → (ι → K) → (ι → K)) :
    Distribution ((T × (ι → K)) × (T × (ι → K))) :=
  Distribution.bind (graphDistribution E hE) fun uv =>
    (clDistribution (L uv.1) (R uv.2)).map fun xy =>
      ((uv.1, xy.1), (uv.2, xy.2))

end MIPStarRE.QPBT
