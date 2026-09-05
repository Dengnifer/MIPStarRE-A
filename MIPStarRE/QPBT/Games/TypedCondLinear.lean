import MIPStarRE.QPBT.Games.CondLinearTheorems
import MIPStarRE.QPBT.Games.DistributionAux

/-! # Typed conditionally linear distributions

Typed question distributions first sample an ordered edge of the type graph and
then sample the corresponding pair of conditionally linear images of one common
uniform seed.

## References

These are `def:typed-cl-functions` and `def:typed-cl-distributions` in
`blueprint/src/chapter/ch12_qpbt_games.tex:1370-1418`, with paper origin
`references/qpbt-paper/07_types.tex:57-94`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

/-- A typed family whose member at every type is `ell`-level conditionally
linear. Finiteness of the index type is not needed for this pointwise condition;
it is required when the family indexes a typed distribution. Blueprint
`ch12_qpbt_games.tex:1370-1374`, paper
`references/qpbt-paper/07_types.tex:57-63`. -/
def IsTypedCondLinearFamily (K T : Type*) [Field K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ell : ℕ) (L : T → (ι → K) → (ι → K)) : Prop :=
  ∀ t, IsCondLinear ell (L t)

/-- The typed CL distribution: sample a type pair from the graph distribution,
then bind it to the CL distribution selected by those two types. This is
`def:typed-cl-distributions`, blueprint `ch12_qpbt_games.tex:1414-1418`, paper
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

/-- A typed conditionally linear distribution built from a single family is
symmetric under exchanging the two players: the edge law of
`def:graph-distribution` is symmetric, and exchanging the two types exchanges
the two images of the common seed.  This is not a named statement of the source
article; it is `lem:typed-cl-distribution-symm` in
`blueprint/src/chapter/ch12_qpbt_games.tex`. -/
theorem typedCLDistribution_symm {K T ι : Type*}
    [Field K] [Fintype K] [DecidableEq K]
    [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
    (E : Finset (Sym2 T)) (hE : E.Nonempty)
    (L : T → (ι → K) → (ι → K))
    (c : (T × (ι → K)) × (T × (ι → K))) :
    (typedCLDistribution E hE L L).weight c =
      (typedCLDistribution E hE L L).weight c.swap := by
  classical
  have hinner : ∀ (u v : T) (w : (T × (ι → K)) × (T × (ι → K))),
      ((clDistribution (L u) (L v)).map fun xy => ((u, xy.1), (v, xy.2))).weight w =
        (((Finset.univ : Finset (ι → K)).filter
            fun z => ((u, L u z), (v, L v z)) = w).card : Error) *
          (1 / (Fintype.card (ι → K) : Error)) := by
    intro u v w
    have hmap : ((clDistribution (L u) (L v)).map fun xy => ((u, xy.1), (v, xy.2))) =
        (uniformDistribution (ι → K)).map fun z => ((u, L u z), (v, L v z)) := by
      rw [clDistribution]
      exact Distribution.map_map _ _ _
    rw [hmap, uniformDistribution_map_weight]
  have hfib : ∀ (u v : T) (w : (T × (ι → K)) × (T × (ι → K))),
      ((Finset.univ : Finset (ι → K)).filter
          fun z => ((u, L u z), (v, L v z)) = w) =
        ((Finset.univ : Finset (ι → K)).filter
          fun z => ((v, L v z), (u, L u z)) = w.swap) := by
    rintro u v ⟨w₁, w₂⟩
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.swap_prod_mk,
      Prod.mk.injEq]
    exact and_comm
  have hbind : ∀ w : (T × (ι → K)) × (T × (ι → K)),
      (typedCLDistribution E hE L L).weight w =
        ∑ uv : T × T, (graphDistribution E hE).weight uv *
          ((((Finset.univ : Finset (ι → K)).filter
              fun z => ((uv.1, L uv.1 z), (uv.2, L uv.2 z)) = w).card : Error) *
            (1 / (Fintype.card (ι → K) : Error))) := by
    intro w
    have hsupport : (∑ uv ∈ (graphDistribution E hE).support,
        (graphDistribution E hE).weight uv *
          ((clDistribution (L uv.1) (L uv.2)).map
            fun xy => ((uv.1, xy.1), (uv.2, xy.2))).weight w) =
        ∑ uv : T × T, (graphDistribution E hE).weight uv *
          ((clDistribution (L uv.1) (L uv.2)).map
            fun xy => ((uv.1, xy.1), (uv.2, xy.2))).weight w := by
      refine Finset.sum_subset (Finset.subset_univ _) fun uv _ huv => ?_
      rw [(graphDistribution E hE).outsideSupport uv huv, zero_mul]
    change (∑ uv ∈ (graphDistribution E hE).support,
      (graphDistribution E hE).weight uv *
        ((clDistribution (L uv.1) (L uv.2)).map
          fun xy => ((uv.1, xy.1), (uv.2, xy.2))).weight w) = _
    rw [hsupport]
    exact Finset.sum_congr rfl fun uv _ => by rw [hinner uv.1 uv.2 w]
  rw [hbind c, hbind c.swap]
  refine Fintype.sum_equiv (Equiv.prodComm T T) _ _ ?_
  rintro ⟨u, v⟩
  change (graphDistribution E hE).weight (u, v) *
      ((((Finset.univ : Finset (ι → K)).filter
          fun z => ((u, L u z), (v, L v z)) = c).card : Error) *
        (1 / (Fintype.card (ι → K) : Error))) =
    (graphDistribution E hE).weight (v, u) *
      ((((Finset.univ : Finset (ι → K)).filter
          fun z => ((v, L v z), (u, L u z)) = c.swap).card : Error) *
        (1 / (Fintype.card (ι → K) : Error)))
  rw [graphDistribution_symm E hE u v, hfib u v c]

end MIPStarRE.QPBT
