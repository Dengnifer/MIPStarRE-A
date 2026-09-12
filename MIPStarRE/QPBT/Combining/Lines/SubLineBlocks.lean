import MIPStarRE.QPBT.Combining.Lines.RestrictedMixture
import MIPStarRE.QPBT.Combining.Lines.SubLineSupport

/-!
# Independent blocks of the restricted line-point laws

This module isolates the independent generating blocks of the restricted
line-point laws used by the sampling procedure of the sub-line lemma.  A
uniformly sampled low-degree vector splits into a point block and a
seed-direction block; the coordinate-index event constrains only the second
block, so conditioning on it leaves the point block uniform and independent.
The conditioned seed-direction block is the fresh diagonal direction pair of
the sub-line construction, and the uniform mixture of those pairs over the
coordinate index is the unconditioned law.

## References

The generating descriptions support `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The restricted laws themselves are `def:ith-restricted-line`, blueprint lines
1209--1228, paper lines 1038--1048.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-! ## The block decomposition of an ambient low-degree vector -/

/-- Split an ambient low-degree vector into its point block and its
seed-direction block.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`. -/
def ldSpaceBlockEquiv (L : LdParams) :
    LdSpace L ≃
      (Fin L.m → ScalarQ L) × (ScalarQ L × (Fin L.m → ScalarQ L)) where
  toFun z := (LdSpace.point z, LdSpace.seed z, LdSpace.direction z)
  invFun w := fun i =>
    match i with
    | .inl (.inl j) => w.1 j
    | .inl (.inr _) => w.2.1
    | .inr j => w.2.2 j
  left_inv z := by
    funext i
    rcases i with (j | u) | j <;> rfl
  right_inv w := rfl

/-- The coordinate-index event of `def:ith-restricted-line` read on the
seed-direction block of an ambient low-degree vector.  Blueprint
`def:ith-restricted-line`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1038-1048`. -/
def ldSeedDirEvent (L : LdParams) (i : Fin L.m)
    (sw : ScalarQ L × (Fin L.m → ScalarQ L)) : Prop :=
  chiIndex L sw.1 = i

/-- Decidability of the coordinate-index event on the seed-direction block. -/
instance ldSeedDirEvent_decidablePred (L : LdParams) (i : Fin L.m) :
    DecidablePred (ldSeedDirEvent L i) := by
  intro sw
  unfold ldSeedDirEvent
  infer_instance

/-- Each coordinate-index event of the seed-direction block carries mass
`1 / m` under the uniform law, because the retained seed is uniform and its
`m` coordinate-index fibers are equal.  Blueprint
`lem:restricted-line-mixture-bounds`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1049-1051`. -/
theorem ldSeedDirEvent_mass (L : LdParams) (i : Fin L.m) :
    ∑ sw ∈ (uniformDistribution
          (ScalarQ L × (Fin L.m → ScalarQ L))).support.filter
        (ldSeedDirEvent L i),
        (uniformDistribution
          (ScalarQ L × (Fin L.m → ScalarQ L))).weight sw =
      1 / (L.m : ℝ) := by
  classical
  have hmap : (uniformDistribution
        (ScalarQ L × (Fin L.m → ScalarQ L))).map
        (fun sw => chiIndex L sw.1) = uniformDistribution (Fin L.m) := by
    rw [← Distribution.map_map _ Prod.fst (chiIndex L),
      uniformDistribution_map_fst, uniformDistribution_map_chiIndex]
  rw [Distribution.sum_filter_weight_eq_avgOver,
    show (fun sw : ScalarQ L × (Fin L.m → ScalarQ L) =>
        if ldSeedDirEvent L i sw then (1 : ℝ) else 0) =
      fun sw => (fun j : Fin L.m => if j = i then (1 : ℝ) else 0)
        (chiIndex L sw.1) from rfl,
    ← Distribution.avgOver_map
      (uniformDistribution (ScalarQ L × (Fin L.m → ScalarQ L)))
      (fun sw => chiIndex L sw.1)
      (fun j : Fin L.m => if j = i then (1 : ℝ) else 0), hmap]
  unfold avgOver
  simp [uniformDistribution_weight_apply, mul_ite]

/-- Every coordinate-index event of the seed-direction block has positive
mass.  Blueprint `def:ith-restricted-line`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1038-1048`. -/
theorem ldSeedDirEvent_positive (L : LdParams) (i : Fin L.m) :
    0 < ∑ sw ∈ (uniformDistribution
          (ScalarQ L × (Fin L.m → ScalarQ L))).support.filter
        (ldSeedDirEvent L i),
      (uniformDistribution
        (ScalarQ L × (Fin L.m → ScalarQ L))).weight sw := by
  rw [ldSeedDirEvent_mass]
  have hm : (0 : ℝ) < (L.m : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one L.hm
  positivity

/-! ## Fresh diagonal direction pairs -/

/-- The fresh diagonal direction pair at coordinate index `i`: a scalar seed
uniform in the fiber of `i` together with a direction block uniform on the
whole space.  This is the auxiliary randomness of the sampling procedure of
blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
noncomputable def freshDiagonalPairDist (L : LdParams) (i : Fin L.m) :
    Distribution (ScalarQ L × (Fin L.m → ScalarQ L)) :=
  Distribution.restrict
    (uniformDistribution (ScalarQ L × (Fin L.m → ScalarQ L)))
    (ldSeedDirEvent L i) (ldSeedDirEvent_positive L i)

/-- Every fresh diagonal direction pair law has total mass one. -/
theorem freshDiagonalPairDist_isProbability (L : LdParams) (i : Fin L.m) :
    (freshDiagonalPairDist L i).IsProbability :=
  Distribution.restrict_isProbability _ _ (ldSeedDirEvent_positive L i)

/-- The uniform mixture over the coordinate index of the fresh diagonal
direction pairs is the unconditioned uniform seed-direction law.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem bind_uniform_freshDiagonalPairDist (L : LdParams) :
    Distribution.bind (uniformDistribution (Fin L.m))
        (freshDiagonalPairDist L) =
      uniformDistribution (ScalarQ L × (Fin L.m → ScalarQ L)) :=
  Distribution.bind_uniform_restrict_eq _ (ldSeedDirEvent L)
    (ldSeedDirEvent_positive L)
    (fun i => by rw [ldSeedDirEvent_mass, Fintype.card_fin])
    (fun sw => ⟨chiIndex L sw.1, rfl, fun i hi => hi.symm⟩)

/-! ## Independence of the point block under the coordinate-index event -/

/-- Conditioning the uniform ambient low-degree law on the coordinate-index
event of its seed leaves the point block uniform and independent of the fresh
diagonal direction pair carried by the seed-direction block.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem restrict_uniform_ldSeedEvent_map_block (L : LdParams) (i : Fin L.m) :
    (Distribution.restrict (uniformDistribution (LdSpace L)) (ldSeedEvent L i)
        (ldSeedEvent_positive L i)).map (ldSpaceBlockEquiv L) =
      Distribution.prod (uniformDistribution (Fin L.m → ScalarQ L))
        (freshDiagonalPairDist L i) := by
  classical
  have hequiv := uniformDistribution_map_equiv (ldSpaceBlockEquiv L)
  have hprod : 0 < ∑ w ∈ (uniformDistribution ((Fin L.m → ScalarQ L) ×
          (ScalarQ L × (Fin L.m → ScalarQ L)))).support.filter
        (fun w => ldSeedDirEvent L i w.2),
      (uniformDistribution ((Fin L.m → ScalarQ L) ×
        (ScalarQ L × (Fin L.m → ScalarQ L)))).weight w := by
    rw [uniformDistribution_snd_event_mass]
    exact ldSeedDirEvent_positive L i
  have hposA : 0 < ∑ w ∈ ((uniformDistribution (LdSpace L)).map
        (ldSpaceBlockEquiv L)).support.filter
        (fun w => ldSeedDirEvent L i w.2),
      ((uniformDistribution (LdSpace L)).map
        (ldSpaceBlockEquiv L)).weight w := by
    rw [hequiv]
    exact hprod
  rw [← Distribution.restrict_map (uniformDistribution (LdSpace L))
      (ldSpaceBlockEquiv L) (fun w => ldSeedDirEvent L i w.2)
      (ldSeedEvent L i) (fun _ => Iff.rfl) hposA (ldSeedEvent_positive L i),
    Distribution.restrict_congr hequiv (fun w => ldSeedDirEvent L i w.2)
      hposA hprod,
    restrict_uniform_prod_snd (ldSeedDirEvent L i)
      (ldSeedDirEvent_positive L i) hprod]
  rfl

/-! ## Generating form of the restricted line-point laws -/

/-- The axis-line decoder read on the block decomposition. -/
def aLineDescOfBlock (L : LdParams)
    (w : (Fin L.m → ScalarQ L) × (ScalarQ L × (Fin L.m → ScalarQ L))) :
    LineDesc L :=
  aLineDescOf L ((ldSpaceBlockEquiv L).symm w)

/-- The diagonal-line decoder read on the block decomposition. -/
def dLineDescOfBlock (L : LdParams)
    (w : (Fin L.m → ScalarQ L) × (ScalarQ L × (Fin L.m → ScalarQ L)))  :
    LineDesc L :=
  dLineDescOf L ((ldSpaceBlockEquiv L).symm w)

/-- The `i`-th restricted axis-line law is the law of the canonical
axis-parallel line through a uniform point block, in the coordinate direction
named by an independent fresh diagonal direction pair at index `i`, together
with that same point.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem restrictedALineDist_eq_map_prod (L : LdParams) (i : Fin L.m) :
    restrictedALineDist L i =
      (Distribution.prod (uniformDistribution (Fin L.m → ScalarQ L))
          (freshDiagonalPairDist L i)).map
        (fun w => (aLineDescOfBlock L w, w.1)) := by
  classical
  have hfun : (fun z : LdSpace L =>
        (aLineDescOfBlock L (ldSpaceBlockEquiv L z),
          (ldSpaceBlockEquiv L z).1)) =
      fun z : LdSpace L => (aLineDescOf L z, LdSpace.point z) := by
    funext z
    have h : (ldSpaceBlockEquiv L).symm (ldSpaceBlockEquiv L z) = z :=
      (ldSpaceBlockEquiv L).symm_apply_apply z
    show (aLineDescOf L ((ldSpaceBlockEquiv L).symm (ldSpaceBlockEquiv L z)),
        LdSpace.point z) = (aLineDescOf L z, LdSpace.point z)
    rw [h]
  rw [restrictedALineDist_eq_map_restrict,
    ← restrict_uniform_ldSeedEvent_map_block, Distribution.map_map, hfun]

/-- The `i`-th restricted diagonal-line law is the law of the canonical
diagonal line through a uniform point block, in the prefix-projected direction
of an independent fresh diagonal direction pair at index `i`, together with
that same point.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem restrictedDLineDist_eq_map_prod (L : LdParams) (i : Fin L.m) :
    restrictedDLineDist L i =
      (Distribution.prod (uniformDistribution (Fin L.m → ScalarQ L))
          (freshDiagonalPairDist L i)).map
        (fun w => (dLineDescOfBlock L w, w.1)) := by
  classical
  have hfun : (fun z : LdSpace L =>
        (dLineDescOfBlock L (ldSpaceBlockEquiv L z),
          (ldSpaceBlockEquiv L z).1)) =
      fun z : LdSpace L => (dLineDescOf L z, LdSpace.point z) := by
    funext z
    have h : (ldSpaceBlockEquiv L).symm (ldSpaceBlockEquiv L z) = z :=
      (ldSpaceBlockEquiv L).symm_apply_apply z
    show (dLineDescOf L ((ldSpaceBlockEquiv L).symm (ldSpaceBlockEquiv L z)),
        LdSpace.point z) = (dLineDescOf L z, LdSpace.point z)
    rw [h]
  rw [restrictedDLineDist_eq_map_restrict,
    ← restrict_uniform_ldSeedEvent_map_block, Distribution.map_map, hfun]

end

end MIPStarRE.QPBT
