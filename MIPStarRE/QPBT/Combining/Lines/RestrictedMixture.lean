import MIPStarRE.QPBT.Combining.Defs
import MIPStarRE.QPBT.Games.DistributionBind
import MIPStarRE.QPBT.Games.DistributionRestriction

/-!
# Uniform coordinate-index mixtures of the line-point laws

This module proves that the axis-parallel and diagonal line-point laws are the
uniform mixtures of their coordinate-index restrictions.  The identity rests on
the exact seed decomposition of `chiIndex`: the retained scalar seed is uniform,
so each of its `m` coordinate-index fibers carries mass `1 / m`, and every
line conditioning map keeps that seed.

## References

The mixture assertion is the opening sentence of blueprint
`lem:restricted-line-mixture-bounds`, formalizing the unlabelled observation at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1049-1051`.
The restricted laws are blueprint `def:ith-restricted-line`, paper lines
1038--1048.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-! ## The uniform coordinate-index law of the retained seed -/

/-- The coordinate index of the retained seed of a uniformly sampled low-degree
vector is uniform.  Formalization-only auxiliary for blueprint
`def:ith-restricted-line`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1038-1048`. -/
theorem uniformDistribution_map_chiIndex_ldSeed (L : LdParams) :
    (uniformDistribution (LdSpace L)).map
        (fun z : LdSpace L => chiIndex L z.seed) =
      uniformDistribution (Fin L.m) := by
  classical
  haveI : Nonempty (ScalarQ L) := ⟨0⟩
  haveI : Nonempty (Fin L.m) :=
    Fin.pos_iff_nonempty.mp (lt_of_lt_of_le Nat.zero_lt_one L.hm)
  rw [← Distribution.map_map (uniformDistribution (LdSpace L))
      (fun z : LdSpace L => LdSpace.seed z) (chiIndex L),
    map_uniformDistribution_seed, uniformDistribution_map_chiIndex]

/-! ## The mass of a coordinate-index event -/

/-- Every coordinate-index event of a line conditioning map that keeps the
shared scalar coordinate carries mass `1 / m`.  This is the equal-weight
statement behind blueprint `lem:restricted-line-mixture-bounds`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1049-1051`. -/
theorem clDistribution_seedEvent_mass (L : LdParams) (i : Fin L.m)
    (CL : LdSpace L → LdSpace L)
    (hseed : ∀ z : LdSpace L, (CL z).seed = z.seed) :
    ∑ sample ∈
        (clDistribution CL (ldPointCL L)).support.filter
          (restrictedLineSeedEvent L i),
      (clDistribution CL (ldPointCL L)).weight sample = 1 / (L.m : ℝ) := by
  classical
  haveI : Nonempty (Fin L.m) :=
    Fin.pos_iff_nonempty.mp (lt_of_lt_of_le Nat.zero_lt_one L.hm)
  rw [Distribution.sum_filter_weight_eq_avgOver]
  unfold clDistribution
  rw [Distribution.avgOver_map]
  have hpoint : ∀ z : LdSpace L,
      (if restrictedLineSeedEvent L i (CL z, ldPointCL L z) then (1 : ℝ)
        else 0) = if chiIndex L z.seed = i then 1 else 0 := by
    intro z
    by_cases h : chiIndex L z.seed = i
    · rw [if_pos h, if_pos]
      change chiIndex L (LdSpace.seed (CL z)) = i
      rw [hseed z]
      exact h
    · rw [if_neg h, if_neg]
      change ¬ chiIndex L (LdSpace.seed (CL z)) = i
      rw [hseed z]
      exact h
  rw [avgOver_congr _ _ _ hpoint,
    show (fun z : LdSpace L => if chiIndex L z.seed = i then (1 : ℝ) else 0) =
        fun z : LdSpace L => (fun j : Fin L.m => if j = i then (1 : ℝ) else 0)
          (chiIndex L z.seed) from rfl,
    ← Distribution.avgOver_map (uniformDistribution (LdSpace L))
      (fun z : LdSpace L => chiIndex L z.seed)
      (fun j : Fin L.m => if j = i then (1 : ℝ) else 0),
    uniformDistribution_map_chiIndex_ldSeed]
  unfold avgOver
  simp [uniformDistribution_weight_apply, mul_ite]

/-! ## The two source mixture identities -/

/-- The axis-parallel line-point law is the uniform mixture of its
coordinate-index restrictions.  This is the axis half of
blueprint `lem:restricted-line-mixture-bounds`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1049-1051`. -/
theorem aLinePointDist_eq_bind_restricted (L : LdParams) :
    aLinePointDist L =
      Distribution.bind (uniformDistribution (Fin L.m))
        (restrictedALineDist L) := by
  classical
  haveI : Nonempty (Fin L.m) :=
    Fin.pos_iff_nonempty.mp (lt_of_lt_of_le Nat.zero_lt_one L.hm)
  have hmix := Distribution.bind_uniform_restrict_eq
    (clDistribution (ldALineCL L) (ldPointCL L))
    (restrictedLineSeedEvent L) (restrictedALineSeedEvent_positive L)
    (fun i => by
      rw [clDistribution_seedEvent_mass L i (ldALineCL L) fun _ => rfl,
        Fintype.card_fin])
    (fun sample => ⟨chiIndex L (LdSpace.seed sample.1), rfl, fun i hi => hi.symm⟩)
  rw [aLinePointDist, ← hmix, Distribution.bind_map]
  rfl

/-- The diagonal line-point law is the uniform mixture of its coordinate-index
restrictions.  This is the diagonal half of
blueprint `lem:restricted-line-mixture-bounds`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1049-1051`. -/
theorem dLinePointDist_eq_bind_restricted (L : LdParams) :
    dLinePointDist L =
      Distribution.bind (uniformDistribution (Fin L.m))
        (restrictedDLineDist L) := by
  classical
  haveI : Nonempty (Fin L.m) :=
    Fin.pos_iff_nonempty.mp (lt_of_lt_of_le Nat.zero_lt_one L.hm)
  have hmix := Distribution.bind_uniform_restrict_eq
    (clDistribution (ldDLineCL L) (ldPointCL L))
    (restrictedLineSeedEvent L) (restrictedDLineSeedEvent_positive L)
    (fun i => by
      rw [clDistribution_seedEvent_mass L i (ldDLineCL L) fun _ => rfl,
        Fintype.card_fin])
    (fun sample => ⟨chiIndex L (LdSpace.seed sample.1), rfl, fun i hi => hi.symm⟩)
  rw [dLinePointDist, ← hmix, Distribution.bind_map]
  rfl

end

end MIPStarRE.QPBT
