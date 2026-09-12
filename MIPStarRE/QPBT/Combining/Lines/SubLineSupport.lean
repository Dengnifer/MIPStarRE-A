import MIPStarRE.QPBT.Combining.Defs

/-!
# Generating laws of the restricted line-point distributions

This module rewrites the two restricted line-point laws of
`def:ith-restricted-line` as push-forwards of a single uniformly sampled
low-degree vector conditioned on the coordinate-index fiber of its retained
scalar seed.  In that form the point block, the seed and the direction block
of the sampled vector are visibly the independent generating data of the
restricted law, which is the description used by the sampling procedure of the
sub-line lemma: there the projected pairs are built either from a direction
block inherited from the extended line or from freshly sampled data, and each
is asserted to follow a restricted law.

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

/-! ## Restriction of a push-forward -/

/-- Formalization-only auxiliary: restricting a push-forward distribution to a
decidable event is the push-forward of the restriction to the pre-image of
that event.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem Distribution.restrict_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (μ : Distribution α) (f : α → β) (p : β → Prop) [DecidablePred p]
    (q : α → Prop) [DecidablePred q] (hq : ∀ a, q a ↔ p (f a))
    (hpos : 0 < ∑ b ∈ (μ.map f).support.filter p, (μ.map f).weight b)
    (hpos' : 0 < ∑ a ∈ μ.support.filter q, μ.weight a) :
    Distribution.restrict (μ.map f) p hpos =
      (Distribution.restrict μ q hpos').map f := by
  classical
  have hfiber : ∀ b : β, p b →
      μ.support.filter (fun a => f a = b) =
        (μ.support.filter q).filter (fun a => f a = b) := by
    intro b hb
    ext a
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨ha, hab⟩
      exact ⟨⟨ha, (hq a).mpr (hab ▸ hb)⟩, hab⟩
    · rintro ⟨⟨ha, -⟩, hab⟩
      exact ⟨ha, hab⟩
  have himg : (μ.map f).support.filter p = (μ.support.filter q).image f := by
    ext b
    simp only [Distribution.map_support, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hpb⟩
      exact ⟨a, ⟨ha, (hq a).mpr hpb⟩, rfl⟩
    · rintro ⟨a, ⟨ha1, ha2⟩, rfl⟩
      exact ⟨⟨a, ha1, rfl⟩, (hq a).mp ha2⟩
  have hmass : (∑ b ∈ (μ.map f).support.filter p, (μ.map f).weight b) =
      ∑ a ∈ μ.support.filter q, μ.weight a := by
    rw [himg]
    rw [← Finset.sum_fiberwise_of_maps_to
      (s := μ.support.filter q) (t := (μ.support.filter q).image f)
      (g := f) (fun a ha => Finset.mem_image_of_mem f ha) μ.weight]
    refine Finset.sum_congr rfl fun b hb => ?_
    obtain ⟨a0, ha0, rfl⟩ := Finset.mem_image.mp hb
    rw [Distribution.map_weight,
      hfiber _ ((hq a0).mp (Finset.mem_filter.mp ha0).2)]
  refine Distribution.ext_of_support_of_weight ?_ ?_
  · exact himg
  · funext b
    show (if p b then (μ.map f).weight b /
        ∑ c ∈ (μ.map f).support.filter p, (μ.map f).weight c else 0) =
      ∑ a ∈ (μ.support.filter q).filter (fun a => f a = b),
        (if q a then μ.weight a / ∑ c ∈ μ.support.filter q, μ.weight c else 0)
    by_cases hb : p b
    · rw [if_pos hb, hmass, Distribution.map_weight, hfiber b hb,
        Finset.sum_div]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [if_pos (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2]
    · rw [if_neg hb]
      refine (Finset.sum_eq_zero fun a ha => ?_).symm
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
      exact absurd (ha2 ▸ (hq a).mp (Finset.mem_filter.mp ha1).2) hb

/-! ## The coordinate-index event on a single uniform vector -/

/-- The coordinate-index event of `def:ith-restricted-line` read on the single
uniformly sampled low-degree vector that generates the line-point laws.
Blueprint `def:ith-restricted-line`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1038-1048`. -/
def ldSeedEvent (L : LdParams) (i : Fin L.m) (z : LdSpace L) : Prop :=
  chiIndex L (LdSpace.seed z) = i

/-- Decidability of the coordinate-index event. -/
instance ldSeedEvent_decidablePred (L : LdParams) (i : Fin L.m) :
    DecidablePred (ldSeedEvent L i) := by
  intro z
  unfold ldSeedEvent
  infer_instance

/-- The coordinate-index event has positive mass under the uniform law on
low-degree vectors, so the conditioning below is normalized.  Blueprint
`def:ith-restricted-line`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1038-1048`. -/
theorem ldSeedEvent_positive (L : LdParams) (i : Fin L.m) :
    0 < ∑ z ∈ (uniformDistribution (LdSpace L)).support.filter
        (ldSeedEvent L i),
      (uniformDistribution (LdSpace L)).weight z := by
  classical
  refine Finset.sum_pos'
    (fun a _ => (uniformDistribution (LdSpace L)).nonnegative a)
    ⟨(fun _ => seedOfIndexResidue L i ⟨0, L.seedFiberCard_pos⟩),
      Finset.mem_filter.mpr ⟨by simp, ?_⟩, ?_⟩
  · show chiIndex L (seedOfIndexResidue L i ⟨0, L.seedFiberCard_pos⟩) = i
    exact chiIndex_seedOfIndexResidue L i _
  · simp only [uniformDistribution, Distribution.uniformOnFinset_weight,
      Finset.mem_univ, if_true]
    positivity

/-! ## Canonical representatives are unchanged by the conditioning maps -/

/-- Two axis-line descriptions with the same seed and the same base agree:
the stored proof of `def:line-representative` invariance is a proposition and
carries no further data.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem lineDesc_axis_congr {L : LdParams}
    {b b' : Fin L.m → ScalarQ L} {s : ScalarQ L} (h : b = b')
    (hb : lineRepMap (coordinateDirection (chiIndex L s)) b = b)
    (hb' : lineRepMap (coordinateDirection (chiIndex L s)) b' = b') :
    LineDesc.axis b s hb = LineDesc.axis b' s hb' := by
  subst h
  rfl

/-- Two diagonal-line descriptions with the same seed, the same base and the
same direction agree: the stored proofs of `def:line-representative`
invariance and of the prefix-zero condition are propositions and carry no
further data.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem lineDesc_diagonal_congr {L : LdParams}
    {b b' d d' : Fin L.m → ScalarQ L} {s : ScalarQ L}
    (hb : b = b') (hd : d = d')
    (h1 : lineRepMap d b = b)
    (h2 : ∀ j : Fin L.m, j.val < (chiIndex L s).val → d j = 0)
    (h1' : lineRepMap d' b' = b')
    (h2' : ∀ j : Fin L.m, j.val < (chiIndex L s).val → d' j = 0) :
    LineDesc.diagonal b s d h1 h2 = LineDesc.diagonal b' s d' h1' h2' := by
  subst hb
  subst hd
  rfl

/-- The axis-line decoder is unchanged by the axis conditioning map: the
canonical representative of `def:line-representative` is idempotent, so
decoding the conditioned vector and decoding the original vector agree.
Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem aLineDescOf_ldALineCL (L : LdParams) (z : LdSpace L) :
    aLineDescOf L (ldALineCL L z) = aLineDescOf L z :=
  lineDesc_axis_congr (lineRepMap_apply_self _ _) _ _

/-- The diagonal-line decoder is unchanged by the diagonal conditioning map:
the prefix projection and the canonical representative of
`def:line-representative` are both idempotent.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem dLineDescOf_ldDLineCL (L : LdParams) (z : LdSpace L) :
    dLineDescOf L (ldDLineCL L z) = dLineDescOf L z := by
  have hdir : prefixProjection (chiIndex L (LdSpace.seed (ldDLineCL L z)))
        (LdSpace.direction (ldDLineCL L z))
      = prefixProjection (chiIndex L (LdSpace.seed z)) (LdSpace.direction z) :=
    prefixProjection_idempotent _ _
  have hpt : lineRepMap
        (prefixProjection (chiIndex L (LdSpace.seed (ldDLineCL L z)))
          (LdSpace.direction (ldDLineCL L z)))
        (LdSpace.point (ldDLineCL L z))
      = lineRepMap
        (prefixProjection (chiIndex L (LdSpace.seed z)) (LdSpace.direction z))
        (LdSpace.point z) := by
    rw [hdir]
    exact lineRepMap_apply_self _ _
  exact lineDesc_diagonal_congr hpt hdir _ _ _ _

/-! ## Generating laws of the restricted line-point distributions -/

/-- The `i`-th restricted axis-line law is the law of the pair consisting of
the canonical axis-parallel line through a low-degree vector and its point
block, when that vector is uniform conditioned on the coordinate-index fiber
of its seed.  This is the generating description used in the sampling
procedure of blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem restrictedALineDist_eq_map_restrict (L : LdParams) (i : Fin L.m) :
    restrictedALineDist L i =
      (Distribution.restrict (uniformDistribution (LdSpace L))
          (ldSeedEvent L i) (ldSeedEvent_positive L i)).map
        (fun z => (aLineDescOf L z, LdSpace.point z)) := by
  classical
  have hcomp :
      (fun z : LdSpace L =>
          (aLineDescOf L (ldALineCL L z), LdSpace.point (ldPointCL L z))) =
        fun z : LdSpace L => (aLineDescOf L z, LdSpace.point z) := by
    funext z
    rw [aLineDescOf_ldALineCL]
    rfl
  unfold restrictedALineDist restrictedALinePreDist clDistribution
  rw [Distribution.restrict_map (uniformDistribution (LdSpace L))
      (fun z => (ldALineCL L z, ldPointCL L z))
      (restrictedLineSeedEvent L i) (ldSeedEvent L i) (fun _ => Iff.rfl)
      _ (ldSeedEvent_positive L i),
    Distribution.map_map]
  exact congrArg _ hcomp

/-- The `i`-th restricted diagonal-line law is the law of the pair consisting
of the canonical diagonal line through a low-degree vector and its point
block, when that vector is uniform conditioned on the coordinate-index fiber
of its seed.  This is the generating description used in the sampling
procedure of blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem restrictedDLineDist_eq_map_restrict (L : LdParams) (i : Fin L.m) :
    restrictedDLineDist L i =
      (Distribution.restrict (uniformDistribution (LdSpace L))
          (ldSeedEvent L i) (ldSeedEvent_positive L i)).map
        (fun z => (dLineDescOf L z, LdSpace.point z)) := by
  classical
  have hcomp :
      (fun z : LdSpace L =>
          (dLineDescOf L (ldDLineCL L z), LdSpace.point (ldPointCL L z))) =
        fun z : LdSpace L => (dLineDescOf L z, LdSpace.point z) := by
    funext z
    rw [dLineDescOf_ldDLineCL]
    rfl
  unfold restrictedDLineDist restrictedDLinePreDist clDistribution
  rw [Distribution.restrict_map (uniformDistribution (LdSpace L))
      (fun z => (ldDLineCL L z, ldPointCL L z))
      (restrictedLineSeedEvent L i) (ldSeedEvent L i) (fun _ => Iff.rfl)
      _ (ldSeedEvent_positive L i),
    Distribution.map_map]
  exact congrArg _ hcomp

end

end MIPStarRE.QPBT
