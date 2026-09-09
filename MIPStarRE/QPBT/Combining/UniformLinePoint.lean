import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Questions
import MIPStarRE.QPBT.Combining.Witnesses
import MIPStarRE.QPBT.Games.DistributionMarginals
import MIPStarRE.LDT.Basic.DistributionAvg

/-!
# A uniform point of the extended space from the sub-line law

The first scalar estimate in the combining argument samples an extended line
from the directly indexed sub-line witness and then a uniform affine parameter.
This module records that the resulting extended point is uniform and hence
that its two source coordinate blocks are independent uniform points.
This is an auxiliary law. Transport to the source's seed-indexed extended
distribution remains open, as recorded in
`docs/paper-gaps/qpbt_subline-claims-line-marginal.tex`.

## References

These statements support `lem:claim-17-1` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`.  The paper uses this sampling
fact at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1159-1166`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-- A dependent mixture of a constant family is the constant law. -/
private theorem Distribution.bind_const_current {α β : Type*} [DecidableEq β]
    (μ : Distribution α) (hμ : μ.IsProbability) (ν : Distribution β) :
    Distribution.bind μ (fun _ => ν) = ν := by
  have hne : μ.support.Nonempty := by
    rw [← Finset.card_pos]
    by_contra hcard
    have hempty : μ.support = ∅ := by
      rw [← Finset.card_eq_zero]
      omega
    have htotal := hμ.weight_sum_eq_one
    rw [hempty] at htotal
    simp at htotal
  refine Distribution.ext_of_support_of_weight ?_ ?_
  · change μ.support.biUnion (fun _ => ν.support) = ν.support
    ext b
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨a, -, hb⟩
      exact hb
    · intro hb
      obtain ⟨a, ha⟩ := hne
      exact ⟨a, ha, hb⟩
  · funext b
    change (∑ a ∈ μ.support, μ.weight a * ν.weight b) = ν.weight b
    rw [← Finset.sum_mul, hμ.weight_sum_eq_one, one_mul]

/-- If every slice of a map of a pair carries the second uniform law to one
fixed law, then the map carries the uniform law of the pair to that law. -/
theorem uniformDistribution_map_uncurry {α β γ : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β] [DecidableEq γ]
    (g : α × β → γ) (ν : Distribution γ)
    (hg : ∀ a, (uniformDistribution β).map (fun b => g (a, b)) = ν) :
    (uniformDistribution (α × β)).map g = ν := by
  rw [← bind_uniformDistribution_map (fun a b => g (a, b)),
    show (fun a => (uniformDistribution β).map (fun b => g (a, b))) =
      fun _ => ν from funext hg]
  exact Distribution.bind_const_current _ (uniformDistribution_isProbability α) ν

/-- For the zero direction, the canonical representative map is the identity. -/
private theorem lineRepMap_zero_apply_current {K : Type*} [Field K] {m : ℕ}
    (u : Fin m → K) : lineRepMap (0 : Fin m → K) u = u := by
  have hspan : Submodule.span K ({0} : Set (Fin m → K)) = ⊥ := by simp
  have h := sub_lineRepMap_mem_span (0 : Fin m → K) u
  rw [hspan, Submodule.mem_bot, sub_eq_zero] at h
  exact h.symm

/-- The canonical representative of a uniform ambient point, translated by an
independent uniform affine parameter, gives a uniform ambient point. The input
point, rather than its canonical representative, varies in the fibers. -/
theorem uniformDistribution_map_lineRepMap_add_smul_current
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] {m : ℕ}
    (v : Fin m → K) :
    (uniformDistribution ((Fin m → K) × K)).map
        (fun w => lineRepMap v w.1 + w.2 • v) =
      uniformDistribution (Fin m → K) := by
  refine uniformDistribution_map_of_card_fiber _ (Fintype.card K) fun x => ?_
  by_cases hv : v = 0
  · subst hv
    have hfilter :
        ((Finset.univ : Finset ((Fin m → K) × K)).filter
            fun w => lineRepMap (0 : Fin m → K) w.1 + w.2 • (0 : Fin m → K) = x) =
          ({x} : Finset (Fin m → K)) ×ˢ (Finset.univ : Finset K) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_product, Finset.mem_singleton, and_true, smul_zero,
        add_zero, lineRepMap_zero_apply_current]
    rw [hfilter, Finset.card_product]
    simp
  · have hinj : Function.Injective
        (fun c : K => (lineRepMap v x + c • v, directLineRepParameter v x)) := by
      intro c₁ c₂ hc
      have hc' : c₁ • v = c₂ • v := by
        have h := congrArg Prod.fst hc
        simpa using h
      have hsub : (c₁ - c₂) • v = 0 := by
        rw [sub_smul, hc', sub_self]
      rcases smul_eq_zero.mp hsub with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hv
    have himg :
        ((Finset.univ : Finset ((Fin m → K) × K)).filter
            fun w => lineRepMap v w.1 + w.2 • v = x) =
          (Finset.univ : Finset K).image
            (fun c => (lineRepMap v x + c • v, directLineRepParameter v x)) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hw
        have hrep : lineRepMap v w.1 = lineRepMap v x := by
          rw [← hw, lineRepMap_add_smul, lineRepMap_apply_self]
        have hx : x = lineRepMap v x + w.2 • v := by
          rw [← hrep]
          exact hw.symm
        have ht : directLineRepParameter v x = w.2 :=
          directLineRepParameter_eq_of_nonzero hv hx
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
          (sub_lineRepMap_mem_span v w.1)
        refine ⟨c, ?_⟩
        have hw1 : lineRepMap v x + c • v = w.1 := by
          rw [← hrep, hc]
          abel
        rw [Prod.ext_iff]
        exact ⟨hw1, ht⟩
      · rintro ⟨c, rfl⟩
        show lineRepMap v (lineRepMap v x + c • v) +
          directLineRepParameter v x • v = x
        rw [lineRepMap_add_smul, lineRepMap_apply_self]
        exact (directLineRepParameter_spec v x).symm
    rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_univ]

/-- Reading a point at a uniform affine parameter on the canonical line of a
uniform direct sample gives a uniform point of the direct coordinate space. -/
theorem uniformDistribution_map_directLine_add_smul (D : DirectLdParams)
    (V : Fin D.m × (Fin D.m → DirectScalarQ D) → (Fin D.m → DirectScalarQ D)) :
    (uniformDistribution (DirectLdSpace D × DirectScalarQ D)).map
        (fun p => lineRepMap (V (p.1.index, p.1.direction)) p.1.point +
          p.2 • V (p.1.index, p.1.direction)) =
      uniformDistribution (Fin D.m → DirectScalarQ D) := by
  classical
  let e : DirectLdSpace D × DirectScalarQ D ≃
      (Fin D.m × (Fin D.m → DirectScalarQ D)) ×
        ((Fin D.m → DirectScalarQ D) × DirectScalarQ D) :=
    { toFun := fun p => ((p.1.index, p.1.direction), (p.1.point, p.2))
      invFun := fun w => (⟨w.2.1, w.1.1, w.1.2⟩, w.2.2)
      left_inv := by rintro ⟨⟨pt, i, dir⟩, t⟩; rfl
      right_inv := by rintro ⟨⟨i, dir⟩, pt, t⟩; rfl }
  have hequiv :
      (uniformDistribution (DirectLdSpace D × DirectScalarQ D)).map e =
        uniformDistribution ((Fin D.m × (Fin D.m → DirectScalarQ D)) ×
          ((Fin D.m → DirectScalarQ D) × DirectScalarQ D)) :=
    uniformDistribution_map_equiv e
  have hmap :
      (uniformDistribution (DirectLdSpace D × DirectScalarQ D)).map
          (fun p => lineRepMap (V (p.1.index, p.1.direction)) p.1.point +
            p.2 • V (p.1.index, p.1.direction)) =
        ((uniformDistribution (DirectLdSpace D × DirectScalarQ D)).map e).map
          (fun w => lineRepMap (V w.1) w.2.1 + w.2.2 • V w.1) := by
    rw [Distribution.map_map]
    rfl
  rw [hmap, hequiv]
  refine uniformDistribution_map_uncurry _ _ fun a => ?_
  exact uniformDistribution_map_lineRepMap_add_smul_current (V a)

/-- Averaging a function at a uniform affine parameter on the canonical line
of a uniform direct sample is averaging it at a uniform point. -/
theorem avgOver_uniform_directLdSpace_line_add_smul (D : DirectLdParams)
    (V : Fin D.m × (Fin D.m → DirectScalarQ D) → (Fin D.m → DirectScalarQ D))
    (g : (Fin D.m → DirectScalarQ D) → ℝ) :
    avgOver (uniformDistribution (DirectLdSpace D)) (fun s =>
        avgOver (uniformDistribution (DirectScalarQ D)) (fun t =>
          g (lineRepMap (V (s.index, s.direction)) s.point +
            t • V (s.index, s.direction)))) =
      avgOver (uniformDistribution (Fin D.m → DirectScalarQ D)) g := by
  classical
  rw [← avgOver_uniform_prod]
  calc
    avgOver (uniformDistribution (DirectLdSpace D × DirectScalarQ D))
          (fun p => g (lineRepMap (V (p.1.index, p.1.direction)) p.1.point +
            p.2 • V (p.1.index, p.1.direction))) =
        avgOver ((uniformDistribution
            (DirectLdSpace D × DirectScalarQ D)).map
          (fun p => lineRepMap (V (p.1.index, p.1.direction)) p.1.point +
            p.2 • V (p.1.index, p.1.direction))) g :=
      (Distribution.avgOver_map _ _ g).symm
    _ = avgOver (uniformDistribution (Fin D.m → DirectScalarQ D)) g := by
      rw [uniformDistribution_map_directLine_add_smul]

/-- A uniform point on a line drawn from the directly indexed line-point law
is uniform in the ambient coordinate space. -/
theorem avgOver_directLinePointDist_line_add_smul (D : DirectLdParams)
    (g : (Fin D.m → DirectScalarQ D) → ℝ) :
    avgOver ((directLinePointDist D).map Prod.fst) (fun line =>
        avgOver (uniformDistribution (DirectScalarQ D)) (fun t =>
          g (line.base + t • line.direction))) =
      avgOver (uniformDistribution (Fin D.m → DirectScalarQ D)) g := by
  classical
  have haxis :
      avgOver (directALinePointDist D) (fun sample =>
          avgOver (uniformDistribution (DirectScalarQ D)) (fun t =>
            g (sample.1.base + t • sample.1.direction))) =
        avgOver (uniformDistribution (Fin D.m → DirectScalarQ D)) g := by
    rw [directALinePointDist, Distribution.avgOver_map]
    exact avgOver_uniform_directLdSpace_line_add_smul D
      (fun w => coordinateDirection w.1) g
  have hdiag :
      avgOver (directDLinePointDist D) (fun sample =>
          avgOver (uniformDistribution (DirectScalarQ D)) (fun t =>
            g (sample.1.base + t • sample.1.direction))) =
        avgOver (uniformDistribution (Fin D.m → DirectScalarQ D)) g := by
    rw [directDLinePointDist, Distribution.avgOver_map]
    exact avgOver_uniform_directLdSpace_line_add_smul D
      (fun w => directPrefixProjection w.1 w.2) g
  rw [Distribution.avgOver_map, directLinePointDist,
    WinImplications.avgOver_mix, haxis, hdiag]
  ring

/-- Identify the directly indexed extended coordinates with the combining
coordinate split. -/
private def extendedFinCombineEquiv (P : AdmissibleParams) :
    Fin P.extendedDirectLd.m ≃ ((Fin P.m ⊕ Fin P.m) ⊕ Fin 2) :=
  (finCongr (by rfl)).trans (finCombineEquiv P.m)

/-- Split an extended point into its two source blocks and two remaining
scalar coordinates. -/
private noncomputable def extendedPointBlocksEquiv (P : AdmissibleParams) :
    (Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) ≃
      ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)) ×
        (Fin 2 → PauliScalar P) :=
  (Equiv.arrowCongr (extendedFinCombineEquiv P)
      (extendedDirectScalarEquiv P)).trans
    ((Equiv.sumArrowEquivProdArrow (Fin P.m ⊕ Fin P.m) (Fin 2)
      (PauliScalar P)).trans
      (Equiv.prodCongr
        (Equiv.sumArrowEquivProdArrow (Fin P.m) (Fin P.m) (PauliScalar P))
        (Equiv.refl (Fin 2 → PauliScalar P))))

/-- The two source blocks of a uniform extended point are independent and
uniform after the canonical scalar identification. -/
private theorem uniformDistribution_map_projX_projZ_pauli_current
    (P : AdmissibleParams) :
    (uniformDistribution
          (Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd)).map
        (fun u => (projX (directPointToPauli P u),
          projZ (directPointToPauli P u))) =
      uniformDistribution
        ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)) := by
  classical
  apply uniformDistribution_map_fst_of_equiv (extendedPointBlocksEquiv P)
  intro u
  apply Prod.ext <;> funext i <;> rfl

/-- Under a sub-line witness, the two source blocks of the point at a uniform
affine parameter are independent uniform source points. -/
theorem SubLineWitness.avgOver_projX_projZ (P : AdmissibleParams)
    (sublines : SubLineWitness P)
    (f : ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)) → ℝ) :
    avgOver sublines.D (fun sample =>
        avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
          (fun t =>
            f (projX (directPointToPauli P
                (sample.1.base + t • sample.1.direction)),
              projZ (directPointToPauli P
                (sample.1.base + t • sample.1.direction))))) =
      avgOver (uniformDistribution
        ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P))) f := by
  classical
  have hmarginal :
      avgOver sublines.D (fun sample =>
          avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
            (fun t => f (projX (directPointToPauli P
                (sample.1.base + t • sample.1.direction)),
              projZ (directPointToPauli P
                (sample.1.base + t • sample.1.direction))))) =
        avgOver ((directLinePointDist P.extendedDirectLd).map Prod.fst)
          (fun line =>
            avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
              (fun t => f (projX (directPointToPauli P
                  (line.base + t • line.direction)),
                projZ (directPointToPauli P
                  (line.base + t • line.direction))))) := by
    rw [← sublines.extended_marginal, Distribution.avgOver_map]
  refine hmarginal.trans ?_
  refine (avgOver_directLinePointDist_line_add_smul P.extendedDirectLd
    (fun u => f (projX (directPointToPauli P u),
      projZ (directPointToPauli P u)))).trans ?_
  rw [← uniformDistribution_map_projX_projZ_pauli_current,
    Distribution.avgOver_map]

end

end MIPStarRE.QPBT
