import MIPStarRE.QPBT.Combining.Lines.SubLineExtended

/-!
# Uniform points of a line and the blocks of a coordinate direction

This module records the two elementary geometric inputs of the sampling
procedure of the sub-line lemma. First, for independent uniform inputs `u` in
the ambient coordinate space and `t` in the scalar field, the point
`lineRepMap v u + t • v` is uniform. This map on ambient-point--parameter pairs
has fibers of size `q`: for nonzero `v`, `u` varies over a coset of the span of
`v`, while its canonical representative and `t` are fixed; for zero `v`, `u`
is fixed and `t` is free. Second, the two coordinate
blocks of an elementary coordinate direction of the extended space are the
corresponding elementary direction of the source space in the block that
carries the coordinate, and zero in the other block and at the two scalar
coordinates.

## References

The two statements support `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The canonical representative map is blueprint
`def:line-representative`; the coordinate blocks are those of
blueprint `def:combine-map`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-! ## The canonical representative for the zero direction -/

/-- For the zero direction the canonical representative map of
`def:line-representative` is the identity, since the span of the zero vector
is trivial.  Blueprint `def:line-representative`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:143-174`.
-/
theorem lineRepMap_zero_apply {K : Type*} [Field K] {m : ℕ}
    (u : Fin m → K) : lineRepMap (0 : Fin m → K) u = u := by
  have hspan : Submodule.span K ({0} : Set (Fin m → K)) = ⊥ := by simp
  have h := sub_lineRepMap_mem_span (0 : Fin m → K) u
  rw [hspan, Submodule.mem_bot, sub_eq_zero] at h
  exact h.symm

/-! ## Uniform points of a line -/

/-- The point at a uniformly random affine parameter on the line through the
canonical representative of a uniformly random point is uniformly random on
the whole coordinate space.  Every fiber of the parameterization has exactly
`q` elements in the ambient-point--parameter domain: for a nonzero direction
the parameter and canonical representative are fixed, while the input point
varies over a coset of the span of the direction. For the zero direction the
input point is fixed and the parameter is free. Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem uniformDistribution_map_lineRepMap_add_smul {K : Type*} [Field K]
    [Fintype K] [DecidableEq K] {m : ℕ} (v : Fin m → K) :
    (uniformDistribution ((Fin m → K) × K)).map
        (fun w => lineRepMap v w.1 + w.2 • v) =
      uniformDistribution (Fin m → K) := by
  refine uniformDistribution_map_of_card_fiber _ (Fintype.card K) fun x => ?_
  by_cases hv : v = 0
  · subst hv
    have hfilter :
        ((Finset.univ : Finset ((Fin m → K) × K)).filter
            fun w => lineRepMap (0 : Fin m → K) w.1 + w.2 • (0 : Fin m → K)
              = x)
          = ({x} : Finset (Fin m → K)) ×ˢ (Finset.univ : Finset K) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_product, Finset.mem_singleton, and_true, smul_zero,
        add_zero, lineRepMap_zero_apply]
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
            fun w => lineRepMap v w.1 + w.2 • v = x)
          = (Finset.univ : Finset K).image
              (fun c => (lineRepMap v x + c • v,
                directLineRepParameter v x)) := by
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

/-! ## Injectivity of the two block embeddings -/

/-- The `X`-block coordinate embedding of `def:combine-map` is injective.
Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem embX_injective (m : ℕ) : Function.Injective (embX m) := by
  intro i j hij
  simpa using (finCombineEquiv m).symm.injective hij

/-- The `Z`-block coordinate embedding of `def:combine-map` is injective.
Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem embZ_injective (m : ℕ) : Function.Injective (embZ m) := by
  intro i j hij
  simpa using (finCombineEquiv m).symm.injective hij

/-! ## The blocks of an elementary coordinate direction -/

/-- The `X` block of the elementary direction at an `X`-block coordinate is
the elementary direction of the source space at that coordinate.  Blueprint
`def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem projX_coordinateDirection_embX {K : Type*} [Field K] {m : ℕ}
    (i : Fin m) :
    projX (coordinateDirection (embX m i) : Fin (2 * m + 2) → K) =
      coordinateDirection i := by
  funext j
  simp [projX, coordinateDirection, Pi.single_apply, (embX_injective m).eq_iff]

/-- The `X` block of the elementary direction at a `Z`-block coordinate
vanishes.  Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem projX_coordinateDirection_embZ {K : Type*} [Field K] {m : ℕ}
    (i : Fin m) :
    projX (coordinateDirection (embZ m i) : Fin (2 * m + 2) → K) = 0 := by
  funext j
  have hne : embX m j ≠ embZ m i := by
    intro h
    simpa using (finCombineEquiv m).symm.injective h
  simp [projX, coordinateDirection, hne]

/-- The `X` block of the elementary direction at the first scalar coordinate
vanishes.  Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem projX_coordinateDirection_alphaVar {K : Type*} [Field K] {m : ℕ} :
    projX (coordinateDirection (alphaVar m) : Fin (2 * m + 2) → K) = 0 := by
  funext j
  have hne : embX m j ≠ alphaVar m := by
    intro h
    simpa using (finCombineEquiv m).symm.injective h
  simp [projX, coordinateDirection, hne]

/-- The `X` block of the elementary direction at the second scalar coordinate
vanishes.  Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem projX_coordinateDirection_betaVar {K : Type*} [Field K] {m : ℕ} :
    projX (coordinateDirection (betaVar m) : Fin (2 * m + 2) → K) = 0 := by
  funext j
  have hne : embX m j ≠ betaVar m := by
    intro h
    simpa using (finCombineEquiv m).symm.injective h
  simp [projX, coordinateDirection, hne]

/-- The `Z` block of the elementary direction at a `Z`-block coordinate is
the elementary direction of the source space at that coordinate.  Blueprint
`def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem projZ_coordinateDirection_embZ {K : Type*} [Field K] {m : ℕ}
    (i : Fin m) :
    projZ (coordinateDirection (embZ m i) : Fin (2 * m + 2) → K) =
      coordinateDirection i := by
  funext j
  simp [projZ, coordinateDirection, Pi.single_apply, (embZ_injective m).eq_iff]

/-- The `Z` block of the elementary direction at an `X`-block coordinate
vanishes.  Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem projZ_coordinateDirection_embX {K : Type*} [Field K] {m : ℕ}
    (i : Fin m) :
    projZ (coordinateDirection (embX m i) : Fin (2 * m + 2) → K) = 0 := by
  funext j
  have hne : embZ m j ≠ embX m i := by
    intro h
    simpa using (finCombineEquiv m).symm.injective h
  simp [projZ, coordinateDirection, hne]

/-- The `Z` block of the elementary direction at the first scalar coordinate
vanishes.  Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem projZ_coordinateDirection_alphaVar {K : Type*} [Field K] {m : ℕ} :
    projZ (coordinateDirection (alphaVar m) : Fin (2 * m + 2) → K) = 0 := by
  funext j
  have hne : embZ m j ≠ alphaVar m := by
    intro h
    simpa using (finCombineEquiv m).symm.injective h
  simp [projZ, coordinateDirection, hne]

/-- The `Z` block of the elementary direction at the second scalar coordinate
vanishes.  Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem projZ_coordinateDirection_betaVar {K : Type*} [Field K] {m : ℕ} :
    projZ (coordinateDirection (betaVar m) : Fin (2 * m + 2) → K) = 0 := by
  funext j
  have hne : embZ m j ≠ betaVar m := by
    intro h
    simpa using (finCombineEquiv m).symm.injective h
  simp [projZ, coordinateDirection, hne]

/-! ## The coordinates occupied by the two blocks -/

/-- The `i`-th `X`-block coordinate of the extended space is its `i`-th
coordinate.  Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem embX_val (m : ℕ) (i : Fin m) : (embX m i).val = i.val := rfl

/-- The `i`-th `Z`-block coordinate of the extended space is its `(m + i)`-th
coordinate.  Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem embZ_val (m : ℕ) (i : Fin m) : (embZ m i).val = m + i.val := rfl

/-- The extended coordinate carrying the first scalar is the coordinate
`2 m`.  Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem alphaVar_val (m : ℕ) : (alphaVar m).val = 2 * m := by
  simp [alphaVar, finCombineEquiv]

/-- The extended coordinate carrying the second scalar is the coordinate
`2 m + 1`.  Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem betaVar_val (m : ℕ) : (betaVar m).val = 2 * m + 1 := by
  simp [betaVar, finCombineEquiv]

/-! ## The blocks of a point of an extended line -/

/-- Transporting the extended scalar field to the source scalar field carries
a point of a line to a point of the transported line, since the transport is
a coordinatewise field isomorphism.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem directPointToPauli_mem_linePoints (P : AdmissibleParams)
    {b d x : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd}
    (hx : x ∈ linePoints b d) :
    directPointToPauli P x ∈
      linePoints (directPointToPauli P b) (directPointToPauli P d) := by
  obtain ⟨t, rfl⟩ := hx
  refine ⟨extendedDirectScalarEquiv P t, ?_⟩
  funext i
  simp [directPointToPauli]

/-- The `X` block of a point of a line lies on the source line through the
canonical representative of the `X` block of the base, as soon as the `X`
block of the direction is a multiple of the source direction.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem projX_mem_linePoints {K : Type*} [Field K] {m : ℕ}
    (b d : Fin (2 * m + 2) → K) (dX : Fin m → K)
    (hd : projX d ∈ Submodule.span K ({dX} : Set (Fin m → K)))
    {x : Fin (2 * m + 2) → K} (hx : x ∈ linePoints b d) :
    projX x ∈ linePoints (lineRepMap dX (projX b)) dX := by
  obtain ⟨t, rfl⟩ := hx
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hd
  rw [linePoints_eq_of_mem _ dX (projX b)
    (mem_linePoints_lineRepMap dX (projX b))]
  refine ⟨t * c, ?_⟩
  rw [projX_add, projX_smul, ← hc]
  module

/-- The `Z` block of a point of a line lies on the source line through the
canonical representative of the `Z` block of the base, as soon as the `Z`
block of the direction is a multiple of the source direction.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem projZ_mem_linePoints {K : Type*} [Field K] {m : ℕ}
    (b d : Fin (2 * m + 2) → K) (dZ : Fin m → K)
    (hd : projZ d ∈ Submodule.span K ({dZ} : Set (Fin m → K)))
    {x : Fin (2 * m + 2) → K} (hx : x ∈ linePoints b d) :
    projZ x ∈ linePoints (lineRepMap dZ (projZ b)) dZ := by
  obtain ⟨t, rfl⟩ := hx
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hd
  rw [linePoints_eq_of_mem _ dZ (projZ b)
    (mem_linePoints_lineRepMap dZ (projZ b))]
  refine ⟨t * c, ?_⟩
  rw [projZ_add, projZ_smul, ← hc]
  module

/-! ## Incidence of the blocks of an extended line -/

/-- The identification of the extended scalar field with the source scalar
field carries an elementary coordinate direction to the elementary coordinate
direction at the same coordinate.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem directPointToPauli_coordinateDirection (P : AdmissibleParams)
    (k : Fin P.extendedDirectLd.m) :
    directPointToPauli P (coordinateDirection k) = coordinateDirection k := by
  funext j
  simp [directPointToPauli, coordinateDirection, Pi.single_apply]

/-- Incidence of the `X` blocks: if a source line has as base the canonical
representative, in its own direction, of the `X` block of the base of an
extended line, and if the `X` block of the direction of the extended line
lies in the span of the source direction, then the `X` block of every point
of the extended line is a point of the source line.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem projX_mem_pointSet (P : AdmissibleParams)
    (base dir : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd)
    (lineX : LineDesc P.toLdParams)
    (hbase : lineX.base =
      lineRepMap lineX.direction (projX (directPointToPauli P base)))
    (hdir : projX (directPointToPauli P dir) ∈
      Submodule.span (PauliScalar P)
        ({lineX.direction} : Set (Fin P.m → PauliScalar P)))
    {u : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd}
    (hu : u ∈ linePoints base dir) :
    projX (directPointToPauli P u) ∈ lineX.pointSet := by
  rw [LineDesc.pointSet, hbase]
  exact projX_mem_linePoints _ _ _ hdir (directPointToPauli_mem_linePoints P hu)

/-- Incidence of the `Z` blocks: if a source line has as base the canonical
representative, in its own direction, of the `Z` block of the base of an
extended line, and if the `Z` block of the direction of the extended line
lies in the span of the source direction, then the `Z` block of every point
of the extended line is a point of the source line.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem projZ_mem_pointSet (P : AdmissibleParams)
    (base dir : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd)
    (lineZ : LineDesc P.toLdParams)
    (hbase : lineZ.base =
      lineRepMap lineZ.direction (projZ (directPointToPauli P base)))
    (hdir : projZ (directPointToPauli P dir) ∈
      Submodule.span (PauliScalar P)
        ({lineZ.direction} : Set (Fin P.m → PauliScalar P)))
    {u : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd}
    (hu : u ∈ linePoints base dir) :
    projZ (directPointToPauli P u) ∈ lineZ.pointSet := by
  rw [LineDesc.pointSet, hbase]
  exact projZ_mem_linePoints _ _ _ hdir (directPointToPauli_mem_linePoints P hu)

end

end MIPStarRE.QPBT
