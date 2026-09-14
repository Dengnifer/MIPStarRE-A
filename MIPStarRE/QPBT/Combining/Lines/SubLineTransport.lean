import MIPStarRE.QPBT.Combining.Lines.SubLinePrefix

/-!
# Uniformity under the identification of the two scalar fields

The extended line of the sub-line construction lives over the scalar field of
the directly indexed extended game, while the two source lines live over the
scalar field of the Pauli basis test.  The two fields are identified
coordinatewise by a field isomorphism, so that identification is a bijection
of the coordinate spaces and therefore carries uniform laws to uniform laws.
This module records that transport for a whole extended point and for the two
source blocks of an extended point, and it records the resampling rule that
reading a function at the point of a uniformly random affine parameter on the
line through the canonical representative of a uniformly random point is the
same as reading that function at a uniformly random point.

## References

The statements support `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The coordinate blocks are those of `def:combine-map`, blueprint lines
445--480, paper lines 970--989.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-! ## The identification of the two scalar fields as a bijection -/

/-- The coordinatewise identification of the extended scalar field with the
source scalar field on one source block, presented as a bijection.  Blueprint
`def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
noncomputable def directBlockToPauliEquiv (P : AdmissibleParams) :
    (Fin P.m → DirectScalarQ P.extendedDirectLd) ≃ (Fin P.m → PauliScalar P) where
  toFun v := fun i => extendedDirectScalarEquiv P (v i)
  invFun v := fun i => (extendedDirectScalarEquiv P).symm (v i)
  left_inv v := by
    funext i
    simp
  right_inv v := by
    funext i
    simp

/-- The coordinatewise identification of the extended scalar field with the
source scalar field on a whole extended point, presented as a bijection.
Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
noncomputable def directPointToPauliEquiv (P : AdmissibleParams) :
    (Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd) ≃
      (Fin (2 * P.m + 2) → PauliScalar P) where
  toFun := directPointToPauli P
  invFun v := fun i => (extendedDirectScalarEquiv P).symm (v i)
  left_inv v := by
    funext i
    simp [directPointToPauli]
  right_inv v := by
    funext i
    simp [directPointToPauli]

/-- The `X` block of a transported extended point is the transport of its `X`
block.  Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem projX_directPointToPauli_eq (P : AdmissibleParams)
    (u : Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd) :
    projX (directPointToPauli P u) = directBlockToPauliEquiv P (projX u) := rfl

/-- The `Z` block of a transported extended point is the transport of its `Z`
block.  Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem projZ_directPointToPauli_eq (P : AdmissibleParams)
    (u : Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd) :
    projZ (directPointToPauli P u) = directBlockToPauliEquiv P (projZ u) := rfl

/-! ## Transport of the uniform laws -/

/-- A uniformly random extended point transported to the source scalar field
is uniformly random.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem uniformDistribution_map_directPointToPauli (P : AdmissibleParams) :
    (uniformDistribution
          (Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd)).map
        (directPointToPauli P) =
      uniformDistribution (Fin (2 * P.m + 2) → PauliScalar P) :=
  uniformDistribution_map_equiv (directPointToPauliEquiv P)

/-- A uniformly random source block transported to the source scalar field is
uniformly random.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem uniformDistribution_map_directBlockToPauli (P : AdmissibleParams) :
    (uniformDistribution (Fin P.m → DirectScalarQ P.extendedDirectLd)).map
        (fun v => directBlockToPauliEquiv P v) =
      uniformDistribution (Fin P.m → PauliScalar P) :=
  uniformDistribution_map_equiv (directBlockToPauliEquiv P)

/-- The two source blocks of a uniformly random extended point, read in the
source scalar field, are independent and uniformly random.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem uniformDistribution_map_projX_projZ_pauli (P : AdmissibleParams) :
    (uniformDistribution
          (Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd)).map
        (fun u => (projX (directPointToPauli P u),
          projZ (directPointToPauli P u))) =
      Distribution.prod (uniformDistribution (Fin P.m → PauliScalar P))
        (uniformDistribution (Fin P.m → PauliScalar P)) := by
  classical
  have hfun :
      (fun u : Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd =>
          (projX (directPointToPauli P u), projZ (directPointToPauli P u))) =
        fun u => (Equiv.prodCongr (directBlockToPauliEquiv P)
          (directBlockToPauliEquiv P)) (projX u, projZ u) := rfl
  rw [hfun, ← Distribution.map_map _ (fun u => (projX u, projZ u)),
    uniformDistribution_map_projX_projZ, ← uniformDistribution_prod,
    uniformDistribution_map_equiv, uniformDistribution_prod]

/-! ## Resampling a uniform point along a line -/

/-- Reading a function at the point of a uniformly random affine parameter on
the line through the canonical representative, in a fixed direction, of a
uniformly random point is the same as reading that function at a uniformly
random point.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem uniformDistribution_map_lineRepMap_add_smul_comp {K : Type*} [Field K]
    [Fintype K] [DecidableEq K] {m : ℕ} {γ : Type*} [DecidableEq γ]
    (v : Fin m → K) (g : (Fin m → K) → γ) :
    (Distribution.prod (uniformDistribution (Fin m → K))
          (uniformDistribution K)).map
        (fun w => g (lineRepMap v w.1 + w.2 • v)) =
      (uniformDistribution (Fin m → K)).map g := by
  classical
  rw [← uniformDistribution_prod,
    ← Distribution.map_map _ (fun w : (Fin m → K) × K =>
      lineRepMap v w.1 + w.2 • v) g,
    uniformDistribution_map_lineRepMap_add_smul]

end

end MIPStarRE.QPBT
