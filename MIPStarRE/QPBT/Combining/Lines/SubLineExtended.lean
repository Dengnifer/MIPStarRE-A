import MIPStarRE.QPBT.Combining.Lines.SubLineBlocks
import MIPStarRE.QPBT.Combining.Witnesses

/-!
# Coordinate blocks of an extended point and of an extended direct sample

This module records the block decomposition used by the sampling procedure of
the sub-line lemma on the extended dimension.  A point of the extended space
is the tuple consisting of its two source point blocks and its two scalar
coordinates, and this decomposition is a bijection carrying the uniform law to
the uniform law; in particular the two source blocks of a uniform extended
point are independent and uniform.  The decomposition is linear, so it
commutes with the affine parameterization of a line, and it commutes with the
canonical identification of the extended scalar field with the source scalar
field.  The stored coordinate index of an extended direct sample splits along
the same three coordinate ranges.

## References

The decompositions support `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The coordinate blocks are those of `def:combine-map`, blueprint lines
445--480, paper lines 970--989.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-! ## Linearity of the coordinate blocks -/

/-- The `X` block of a sum of extended points is the sum of the blocks.
Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem projX_add {K : Type*} [AddCommMonoid K] {m : ℕ}
    (u v : Fin (2 * m + 2) → K) :
    projX (u + v) = projX u + projX v := rfl

/-- The `Z` block of a sum of extended points is the sum of the blocks.
Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem projZ_add {K : Type*} [AddCommMonoid K] {m : ℕ}
    (u v : Fin (2 * m + 2) → K) :
    projZ (u + v) = projZ u + projZ v := rfl

/-- The `X` block of a scalar multiple of an extended point is the scalar
multiple of the block.  Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem projX_smul {K : Type*} [Monoid K] {m : ℕ} (t : K)
    (u : Fin (2 * m + 2) → K) :
    projX (t • u) = t • projX u := rfl

/-- The `Z` block of a scalar multiple of an extended point is the scalar
multiple of the block.  Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem projZ_smul {K : Type*} [Monoid K] {m : ℕ} (t : K)
    (u : Fin (2 * m + 2) → K) :
    projZ (t • u) = t • projZ u := rfl

/-! ## The coordinate blocks of an extended point -/

/-- Split an extended point into its two source point blocks and its two
scalar coordinates.  Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
def extendedPointBlockEquiv (P : AdmissibleParams) :
    (Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd) ≃
      ((Fin P.m → DirectScalarQ P.extendedDirectLd) ×
          (Fin P.m → DirectScalarQ P.extendedDirectLd)) ×
        (Fin 2 → DirectScalarQ P.extendedDirectLd) :=
  (Equiv.arrowCongr (finCombineEquiv P.m)
      (Equiv.refl (DirectScalarQ P.extendedDirectLd))).trans
    ((Equiv.sumArrowEquivProdArrow _ _ _).trans
      (Equiv.prodCongr (Equiv.sumArrowEquivProdArrow _ _ _) (Equiv.refl _)))

/-- The first block of the decomposition is the `X` block. -/
theorem extendedPointBlockEquiv_projX (P : AdmissibleParams)
    (u : Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd) :
    (extendedPointBlockEquiv P u).1.1 = projX u := by
  funext i
  rfl

/-- The second block of the decomposition is the `Z` block. -/
theorem extendedPointBlockEquiv_projZ (P : AdmissibleParams)
    (u : Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd) :
    (extendedPointBlockEquiv P u).1.2 = projZ u := by
  funext i
  rfl

/-- The first scalar coordinate of the decomposition is `alpha`. -/
theorem extendedPointBlockEquiv_alpha (P : AdmissibleParams)
    (u : Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd) :
    (extendedPointBlockEquiv P u).2 0 = u (alphaVar P.m) := rfl

/-- The second scalar coordinate of the decomposition is `beta`. -/
theorem extendedPointBlockEquiv_beta (P : AdmissibleParams)
    (u : Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd) :
    (extendedPointBlockEquiv P u).2 1 = u (betaVar P.m) := rfl

/-- The block decomposition of an extended point carries the uniform law to
the uniform law.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem uniformDistribution_map_extendedPointBlockEquiv (P : AdmissibleParams) :
    (uniformDistribution
          (Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd)).map
        (extendedPointBlockEquiv P) =
      uniformDistribution
        (((Fin P.m → DirectScalarQ P.extendedDirectLd) ×
            (Fin P.m → DirectScalarQ P.extendedDirectLd)) ×
          (Fin 2 → DirectScalarQ P.extendedDirectLd)) :=
  uniformDistribution_map_equiv _

/-- The two source blocks of a uniformly sampled extended point are
independent and uniform.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem uniformDistribution_map_projX_projZ (P : AdmissibleParams) :
    (uniformDistribution
          (Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd)).map
        (fun u => (projX u, projZ u)) =
      Distribution.prod
        (uniformDistribution (Fin P.m → DirectScalarQ P.extendedDirectLd))
        (uniformDistribution (Fin P.m → DirectScalarQ P.extendedDirectLd)) := by
  have hfun :
      (fun u : Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd =>
          (projX u, projZ u)) =
        fun u => (extendedPointBlockEquiv P u).1 := by
    funext u
    rw [Prod.ext_iff]
    exact ⟨(extendedPointBlockEquiv_projX P u).symm,
      (extendedPointBlockEquiv_projZ P u).symm⟩
  rw [hfun, ← Distribution.map_map _ (extendedPointBlockEquiv P) Prod.fst,
    uniformDistribution_map_extendedPointBlockEquiv,
    uniformDistribution_map_fst, uniformDistribution_prod]

/-! ## Transport to the source scalar field -/

/-- The `X` block of an extended point transported to the source scalar field
is the transport of its `X` block.  Blueprint
`def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem projX_directPointToPauli (P : AdmissibleParams)
    (u : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) :
    projX (directPointToPauli P u) =
      fun i => extendedDirectScalarEquiv P (projX u i) := rfl

/-- The `Z` block of an extended point transported to the source scalar field
is the transport of its `Z` block.  Blueprint
`def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem projZ_directPointToPauli (P : AdmissibleParams)
    (u : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) :
    projZ (directPointToPauli P u) =
      fun i => extendedDirectScalarEquiv P (projZ u i) := rfl

/-! ## The blocks of an extended direct sample -/

/-- The stored index, point block and direction block of a uniformly sampled
direct low-degree vector are independent and uniform.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem uniformDistribution_map_directLdSpaceIndexEquiv (D : DirectLdParams) :
    (uniformDistribution (DirectLdSpace D)).map (directLdSpaceIndexEquiv D) =
      uniformDistribution
        (Fin D.m ×
          ((Fin D.m → DirectScalarQ D) × (Fin D.m → DirectScalarQ D))) :=
  uniformDistribution_map_equiv _

/-! ## Compatibility data read off the coordinate blocks -/

/-- An extended line is compatible with two source lines as soon as each of
its two point blocks is an affine reparameterization of the corresponding
source line: the base block is a point of the source line and the direction
block is a multiple of the source direction.  The two scalar coordinates of
the compatibility data are the `alpha` and `beta` coordinates of the extended
base and direction.  This supplies the domain condition preceding Equation
`eq:combine-lines` in blueprint
`def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem isCombineLineCompatible_of_blocks {K : Type*} [Field K] {m : ℕ}
    (u v : Fin (2 * m + 2) → K) (uX vX uZ vZ : Fin m → K) (aX bX aZ bZ : K)
    (hX : projX u = uX + aX • vX) (hXv : projX v = bX • vX)
    (hZ : projZ u = uZ + aZ • vZ) (hZv : projZ v = bZ • vZ) :
    IsCombineLineCompatible u v uX vX uZ vZ aX bX aZ bZ
      (u (alphaVar m)) (v (alphaVar m)) (u (betaVar m)) (v (betaVar m)) := by
  refine ⟨rfl, rfl, rfl, rfl, fun t => ⟨?_, ?_⟩⟩
  · rw [projX_add, projX_smul, hX, hXv]
    module
  · rw [projZ_add, projZ_smul, hZ, hZv]
    module

/-- An extended line whose two source lines carry the inherited direction
blocks is compatible with them, with both affine reparameterizations the
identity.  Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem isCombineLineCompatible_inherited {K : Type*} [Field K] {m : ℕ}
    (u v : Fin (2 * m + 2) → K) :
    IsCombineLineCompatible u v (projX u) (projX v) (projZ u) (projZ v)
      0 1 0 1 (u (alphaVar m)) (v (alphaVar m)) (u (betaVar m))
      (v (betaVar m)) :=
  isCombineLineCompatible_of_blocks u v _ _ _ _ 0 1 0 1
    (by module) (by module) (by module) (by module)

end

end MIPStarRE.QPBT
