import MIPStarRE.QPBT.Combining.Lines.SubLineUniform

/-!
# Coordinate blocks of a truncated extended direction

This module computes the two source blocks of the direction of an extended
diagonal line.  That direction is obtained from an unrestricted extended
vector by zeroing the coordinates that precede the stored coordinate index,
so each source block is again a prefix truncation: when the stored index is
the `i`-th coordinate of a block, that block inherits the truncation at `i`,
every preceding block vanishes, and later blocks are retained untruncated.
The computation is recorded after transport to the source scalar field, since
the extended direction and the source line directions are presented over the
two identified scalar fields.

## References

The block computations support `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The truncation is the prefix restriction of blueprint
`def:ld-question-distribution`; the coordinate blocks are those of
blueprint `def:combine-map`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-! ## Truncation at the first coordinate -/

/-- Zeroing the coordinates preceding the first coordinate changes nothing.
Blueprint `def:ld-question-distribution`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/
theorem prefixProjection_of_val_zero {L : LdParams} {i : Fin L.m}
    (hi : i.val = 0) (v : Fin L.m → ScalarQ L) :
    prefixProjection i v = v := by
  funext j
  simp [prefixProjection, hi]

/-! ## The `X` block of a truncated extended direction -/

/-- The `X` block of an extended direction truncated at an `X`-block
coordinate is the `X` block truncated at that coordinate of the source space.
Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem projX_directPrefixProjection_embX (P : AdmissibleParams) (i : Fin P.m)
    (v : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) :
    projX (directPointToPauli P
        (directPrefixProjection (D := P.extendedDirectLd) (embX P.m i) v)) =
      prefixProjection (P := P.toLdParams) i (projX (directPointToPauli P v)) := by
  funext a
  change extendedDirectScalarEquiv P
      (if (embX P.m a).val < (embX P.m i).val then 0 else v (embX P.m a)) =
    if a.val < i.val then 0 else extendedDirectScalarEquiv P (v (embX P.m a))
  rw [embX_val, embX_val]
  by_cases h : a.val < i.val
  · rw [if_pos h, if_pos h, map_zero]
  · rw [if_neg h, if_neg h]

/-- The `X` block of an extended direction truncated at a `Z`-block
coordinate vanishes.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem projX_directPrefixProjection_embZ (P : AdmissibleParams) (i : Fin P.m)
    (v : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) :
    projX (directPointToPauli P
      (directPrefixProjection (D := P.extendedDirectLd) (embZ P.m i) v)) = 0 := by
  funext a
  have ha : a.val < P.m := a.isLt
  change extendedDirectScalarEquiv P
      (if (embX P.m a).val < (embZ P.m i).val then 0 else v (embX P.m a)) =
    (0 : PauliScalar P)
  rw [embX_val, embZ_val, if_pos (by omega), map_zero]

/-- The `X` block of an extended direction truncated at the first scalar
coordinate vanishes.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem projX_directPrefixProjection_alphaVar (P : AdmissibleParams)
    (v : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) :
    projX (directPointToPauli P
      (directPrefixProjection (D := P.extendedDirectLd) (alphaVar P.m) v)) = 0 := by
  funext a
  have ha : a.val < P.m := a.isLt
  change extendedDirectScalarEquiv P
      (if (embX P.m a).val < (alphaVar P.m).val then 0 else v (embX P.m a)) =
    (0 : PauliScalar P)
  rw [embX_val, alphaVar_val, if_pos (by omega), map_zero]

/-- The `X` block of an extended direction truncated at the second scalar
coordinate vanishes.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem projX_directPrefixProjection_betaVar (P : AdmissibleParams)
    (v : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) :
    projX (directPointToPauli P
      (directPrefixProjection (D := P.extendedDirectLd) (betaVar P.m) v)) = 0 := by
  funext a
  have ha : a.val < P.m := a.isLt
  change extendedDirectScalarEquiv P
      (if (embX P.m a).val < (betaVar P.m).val then 0 else v (embX P.m a)) =
    (0 : PauliScalar P)
  rw [embX_val, betaVar_val, if_pos (by omega), map_zero]

/-! ## The `Z` block of a truncated extended direction -/

/-- The `Z` block of an extended direction truncated at a `Z`-block
coordinate is the `Z` block truncated at that coordinate of the source space.
Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem projZ_directPrefixProjection_embZ (P : AdmissibleParams) (i : Fin P.m)
    (v : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) :
    projZ (directPointToPauli P
        (directPrefixProjection (D := P.extendedDirectLd) (embZ P.m i) v)) =
      prefixProjection (P := P.toLdParams) i (projZ (directPointToPauli P v)) := by
  funext a
  change extendedDirectScalarEquiv P
      (if (embZ P.m a).val < (embZ P.m i).val then 0 else v (embZ P.m a)) =
    if a.val < i.val then 0 else extendedDirectScalarEquiv P (v (embZ P.m a))
  rw [embZ_val, embZ_val]
  by_cases h : a.val < i.val
  · rw [if_pos (by omega), if_pos h, map_zero]
  · rw [if_neg (by omega), if_neg h]

/-- The `Z` block of an extended direction truncated at an `X`-block
coordinate is the untruncated `Z` block, since every `Z`-block coordinate
follows every `X`-block coordinate.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem projZ_directPrefixProjection_embX (P : AdmissibleParams) (i : Fin P.m)
    (v : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) :
    projZ (directPointToPauli P
        (directPrefixProjection (D := P.extendedDirectLd) (embX P.m i) v)) =
      projZ (directPointToPauli P v) := by
  funext a
  have hi : i.val < P.m := i.isLt
  change extendedDirectScalarEquiv P
      (if (embZ P.m a).val < (embX P.m i).val then 0 else v (embZ P.m a)) =
    extendedDirectScalarEquiv P (v (embZ P.m a))
  rw [embZ_val, embX_val, if_neg (by omega)]

/-- The `Z` block of an extended direction truncated at the first scalar
coordinate vanishes.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem projZ_directPrefixProjection_alphaVar (P : AdmissibleParams)
    (v : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) :
    projZ (directPointToPauli P
      (directPrefixProjection (D := P.extendedDirectLd) (alphaVar P.m) v)) = 0 := by
  funext a
  have ha : a.val < P.m := a.isLt
  change extendedDirectScalarEquiv P
      (if (embZ P.m a).val < (alphaVar P.m).val then 0 else v (embZ P.m a)) =
    (0 : PauliScalar P)
  rw [embZ_val, alphaVar_val, if_pos (by omega), map_zero]

/-- The `Z` block of an extended direction truncated at the second scalar
coordinate vanishes.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem projZ_directPrefixProjection_betaVar (P : AdmissibleParams)
    (v : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) :
    projZ (directPointToPauli P
      (directPrefixProjection (D := P.extendedDirectLd) (betaVar P.m) v)) = 0 := by
  funext a
  have ha : a.val < P.m := a.isLt
  change extendedDirectScalarEquiv P
      (if (embZ P.m a).val < (betaVar P.m).val then 0 else v (embZ P.m a)) =
    (0 : PauliScalar P)
  rw [embZ_val, betaVar_val, if_pos (by omega), map_zero]

end

end MIPStarRE.QPBT
