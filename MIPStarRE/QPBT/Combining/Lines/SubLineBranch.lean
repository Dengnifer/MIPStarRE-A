import MIPStarRE.QPBT.Combining.Lines.SubLineTransport

/-!
# The branch data of the sub-line sampling procedure

The sampling procedure of the sub-line lemma draws a line kind, a stored
extended coordinate, and an unrestricted extended direction, and forms from
them the direction of the extended line: the elementary direction at the
stored coordinate in the axis branch, and the extended direction with the
coordinates preceding the stored coordinate replaced by zero in the diagonal
branch.  The two source lines are then read off the two coordinate blocks.
This module fixes the coordinate index that each source line must carry: the
stored coordinate itself when it belongs to that block, the first coordinate
otherwise.  With that choice the source block of the extended direction always
lies in the line spanned by the corresponding source direction, which is the
incidence hypothesis of the two projection lemmas.  The module also records
that moving an extended point to its canonical representative does not change
the canonical representative of either of its source blocks.

## References

The statements support `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The coordinate blocks are those of blueprint `def:combine-map`, paper lines 970--989;
the prefix truncation is that of
blueprint `def:ld-question-distribution`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-! ## The three ranges of extended coordinates -/

/-- Every extended coordinate is an `X`-block coordinate, a `Z`-block
coordinate, or one of the two scalar coordinates.  Blueprint
`def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem extendedCoordinate_cases (m : ℕ) (k : Fin (2 * m + 2)) :
    (∃ i : Fin m, k = embX m i) ∨ (∃ j : Fin m, k = embZ m j) ∨
      k = alphaVar m ∨ k = betaVar m := by
  rcases lt_or_ge k.val m with hk | hk
  · exact Or.inl ⟨⟨k.val, hk⟩, Fin.ext (embX_val m ⟨k.val, hk⟩).symm⟩
  · rcases lt_or_ge k.val (2 * m) with hk2 | hk2
    · refine Or.inr (Or.inl ⟨⟨k.val - m, by omega⟩, Fin.ext ?_⟩)
      rw [embZ_val]
      change k.val = m + (k.val - m)
      omega
    · have hk3 : k.val < 2 * m + 2 := k.isLt
      rcases Nat.lt_or_ge k.val (2 * m + 1) with hk4 | hk4
      · refine Or.inr (Or.inr (Or.inl (Fin.ext ?_)))
        rw [alphaVar_val]
        omega
      · refine Or.inr (Or.inr (Or.inr (Fin.ext ?_)))
        rw [betaVar_val]
        omega

/-! ## Linearity of the identification of the two scalar fields -/

/-- The identification of the two scalar fields is additive on extended
points.  Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem directPointToPauli_add (P : AdmissibleParams)
    (u v : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) :
    directPointToPauli P (u + v) =
      directPointToPauli P u + directPointToPauli P v := by
  funext i
  simp [directPointToPauli]

/-- The identification of the two scalar fields carries a scalar multiple of
an extended point to the multiple by the identified scalar.  Blueprint
`def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem directPointToPauli_smul (P : AdmissibleParams)
    (t : DirectScalarQ P.extendedDirectLd)
    (u : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) :
    directPointToPauli P (t • u) =
      extendedDirectScalarEquiv P t • directPointToPauli P u := by
  funext i
  simp [directPointToPauli]

/-! ## The coordinate index carried by each source line -/

/-- The first coordinate of the source space.  Blueprint
`eq:chi-func`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:958-961`.
-/
def subLineFirstIndex (P : AdmissibleParams) : Fin P.m :=
  ⟨0, lt_of_lt_of_le Nat.zero_lt_one P.one_le_m⟩

/-- The coordinate index carried by the source `X` line of a branch: the
stored extended coordinate when it is an `X`-block coordinate, and the first
coordinate otherwise.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
def subLineXIndex (P : AdmissibleParams) (k : Fin (2 * P.m + 2)) : Fin P.m :=
  if h : k.val < P.m then ⟨k.val, h⟩ else subLineFirstIndex P

/-- The coordinate index carried by the source `Z` line of a branch: the
stored extended coordinate when it is a `Z`-block coordinate, and the first
coordinate otherwise.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
def subLineZIndex (P : AdmissibleParams) (k : Fin (2 * P.m + 2)) : Fin P.m :=
  if h : P.m ≤ k.val ∧ k.val < 2 * P.m then ⟨k.val - P.m, by omega⟩
  else subLineFirstIndex P

/-- At an `X`-block coordinate the source `X` line carries that coordinate. -/
theorem subLineXIndex_embX (P : AdmissibleParams) (i : Fin P.m) :
    subLineXIndex P (embX P.m i) = i := by
  have h : (embX P.m i).val < P.m := by
    rw [embX_val]
    exact i.isLt
  rw [subLineXIndex, dif_pos h]
  exact Fin.ext (embX_val P.m i)

/-- At a `Z`-block coordinate the source `X` line carries the first
coordinate. -/
theorem subLineXIndex_embZ (P : AdmissibleParams) (j : Fin P.m) :
    subLineXIndex P (embZ P.m j) = subLineFirstIndex P := by
  have h : ¬ (embZ P.m j).val < P.m := by
    rw [embZ_val]
    omega
  rw [subLineXIndex, dif_neg h]

/-- At the first scalar coordinate the source `X` line carries the first
coordinate. -/
theorem subLineXIndex_alphaVar (P : AdmissibleParams) :
    subLineXIndex P (alphaVar P.m) = subLineFirstIndex P := by
  have h : ¬ (alphaVar P.m).val < P.m := by
    rw [alphaVar_val]
    omega
  rw [subLineXIndex, dif_neg h]

/-- At the second scalar coordinate the source `X` line carries the first
coordinate. -/
theorem subLineXIndex_betaVar (P : AdmissibleParams) :
    subLineXIndex P (betaVar P.m) = subLineFirstIndex P := by
  have h : ¬ (betaVar P.m).val < P.m := by
    rw [betaVar_val]
    omega
  rw [subLineXIndex, dif_neg h]

/-- At an `X`-block coordinate the source `Z` line carries the first
coordinate. -/
theorem subLineZIndex_embX (P : AdmissibleParams) (i : Fin P.m) :
    subLineZIndex P (embX P.m i) = subLineFirstIndex P := by
  have h : ¬ (P.m ≤ (embX P.m i).val ∧ (embX P.m i).val < 2 * P.m) := by
    rw [embX_val]
    have := i.isLt
    omega
  rw [subLineZIndex, dif_neg h]

/-- At a `Z`-block coordinate the source `Z` line carries that coordinate. -/
theorem subLineZIndex_embZ (P : AdmissibleParams) (j : Fin P.m) :
    subLineZIndex P (embZ P.m j) = j := by
  have hj := j.isLt
  have h : P.m ≤ (embZ P.m j).val ∧ (embZ P.m j).val < 2 * P.m := by
    rw [embZ_val]
    omega
  rw [subLineZIndex, dif_pos h]
  refine Fin.ext ?_
  change (embZ P.m j).val - P.m = j.val
  rw [embZ_val]
  omega

/-- At the first scalar coordinate the source `Z` line carries the first
coordinate. -/
theorem subLineZIndex_alphaVar (P : AdmissibleParams) :
    subLineZIndex P (alphaVar P.m) = subLineFirstIndex P := by
  have h : ¬ (P.m ≤ (alphaVar P.m).val ∧ (alphaVar P.m).val < 2 * P.m) := by
    rw [alphaVar_val]
    omega
  rw [subLineZIndex, dif_neg h]

/-- At the second scalar coordinate the source `Z` line carries the first
coordinate. -/
theorem subLineZIndex_betaVar (P : AdmissibleParams) :
    subLineZIndex P (betaVar P.m) = subLineFirstIndex P := by
  have h : ¬ (P.m ≤ (betaVar P.m).val ∧ (betaVar P.m).val < 2 * P.m) := by
    rw [betaVar_val]
    omega
  rw [subLineZIndex, dif_neg h]

/-! ## The two directions of a branch -/

/-- The direction of the extended line of a branch: the elementary direction
at the stored coordinate in the axis branch, and the extended direction with
the coordinates preceding the stored coordinate replaced by zero in the
diagonal branch.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
def subLineExtDirection (P : AdmissibleParams) (kind : LineKind)
    (k : Fin (2 * P.m + 2))
    (w : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) :
    Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd :=
  match kind with
  | .axis => coordinateDirection k
  | .diagonal => directPrefixProjection (D := P.extendedDirectLd) k w

/-- The direction of a source line of a branch: the elementary direction at
its coordinate index in the axis branch, and the given source block with the
coordinates preceding that index replaced by zero in the diagonal branch.
Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
def subLineSourceDirection (P : AdmissibleParams) (kind : LineKind)
    (i : Fin P.m) (v : Fin P.m → PauliScalar P) : Fin P.m → PauliScalar P :=
  match kind with
  | .axis => coordinateDirection i
  | .diagonal => prefixProjection (P := P.toLdParams) i v

/-! ## Incidence of the two source blocks of a branch direction -/

/-- The `X` block of the direction of the extended line of a branch lies in
the line spanned by the direction of its source `X` line.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem projX_subLineExtDirection_mem_span (P : AdmissibleParams)
    (kind : LineKind) (k : Fin (2 * P.m + 2))
    (w : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) :
    projX (directPointToPauli P (subLineExtDirection P kind k w)) ∈
      Submodule.span (PauliScalar P)
        ({subLineSourceDirection P kind (subLineXIndex P k)
          (projX (directPointToPauli P w))} :
          Set (Fin P.m → PauliScalar P)) := by
  rcases extendedCoordinate_cases P.m k with ⟨i, rfl⟩ | ⟨j, rfl⟩ | rfl | rfl <;>
    cases kind
  · have hval : projX (directPointToPauli P
        (coordinateDirection (embX P.m i))) =
        (coordinateDirection i : Fin P.m → PauliScalar P) := by
      rw [directPointToPauli_coordinateDirection]
      exact projX_coordinateDirection_embX i
    rw [subLineXIndex_embX]
    change projX (directPointToPauli P
      (coordinateDirection (embX P.m i))) ∈ _
    rw [hval]
    exact Submodule.mem_span_singleton_self _
  · rw [subLineXIndex_embX]
    change projX (directPointToPauli P
      (directPrefixProjection (D := P.extendedDirectLd) (embX P.m i) w)) ∈ _
    rw [projX_directPrefixProjection_embX]
    exact Submodule.mem_span_singleton_self _
  · have hval : projX (directPointToPauli P
        (coordinateDirection (embZ P.m j))) = 0 := by
      rw [directPointToPauli_coordinateDirection]
      exact projX_coordinateDirection_embZ j
    change projX (directPointToPauli P
      (coordinateDirection (embZ P.m j))) ∈ _
    rw [hval]
    exact Submodule.zero_mem _
  · change projX (directPointToPauli P
      (directPrefixProjection (D := P.extendedDirectLd) (embZ P.m j) w)) ∈ _
    rw [projX_directPrefixProjection_embZ]
    exact Submodule.zero_mem _
  · have hval : projX (directPointToPauli P
        (coordinateDirection (alphaVar P.m))) = 0 := by
      rw [directPointToPauli_coordinateDirection]
      exact projX_coordinateDirection_alphaVar
    change projX (directPointToPauli P
      (coordinateDirection (alphaVar P.m))) ∈ _
    rw [hval]
    exact Submodule.zero_mem _
  · change projX (directPointToPauli P
      (directPrefixProjection (D := P.extendedDirectLd) (alphaVar P.m) w)) ∈ _
    rw [projX_directPrefixProjection_alphaVar]
    exact Submodule.zero_mem _
  · have hval : projX (directPointToPauli P
        (coordinateDirection (betaVar P.m))) = 0 := by
      rw [directPointToPauli_coordinateDirection]
      exact projX_coordinateDirection_betaVar
    change projX (directPointToPauli P
      (coordinateDirection (betaVar P.m))) ∈ _
    rw [hval]
    exact Submodule.zero_mem _
  · change projX (directPointToPauli P
      (directPrefixProjection (D := P.extendedDirectLd) (betaVar P.m) w)) ∈ _
    rw [projX_directPrefixProjection_betaVar]
    exact Submodule.zero_mem _

/-- The `Z` block of the direction of the extended line of a branch lies in
the line spanned by the direction of its source `Z` line.  In the diagonal
branch at an `X`-block coordinate the `Z` block is untruncated, which is why
the source `Z` line carries the first coordinate there.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem projZ_subLineExtDirection_mem_span (P : AdmissibleParams)
    (kind : LineKind) (k : Fin (2 * P.m + 2))
    (w : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) :
    projZ (directPointToPauli P (subLineExtDirection P kind k w)) ∈
      Submodule.span (PauliScalar P)
        ({subLineSourceDirection P kind (subLineZIndex P k)
          (projZ (directPointToPauli P w))} :
          Set (Fin P.m → PauliScalar P)) := by
  rcases extendedCoordinate_cases P.m k with ⟨i, rfl⟩ | ⟨j, rfl⟩ | rfl | rfl <;>
    cases kind
  · have hval : projZ (directPointToPauli P
        (coordinateDirection (embX P.m i))) = 0 := by
      rw [directPointToPauli_coordinateDirection]
      exact projZ_coordinateDirection_embX i
    change projZ (directPointToPauli P
      (coordinateDirection (embX P.m i))) ∈ _
    rw [hval]
    exact Submodule.zero_mem _
  · rw [subLineZIndex_embX]
    change projZ (directPointToPauli P
      (directPrefixProjection (D := P.extendedDirectLd) (embX P.m i) w)) ∈ _
    rw [projZ_directPrefixProjection_embX]
    change _ ∈ Submodule.span (PauliScalar P)
      ({prefixProjection (P := P.toLdParams) (subLineFirstIndex P)
        (projZ (directPointToPauli P w))} : Set (Fin P.m → PauliScalar P))
    rw [prefixProjection_of_val_zero (L := P.toLdParams)
      (i := subLineFirstIndex P) rfl]
    exact Submodule.mem_span_singleton_self _
  · have hval : projZ (directPointToPauli P
        (coordinateDirection (embZ P.m j))) =
        (coordinateDirection j : Fin P.m → PauliScalar P) := by
      rw [directPointToPauli_coordinateDirection]
      exact projZ_coordinateDirection_embZ j
    rw [subLineZIndex_embZ]
    change projZ (directPointToPauli P
      (coordinateDirection (embZ P.m j))) ∈ _
    rw [hval]
    exact Submodule.mem_span_singleton_self _
  · rw [subLineZIndex_embZ]
    change projZ (directPointToPauli P
      (directPrefixProjection (D := P.extendedDirectLd) (embZ P.m j) w)) ∈ _
    rw [projZ_directPrefixProjection_embZ]
    exact Submodule.mem_span_singleton_self _
  · have hval : projZ (directPointToPauli P
        (coordinateDirection (alphaVar P.m))) = 0 := by
      rw [directPointToPauli_coordinateDirection]
      exact projZ_coordinateDirection_alphaVar
    change projZ (directPointToPauli P
      (coordinateDirection (alphaVar P.m))) ∈ _
    rw [hval]
    exact Submodule.zero_mem _
  · change projZ (directPointToPauli P
      (directPrefixProjection (D := P.extendedDirectLd) (alphaVar P.m) w)) ∈ _
    rw [projZ_directPrefixProjection_alphaVar]
    exact Submodule.zero_mem _
  · have hval : projZ (directPointToPauli P
        (coordinateDirection (betaVar P.m))) = 0 := by
      rw [directPointToPauli_coordinateDirection]
      exact projZ_coordinateDirection_betaVar
    change projZ (directPointToPauli P
      (coordinateDirection (betaVar P.m))) ∈ _
    rw [hval]
    exact Submodule.zero_mem _
  · change projZ (directPointToPauli P
      (directPrefixProjection (D := P.extendedDirectLd) (betaVar P.m) w)) ∈ _
    rw [projZ_directPrefixProjection_betaVar]
    exact Submodule.zero_mem _

/-! ## Canonical representatives of the two source blocks -/

/-- Replacing an extended point by its canonical representative in the
direction of the extended line does not change the canonical representative
of its `X` block in the direction of the source `X` line, as soon as the `X`
block of the extended direction lies in the line spanned by the source
direction.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem lineRepMap_projX_directPointToPauli_lineRepMap (P : AdmissibleParams)
    (v x : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd)
    (dX : Fin P.m → PauliScalar P)
    (hdir : projX (directPointToPauli P v) ∈
      Submodule.span (PauliScalar P) ({dX} : Set (Fin P.m → PauliScalar P))) :
    lineRepMap dX (projX (directPointToPauli P (lineRepMap v x))) =
      lineRepMap dX (projX (directPointToPauli P x)) := by
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (sub_lineRepMap_mem_span v x)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hdir
  have hx : x = lineRepMap v x + t • v := by
    rw [ht]
    abel
  have hstep : projX (directPointToPauli P x) =
      projX (directPointToPauli P (lineRepMap v x)) +
        (extendedDirectScalarEquiv P t * c) • dX := by
    conv_lhs => rw [hx]
    rw [directPointToPauli_add, directPointToPauli_smul, projX_add, projX_smul,
      ← hc]
    module
  rw [hstep, lineRepMap_add_smul]

/-- Replacing an extended point by its canonical representative in the
direction of the extended line does not change the canonical representative
of its `Z` block in the direction of the source `Z` line, as soon as the `Z`
block of the extended direction lies in the line spanned by the source
direction.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem lineRepMap_projZ_directPointToPauli_lineRepMap (P : AdmissibleParams)
    (v x : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd)
    (dZ : Fin P.m → PauliScalar P)
    (hdir : projZ (directPointToPauli P v) ∈
      Submodule.span (PauliScalar P) ({dZ} : Set (Fin P.m → PauliScalar P))) :
    lineRepMap dZ (projZ (directPointToPauli P (lineRepMap v x))) =
      lineRepMap dZ (projZ (directPointToPauli P x)) := by
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (sub_lineRepMap_mem_span v x)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hdir
  have hx : x = lineRepMap v x + t • v := by
    rw [ht]
    abel
  have hstep : projZ (directPointToPauli P x) =
      projZ (directPointToPauli P (lineRepMap v x)) +
        (extendedDirectScalarEquiv P t * c) • dZ := by
    conv_lhs => rw [hx]
    rw [directPointToPauli_add, directPointToPauli_smul, projZ_add, projZ_smul,
      ← hc]
    module
  rw [hstep, lineRepMap_add_smul]

end

end MIPStarRE.QPBT
