import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Combining.Strategy

/-!
# The questions measured by the combined strategy

`lem:ld-combined-question-law` identifies the pair of questions measured by the
combined strategy of `def:ld-combined-strategy` on a sample of the combined
game.  The coordinate index of the common sample is uniform on the `m + k`
coordinates of the combined dimension, and the identification splits according
to whether that index is a point coordinate or a combining coordinate.

On a point coordinate `j`, all three question types measure the canonical
question of the same type of the original game attached to the *projected*
sample `directCombinedSampleProjection`: the point part of the sampled point,
the index `j`, and the point part of the sampled direction.  This uses the
coordinate order of `def:ld-combining-map`: the point coordinates precede the
combining coordinates, so the coordinate direction of a point coordinate has
point part the corresponding coordinate direction, and the prefix projection at
a point coordinate restricts to the prefix projection at that coordinate of the
point part.

On a combining coordinate, every direction produced by the question
distribution has vanishing point part, so all three question types measure the
point question at the point part of the sampled point.

The projected sample is read from the *canonical* base of the combined line,
which need not project to the canonical base of the image line; the two agree
after rebasing along the image direction, which is
`lineRepMap_directCombinedPointPart_lineRepMap`.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1409-1503`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:473-508`
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries

noncomputable section

/-! ## Coordinates of the combined dimension -/

@[simp] theorem combinedPointVar_val (m k : ℕ) (j : Fin m) :
    (combinedPointVar m k j).val = j.val := by
  simp [combinedPointVar]

@[simp] theorem combinedCoefficientVar_val (m k : ℕ) (r : Fin k) :
    (combinedCoefficientVar m k r).val = m + r.val := by
  simp [combinedCoefficientVar]

/-- Prefix restriction is idempotent.  Public copy of the private
`directPrefixProjection_idem` of
`MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/SeedFiberValue.lean`; see
issue #204 on private originals. -/
theorem directPrefixProjection_idempotent (D : DirectLdParams) (i : Fin D.m)
    (v : Fin D.m → DirectScalarQ D) :
    directPrefixProjection i (directPrefixProjection i v) =
      directPrefixProjection i v := by
  funext j
  unfold directPrefixProjection
  split_ifs <;> rfl

/-- The coordinate direction of a point coordinate of the combined dimension
has point part the corresponding coordinate direction. -/
@[simp] theorem directCombinedPointPart_coordinateDirection_pointVar
    (D : DirectLdParams) (j : Fin D.m) :
    directCombinedPointPart D (coordinateDirection (combinedPointVar D.m D.k j)) =
      coordinateDirection j := by
  funext j'
  show (coordinateDirection (combinedPointVar D.m D.k j) :
      Fin (D.m + D.k) → DirectScalarQ D) (combinedPointVar D.m D.k j') =
    coordinateDirection j j'
  by_cases h : j' = j
  · subst h
    rw [coordinateDirection, coordinateDirection, Pi.single_eq_same,
      Pi.single_eq_same]
  · rw [coordinateDirection, coordinateDirection,
      Pi.single_eq_of_ne fun hc => h (combinedPointVar_injective D.m D.k hc),
      Pi.single_eq_of_ne h]

/-- The coordinate direction of a combining coordinate of the combined
dimension has vanishing point part. -/
@[simp] theorem directCombinedPointPart_coordinateDirection_coefficientVar
    (D : DirectLdParams) (r : Fin D.k) :
    directCombinedPointPart D
        (coordinateDirection (combinedCoefficientVar D.m D.k r)) = 0 := by
  funext j
  show (coordinateDirection (combinedCoefficientVar D.m D.k r) :
      Fin (D.m + D.k) → DirectScalarQ D) (combinedPointVar D.m D.k j) = 0
  rw [coordinateDirection,
    Pi.single_eq_of_ne (combinedCoefficientVar_ne_combinedPointVar D.m D.k r j).symm]

/-- Prefix projection at a point coordinate restricts to prefix projection at
that coordinate of the point part.  This is the coordinate order of
`def:ld-combining-map`: the point coordinates precede the combining ones. -/
@[simp] theorem directCombinedPointPart_directPrefixProjection_pointVar
    (D : DirectLdParams) (j : Fin D.m)
    (w : Fin D.combined.m → DirectScalarQ D) :
    directCombinedPointPart D
        (directPrefixProjection (combinedPointVar D.m D.k j) w) =
      directPrefixProjection j (directCombinedPointPart D w) := by
  funext j'
  show (if (combinedPointVar D.m D.k j').val < (combinedPointVar D.m D.k j).val
      then 0 else w (combinedPointVar D.m D.k j')) =
    if j'.val < j.val then 0 else directCombinedPointPart D w j'
  rw [combinedPointVar_val, combinedPointVar_val]
  rfl

/-- Prefix projection at a combining coordinate annihilates the point part:
every point coordinate precedes every combining coordinate. -/
@[simp] theorem directCombinedPointPart_directPrefixProjection_coefficientVar
    (D : DirectLdParams) (r : Fin D.k)
    (w : Fin D.combined.m → DirectScalarQ D) :
    directCombinedPointPart D
        (directPrefixProjection (combinedCoefficientVar D.m D.k r) w) = 0 := by
  funext j'
  show (if (combinedPointVar D.m D.k j').val <
      (combinedCoefficientVar D.m D.k r).val
      then 0 else w (combinedPointVar D.m D.k j')) = 0
  rw [combinedPointVar_val, combinedCoefficientVar_val, if_pos]
  omega

/-! ## Canonical bases -/

private theorem directCombinedPointPart_sub_smul (D : DirectLdParams)
    (z V : Fin D.combined.m → DirectScalarQ D) (c : DirectScalarQ D) :
    directCombinedPointPart D (z - c • V) =
      directCombinedPointPart D z - c • directCombinedPointPart D V :=
  rfl

/-- A line of the combined space whose direction has vanishing point part lies
in a fiber of the projection to the point coordinates, so its canonical base
projects to the point part of every one of its points. -/
theorem directCombinedPointPart_lineRepMap_of_pointPart_eq_zero
    (D : DirectLdParams) (V z : Fin D.combined.m → DirectScalarQ D)
    (hV : directCombinedPointPart D V = 0) :
    directCombinedPointPart D (lineRepMap V z) = directCombinedPointPart D z := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (sub_lineRepMap_mem_span V z)
  have hz : lineRepMap V z = z - c • V := by rw [hc]; abel
  rw [hz, directCombinedPointPart_sub_smul, hV, smul_zero, sub_zero]

/-- The canonical base of a line of the combined space projects to a point of
the image line, so rebasing its projection along the image direction returns
the canonical base of the image line.  The canonical base of a line of the
combined space need not itself project to the canonical base of its image; this
is why the answer relabellings of `def:ld-combined-strategy` carry the affine
shift `directCombinedRebaseParameter`. -/
theorem lineRepMap_directCombinedPointPart_lineRepMap (D : DirectLdParams)
    (V z : Fin D.combined.m → DirectScalarQ D) :
    lineRepMap (directCombinedPointPart D V)
        (directCombinedPointPart D (lineRepMap V z)) =
      lineRepMap (directCombinedPointPart D V) (directCombinedPointPart D z) := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (sub_lineRepMap_mem_span V z)
  have hz : lineRepMap V z = z - c • V := by rw [hc]; abel
  rw [hz, directCombinedPointPart_sub_smul, sub_eq_add_neg, ← neg_smul]
  exact lineRepMap_add_smul _ _ (-c)

/-! ## The measured questions -/

/-- The sample of the original game to which a sample of the combined game
projects at a point coordinate index: the point part of the sampled point, the
index, and the point part of the sampled direction. -/
def directCombinedSampleProjection (D : DirectLdParams) (j : Fin D.m)
    (sample : DirectLdSpace D.combined) : DirectLdSpace D :=
  ⟨directCombinedPointPart D sample.point, j,
    directCombinedPointPart D sample.direction⟩

/-- First half of `lem:ld-combined-question-law`: on a sample whose coordinate
index is the point coordinate `j`, the combined strategy measures, for every
question type, the canonical question of that type of the original game
attached to the projected sample. -/
theorem directCombined_measuredQuestion_of_pointVar (D : DirectLdParams)
    (t : LdType) (j : Fin D.m) (sample : DirectLdSpace D.combined)
    (hindex : sample.index = combinedPointVar D.m D.k j) :
    directCombinedMeasuredQuestion D (t, directLdMap D.combined t sample) =
      (t, directLdMap D t (directCombinedSampleProjection D j sample)) := by
  cases t with
  | point => rfl
  | aline =>
      have hbase := lineRepMap_directCombinedPointPart_lineRepMap D
        (coordinateDirection (combinedPointVar D.m D.k j)) sample.point
      rw [directCombinedPointPart_coordinateDirection_pointVar] at hbase
      simp only [directLdMap, directCombinedMeasuredQuestion, hindex,
        directCombinedIndexSplit_combinedPointVar,
        directCombinedSampleProjection]
      exact congrArg (fun x : Fin D.m → DirectScalarQ D =>
        ((LdType.aline, ⟨x, j, 0⟩) : DirectLdQuestion D)) hbase
  | dline =>
      have hbase := lineRepMap_directCombinedPointPart_lineRepMap D
        (directPrefixProjection (combinedPointVar D.m D.k j) sample.direction)
        sample.point
      rw [directCombinedPointPart_directPrefixProjection_pointVar] at hbase
      simp only [directLdMap, directCombinedMeasuredQuestion, hindex,
        directCombinedIndexSplit_combinedPointVar,
        directCombinedSampleProjection,
        directCombinedPointPart_directPrefixProjection_pointVar,
        directPrefixProjection_idempotent]
      exact congrArg (fun x : Fin D.m → DirectScalarQ D =>
        ((LdType.dline, ⟨x, j,
          directPrefixProjection j
            (directCombinedPointPart D sample.direction)⟩) :
          DirectLdQuestion D)) hbase

/-- Second half of `lem:ld-combined-question-law`: on a sample whose coordinate
index is a combining coordinate, every direction produced by the question
distribution has vanishing point part, so the combined strategy measures, for
every question type, the point question at the point part of the sampled
point. -/
theorem directCombined_measuredQuestion_of_coefficientVar (D : DirectLdParams)
    (t : LdType) (r : Fin D.k) (sample : DirectLdSpace D.combined)
    (hindex : sample.index = combinedCoefficientVar D.m D.k r) :
    directCombinedMeasuredQuestion D (t, directLdMap D.combined t sample) =
      directLdPointQuestionOf D (directCombinedPointPart D sample.point) := by
  cases t with
  | point => rfl
  | aline =>
      have hbase := directCombinedPointPart_lineRepMap_of_pointPart_eq_zero D
        (coordinateDirection (combinedCoefficientVar D.m D.k r)) sample.point
        (directCombinedPointPart_coordinateDirection_coefficientVar D r)
      simp only [directLdMap, directCombinedMeasuredQuestion, hindex,
        directCombinedIndexSplit_combinedCoefficientVar]
      exact congrArg (fun x : Fin D.m → DirectScalarQ D =>
        directLdPointQuestionOf D x) hbase
  | dline =>
      have hbase := directCombinedPointPart_lineRepMap_of_pointPart_eq_zero D
        (directPrefixProjection (combinedCoefficientVar D.m D.k r) sample.direction)
        sample.point
        (directCombinedPointPart_directPrefixProjection_coefficientVar D r
          sample.direction)
      simp only [directLdMap, directCombinedMeasuredQuestion, hindex,
        directCombinedIndexSplit_combinedCoefficientVar]
      exact congrArg (fun x : Fin D.m → DirectScalarQ D =>
        directLdPointQuestionOf D x) hbase

/-! ## The law of the projected sample -/

/-- A point of the combined space is recovered from its two parts. -/
@[simp] theorem combinedPoint_combinedPointPart_combinedCoefficientPart
    {K : Type*} {m k : ℕ} (z : Fin (m + k) → K) :
    combinedPoint (combinedPointPart z) (combinedCoefficientPart z) = z := by
  funext i
  rw [combinedPoint]
  rcases hi : finSumFinEquiv.symm i with j | r
  · show combinedPointPart z j = z i
    rw [combinedPointPart, combinedPointVar, ← hi, Equiv.apply_symm_apply]
  · show combinedCoefficientPart z r = z i
    rw [combinedCoefficientPart, combinedCoefficientVar, ← hi,
      Equiv.apply_symm_apply]

/-- The decomposition of a sample of the combined game into its two point
parts, its two combining parts, and its coordinate index. -/
private def directCombinedSpaceEquiv (D : DirectLdParams) :
    DirectLdSpace D.combined ≃
      (((Fin D.m → DirectScalarQ D) × (Fin D.m → DirectScalarQ D)) ×
        (((Fin D.k → DirectScalarQ D) × (Fin D.k → DirectScalarQ D)) ×
          Fin D.combined.m)) where
  toFun sample :=
    ((directCombinedPointPart D sample.point,
        directCombinedPointPart D sample.direction),
      ((directCombinedCoefficientPart D sample.point,
        directCombinedCoefficientPart D sample.direction), sample.index))
  invFun x :=
    ⟨combinedPoint x.1.1 x.2.1.1, x.2.2, combinedPoint x.1.2 x.2.1.2⟩
  left_inv sample := by
    obtain ⟨point, index, direction⟩ := sample
    dsimp only
    congr 1 <;>
      first
        | rfl
        | exact combinedPoint_combinedPointPart_combinedCoefficientPart _
  right_inv x := by
    obtain ⟨⟨u, v⟩, ⟨α, w⟩, i⟩ := x
    dsimp only
    simp only [Prod.mk.injEq]
    exact ⟨⟨combinedPointPart_combinedPoint u α,
        combinedPointPart_combinedPoint v w⟩,
      ⟨combinedCoefficientPart_combinedPoint u α,
        combinedCoefficientPart_combinedPoint v w⟩, trivial⟩

/-- The distributional half of `lem:ld-combined-question-law`: the two point
parts of a uniform sample of the combined game are jointly uniform, hence
independent of the combining parts and of the coordinate index.  Together with
`directCombined_measuredQuestion_of_pointVar` this says that, conditioned on a
point coordinate index, the questions measured by the combined strategy are the
canonical questions of a uniform sample of the original game. -/
theorem directCombinedSample_pointParts_uniform (D : DirectLdParams) :
    (uniformDistribution (DirectLdSpace D.combined)).map
        (fun sample => (directCombinedPointPart D sample.point,
          directCombinedPointPart D sample.direction)) =
      uniformDistribution
        ((Fin D.m → DirectScalarQ D) × (Fin D.m → DirectScalarQ D)) :=
  uniformDistribution_map_fst_of_equiv (e := directCombinedSpaceEquiv D) _
    fun _ => rfl

/-- The coordinate index of a uniform sample of the combined game is uniform on
the `m + k` coordinates of the combined dimension; this is the index of
`lem:ld-combined-question-law`, whose two cases are the point coordinates and
the combining coordinates. -/
theorem directCombinedSample_index_uniform (D : DirectLdParams) :
    (uniformDistribution (DirectLdSpace D.combined)).map
        (fun sample => sample.index) =
      uniformDistribution (Fin D.combined.m) :=
  uniformDistribution_map_fst_of_equiv (e := directLdSpaceIndexEquiv D.combined)
    _ fun _ => rfl

/-- The decomposition of a sample of the combined game into its coordinate
index and its two point parts on the one side, and its two combining parts on
the other. -/
private def directCombinedSpaceIndexEquiv (D : DirectLdParams) :
    DirectLdSpace D.combined ≃
      ((Fin D.combined.m ×
          ((Fin D.m → DirectScalarQ D) × (Fin D.m → DirectScalarQ D))) ×
        ((Fin D.k → DirectScalarQ D) × (Fin D.k → DirectScalarQ D))) where
  toFun sample :=
    ((sample.index,
        (directCombinedPointPart D sample.point,
          directCombinedPointPart D sample.direction)),
      (directCombinedCoefficientPart D sample.point,
        directCombinedCoefficientPart D sample.direction))
  invFun x := ⟨combinedPoint x.1.2.1 x.2.1, x.1.1, combinedPoint x.1.2.2 x.2.2⟩
  left_inv sample := by
    obtain ⟨point, index, direction⟩ := sample
    dsimp only
    congr 1 <;>
      first
        | rfl
        | exact combinedPoint_combinedPointPart_combinedCoefficientPart _
  right_inv x := by
    obtain ⟨⟨i, u, v⟩, α, w⟩ := x
    dsimp only
    simp only [Prod.mk.injEq]
    exact ⟨⟨trivial, combinedPointPart_combinedPoint u α,
        combinedPointPart_combinedPoint v w⟩,
      combinedCoefficientPart_combinedPoint u α,
      combinedCoefficientPart_combinedPoint v w⟩

/-- The distributional half of `lem:ld-combined-question-law`: the coordinate
index of a uniform sample of the combined game and the two point parts of that
sample are jointly uniform on the product of the `m + k` coordinates with two
copies of `F_q^m`.  Conditioned on a point coordinate index, the point parts
are therefore uniform, so by
`directCombined_measuredQuestion_of_pointVar` the questions measured by the
combined strategy are the canonical questions of a uniform sample of the
original game at the same ordered type pair; conditioned on a combining
coordinate index, the point part of the sampled point is uniform, so by
`directCombined_measuredQuestion_of_coefficientVar` both measured questions are
the point question at a uniform point.  This single statement subsumes the two
marginal laws `directCombinedSample_pointParts_uniform` and
`directCombinedSample_index_uniform`, which it refines by recording that the
index and the point parts are independent. -/
theorem directCombinedSample_indexPointParts_uniform (D : DirectLdParams) :
    (uniformDistribution (DirectLdSpace D.combined)).map
        (fun sample => (sample.index,
          (directCombinedPointPart D sample.point,
            directCombinedPointPart D sample.direction))) =
      uniformDistribution
        (Fin D.combined.m ×
          ((Fin D.m → DirectScalarQ D) × (Fin D.m → DirectScalarQ D))) :=
  uniformDistribution_map_fst_of_equiv (e := directCombinedSpaceIndexEquiv D) _
    fun _ => rfl

end

end MIPStarRE.QPBT
