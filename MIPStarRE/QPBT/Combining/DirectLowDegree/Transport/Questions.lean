import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Correspondence

/-!
# Question and answer transport for the directly indexed low-degree game

This module reads low individual degree test questions as canonical direct
questions and rebases direct answers to the LDT line parametrization.

Points and lines are decoded with the coordinate order reversed
(`directPointEquiv`), so that the suffix-zero direction restriction of the
LDT diagonal test becomes the prefix-zero restriction of the direct game.
An LDT diagonal line reveals no coordinate index, whereas a direct diagonal
question carries one.  The transported question uses the *leading index* of
the decoded direction, the least coordinate at which the direction is
nonzero.  Under the direct sampler, this is the index attached to the sampled
direction exactly when the direction is nonzero at the sampled index
(`directDiagonalIndexOf_prefixProjection`), an event of conditional
probability `1 - 1/q`; on the LDT side, the leading index of a decoded
`j`-restricted direction is `Fin.rev j` exactly when its pivot coordinate is
nonzero (`directDiagonalIndexOf_extendRestrictedDirection`).  Diagonal answers
on zero-direction lines are read as the constant polynomial carrying their
value at the base point, following `rem:ld-win-zero-direction`.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:230-272`
- `references/ldt-paper/test_definition.tex:49-65`
- `blueprint/src/chapter/ch13_qpbt_test.tex:120-121`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.Quantum

noncomputable section

/-! ## Canonical line rebasing of LDT lines -/

/-- A chosen affine parameter expressing a point relative to its canonical
line representative. -/
noncomputable def directLineRepParameter
    {K : Type*} [Field K] {m : ℕ} (v u : Fin m → K) : K :=
  Classical.choose (mem_linePoints_lineRepMap v u)

/-- The chosen canonical rebase parameter reconstructs the original point. -/
theorem directLineRepParameter_spec
    {K : Type*} [Field K] {m : ℕ} (v u : Fin m → K) :
    u = lineRepMap v u + directLineRepParameter v u • v :=
  Classical.choose_spec (mem_linePoints_lineRepMap v u)

/-- Canonical line representatives are unchanged by translation along their
direction. -/
theorem lineRepMap_add_smul
    {K : Type*} [Field K] {m : ℕ}
    (v u : Fin m → K) (t : K) :
    lineRepMap v (u + t • v) = lineRepMap v u := by
  let W : Submodule K (Fin m → K) := Submodule.span K ({v} : Set (Fin m → K))
  have hv : v ∈ W := Submodule.subset_span (Set.mem_singleton v)
  have hzero : lineRepMap v v = 0 := by
    simp [lineRepMap, canonicalProjOfKernel, W, LinearMap.comp_apply,
      Submodule.projectionOnto_apply_of_mem_right
        (isCompl_registerSubmodule_canonicalComplement W).symm hv]
  simp [map_add, map_smul, hzero]

/-- For a nonzero direction, the canonical rebase parameter is unique. -/
theorem directLineRepParameter_eq_of_nonzero
    {K : Type*} [Field K] {m : ℕ}
    {v u : Fin m → K} (hv : v ≠ 0) {t : K}
    (ht : u = lineRepMap v u + t • v) :
    directLineRepParameter v u = t := by
  have hfun : directLineRepParameter v u • v = t • v := by
    apply add_left_cancel (a := lineRepMap v u)
    exact (directLineRepParameter_spec v u).symm.trans ht
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    apply hv
    funext i
    simpa using not_exists.mp h i
  have hcoord := congrFun hfun i
  simp only [Pi.smul_apply, smul_eq_mul] at hcoord
  exact mul_right_cancel₀ hi hcoord

/-- Translating a point on a nonzero line adds the translation to its
canonical rebase parameter. -/
theorem directLineRepParameter_add_smul
    {K : Type*} [Field K] {m : ℕ}
    {v u : Fin m → K} (hv : v ≠ 0) (t : K) :
    directLineRepParameter v (u + t • v) =
      directLineRepParameter v u + t := by
  apply directLineRepParameter_eq_of_nonzero hv
  rw [lineRepMap_add_smul]
  calc
    u + t • v =
        (lineRepMap v u + directLineRepParameter v u • v) + t • v := by
      rw [← directLineRepParameter_spec v u]
    _ = lineRepMap v u + (directLineRepParameter v u + t) • v := by
      module

/-! ## The leading index of a direction -/

/-- The coordinates at which a direct direction vector is nonzero. -/
def directionSupport (D : DirectLdParams) (v : Fin D.m → DirectScalarQ D) :
    Finset (Fin D.m) :=
  open Classical in
  Finset.univ.filter fun j => v j ≠ 0

theorem mem_directionSupport (D : DirectLdParams)
    (v : Fin D.m → DirectScalarQ D) (j : Fin D.m) :
    j ∈ directionSupport D v ↔ v j ≠ 0 := by
  simp [directionSupport]

/-- The leading index of a direction: the least coordinate at which it is
nonzero, or the last coordinate for the zero direction.  Every coordinate
before the leading index vanishes, so a direction is the prefix projection of
itself at its leading index, and the pair (leading index, direction) is a
canonical direct diagonal sample.  It is the direct index of the sample
whenever the sampled direction is nonzero at the sampled index. -/
noncomputable def directDiagonalIndexOf (D : DirectLdParams)
    (v : Fin D.m → DirectScalarQ D) : Fin D.m :=
  open Classical in
  if h : (directionSupport D v).Nonempty then (directionSupport D v).min' h
  else Fin.rev D.firstIndex

/-- Coordinates before the leading index vanish. -/
theorem directDiagonalIndexOf_prefix_zero (D : DirectLdParams)
    (v : Fin D.m → DirectScalarQ D) :
    ∀ j : Fin D.m, j.val < (directDiagonalIndexOf D v).val → v j = 0 := by
  classical
  intro j hj
  by_contra hne
  have hmem : j ∈ directionSupport D v := (mem_directionSupport D v j).mpr hne
  have hnonempty : (directionSupport D v).Nonempty := ⟨j, hmem⟩
  have hle : directDiagonalIndexOf D v ≤ j := by
    unfold directDiagonalIndexOf
    rw [dif_pos hnonempty]
    exact Finset.min'_le _ _ hmem
  exact absurd (Fin.lt_def.mpr hj) (not_lt.mpr hle)

/-- A direction vanishing before `i` and nonzero at `i` has leading index
`i`. -/
theorem directDiagonalIndexOf_eq (D : DirectLdParams)
    {v : Fin D.m → DirectScalarQ D} {i : Fin D.m}
    (hzero : ∀ j : Fin D.m, j.val < i.val → v j = 0) (hi : v i ≠ 0) :
    directDiagonalIndexOf D v = i := by
  classical
  have hmem : i ∈ directionSupport D v := (mem_directionSupport D v i).mpr hi
  have hnonempty : (directionSupport D v).Nonempty := ⟨i, hmem⟩
  unfold directDiagonalIndexOf
  rw [dif_pos hnonempty]
  apply le_antisymm
  · exact Finset.min'_le _ _ hmem
  · apply Finset.le_min'
    intro j hj
    by_contra hlt
    exact (mem_directionSupport D v j).mp hj
      (hzero j (Fin.lt_def.mp (not_le.mp hlt)))

/-- The leading index of a prefix-projected direction is the projection index
whenever the direction is nonzero there.  This is the generic direct
diagonal sample: the sampled index is recovered from the projected direction
alone. -/
theorem directDiagonalIndexOf_prefixProjection (D : DirectLdParams)
    (i : Fin D.m) (v : Fin D.m → DirectScalarQ D) (hi : v i ≠ 0) :
    directDiagonalIndexOf D (directPrefixProjection i v) = i := by
  apply directDiagonalIndexOf_eq
  · intro j hj
    simp [directPrefixProjection, hj]
  · simpa [directPrefixProjection] using hi

/-- Prefix projection at the leading index is the identity. -/
theorem directPrefixProjection_directDiagonalIndexOf (D : DirectLdParams)
    (v : Fin D.m → DirectScalarQ D) :
    directPrefixProjection (directDiagonalIndexOf D v) v = v := by
  funext j
  unfold directPrefixProjection
  split_ifs with hj
  · exact (directDiagonalIndexOf_prefix_zero D v j hj).symm
  · rfl

/-! ## Decoding LDT points and lines -/

/-- Decode an LDT point into the fixed direct scalar field, reversing the
coordinate order. -/
abbrev ldtPointToDirect (D : DirectLdParams) :
    Point D.toLDTParameters → Fin D.m → DirectScalarQ D :=
  (directPointEquiv D).symm

/-- The direct canonical axis question represented by an LDT axis line.
The LDT coordinate index is reversed together with the point
coordinates. -/
noncomputable def directAxisQuestionOf (D : DirectLdParams)
    (line : AxisParallelLine D.toLDTParameters) : DirectLdQuestion D :=
  let u := ldtPointToDirect D line.base
  let i : Fin D.m := Fin.rev line.direction
  let v : Fin D.m → DirectScalarQ D := coordinateDirection i
  (.aline, ⟨lineRepMap v u, i, 0⟩)

/-- The direct canonical diagonal question represented by an LDT diagonal
line.  The decoded direction is kept and the direct index is its leading
index, so the question is the canonical direct question of the direct sample
formed by the decoded base, the leading index, and the decoded direction
(`directDiagonalQuestionOf_eq_directLdMap`). -/
noncomputable def directDiagonalQuestionOf (D : DirectLdParams)
    (line : DiagonalLine D.toLDTParameters) : DirectLdQuestion D :=
  let u := ldtPointToDirect D line.base
  let v := ldtPointToDirect D line.direction
  (.dline, ⟨lineRepMap v u, directDiagonalIndexOf D v, v⟩)

/-- The direct point question represented by an LDT point. -/
noncomputable def directPointQuestionOf (D : DirectLdParams)
    (u : Point D.toLDTParameters) : DirectLdQuestion D :=
  directLdPointQuestionOf D (ldtPointToDirect D u)

/-- Every transported diagonal question is the canonical direct question of
the direct sample carrying the leading index, hence lies in the support of
the direct diagonal sampler. -/
theorem directDiagonalQuestionOf_eq_directLdMap (D : DirectLdParams)
    (line : DiagonalLine D.toLDTParameters) :
    directDiagonalQuestionOf D line =
      (.dline, directLdMap D .dline
        ⟨ldtPointToDirect D line.base,
          directDiagonalIndexOf D (ldtPointToDirect D line.direction),
          ldtPointToDirect D line.direction⟩) := by
  unfold directDiagonalQuestionOf directLdMap
  simp only [directPrefixProjection_directDiagonalIndexOf]

/-- The LDT diagonal line represented by a direct sample: the encoded
point and the encoded direction. -/
def ldtDiagonalLineOf (D : DirectLdParams) (sample : DirectLdSpace D) :
    DiagonalLine D.toLDTParameters :=
  { base := directPointEquiv D sample.point
    direction := directPointEquiv D sample.direction }

/-- Round trip on generic direct samples: when the sampled direction is
nonzero at the sampled index, the LDT line of the canonical direct
diagonal question transports back to that question, index included. -/
theorem directDiagonalQuestionOf_ldtDiagonalLineOf (D : DirectLdParams)
    (sample : DirectLdSpace D)
    (hgeneric : sample.direction sample.index ≠ 0) :
    directDiagonalQuestionOf D
        (ldtDiagonalLineOf D (directLdMap D .dline sample)) =
      (.dline, directLdMap D .dline sample) := by
  cases sample with
  | mk point index direction =>
      unfold directDiagonalQuestionOf ldtDiagonalLineOf directLdMap
      simp only [ldtPointToDirect, Equiv.symm_apply_apply, lineRepMap_apply_self,
        directDiagonalIndexOf_prefixProjection D index direction hgeneric]

/-- An LDT `j`-restricted diagonal direction decodes to a direct direction
vanishing before index `Fin.rev j`: the suffix restriction of the low
individual degree test is the prefix restriction of the direct game. -/
theorem ldtPointToDirect_extendRestrictedDirection_prefix_zero
    (D : DirectLdParams) (j : Fin D.m)
    (free : Fin (j.val + 1) → Fq D.toLDTParameters) :
    letI := D.toLDTFieldModel
    ∀ c : Fin D.m, c.val < (Fin.rev j).val →
      ldtPointToDirect D (extendRestrictedDirection j free) c = 0 := by
  letI := D.toLDTFieldModel
  intro c hc
  have hj := j.isLt
  have hgt : ¬ (Fin.rev c).val ≤ j.val := by
    rw [Fin.val_rev] at hc ⊢
    omega
  simp only [ldtPointToDirect, directPointEquiv_symm_apply,
    extendRestrictedDirection, dif_neg hgt]
  exact (FieldModel.equiv (q := D.q)).symm_apply_apply 0

/-- The leading index of a decoded `j`-restricted direction is `Fin.rev j`
exactly on the generic event that its pivot coordinate `j` is nonzero. -/
theorem directDiagonalIndexOf_extendRestrictedDirection
    (D : DirectLdParams) (j : Fin D.m)
    (free : Fin (j.val + 1) → Fq D.toLDTParameters) :
    letI := D.toLDTFieldModel
    free ⟨j.val, Nat.lt_succ_self _⟩ ≠ zeroCoord →
      directDiagonalIndexOf D
          (ldtPointToDirect D (extendRestrictedDirection j free)) =
        Fin.rev j := by
  letI := D.toLDTFieldModel
  intro hpivot
  apply directDiagonalIndexOf_eq
  · exact ldtPointToDirect_extendRestrictedDirection_prefix_zero D j free
  · simp only [ldtPointToDirect, directPointEquiv_symm_apply, Fin.rev_rev,
      extendRestrictedDirection, dif_pos (le_refl j.val)]
    intro h
    apply hpivot
    have hcoded := congrArg (directScalarEquiv D) h
    rw [Equiv.apply_symm_apply] at hcoded
    exact hcoded

/-! ## Rebasing lines -/

/-- Decoding an axis-line rebase is translation by the decoded scalar along
the reversed direct coordinate direction. -/
theorem ldtPointToDirect_axis_rebase (D : DirectLdParams)
    (line : AxisParallelLine D.toLDTParameters)
    (t : Fq D.toLDTParameters) :
    letI := D.toLDTFieldModel
    ldtPointToDirect D (line.rebaseAt t).base =
      ldtPointToDirect D line.base +
        (directScalarEquiv D).symm t •
          coordinateDirection (Fin.rev line.direction) := by
  letI := D.toLDTFieldModel
  funext i
  simp only [ldtPointToDirect, directPointEquiv_symm_apply,
    AxisParallelLine.rebaseAt, AxisParallelLine.pointAt, Pi.add_apply,
    Pi.smul_apply]
  by_cases hi : i = Fin.rev line.direction
  · subst hi
    simp only [coordinateDirection, Fin.rev_rev, if_pos, smul_eq_mul]
    rw [Pi.single_eq_same, mul_one]
    exact (FieldModel.equiv (q := D.q)).symm_apply_apply _
  · have hrev : Fin.rev i ≠ line.direction := by
      intro h
      apply hi
      rw [← h, Fin.rev_rev]
    simp [hi, hrev, coordinateDirection]

/-- Decoding a diagonal-line rebase is translation by the decoded scalar
along the decoded direct direction. -/
theorem ldtPointToDirect_diagonal_rebase (D : DirectLdParams)
    (line : DiagonalLine D.toLDTParameters)
    (t : Fq D.toLDTParameters) :
    letI := D.toLDTFieldModel
    ldtPointToDirect D (line.rebaseAt t).base =
      ldtPointToDirect D line.base +
        (directScalarEquiv D).symm t • ldtPointToDirect D line.direction := by
  letI := D.toLDTFieldModel
  funext i
  change decodeScalar
      (addCoord (line.base (Fin.rev i))
        (mulCoord t (line.direction (Fin.rev i)))) =
    decodeScalar (line.base (Fin.rev i)) +
      decodeScalar t * decodeScalar (line.direction (Fin.rev i))
  simp [addCoord, mulCoord]

/-- Canonical direct axis questions do not depend on the chosen base point of
the LDT line. -/
theorem directAxisQuestionOf_rebase (D : DirectLdParams)
    (line : AxisParallelLine D.toLDTParameters)
    (t : Fq D.toLDTParameters) :
    letI := D.toLDTFieldModel
    directAxisQuestionOf D (line.rebaseAt t) = directAxisQuestionOf D line := by
  letI := D.toLDTFieldModel
  simp only [directAxisQuestionOf, AxisParallelLine.rebaseAt_direction]
  rw [ldtPointToDirect_axis_rebase, lineRepMap_add_smul]

/-- Canonical direct diagonal questions do not depend on the chosen base point
of the LDT line; the leading index depends only on the direction. -/
theorem directDiagonalQuestionOf_rebase (D : DirectLdParams)
    (line : DiagonalLine D.toLDTParameters)
    (t : Fq D.toLDTParameters) :
    letI := D.toLDTFieldModel
    directDiagonalQuestionOf D (line.rebaseAt t) =
      directDiagonalQuestionOf D line := by
  letI := D.toLDTFieldModel
  simp only [directDiagonalQuestionOf, DiagonalLine.rebaseAt]
  have hrebase := ldtPointToDirect_diagonal_rebase D line t
  change ldtPointToDirect D (line.pointAt t) =
      ldtPointToDirect D line.base +
        (directScalarEquiv D).symm t • ldtPointToDirect D line.direction at hrebase
  rw [hrebase, lineRepMap_add_smul]

/-- The fixed scalar coding transports field addition to LDT coordinate
addition. -/
theorem directScalarEquiv_add (D : DirectLdParams)
    (x y : DirectScalarQ D) :
    letI := D.toLDTFieldModel
    directScalarEquiv D (x + y) =
      addCoord (directScalarEquiv D x) (directScalarEquiv D y) := by
  letI := D.toLDTFieldModel
  change FieldModel.equiv (x + y) =
    FieldModel.equiv
      (FieldModel.equiv.symm (FieldModel.equiv x) +
        FieldModel.equiv.symm (FieldModel.equiv y))
  rw [FieldModel.equiv.symm_apply_apply, FieldModel.equiv.symm_apply_apply]

private theorem coordinateDirection_ne_zero
    {K : Type*} [Field K] {m : ℕ} (i : Fin m) :
    (coordinateDirection i : Fin m → K) ≠ 0 := by
  intro h
  have hi := congrFun h i
  simp [coordinateDirection] at hi

/-- Canonical rebase parameter for an LDT axis-parallel line. -/
noncomputable def directAxisRebaseParameter (D : DirectLdParams)
    (line : AxisParallelLine D.toLDTParameters) : DirectScalarQ D :=
  directLineRepParameter (coordinateDirection (Fin.rev line.direction))
    (ldtPointToDirect D line.base)

/-- Canonical rebase parameter for an LDT diagonal line. -/
noncomputable def directDiagonalRebaseParameter (D : DirectLdParams)
    (line : DiagonalLine D.toLDTParameters) : DirectScalarQ D :=
  directLineRepParameter (ldtPointToDirect D line.direction)
    (ldtPointToDirect D line.base)

/-- Axis-line canonical parameters add under LDT line rebasing. -/
theorem directAxisRebaseParameter_rebase (D : DirectLdParams)
    (line : AxisParallelLine D.toLDTParameters)
    (t : Fq D.toLDTParameters) :
    letI := D.toLDTFieldModel
    directAxisRebaseParameter D (line.rebaseAt t) =
      directAxisRebaseParameter D line + (directScalarEquiv D).symm t := by
  letI := D.toLDTFieldModel
  unfold directAxisRebaseParameter
  rw [ldtPointToDirect_axis_rebase]
  exact directLineRepParameter_add_smul
    (coordinateDirection_ne_zero (Fin.rev line.direction)) _

/-- Nonzero diagonal-line canonical parameters add under LDT line rebasing. -/
theorem directDiagonalRebaseParameter_rebase (D : DirectLdParams)
    (line : DiagonalLine D.toLDTParameters)
    (t : Fq D.toLDTParameters)
    (hdir : ldtPointToDirect D line.direction ≠ 0) :
    letI := D.toLDTFieldModel
    directDiagonalRebaseParameter D (line.rebaseAt t) =
      directDiagonalRebaseParameter D line + (directScalarEquiv D).symm t := by
  letI := D.toLDTFieldModel
  unfold directDiagonalRebaseParameter
  rw [ldtPointToDirect_diagonal_rebase]
  exact directLineRepParameter_add_smul hdir _

/-! ## Reading direct answers as LDT answers -/

/-- The constant diagonal-line answer with the given direct value. -/
noncomputable def constantDiagonalAnswer (D : DirectLdParams)
    (x : DirectScalarQ D) :
    letI := D.toLDTFieldModel
    DiagonalLinePolynomial D.toLDTParameters := by
  letI := D.toLDTFieldModel
  exact { poly := Polynomial.C x
          degreeBounded := by simp }

/-- Constant answers are fixed by every reparametrization. -/
theorem constantDiagonalAnswer_reparamAt (D : DirectLdParams)
    (x : DirectScalarQ D) (t : Fq D.toLDTParameters) :
    letI := D.toLDTFieldModel
    DiagonalLinePolynomial.reparamAt (constantDiagonalAnswer D x) t =
      constantDiagonalAnswer D x := by
  letI := D.toLDTFieldModel
  apply DiagonalLinePolynomial.ext
  simp [constantDiagonalAnswer, DiagonalLinePolynomial.reparamAt]

/-- A constant answer evaluates to its value at every parameter. -/
theorem constantDiagonalAnswer_apply (D : DirectLdParams)
    (x : DirectScalarQ D) (t : Fq D.toLDTParameters) :
    letI := D.toLDTFieldModel
    constantDiagonalAnswer D x t = directScalarEquiv D x := by
  letI := D.toLDTFieldModel
  change encodeScalar ((Polynomial.C x).eval (decodeScalar t)) =
    directScalarEquiv D x
  rw [Polynomial.eval_C]
  rfl

/-- Read one simultaneous coordinate from a direct point answer. -/
noncomputable def directPointAnswerReadout (D : DirectLdParams) (r : Fin D.k) :
    letI := D.toLDTFieldModel
    DirectLdAnswer D → Fq D.toLDTParameters := by
  letI := D.toLDTFieldModel
  intro answer
  exact match answer with
    | .pointVals a => directScalarEquiv D (a r)
    | .alinePolys _ => directScalarEquiv D 0
    | .dlinePolys _ => directScalarEquiv D 0

/-- Read one simultaneous coordinate from a direct axis-line answer and
rebase its polynomial from the canonical direct line to the LDT line. -/
noncomputable def directAxisAnswerReadout (D : DirectLdParams) (r : Fin D.k)
    (line : AxisParallelLine D.toLDTParameters) :
    letI := D.toLDTFieldModel
    DirectLdAnswer D → AxisLinePolynomial D.toLDTParameters := by
  letI := D.toLDTFieldModel
  intro answer
  exact match answer with
    | .alinePolys a => AxisLinePolynomial.reparamAt
        (directAxisAnswerEquiv D (a r))
        (directScalarEquiv D (directAxisRebaseParameter D line))
    | .pointVals _ => default
    | .dlinePolys _ => default

/-- Read one simultaneous coordinate from a direct diagonal-line answer.  For
a nonzero direction the polynomial is rebased from the canonical direct line
to the LDT line.  A zero direction is the singleton line through its base,
where the direct predicate accepts an answer exactly when its polynomial
function is constant with the point's value (`rem:ld-win-zero-direction`);
the answer is read as the constant polynomial carrying its value at the base
point, which is fixed by every reparametrization.  Wrong-form answers are
sent to the default polynomial. -/
noncomputable def directDiagonalAnswerReadout (D : DirectLdParams) (r : Fin D.k)
    (line : DiagonalLine D.toLDTParameters) :
    letI := D.toLDTFieldModel
    DirectLdAnswer D → DiagonalLinePolynomial D.toLDTParameters := by
  letI := D.toLDTFieldModel
  classical
  intro answer
  exact match answer with
    | .dlinePolys a =>
        if ldtPointToDirect D line.direction = 0 then
          constantDiagonalAnswer D (evalCoefficient (a r) 0)
        else
          DiagonalLinePolynomial.reparamAt (directDiagonalAnswerEquiv D (a r))
            (directScalarEquiv D (directDiagonalRebaseParameter D line))
    | .pointVals _ => default
    | .alinePolys _ => default

/-- Axis answer readout is covariant under LDT line rebasing. -/
theorem directAxisAnswerReadout_rebase (D : DirectLdParams) (r : Fin D.k)
    (line : AxisParallelLine D.toLDTParameters)
    (t : Fq D.toLDTParameters) (answer : DirectLdAnswer D) :
    letI := D.toLDTFieldModel
    directAxisAnswerReadout D r (line.rebaseAt t) answer =
      AxisLinePolynomial.reparamAt (directAxisAnswerReadout D r line answer) t := by
  letI := D.toLDTFieldModel
  cases answer with
  | pointVals a => simp [directAxisAnswerReadout]
  | dlinePolys a => simp [directAxisAnswerReadout]
  | alinePolys a =>
      simp only [directAxisAnswerReadout]
      rw [directAxisRebaseParameter_rebase, directScalarEquiv_add]
      rw [(directScalarEquiv D).apply_symm_apply]
      exact (AxisLinePolynomial.reparamAt_reparamAt
        (directAxisAnswerEquiv D (a r)) _ _).symm

/-- Diagonal answer readout is covariant under LDT line rebasing, including
the constant zero-direction convention. -/
theorem directDiagonalAnswerReadout_rebase (D : DirectLdParams) (r : Fin D.k)
    (line : DiagonalLine D.toLDTParameters)
    (t : Fq D.toLDTParameters) (answer : DirectLdAnswer D) :
    letI := D.toLDTFieldModel
    directDiagonalAnswerReadout D r (line.rebaseAt t) answer =
      DiagonalLinePolynomial.reparamAt
        (directDiagonalAnswerReadout D r line answer) t := by
  letI := D.toLDTFieldModel
  cases answer with
  | pointVals a => simp [directDiagonalAnswerReadout]
  | alinePolys a => simp [directDiagonalAnswerReadout]
  | dlinePolys a =>
      by_cases hdir : ldtPointToDirect D line.direction = 0
      · have hrebase : ldtPointToDirect D (line.rebaseAt t).direction = 0 := by
          simpa [DiagonalLine.rebaseAt] using hdir
        simp [directDiagonalAnswerReadout, hdir, hrebase,
          constantDiagonalAnswer_reparamAt]
      · have hrebase : ldtPointToDirect D (line.rebaseAt t).direction ≠ 0 := by
          simpa [DiagonalLine.rebaseAt] using hdir
        simp only [directDiagonalAnswerReadout, hdir, hrebase, ↓reduceIte]
        rw [directDiagonalRebaseParameter_rebase D line t hdir,
          directScalarEquiv_add, (directScalarEquiv D).apply_symm_apply]
        exact (DiagonalLinePolynomial.reparamAt_reparamAt
          (directDiagonalAnswerEquiv D (a r)) _ _).symm

end

end MIPStarRE.QPBT
