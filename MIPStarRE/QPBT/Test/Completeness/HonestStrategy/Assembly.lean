import MIPStarRE.QPBT.Test.Completeness.HonestStrategy

/-!
# Assembling the honest Pauli strategy

This module assembles the measurements of
`MIPStarRE.QPBT.Test.Completeness.HonestStrategy` into a single measurement
family indexed by the question type of the Pauli basis test.  Each honest
measurement acts on the tensor product of the Pauli register with the qubit
supplied to the Magic Square construction, and every outcome is relabelled into
the common answer alphabet of the test.  The results recorded here are the
projectivity and the symmetry of every effect of that family.

## References

The strategy assembled here is the one displayed in the proof of
`lem:pauli-completeness`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1290-1360`;
blueprint `blueprint/src/chapter/ch13_qpbt_test.tex:390-395`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

variable {K ι : Type*} [Field K] [Fintype K] [DecidableEq K] [Algebra (ZMod 2) K]
  [Fintype ι] [DecidableEq ι]

/-! ### Measurement assembly lemmas -/

/-- The one-outcome measurement, used to make the harmless branches of the
honest strategy total on questions outside the sampler support. -/
noncomputable def unitMeasurement (V : Type*) [Fintype V] [DecidableEq V] :
    Measurement Unit V :=
  Measurement.ofSumEqOne (fun _ => 1)
    (fun _ => Matrix.PosSemidef.one.nonneg) (by simp)

/-- A deterministic measurement with prescribed outcome. -/
noncomputable def deterministicMeasurement {α V : Type*}
    [Fintype α] [DecidableEq α] [Fintype V] [DecidableEq V]
    (a : α) : Measurement α V :=
  (unitMeasurement V).postprocess fun _ => a

/-- A deterministic measurement is projective. -/
theorem deterministicMeasurement_projective {α V : Type*}
    [Fintype α] [DecidableEq α] [Fintype V] [DecidableEq V]
    (a : α) :
    MIPStarRE.QPBT.Measurement.IsProjective
      (deterministicMeasurement (V := V) a) := by
  apply postprocess_projective_of_injective
  · intro u
    cases u
    exact IsStarProjection.one _
  intro x y _
  exact Subsingleton.elim x y

/-- Every effect of a deterministic measurement is symmetric. -/
theorem deterministicMeasurement_effect_transpose {α V : Type*}
    [Fintype α] [DecidableEq α] [Fintype V] [DecidableEq V]
    (a b : α) :
    ((deterministicMeasurement (V := V) a).effect b)ᵀ =
      (deterministicMeasurement (V := V) a).effect b := by
  apply postprocess_effect_transpose
  intro u
  cases u
  exact Matrix.transpose_one

/-- A deterministic measurement has zero effect away from its prescribed
outcome. -/
theorem deterministicMeasurement_effect_eq_zero_of_ne {α V : Type*}
    [Fintype α] [DecidableEq α] [Fintype V] [DecidableEq V]
    {a₀ a : α} (ha : a ≠ a₀) :
    (deterministicMeasurement (V := V) a₀).effect a = 0 := by
  rw [show deterministicMeasurement (V := V) a₀ =
      (unitMeasurement V).postprocess (fun _ => a₀) by rfl]
  apply postprocess_effect_eq_zero_of_notMem
  rintro ⟨u, hu⟩
  exact ha hu.symm

/-- Placing a projective measurement on the first tensor factor preserves
projectivity. -/
theorem leftPlacedMeasurement_projective {α V W : Type*}
    [Fintype α] [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (M : Measurement α V) (hM : MIPStarRE.QPBT.Measurement.IsProjective M) :
    MIPStarRE.QPBT.Measurement.IsProjective
      (DistanceCalculus.leftPlacedMeasurement (ιB := W) M) := by
  intro a
  exact MIPStarRE.LDT.MakingMeasurementsProjective.isProj_kronecker
    (hM a) (IsStarProjection.one _)

/-- Tensor placement on the first factor preserves symmetry of effects. -/
theorem leftPlacedMeasurement_effect_transpose {α V W : Type*}
    [Fintype α] [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (M : Measurement α V) (hM : ∀ a, (M.effect a)ᵀ = M.effect a) (a : α) :
    ((DistanceCalculus.leftPlacedMeasurement (ιB := W) M).effect a)ᵀ =
      (DistanceCalculus.leftPlacedMeasurement (ιB := W) M).effect a := by
  change (heteroKron (M.effect a) (1 : Op W))ᵀ =
    heteroKron (M.effect a) (1 : Op W)
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [Matrix.transpose_apply, heteroKron, Matrix.kronecker,
    Matrix.kroneckerMap_apply]
  rw [show M.effect a j i = M.effect a i j by
    exact congrFun (congrFun (hM a) i) j]
  by_cases hkl : k = l
  · subst l
    simp
  · simp [hkl, Ne.symm hkl]

/-- Two coarse-grainings of one projective measurement commute. -/
theorem postprocess_effect_commute {ζ α β V : Type*}
    [Fintype ζ] [DecidableEq ζ] [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [Fintype V] [DecidableEq V]
    (M : Measurement ζ V) (hM : MIPStarRE.QPBT.Measurement.IsProjective M)
    (f : ζ → α) (g : ζ → β) (a : α) (b : β) :
    Commute ((M.postprocess f).effect a) ((M.postprocess g).effect b) := by
  rw [Measurement.postprocess_effect, Measurement.postprocess_effect]
  refine Commute.sum_left _ _ _ ?_
  intro x _
  refine Commute.sum_right _ _ _ ?_
  intro y _
  by_cases hxy : x = y
  · subst y
    exact Commute.refl _
  · rw [commute_iff_eq,
      DistanceCalculus.projective_effect_mul_effect_eq_zero M hM hxy,
      DistanceCalculus.projective_effect_mul_effect_eq_zero M hM (Ne.symm hxy)]

/-- Incompatible fibers of two coarse-grainings of one projective measurement
have zero product. -/
theorem postprocess_effect_mul_eq_zero_of_incompatible {ζ α β V : Type*}
    [Fintype ζ] [DecidableEq ζ] [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [Fintype V] [DecidableEq V]
    (M : Measurement ζ V) (hM : MIPStarRE.QPBT.Measurement.IsProjective M)
    (f : ζ → α) (g : ζ → β) (a : α) (b : β)
    (hbad : ∀ z, f z = a → g z = b → False) :
    (M.postprocess f).effect a * (M.postprocess g).effect b = 0 := by
  classical
  rw [Measurement.postprocess_effect, Measurement.postprocess_effect,
    Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro x hx
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro y hy
  by_cases hxy : x = y
  · subst y
    exact (hbad x (Finset.mem_filter.mp hx).2
      (Finset.mem_filter.mp hy).2).elim
  · exact DistanceCalculus.projective_effect_mul_effect_eq_zero M hM hxy

/-- Commutation is preserved when both operators are placed on the first
tensor factor. -/
theorem leftPlaced_commute {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {A B : Op V} (h : Commute A B) :
    Commute (heteroKron A (1 : Op W)) (heteroKron B (1 : Op W)) := by
  rw [commute_iff_eq, heteroKron_mul, heteroKron_mul, h.eq]

/-- A zero product remains zero after placement on the first tensor factor. -/
theorem leftPlaced_mul_eq_zero {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {A B : Op V} (h : A * B = 0) :
    heteroKron A (1 : Op W) * heteroKron B (1 : Op W) = 0 := by
  rw [heteroKron_mul, h]
  ext ⟨i, k⟩ ⟨j, l⟩
  simp [heteroKron, Matrix.kronecker, Matrix.kroneckerMap_apply]

/-- The local Hilbert-space index used by the honest Pauli strategy.  The
second factor is the qubit supplied to the Magic Square construction. -/
abbrev HonestIndex (P : AdmissibleParams) := PauliRegister P × ZMod 2

/-- Place a Pauli-register measurement on the first factor of the honest local
space and relabel its outcomes with a global answer constructor. -/
noncomputable def placedPauliMeasurement {P : AdmissibleParams}
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : Measurement α (PauliRegister P)) (f : α → PauliAnswer P) :
    Measurement (PauliAnswer P) (HonestIndex P) :=
  (DistanceCalculus.leftPlacedMeasurement (ιB := ZMod 2) M).postprocess f

/-- Incompatible coarse-grained outcomes of two measurements on the Pauli
register have zero product after tensor placement. -/
theorem placedPauliMeasurement_mul_eq_zero_of_incompatible {P : AdmissibleParams}
    {ζ : Type*} [Fintype ζ] [DecidableEq ζ]
    (M : Measurement ζ (PauliRegister P))
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M)
    (f g : ζ → PauliAnswer P)
    (a b : PauliAnswer P)
    (hbad : ∀ h, f h = a → g h = b → False) :
    (placedPauliMeasurement M f).effect a *
        (placedPauliMeasurement M g).effect b = 0 := by
  change ((DistanceCalculus.leftPlacedMeasurement (ιB := ZMod 2) M).postprocess f).effect a *
      ((DistanceCalculus.leftPlacedMeasurement (ιB := ZMod 2) M).postprocess g).effect b = 0
  exact postprocess_effect_mul_eq_zero_of_incompatible
    (DistanceCalculus.leftPlacedMeasurement (ιB := ZMod 2) M)
    (leftPlacedMeasurement_projective M hM) f g a b hbad

/-- Coarse-grainings of one Pauli basis measurement commute after tensor
placement. -/
theorem placedPauliMeasurement_commute {P : AdmissibleParams}
    {ζ : Type*} [Fintype ζ] [DecidableEq ζ]
    (M : Measurement ζ (PauliRegister P))
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M)
    (f g : ζ → PauliAnswer P)
    (a b : PauliAnswer P) :
    Commute ((placedPauliMeasurement M f).effect a)
      ((placedPauliMeasurement M g).effect b) := by
  change Commute
    (((DistanceCalculus.leftPlacedMeasurement (ιB := ZMod 2) M).postprocess f).effect a)
    (((DistanceCalculus.leftPlacedMeasurement (ιB := ZMod 2) M).postprocess g).effect b)
  exact postprocess_effect_commute
    (DistanceCalculus.leftPlacedMeasurement (ιB := ZMod 2) M)
    (leftPlacedMeasurement_projective M hM) f g a b

/-- An answer outside a placed coarse-graining's relabelling range has zero
effect. -/
theorem placedPauliMeasurement_effect_eq_zero_of_notMem {P : AdmissibleParams}
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : Measurement α (PauliRegister P)) (f : α → PauliAnswer P)
    {a : PauliAnswer P} (ha : a ∉ Set.range f) :
    (placedPauliMeasurement M f).effect a = 0 := by
  change ((DistanceCalculus.leftPlacedMeasurement (ιB := ZMod 2) M).postprocess f).effect a = 0
  exact postprocess_effect_eq_zero_of_notMem _ _ ha

/-! ### The total honest measurement family -/

/-- Embed a Magic Square answer into the global Pauli-test answer alphabet. -/
def pauliAnswerOfMs {P : AdmissibleParams} : MsAnswer → PauliAnswer P
  | .triple a => .msTriple a
  | .bit a => .bit a

/-- The embedding of Magic Square answers is injective. -/
theorem pauliAnswerOfMs_injective {P : AdmissibleParams} :
    Function.Injective (@pauliAnswerOfMs P) := by
  intro a b h
  cases a <;> cases b <;> simp only [pauliAnswerOfMs] at h <;> cases h <;> rfl

/-- The honest point measurement at a typed Pauli question. -/
noncomputable def honestPointMeasurement (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) : Measurement (PauliAnswer P) (HonestIndex P) :=
  placedPauliMeasurement (pauliPointMeasurement P W (pauliPointBlock W z))
    (fun a => .value a)

/-- The honest axis-line measurement at a typed Pauli question. -/
noncomputable def honestALineMeasurement (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) : Measurement (PauliAnswer P) (HonestIndex P) :=
  placedPauliMeasurement (pauliALineMeasurement P W z) (fun a => .alinePoly a)

/-- The honest diagonal-line measurement at a typed Pauli question. -/
noncomputable def honestDLineMeasurement (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) : Measurement (PauliAnswer P) (HonestIndex P) :=
  placedPauliMeasurement (pauliDLineMeasurement P W z) (fun a => .dlinePoly a)

/-- The honest Pauli/W measurement at a typed Pauli question. -/
noncomputable def honestPauliMeasurement (P : AdmissibleParams) (W : PauliKind) :
    Measurement (PauliAnswer P) (HonestIndex P) :=
  placedPauliMeasurement (pauliBasisMeasurement W) (fun a => .pauliOutcome a)

/-- The honest Pair/W measurement at a typed Pauli question. -/
noncomputable def honestPairWMeasurement (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) : Measurement (PauliAnswer P) (HonestIndex P) :=
  placedPauliMeasurement
    (pauliTraceMeasurement P W
      (pauliPointBlock W z)
      (match W with | .X => pauliRXBlock z | .Z => pauliRZBlock z))
    (fun a => .bit a)

/-- The honest Pair measurement, with a deterministic harmless branch when the
two Pair/W observables anticommute. -/
noncomputable def honestPairMeasurement (P : AdmissibleParams)
    (z : PauliSpace P) : Measurement (PauliAnswer P) (HonestIndex P) := by
  classical
  by_cases hgamma : pauliPairGamma P z = 0
  · exact placedPauliMeasurement (pauliPairMeasurement P z hgamma)
      (fun a => .pairBits a)
  · exact deterministicMeasurement (V := HonestIndex P) (.pairBits (0, 0))

/-- The honest Magic Square measurement at a typed Pauli question. -/
noncomputable def honestMagicMeasurement (P : AdmissibleParams) (t : MsType)
    (z : PauliSpace P) : Measurement (PauliAnswer P) (HonestIndex P) := by
  classical
  by_cases hgamma : pauliPairGamma P z = 0
  · exact deterministicMeasurement (V := HonestIndex P)
      (match t with
      | .constraint _ => (.msTriple 0 : PauliAnswer P)
      | .var _ => (.bit 0 : PauliAnswer P))
  · exact (pauliMagicMeasurement P z hgamma t).postprocess pauliAnswerOfMs

/-- The total honest measurement family, defined on all 26 Pauli question
types and all ambient coefficient vectors. -/
noncomputable def honestMeasurement (P : AdmissibleParams)
    (t : PauliType) (z : PauliSpace P) :
    Measurement (PauliAnswer P) (HonestIndex P) :=
  match t with
  | .point W => honestPointMeasurement P W z
  | .aline W => honestALineMeasurement P W z
  | .dline W => honestDLineMeasurement P W z
  | .pauli W => honestPauliMeasurement P W
  | .pairW W => honestPairWMeasurement P W z
  | .pair => honestPairMeasurement P z
  | .ms t => honestMagicMeasurement P t z

/-- Injective answer relabelling preserves projectivity of a placed Pauli
measurement. -/
theorem placedPauliMeasurement_projective {P : AdmissibleParams}
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : Measurement α (PauliRegister P))
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M)
    (f : α → PauliAnswer P) (hf : Function.Injective f) :
    MIPStarRE.QPBT.Measurement.IsProjective (placedPauliMeasurement M f) := by
  intro a
  by_cases ha : a ∈ Set.range f
  · rcases ha with ⟨b, rfl⟩
    change IsProj (((DistanceCalculus.leftPlacedMeasurement (ιB := ZMod 2) M).postprocess f).effect
      (f b))
    rw [postprocess_effect_of_injective _ f hf b]
    exact MIPStarRE.LDT.MakingMeasurementsProjective.isProj_kronecker
      (hM b) (IsStarProjection.one _)
  · change IsProj
      (((DistanceCalculus.leftPlacedMeasurement (ιB := ZMod 2) M).postprocess f).effect a)
    rw [postprocess_effect_eq_zero_of_notMem _ _ ha]
    exact IsStarProjection.zero _

/-- Injective answer relabelling preserves symmetry of a placed Pauli
measurement. -/
theorem placedPauliMeasurement_effect_transpose {P : AdmissibleParams}
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : Measurement α (PauliRegister P))
    (hM : ∀ a, (M.effect a)ᵀ = M.effect a)
    (f : α → PauliAnswer P) (a : PauliAnswer P) :
    ((placedPauliMeasurement M f).effect a)ᵀ =
      (placedPauliMeasurement M f).effect a := by
  rw [show placedPauliMeasurement M f =
      (DistanceCalculus.leftPlacedMeasurement (ιB := ZMod 2) M).postprocess f by rfl]
  apply postprocess_effect_transpose
  intro b
  exact leftPlacedMeasurement_effect_transpose M hM b

/-- The global honest measurement is projective at every question. -/
theorem honestMeasurement_projective (P : AdmissibleParams) (t : PauliType)
    (z : PauliSpace P) :
    MIPStarRE.QPBT.Measurement.IsProjective (honestMeasurement P t z) := by
  cases t with
  | point W =>
      simpa [honestMeasurement, honestPointMeasurement] using
        (placedPauliMeasurement_projective
          (pauliPointMeasurement P W (pauliPointBlock W z))
          (pauliPointMeasurement_projective P W (pauliPointBlock W z))
          (fun a => PauliAnswer.value a) (by intro; simp))
  | aline W =>
      simpa [honestMeasurement, honestALineMeasurement] using
        (placedPauliMeasurement_projective (pauliALineMeasurement P W z)
          (pauliALineMeasurement_projective P W z)
          (fun a => PauliAnswer.alinePoly a) (by intro; simp))
  | dline W =>
      simpa [honestMeasurement, honestDLineMeasurement] using
        (placedPauliMeasurement_projective (pauliDLineMeasurement P W z)
          (pauliDLineMeasurement_projective P W z)
          (fun a => PauliAnswer.dlinePoly a) (by intro; simp))
  | pauli W =>
      simpa [honestMeasurement, honestPauliMeasurement] using
        (placedPauliMeasurement_projective (pauliBasisMeasurement W)
          (fun a => pauliProj_isProj W a)
          (fun a => PauliAnswer.pauliOutcome a) (by intro; simp))
  | pairW W =>
      simpa [honestMeasurement, honestPairWMeasurement] using
        (placedPauliMeasurement_projective
          (pauliTraceMeasurement P W (pauliPointBlock W z)
            (match W with | .X => pauliRXBlock z | .Z => pauliRZBlock z))
          (pauliTraceMeasurement_projective P W _ _)
          (fun a => PauliAnswer.bit a) (by intro; simp))
  | pair =>
      classical
      by_cases hg : pauliPairGamma P z = 0
      · simpa [honestMeasurement, honestPairMeasurement, hg] using
          (placedPauliMeasurement_projective (pauliPairMeasurement P z hg)
            (pauliPairMeasurement_projective P z hg)
            (fun a => PauliAnswer.pairBits a) (by intro; simp))
      · simpa [honestMeasurement, honestPairMeasurement, hg] using
          (deterministicMeasurement_projective
            (V := HonestIndex P) (α := PauliAnswer P) (.pairBits (0, 0)))
  | ms t =>
      classical
      by_cases hg : pauliPairGamma P z = 0
      · simpa [honestMeasurement, honestMagicMeasurement, hg] using
          (deterministicMeasurement_projective
            (V := HonestIndex P) (α := PauliAnswer P)
            (match t with
            | .constraint _ => (.msTriple 0 : PauliAnswer P)
            | .var _ => (.bit 0 : PauliAnswer P)))
      · simpa [honestMeasurement, honestMagicMeasurement, hg] using
          (postprocess_projective_of_injective (pauliMagicMeasurement P z hg t)
            (pauliMagicMeasurement_projective P z hg t) pauliAnswerOfMs
            pauliAnswerOfMs_injective)

theorem pauliPointMeasurement_effect_transpose (P : AdmissibleParams) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) (a : PauliScalar P) :
    ((pauliPointMeasurement P W u).effect a)ᵀ =
      (pauliPointMeasurement P W u).effect a := by
  apply postprocess_effect_transpose
  intro h
  exact pauliProj_transpose W h

theorem pauliALineMeasurement_effect_transpose (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) (a : Fin (P.d + 1) → PauliScalar P) :
    ((pauliALineMeasurement P W z).effect a)ᵀ =
      (pauliALineMeasurement P W z).effect a := by
  apply postprocess_effect_transpose
  intro h
  exact pauliProj_transpose W h

theorem pauliDLineMeasurement_effect_transpose (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) (a : Fin (P.m * P.d + 1) → PauliScalar P) :
    ((pauliDLineMeasurement P W z).effect a)ᵀ =
      (pauliDLineMeasurement P W z).effect a := by
  apply postprocess_effect_transpose
  intro h
  exact pauliProj_transpose W h

theorem pauliBasisMeasurement_effect_transpose (W : PauliKind) (h : PauliRegister P) :
    ((pauliBasisMeasurement W).effect h)ᵀ = (pauliBasisMeasurement W).effect h := by
  exact pauliProj_transpose W h

/-- The global honest measurement has symmetric effects. -/
theorem honestMeasurement_effect_transpose (P : AdmissibleParams) (t : PauliType)
    (z : PauliSpace P) (a : PauliAnswer P) :
    ((honestMeasurement P t z).effect a)ᵀ =
      (honestMeasurement P t z).effect a := by
  cases t with
  | point W =>
      change ((honestPointMeasurement P W z).effect a)ᵀ =
        (honestPointMeasurement P W z).effect a
      exact placedPauliMeasurement_effect_transpose _
        (pauliPointMeasurement_effect_transpose P W (pauliPointBlock W z)) _ _
  | aline W =>
      change ((honestALineMeasurement P W z).effect a)ᵀ =
        (honestALineMeasurement P W z).effect a
      exact placedPauliMeasurement_effect_transpose _
        (pauliALineMeasurement_effect_transpose P W z) _ _
  | dline W =>
      change ((honestDLineMeasurement P W z).effect a)ᵀ =
        (honestDLineMeasurement P W z).effect a
      exact placedPauliMeasurement_effect_transpose _
        (pauliDLineMeasurement_effect_transpose P W z) _ _
  | pauli W =>
      change ((honestPauliMeasurement P W).effect a)ᵀ =
        (honestPauliMeasurement P W).effect a
      exact placedPauliMeasurement_effect_transpose _
        (pauliBasisMeasurement_effect_transpose W) _ _
  | pairW W =>
      change ((honestPairWMeasurement P W z).effect a)ᵀ =
        (honestPairWMeasurement P W z).effect a
      exact placedPauliMeasurement_effect_transpose _
        (pauliTraceMeasurement_effect_transpose P W _ _) _ _
  | pair =>
      classical
      by_cases hg : pauliPairGamma P z = 0
      · simpa [honestMeasurement, honestPairMeasurement, hg] using
          (placedPauliMeasurement_effect_transpose (pauliPairMeasurement P z hg)
            (fun β => by
              change (pauliPairEffect P z β)ᵀ = pauliPairEffect P z β
              rw [pauliPairEffect, Matrix.transpose_mul,
                pauliTraceMeasurement_effect_transpose,
                pauliTraceMeasurement_effect_transpose]
              exact (pauliTraceMeasurement_effect_commute P z hg β.1 β.2).eq.symm)
            (fun a => PauliAnswer.pairBits a) a)
      · simpa [honestMeasurement, honestPairMeasurement, hg] using
          (deterministicMeasurement_effect_transpose
            (α := PauliAnswer P) (V := HonestIndex P) (.pairBits (0, 0)) a)
  | ms t =>
      classical
      by_cases hg : pauliPairGamma P z = 0
      · simpa [honestMeasurement, honestMagicMeasurement, hg] using
          (deterministicMeasurement_effect_transpose
            (α := PauliAnswer P) (V := HonestIndex P)
            (match t with
            | .constraint _ => (.msTriple 0 : PauliAnswer P)
            | .var _ => (.bit 0 : PauliAnswer P)) a)
      · simpa [honestMeasurement, honestMagicMeasurement, hg] using
          (postprocess_effect_transpose (pauliMagicMeasurement P z hg t)
            pauliAnswerOfMs
            (fun b => pauliMagicMeasurement_effect_transpose P z hg t b) a)

end

end MIPStarRE.QPBT
