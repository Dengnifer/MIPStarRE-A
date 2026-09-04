import MIPStarRE.LDT.MakingMeasurementsProjective.NaimarkOneMeas
import MIPStarRE.QPBT.Combining.Linearity.BLR

/-!
# Naimark rounding of the Fourier-square POVM

This file carries out the dilation step in the proof of the quantum linearity
theorem of Natarajan and Vidick.  The Fourier-square POVM `B^u = (hat O^u)^2`
of a family of binary observables `O^a`, indexed by the Boolean cube `F_2^t`,
is dilated by the one-measurement Naimark construction of the low individual
degree test to a projective measurement `{C^u}` on the enlarged space
`ι × Option (F_2^t)`, whose compression along the canonical ancillary vector is
again `{B^u}`.  The signed character sums `L^a = ∑_u (-1)^{u·a} C^u` are then
binary observables satisfying the exact linearity `L^a L^b = L^{a+b}`.

The one-measurement Naimark construction produces projectors indexed by
`Option (F_2^t)`: one for each Fourier outcome and one for the residual outcome
`none`.  Discarding the residual projector would destroy the resolution of the
identity on the enlarged space, and with it the multiplicativity of the signed
sums.  It is therefore folded into the zero Fourier outcome: the projector
attached to `u = 0` is the complement of the sum of the projectors attached to
the nonzero outcomes.  Since the Fourier-square effects themselves sum to the
identity, the folded projector still compresses to `B^0`.

## Main definitions and results

* `naimarkAncilla`, `norm_naimarkAncilla`, `ancProj_naimarkAncilla`: the
  canonical ancillary unit vector and its rank-one density.
* `roundedFourierPVM` with `roundedFourierPVM_isProj`,
  `roundedFourierPVM_sum_eq_one`, `roundedFourierPVM_mul_eq_zero_of_ne`, and
  `trace_heteroKron_mul_roundedFourierPVM`: the dilated projective measurement
  and its compression to the Fourier-square POVM.
* `roundedObservable` with `roundedObservable_mul` and
  `roundedObservable_isBinaryObservable`: the exactly linear binary observables.
* `trace_heteroKron_mul_roundedObservable`: the compression of the rounded
  observables, in the form consumed by the averaged distance bound.

## References

Natarajan--Vidick, arXiv:1610.03574, proof of Theorem 10,
`references/nv-paper/fullpaper.tex:1095-1104`: the Naimark dilation of `{B^u}`
is at lines 1099--1100, the observables `𝒜(a) = ∑_u (-1)^{u·a} C^u` at lines
1100--1102, and their exact linearity at lines 1103--1104.  The QPBT paper
quotes the theorem at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:711-725`, and
the blueprint statement is `thm:linearity` in
`blueprint/src/chapter/ch15_qpbt_combining.tex:98-133`.  The one-measurement
Naimark construction reused here is `oneMeasNaimark` in
`MIPStarRE/LDT/MakingMeasurementsProjective/NaimarkOneMeas.lean`, with its data
structure in `MIPStarRE/LDT/MakingMeasurementsProjective/Defs.lean`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.Quantum
open MIPStarRE.LDT.MakingMeasurementsProjective

noncomputable section

/-! ## The canonical ancillary vector -/

/-- The canonical ancillary vector of the Naimark dilation: the basis vector of
the residual index `none` in `Option (F_2^t)`.  This is the pure state `|anc⟩`
of `references/nv-paper/fullpaper.tex:1099-1100`; in the one-measurement
Naimark construction it is the initial state `|⊥⟩` of the auxiliary register. -/
def naimarkAncilla (t : ℕ) : EuclideanSpace ℂ (Option (Fin t → ZMod 2)) :=
  EuclideanSpace.single none 1

/-- The canonical ancillary vector is a unit vector. -/
theorem norm_naimarkAncilla (t : ℕ) : ‖naimarkAncilla t‖ = 1 := by
  simp [naimarkAncilla]

/-- The rank-one density `|anc⟩⟨anc|` of the canonical ancillary vector is the
auxiliary projector `|⊥⟩⟨⊥|` of the one-measurement Naimark construction. -/
theorem ancProj_naimarkAncilla (t : ℕ) :
    ancProj (naimarkAncilla t) = naimarkAuxProjector (Fin t → ZMod 2) := by
  ext i j
  cases i <;> cases j <;>
    simp [ancProj, naimarkAncilla, naimarkAuxProjector, Matrix.vecMulVec_apply]

/-! ## The Naimark dilation of the Fourier-square POVM -/

/-- The one-measurement Naimark dilation data of the Fourier-square POVM
`{B^u}`, supplied by `oneMeasNaimark`: a family of projectors on
`ι × Option (F_2^t)`, indexed by `Option (F_2^t)`, summing to at most the
identity and reproducing every expectation value of `{B^u}` in the lifted
state.  This is the projective measurement produced by Naimark's theorem at
`references/nv-paper/fullpaper.tex:1099-1100`, before the residual outcome is
folded into the zero outcome. -/
def fourierNaimarkData {t : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (O : (Fin t → ZMod 2) → Op ι) (hO : ∀ a, IsBinaryObservable (O a)) :
    OneMeasNaimarkData (Fin t → ZMod 2) ι :=
  Classical.choose (oneMeasNaimark (fourierSquareMeasurement O hO).toSubmeasurement)

/-- The Naimark dilation data of `fourierNaimarkData` dilates the Fourier-square
POVM. -/
theorem fourierNaimarkData_source {t : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (O : (Fin t → ZMod 2) → Op ι) (hO : ∀ a, IsBinaryObservable (O a)) :
    (fourierNaimarkData O hO).source = (fourierSquareMeasurement O hO).toSubmeasurement :=
  Classical.choose_spec (oneMeasNaimark (fourierSquareMeasurement O hO).toSubmeasurement)

/-- Formalization-only auxiliary lemma for the rounding below: distinct
projectors of a one-measurement Naimark dilation are orthogonal, since they are
projectors summing to at most the identity. -/
private theorem liftedEffect_mul_liftedEffect_of_ne {α d : Type*}
    [Fintype α] [DecidableEq α] [Fintype d] [DecidableEq d]
    (data : OneMeasNaimarkData α d) {a b : Option α} (hab : a ≠ b) :
    data.liftedEffect a * data.liftedEffect b = 0 :=
  data.toProjSubMeasOption.outcome_orthogonal a b hab

/-- Formalization-only auxiliary lemma for the compression identities below:
the expectation-preservation identity of a one-measurement Naimark dilation,
written with plain traces.  For every operator `X` on the original space,
`Tr((X ⊗ |⊥⟩⟨⊥|) P̂_a) = Tr(X M_a)`. -/
private theorem trace_kronecker_auxProjector_mul_liftedEffect {α d : Type*}
    [Fintype α] [DecidableEq α] [Fintype d] [DecidableEq d]
    (data : OneMeasNaimarkData α d) (X : Op d) (a : α) :
    Matrix.trace (Matrix.kronecker X (naimarkAuxProjector α) * data.liftedEffect (some a)) =
      Matrix.trace (X * data.source.effect a) := by
  have h := data.expectation_preservation X a
  simp only [normalizedTrace, oneMeasLiftedDensity, smul_mul_assoc, Matrix.trace_smul,
    smul_eq_mul, Fintype.card_prod, Nat.cast_mul] at h
  rcases isEmpty_or_nonempty d with hd | hd
  · simp [Matrix.trace]
  · have hd0 : (Fintype.card d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hα : (Fintype.card (Option α) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    rw [mul_comm (Fintype.card d : ℂ), mul_div_mul_left _ _ hα, div_left_inj' hd0] at h
    exact h.symm

/-! ## Folding the residual outcome into the zero Fourier outcome -/

/-- The rounded Fourier projective measurement `{C^u}` on `ι × Option (F_2^t)`,
obtained from the Naimark dilation of the Fourier-square POVM by folding the
residual outcome `none` into the zero Fourier outcome.  For `u ≠ 0` the
projector is the dilated projector of the outcome `u`; for `u = 0` it is the
complement of the sum of the dilated projectors of the nonzero outcomes, so
that the family resolves the identity on the enlarged space.  This is the
projective measurement `{C^u}` of `references/nv-paper/fullpaper.tex:1099-1100`. -/
def roundedFourierPVM {t : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (O : (Fin t → ZMod 2) → Op ι) (hO : ∀ a, IsBinaryObservable (O a))
    (u : Fin t → ZMod 2) : Op (ι × Option (Fin t → ZMod 2)) :=
  if u = 0 then
    1 - ∑ v ∈ Finset.univ.erase 0, (fourierNaimarkData O hO).liftedEffect (some v)
  else (fourierNaimarkData O hO).liftedEffect (some u)

/-- Formalization-only auxiliary lemma for `roundedFourierPVM`: the sum of the
dilated projectors of the nonzero Fourier outcomes absorbs each of them on the
left. -/
private theorem sum_erase_mul_liftedEffect {t : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (O : (Fin t → ZMod 2) → Op ι) (hO : ∀ a, IsBinaryObservable (O a))
    {v : Fin t → ZMod 2} (hv : v ≠ 0) :
    (∑ w ∈ Finset.univ.erase 0, (fourierNaimarkData O hO).liftedEffect (some w)) *
        (fourierNaimarkData O hO).liftedEffect (some v) =
      (fourierNaimarkData O hO).liftedEffect (some v) := by
  rw [Finset.sum_mul, Finset.sum_eq_single v]
  · exact ((fourierNaimarkData O hO).lifted_isProj (some v)).isIdempotentElem.eq
  · intro w _ hwv
    exact liftedEffect_mul_liftedEffect_of_ne _ (fun h => hwv (Option.some_inj.mp h))
  · intro hv'
    exact absurd (Finset.mem_erase.mpr ⟨hv, Finset.mem_univ v⟩) hv'

/-- Formalization-only auxiliary lemma for `roundedFourierPVM`: the sum of the
dilated projectors of the nonzero Fourier outcomes is a projector, its summands
being mutually orthogonal projectors. -/
private theorem isProj_sum_erase {t : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (O : (Fin t → ZMod 2) → Op ι) (hO : ∀ a, IsBinaryObservable (O a)) :
    IsProj (∑ w ∈ Finset.univ.erase 0, (fourierNaimarkData O hO).liftedEffect (some w)) := by
  refine { isIdempotentElem := ?_, isSelfAdjoint := ?_ }
  · unfold IsIdempotentElem
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro w hw
    exact sum_erase_mul_liftedEffect O hO (Finset.ne_of_mem_erase hw)
  · rw [isSelfAdjoint_iff, star_sum]
    refine Finset.sum_congr rfl ?_
    intro w _
    exact ((fourierNaimarkData O hO).lifted_isProj (some w)).isSelfAdjoint.star_eq

/-- Formalization-only auxiliary lemma for `roundedFourierPVM`: the sum of the
dilated projectors of the nonzero Fourier outcomes absorbs each of them on the
right, by taking adjoints in the left absorption. -/
private theorem liftedEffect_mul_sum_erase {t : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (O : (Fin t → ZMod 2) → Op ι) (hO : ∀ a, IsBinaryObservable (O a))
    {v : Fin t → ZMod 2} (hv : v ≠ 0) :
    (fourierNaimarkData O hO).liftedEffect (some v) *
        (∑ w ∈ Finset.univ.erase 0, (fourierNaimarkData O hO).liftedEffect (some w)) =
      (fourierNaimarkData O hO).liftedEffect (some v) := by
  have h := congrArg Matrix.conjTranspose (sum_erase_mul_liftedEffect O hO hv)
  rwa [Matrix.conjTranspose_mul, (isProj_sum_erase O hO).isSelfAdjoint.isHermitian.eq,
    ((fourierNaimarkData O hO).lifted_isProj (some v)).isSelfAdjoint.isHermitian.eq] at h

/-- Every rounded Fourier projector is an orthogonal projection. -/
theorem roundedFourierPVM_isProj {t : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (O : (Fin t → ZMod 2) → Op ι) (hO : ∀ a, IsBinaryObservable (O a))
    (u : Fin t → ZMod 2) :
    IsProj (roundedFourierPVM O hO u) := by
  unfold roundedFourierPVM
  by_cases hu : u = 0
  · rw [if_pos hu]
    exact (isProj_sum_erase O hO).one_sub
  · rw [if_neg hu]
    exact (fourierNaimarkData O hO).lifted_isProj (some u)

/-- The rounded Fourier projectors resolve the identity on the enlarged space. -/
theorem roundedFourierPVM_sum_eq_one {t : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (O : (Fin t → ZMod 2) → Op ι) (hO : ∀ a, IsBinaryObservable (O a)) :
    ∑ u : Fin t → ZMod 2, roundedFourierPVM O hO u = 1 := by
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : Fin t → ZMod 2))]
  have hrest : ∑ u ∈ Finset.univ.erase 0, roundedFourierPVM O hO u =
      ∑ u ∈ Finset.univ.erase 0, (fourierNaimarkData O hO).liftedEffect (some u) := by
    refine Finset.sum_congr rfl ?_
    intro u hu
    unfold roundedFourierPVM
    rw [if_neg (Finset.ne_of_mem_erase hu)]
  rw [hrest]
  unfold roundedFourierPVM
  rw [if_pos rfl, sub_add_cancel]

/-- Distinct rounded Fourier projectors are orthogonal.  This is the
orthogonality of the projectors `C^u` invoked at
`references/nv-paper/fullpaper.tex:1103-1104`. -/
theorem roundedFourierPVM_mul_eq_zero_of_ne {t : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (O : (Fin t → ZMod 2) → Op ι) (hO : ∀ a, IsBinaryObservable (O a))
    {u v : Fin t → ZMod 2} (huv : u ≠ v) :
    roundedFourierPVM O hO u * roundedFourierPVM O hO v = 0 := by
  unfold roundedFourierPVM
  by_cases hu : u = 0 <;> by_cases hv : v = 0
  · exact absurd (hu.trans hv.symm) huv
  · rw [if_pos hu, if_neg hv, Matrix.sub_mul, Matrix.one_mul,
      sum_erase_mul_liftedEffect O hO hv, sub_self]
  · rw [if_neg hu, if_pos hv, Matrix.mul_sub, Matrix.mul_one,
      liftedEffect_mul_sum_erase O hO hu, sub_self]
  · rw [if_neg hu, if_neg hv]
    exact liftedEffect_mul_liftedEffect_of_ne _ (fun h => huv (Option.some_inj.mp h))

/-- The compression identity of the rounded Fourier projective measurement: for
every operator `X` on the original space,
`Tr((X ⊗ |anc⟩⟨anc|) C^u) = Tr(X B^u)`, where `B^u = (hat O^u)^2` is the
Fourier-square effect.  For a nonzero outcome this is the expectation
preservation of the one-measurement Naimark dilation; for the zero outcome it
follows from the resolution of the identity by the `B^u`.  This is the sense in
which `{C^u}` simulates `{B^u}` at `references/nv-paper/fullpaper.tex:1099-1100`. -/
theorem trace_heteroKron_mul_roundedFourierPVM {t : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (O : (Fin t → ZMod 2) → Op ι) (hO : ∀ a, IsBinaryObservable (O a))
    (X : Op ι) (u : Fin t → ZMod 2) :
    Matrix.trace (heteroKron X (ancProj (naimarkAncilla t)) * roundedFourierPVM O hO u) =
      Matrix.trace (X * (operatorFourier O u * operatorFourier O u)) := by
  have hP : ∀ v : Fin t → ZMod 2,
      Matrix.trace (heteroKron X (ancProj (naimarkAncilla t)) *
          (fourierNaimarkData O hO).liftedEffect (some v)) =
        Matrix.trace (X * (operatorFourier O v * operatorFourier O v)) := by
    intro v
    rw [ancProj_naimarkAncilla]
    unfold heteroKron
    rw [trace_kronecker_auxProjector_mul_liftedEffect, fourierNaimarkData_source]
    rfl
  unfold roundedFourierPVM
  by_cases hu : u = 0
  · rw [if_pos hu]
    subst hu
    have hone :
        Matrix.trace (heteroKron X (ancProj (naimarkAncilla t)) * 1) = Matrix.trace (X * 1) := by
      rw [Matrix.mul_one, Matrix.mul_one, ancProj_naimarkAncilla]
      unfold heteroKron naimarkAuxProjector
      simpa using Matrix.trace_kronecker X
        (Matrix.single (none : Option (Fin t → ZMod 2)) none (1 : ℂ))
    have hB : X * (operatorFourier O 0 * operatorFourier O 0) =
        X * 1 - ∑ v ∈ Finset.univ.erase 0, X * (operatorFourier O v * operatorFourier O v) := by
      rw [← Finset.mul_sum, ← Matrix.mul_sub]
      congr 1
      rw [eq_sub_iff_add_eq]
      exact (Finset.add_sum_erase Finset.univ
        (fun v => operatorFourier O v * operatorFourier O v) (Finset.mem_univ 0)).trans
        (sum_operatorFourier_sq_eq_one O hO)
    rw [hB, Matrix.mul_sub, Finset.mul_sum, Matrix.trace_sub, Matrix.trace_sub,
      Matrix.trace_sum, Matrix.trace_sum, hone]
    congr 1
    exact Finset.sum_congr rfl (fun v _ => hP v)
  · rw [if_neg hu]
    exact hP u

/-! ## The rounded observables -/

/-- The rounded observables `L^a = ∑_u (-1)^{u·a} C^u`, the signed sums of the
rounded Fourier projectors.  These are the observables `𝒜(a)` introduced at
`references/nv-paper/fullpaper.tex:1100-1102`; the character `(-1)^{u·a}` is
`booleanCharacter u a`. -/
def roundedObservable {t : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (O : (Fin t → ZMod 2) → Op ι) (hO : ∀ a, IsBinaryObservable (O a))
    (a : Fin t → ZMod 2) : Op (ι × Option (Fin t → ZMod 2)) :=
  ∑ u : Fin t → ZMod 2, booleanCharacter u a • roundedFourierPVM O hO u

/-- The exact linearity `L^a L^b = L^{a+b}` of the rounded observables, for
every pair of Boolean-group elements.  Expanding the product, the orthogonality
and idempotence of the projectors `C^u` leave only the diagonal terms, and the
characters multiply.  This is the deduction at
`references/nv-paper/fullpaper.tex:1103-1104`. -/
theorem roundedObservable_mul {t : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (O : (Fin t → ZMod 2) → Op ι) (hO : ∀ a, IsBinaryObservable (O a))
    (a b : Fin t → ZMod 2) :
    roundedObservable O hO a * roundedObservable O hO b = roundedObservable O hO (a + b) := by
  unfold roundedObservable
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro u _
  rw [Finset.mul_sum, Finset.sum_eq_single u]
  · rw [smul_mul_assoc, mul_smul_comm, smul_smul,
      (roundedFourierPVM_isProj O hO u).isIdempotentElem.eq, ← booleanCharacter_add_right]
  · intro v _ hvu
    rw [smul_mul_assoc, mul_smul_comm, roundedFourierPVM_mul_eq_zero_of_ne O hO hvu.symm,
      smul_zero, smul_zero]
  · intro hu
    exact absurd (Finset.mem_univ u) hu

/-- The rounded observable at the zero group element is the identity. -/
theorem roundedObservable_zero {t : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (O : (Fin t → ZMod 2) → Op ι) (hO : ∀ a, IsBinaryObservable (O a)) :
    roundedObservable O hO 0 = 1 := by
  simp [roundedObservable, roundedFourierPVM_sum_eq_one]

/-- The rounded observables are Hermitian: the characters are real and the
rounded Fourier projectors are self-adjoint. -/
theorem roundedObservable_isHermitian {t : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (O : (Fin t → ZMod 2) → Op ι) (hO : ∀ a, IsBinaryObservable (O a))
    (a : Fin t → ZMod 2) :
    (roundedObservable O hO a).IsHermitian := by
  rw [Matrix.IsHermitian, roundedObservable, Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl ?_
  intro u _
  rw [Matrix.conjTranspose_smul, star_booleanCharacter,
    (roundedFourierPVM_isProj O hO u).isSelfAdjoint.isHermitian.eq]

/-- Every rounded observable is a binary observable: it is Hermitian, and its
square is `L^{a+a} = L^0 = 1` by exact linearity. -/
theorem roundedObservable_isBinaryObservable {t : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (O : (Fin t → ZMod 2) → Op ι) (hO : ∀ a, IsBinaryObservable (O a))
    (a : Fin t → ZMod 2) :
    IsBinaryObservable (roundedObservable O hO a) := by
  refine ⟨roundedObservable_isHermitian O hO a, ?_⟩
  have haa : a + a = 0 := by
    ext i
    exact CharTwo.add_self_eq_zero (a i)
  rw [roundedObservable_mul, haa, roundedObservable_zero]

/-- The compression identity of the rounded observables: for every operator `X`
on the original space,
`Tr((X ⊗ |anc⟩⟨anc|) L^a) = Tr(X ∑_u (-1)^{u·a} B^u)`.  The right-hand side
is the character sum of the Fourier-square POVM whose overlap with `O^a` is
certified by `one_sub_error_le_avg_overlap_fourierSquare`; this is the passage
from `Tr_{ρ'}(A(a) 𝒜(a))` to `Tr_ρ(A(a) ∑_u (-1)^{u·a} (hat A^u)^2)` at
`references/nv-paper/fullpaper.tex:1105-1110`. -/
theorem trace_heteroKron_mul_roundedObservable {t : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (O : (Fin t → ZMod 2) → Op ι) (hO : ∀ a, IsBinaryObservable (O a))
    (X : Op ι) (a : Fin t → ZMod 2) :
    Matrix.trace (heteroKron X (ancProj (naimarkAncilla t)) * roundedObservable O hO a) =
      Matrix.trace (X * ∑ u : Fin t → ZMod 2, booleanCharacter u a •
        (operatorFourier O u * operatorFourier O u)) := by
  simp only [roundedObservable, Finset.mul_sum, Matrix.trace_sum, mul_smul_comm,
    Matrix.trace_smul, trace_heteroKron_mul_roundedFourierPVM]

end

end MIPStarRE.QPBT
