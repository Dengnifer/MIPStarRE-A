import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayerIdentities.PositiveGram.Completion
import MIPStarRE.QPBT.Games.Sandwich.Quantitative

/-! # State-dependent Schmidt mirrors

This module constructs the opposite-register mirror used in the one-sided
pasting argument. The auxiliary construction uses the spectral theorem and
orthonormal completion, including zero Schmidt coefficients.

## References

`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`, `lem:pasting`;
`docs/paper-gaps/qpbt_pasting-product-error.tex`, issue #201. The Schmidt-mirror
argument is a formalization auxiliary, not an additional paper hypothesis.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum
open MIPStarRE.LDT.MakingMeasurementsProjective

/-- The paired-entry estimate for the Schmidt-mirror construction. For nonnegative
Schmidt coefficients, the squared commutator entry is bounded by the two
intertwining errors. This is a Lean-only auxiliary, not a source assertion.
See the one-sided proof in `docs/paper-gaps/qpbt_pasting-product-error.tex`,
issue #201. The matrix estimate is proved in this module. -/
theorem schmidt_pair_mirror_estimate (left right : ℝ) (hleft : 0 ≤ left)
    (hright : 0 ≤ right) (entry target : ℂ) :
    (left - right) ^ 2 * Complex.normSq target ≤
      Complex.normSq ((right : ℂ) * entry - (left : ℂ) * target) +
      Complex.normSq ((left : ℂ) * entry - (right : ℂ) * target) := by
  have hidentity :
      Complex.normSq ((right : ℂ) * entry - (left : ℂ) * target) +
        Complex.normSq ((left : ℂ) * entry - (right : ℂ) * target) -
        (left - right) ^ 2 * Complex.normSq target =
      (left - right) ^ 2 * Complex.normSq entry +
        2 * left * right * Complex.normSq (entry - target) := by
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring
  have hnonneg : 0 ≤ (left - right) ^ 2 * Complex.normSq entry +
      2 * left * right * Complex.normSq (entry - target) :=
    add_nonneg (mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _))
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hleft) hright)
        (Complex.normSq_nonneg _))
  linarith

/-- A square matrix admits Schmidt coordinates, including its zero singular
values. This specializes the existing positive-Gram orthonormal completion
to equal row and column index types; no invertibility is assumed. -/
theorem exists_schmidt_coordinates {ι : Type*} [Fintype ι] [DecidableEq ι]
    (coeff : Op ι) :
    ∃ (left right : Matrix.unitaryGroup ι ℂ) (values : ι → ℝ),
      (∀ index, 0 ≤ values index) ∧
      coeff = (left : Op ι) * Matrix.diagonal (fun index => (values index : ℂ)) *
        (right : Op ι)ᴴ := by
  classical
  let gram := coeffᴴ * coeff
  let hermitian := Matrix.isHermitian_conjTranspose_mul_self coeff
  obtain ⟨rows, hrows⟩ :=
    exists_unitaryGroup_with_positive_gram_spectrum_rows
      coeff gram hermitian rfl (Function.Embedding.subtype _)
  have htranspose : (rows : Op ι)ᵀ * ((rows : Op ι)ᵀ)ᴴ = 1 := by
    rw [show ((rows : Op ι)ᵀ)ᴴ = ((rows : Op ι)ᴴ)ᵀ from rfl,
      ← Matrix.transpose_mul,
      show (rows : Op ι)ᴴ * (rows : Op ι) = 1 from Unitary.coe_star_mul_self rows,
      Matrix.transpose_one]
  let left : Matrix.unitaryGroup ι ℂ :=
    ⟨(rows : Op ι)ᵀ, Matrix.mem_unitaryGroup_iff.mpr htranspose⟩
  let right := hermitian.eigenvectorUnitary
  let values := fun index => Real.sqrt (hermitian.eigenvalues index)
  have hcolumns : coeff * (right : Op ι) =
      (left : Op ι) * Matrix.diagonal (fun index => (values index : ℂ)) := by
    ext row col
    rw [Matrix.mul_diagonal]
    have himage : (coeff * (right : Op ι)) row col =
        (Matrix.toEuclideanLin coeff (hermitian.eigenvectorBasis col)) row := by
      simp [Matrix.mul_apply, right, Matrix.IsHermitian.eigenvectorUnitary_apply,
        Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
    rw [himage]
    by_cases hpositive : 0 < hermitian.eigenvalues col
    · have hrow := hrows ⟨col, hpositive⟩ row
      have hvalue : (values col : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_pos.mpr hpositive).ne'
      change (rows : Op ι) col row =
        ((1 / values col : ℝ) : ℂ) *
          (Matrix.toEuclideanLin coeff (hermitian.eigenvectorBasis col)) row at hrow
      change _ = (rows : Op ι) col row * (values col : ℂ)
      rw [hrow]
      push_cast
      field_simp
    · have hzero :=
        matrix_image_eq_zero_of_nonpositive_gram_eigenvalue
          coeff gram hermitian (Matrix.posSemidef_conjTranspose_mul_self coeff) rfl col hpositive
      have hvalue : values col = 0 := Real.sqrt_eq_zero_of_nonpos (le_of_not_gt hpositive)
      rw [hzero, hvalue]
      simp
  refine ⟨left, right, values, fun index => Real.sqrt_nonneg _, ?_⟩
  calc
    coeff = coeff * (right : Op ι) * (right : Op ι)ᴴ := by
      rw [Matrix.mul_assoc,
        show (right : Op ι) * (right : Op ι)ᴴ = 1 from Unitary.coe_mul_star_self right,
        Matrix.mul_one]
    _ = _ := by rw [hcolumns]

/-- Summing the paired-entry estimate gives the Schmidt commutator bound in
diagonal coordinates. The coefficients may vanish and neither Hermitian
operator is required to be projective. -/
theorem schmidt_diagonal_mirror_estimate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (values : ι → ℝ) (hvalues : ∀ index, 0 ≤ values index)
    (alice bob : Op ι) (halice : alice.IsHermitian) (hbob : bob.IsHermitian) :
    (∑ row, ∑ col, Complex.normSq
      ((bob * Matrix.diagonal (fun index => (values index : ℂ)) -
        Matrix.diagonal (fun index => (values index : ℂ)) * bob) row col)) ≤
      2 * ∑ row, ∑ col, Complex.normSq
        ((alice * Matrix.diagonal (fun index => (values index : ℂ)) -
          Matrix.diagonal (fun index => (values index : ℂ)) * bob) row col) := by
  have hpoint (row col : ι) :
      Complex.normSq (bob row col * (values col : ℂ) - (values row : ℂ) * bob row col) ≤
        Complex.normSq (alice row col * (values col : ℂ) -
          (values row : ℂ) * bob row col) +
        Complex.normSq (alice col row * (values row : ℂ) -
          (values col : ℂ) * bob col row) := by
    have hpair := schmidt_pair_mirror_estimate (values row) (values col)
      (hvalues row) (hvalues col) (alice row col) (bob row col)
    have hleft : Complex.normSq
        (bob row col * (values col : ℂ) - (values row : ℂ) * bob row col) =
        (values row - values col) ^ 2 * Complex.normSq (bob row col) := by
      simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
      ring
    have hright : Complex.normSq
        (alice col row * (values row : ℂ) - (values col : ℂ) * bob col row) =
        Complex.normSq ((values row : ℂ) * alice row col -
          (values col : ℂ) * bob row col) := by
      rw [← Complex.normSq_conj
        (alice col row * (values row : ℂ) - (values col : ℂ) * bob col row)]
      have ha : (starRingEnd ℂ) (alice col row) = alice row col := halice.apply row col
      have hb : (starRingEnd ℂ) (bob col row) = bob row col := hbob.apply row col
      simp only [map_sub, map_mul, Complex.conj_ofReal, ha, hb, mul_comm]
    rw [hleft, hright]
    simpa only [mul_comm] using hpair
  simp only [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hsum := Finset.sum_le_sum fun row (_ : row ∈ (Finset.univ : Finset ι)) =>
    Finset.sum_le_sum fun col (_ : col ∈ (Finset.univ : Finset ι)) => hpoint row col
  simp only [Finset.sum_add_distrib] at hsum
  have hswap : (∑ row : ι, ∑ col : ι, Complex.normSq
      (alice col row * (values row : ℂ) - (values col : ℂ) * bob col row)) =
      ∑ row : ι, ∑ col : ι, Complex.normSq
        (alice row col * (values col : ℂ) - (values row : ℂ) * bob row col) :=
    Finset.sum_comm
  rw [hswap] at hsum
  linarith

private theorem schmidt_entry_mass_eq_trace {ι : Type*} [Fintype ι] (coeff : Op ι) :
    (∑ row, ∑ col, Complex.normSq (coeff row col)) = (coeff * coeffᴴ).trace.re := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.normSq_apply, Complex.mul_re]

private theorem schmidt_entry_mass_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (left right : Matrix.unitaryGroup ι ℂ) (coeff : Op ι) :
    (∑ row, ∑ col, Complex.normSq (((left : Op ι) * coeff * (right : Op ι)ᴴ) row col)) =
      ∑ row, ∑ col, Complex.normSq (coeff row col) := by
  rw [schmidt_entry_mass_eq_trace, schmidt_entry_mass_eq_trace]
  have hright : (right : Op ι)ᴴ * (right : Op ι) = 1 := Unitary.coe_star_mul_self right
  have hleft : (left : Op ι)ᴴ * (left : Op ι) = 1 := Unitary.coe_star_mul_self left
  have hprod : ((left : Op ι) * coeff * (right : Op ι)ᴴ) *
      ((left : Op ι) * coeff * (right : Op ι)ᴴ)ᴴ =
      (left : Op ι) * (coeff * coeffᴴ) * (left : Op ι)ᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (right : Op ι)ᴴ (right : Op ι), hright, Matrix.one_mul]
  rw [hprod, Matrix.trace_mul_cycle, hleft, Matrix.one_mul]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The coefficient matrix of a bipartite vector in the fixed computational
bases. This is a representation adapter, not a change of state. -/
def schmidtCoefficientMatrix (ψ : EuclideanSpace ℂ (ι × ι)) : Op ι :=
  Matrix.of fun row col => ψ (row, col)

/-- Schmidt coordinates chosen from the proved square-matrix decomposition.
The choice is made once for the state and is independent of all measurements. -/
noncomputable def schmidtCoordinates (ψ : EuclideanSpace ℂ (ι × ι)) :
    Matrix.unitaryGroup ι ℂ × Matrix.unitaryGroup ι ℂ × (ι → ℝ) :=
  let existence := exists_schmidt_coordinates (schmidtCoefficientMatrix ψ)
  ⟨Classical.choose existence, Classical.choose (Classical.choose_spec existence),
    Classical.choose (Classical.choose_spec (Classical.choose_spec existence))⟩

/-- The chosen coordinates reconstruct the coefficient matrix with nonnegative
Schmidt coefficients. In particular, this includes nonfaithful reduced states. -/
theorem schmidtCoordinates_spec (ψ : EuclideanSpace ℂ (ι × ι)) :
    (∀ index, 0 ≤ (schmidtCoordinates ψ).2.2 index) ∧
      schmidtCoefficientMatrix ψ = ((schmidtCoordinates ψ).1 : Op ι) *
        Matrix.diagonal (fun index => ((schmidtCoordinates ψ).2.2 index : ℂ)) *
          ((schmidtCoordinates ψ).2.1 : Op ι)ᴴ :=
  Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (exists_schmidt_coordinates (schmidtCoefficientMatrix ψ))))

/-- The unitary identifying the transposed Bob coordinates with the Alice
Schmidt coordinates. Zero Schmidt directions use the orthonormal completion. -/
noncomputable def schmidtMirrorUnitary (ψ : EuclideanSpace ℂ (ι × ι)) :
    Matrix.unitaryGroup ι ℂ :=
  (schmidtCoordinates ψ).1 * star (schmidtCoordinates ψ).2.1

/-- The state-dependent opposite-register mirror, a linear map on Bob
operators. It reverses multiplication because it includes a transpose. -/
noncomputable def schmidtMirror (ψ : EuclideanSpace ℂ (ι × ι)) : Op ι →ₗ[ℂ] Op ι where
  toFun bob := (schmidtMirrorUnitary ψ : Op ι) * bobᵀ * (schmidtMirrorUnitary ψ : Op ι)ᴴ
  map_add' first second := by simp [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]
  map_smul' scalar bob := by
    simp [Matrix.transpose_smul]

/-- Vectorizing a left/right operator difference gives its coefficient-matrix
intertwining error, with the Hilbert norm rather than the function supremum norm. -/
theorem schmidt_action_norm_sq (ψ : EuclideanSpace ℂ (ι × ι)) (alice bob : Op ι) :
    ‖applyOperatorToState (heteroKron alice 1) ψ -
      applyOperatorToState (heteroKron 1 bob) ψ‖ ^ 2 =
      ∑ row, ∑ col, Complex.normSq
        ((alice * schmidtCoefficientMatrix ψ - schmidtCoefficientMatrix ψ * bobᵀ) row col) := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Complex.sq_norm, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro row _
  apply Finset.sum_congr rfl
  intro col _
  congr 1
  simp [applyOperatorToState, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct, heteroKron, Matrix.kronecker,
    Fintype.sum_prod_type, Matrix.mul_apply, schmidtCoefficientMatrix,
    Matrix.one_apply, ite_mul, mul_ite, mul_comm]

/-- Mirrors preserve the identity and therefore completeness of a measurement. -/
theorem schmidtMirror_one (ψ : EuclideanSpace ℂ (ι × ι)) :
    schmidtMirror ψ 1 = 1 := by
  change (schmidtMirrorUnitary ψ : Op ι) * (1 : Op ι)ᵀ *
    (schmidtMirrorUnitary ψ : Op ι)ᴴ = 1
  rw [Matrix.transpose_one, Matrix.mul_one]
  exact Unitary.coe_mul_star_self _

/-- Multiplication is reversed by the Schmidt mirror. -/
theorem schmidtMirror_mul (ψ : EuclideanSpace ℂ (ι × ι)) (first second : Op ι) :
    schmidtMirror ψ (first * second) = schmidtMirror ψ second * schmidtMirror ψ first := by
  have hunitary : (schmidtMirrorUnitary ψ : Op ι)ᴴ *
      (schmidtMirrorUnitary ψ : Op ι) = 1 := Unitary.coe_star_mul_self _
  change _ * (first * second)ᵀ * _ = (_ * secondᵀ * _) * (_ * firstᵀ * _)
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (schmidtMirrorUnitary ψ : Op ι)ᴴ
    (schmidtMirrorUnitary ψ : Op ι), hunitary, Matrix.one_mul]

/-- The mirror preserves adjoints, in addition to reversing products. -/
theorem schmidtMirror_adjoint (ψ : EuclideanSpace ℂ (ι × ι)) (bob : Op ι) :
    schmidtMirror ψ bobᴴ = (schmidtMirror ψ bob)ᴴ := by
  change _ * bobᴴᵀ * _ = (_ * bobᵀ * _)ᴴ
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rfl

/-- The transpose and unitary conjugation preserve positivity of effects. -/
theorem schmidtMirror_posSemidef (ψ : EuclideanSpace ℂ (ι × ι)) (bob : Op ι)
    (hbob : bob.PosSemidef) : (schmidtMirror ψ bob).PosSemidef := by
  have hpositive := hbob.transpose.conjTranspose_mul_mul_same (schmidtMirrorUnitary ψ : Op ι)ᴴ
  simpa only [schmidtMirror, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.conjTranspose_conjTranspose] using hpositive

/-- The state-dependent Schmidt mirror is within twice any Hermitian
opposite-register prediction error, in squared Hilbert norm. This is the
dimension-independent estimate of the one-sided pasting argument in issue #201.
Neither the state nor its reduced density operator is assumed faithful. -/
theorem schmidtMirror_norm_sq_le (ψ : EuclideanSpace ℂ (ι × ι))
    (alice bob : Op ι) (halice : alice.IsHermitian) (hbob : bob.IsHermitian) :
    ‖applyOperatorToState (heteroKron (schmidtMirror ψ bob) 1) ψ -
      applyOperatorToState (heteroKron 1 bob) ψ‖ ^ 2 ≤
      2 * ‖applyOperatorToState (heteroKron alice 1) ψ -
        applyOperatorToState (heteroKron 1 bob) ψ‖ ^ 2 := by
  let left := (schmidtCoordinates ψ).1
  let right := (schmidtCoordinates ψ).2.1
  let values := (schmidtCoordinates ψ).2.2
  let diagonal := Matrix.diagonal (fun index => (values index : ℂ))
  let alice' := (left : Op ι)ᴴ * alice * (left : Op ι)
  let bob' := (right : Op ι)ᴴ * bobᵀ * (right : Op ι)
  have hvalues : ∀ index, 0 ≤ values index := (schmidtCoordinates_spec ψ).1
  have hfactor : schmidtCoefficientMatrix ψ =
      (left : Op ι) * diagonal * (right : Op ι)ᴴ := (schmidtCoordinates_spec ψ).2
  have hmirror : schmidtMirror ψ bob = (left : Op ι) * bob' * (left : Op ι)ᴴ := by
    simp [schmidtMirror, schmidtMirrorUnitary, left, right, bob', Matrix.mul_assoc,
      Matrix.star_eq_conjTranspose]
  have halice' : alice'.IsHermitian := by
    change ((left : Op ι)ᴴ * alice * (left : Op ι))ᴴ = _
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      halice.eq, alice', Matrix.mul_assoc]
  have hbob' : bob'.IsHermitian := by
    change ((right : Op ι)ᴴ * bobᵀ * (right : Op ι))ᴴ = _
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hbob.transpose.eq, bob', Matrix.mul_assoc]
  have hleft : (left : Op ι) * (left : Op ι)ᴴ = 1 := Unitary.coe_mul_star_self left
  have hleft' : (left : Op ι)ᴴ * (left : Op ι) = 1 := Unitary.coe_star_mul_self left
  have hright : (right : Op ι) * (right : Op ι)ᴴ = 1 := Unitary.coe_mul_star_self right
  have hcancel (middle : Op ι) : (left : Op ι) * ((left : Op ι)ᴴ * middle) = middle := by
    rw [← Matrix.mul_assoc, hleft, Matrix.one_mul]
  have hcancel' (middle : Op ι) : (left : Op ι)ᴴ * ((left : Op ι) * middle) = middle := by
    rw [← Matrix.mul_assoc, hleft', Matrix.one_mul]
  have hmirrordiff : schmidtMirror ψ bob * schmidtCoefficientMatrix ψ -
      schmidtCoefficientMatrix ψ * bobᵀ =
      (left : Op ι) * (bob' * diagonal - diagonal * bob') * (right : Op ι)ᴴ := by
    rw [hmirror, hfactor]
    simp only [bob', Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hcancel', hright,
      Matrix.mul_one]
  have halicediff : alice * schmidtCoefficientMatrix ψ - schmidtCoefficientMatrix ψ * bobᵀ =
      (left : Op ι) * (alice' * diagonal - diagonal * bob') * (right : Op ι)ᴴ := by
    rw [hfactor]
    simp only [alice', bob', Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hcancel,
      hright, Matrix.mul_one]
  rw [schmidt_action_norm_sq, schmidt_action_norm_sq, hmirrordiff, halicediff,
    schmidt_entry_mass_unitary, schmidt_entry_mass_unitary]
  exact schmidt_diagonal_mirror_estimate values hvalues alice' bob' halice' hbob'

/-- Applying the fixed Schmidt mirror to every effect produces an actual
measurement; no normalization or completion of its effects is required. -/
noncomputable def schmidtMirrorMeasurement {α : Type*} [Fintype α]
    (ψ : EuclideanSpace ℂ (ι × ι)) (measurement : Measurement α ι) : Measurement α ι :=
  Measurement.ofSumEqOne (fun answer => schmidtMirror ψ (measurement.effect answer))
    (fun answer => Matrix.nonneg_iff_posSemidef.mpr
      (schmidtMirror_posSemidef ψ _ (Matrix.nonneg_iff_posSemidef.mp (measurement.pos answer))))
    (by rw [← map_sum, measurement.sum_eq_one, schmidtMirror_one])

/-- Mirroring commutes with coarse-graining along any evaluation map. -/
theorem schmidtMirrorMeasurement_postprocess {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (ψ : EuclideanSpace ℂ (ι × ι))
    (measurement : Measurement α ι) (evaluation : α → β) (answer : β) :
    ((schmidtMirrorMeasurement ψ measurement).postprocess evaluation).effect answer =
      schmidtMirror ψ ((measurement.postprocess evaluation).effect answer) := by
  change (∑ original ∈ Finset.univ.filter (fun original => evaluation original = answer),
      schmidtMirror ψ (measurement.effect original)) =
    schmidtMirror ψ (∑ original ∈ Finset.univ.filter
      (fun original => evaluation original = answer), measurement.effect original)
  rw [map_sum]

/-- A projective measurement has a projective Schmidt mirror. -/
theorem schmidtMirrorMeasurement_isProjective {α : Type*} [Fintype α]
    (ψ : EuclideanSpace ℂ (ι × ι)) (measurement : Measurement α ι)
    (hprojective : MIPStarRE.QPBT.Measurement.IsProjective measurement) :
    MIPStarRE.QPBT.Measurement.IsProjective (schmidtMirrorMeasurement ψ measurement) := by
  intro answer
  change IsProj (schmidtMirror ψ (measurement.effect answer))
  refine ⟨?_, ?_⟩
  · change schmidtMirror ψ (measurement.effect answer) *
      schmidtMirror ψ (measurement.effect answer) = _
    rw [← schmidtMirror_mul, (hprojective answer).isIdempotentElem.eq]
  · change (schmidtMirror ψ (measurement.effect answer))ᴴ = _
    rw [← schmidtMirror_adjoint,
      (hprojective answer).isSelfAdjoint.isHermitian.eq]

end MIPStarRE.QPBT
