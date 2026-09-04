import MIPStarRE.QPBT.Algebra.SelfDualBasis

/-! # Trace and coordinate identities for self-dual bases

Source `lem:downsize_field` and `lem:one`; blueprint
`blueprint/src/chapter/ch11_qpbt_algebra.tex:259-311`; paper
`references/qpbt-paper/04_preliminaries.tex:505-550,730-767`.
-/

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

-- The paper-facing interface fixes `Fintype ι`; its value is needed only for the matrix sum.
set_option linter.unusedFintypeInType false in
/-- Item 1 of `lem:downsize_field`, blueprint `ch11_qpbt_algebra.tex:259-277`,
paper `04_preliminaries.tex:509-550`. -/
theorem basisCoord_apply_eq_trace {F K ι : Type*} [Field F] [Field K]
    [Algebra F K] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F K)
    (hself : Basis.IsSelfDual b) (x : K) (i : ι) :
    b.equivFun x i = Algebra.trace F K (x * b i) := by
  have htraceMatrix : Algebra.traceMatrix F b = 1 := by
    ext j l
    simpa [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Matrix.one_apply] using hself j l
  have h := congrFun (Algebra.traceMatrix_of_basis_mulVec b x) i
  rw [htraceMatrix] at h
  simpa using h

/-- Item 2 of `lem:downsize_field`, blueprint `ch11_qpbt_algebra.tex:259-277`,
paper `04_preliminaries.tex:509-550`. -/
theorem trace_mul_eq_dotProduct_basisCoord {F K ι : Type*} [Field F] [Field K]
    [Algebra F K] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F K)
    (hself : Basis.IsSelfDual b) (x y : K) :
    Algebra.trace F K (x * y) = dotProduct (b.equivFun x) (b.equivFun y) := by
  have htraceMatrix :
      LinearMap.BilinForm.toMatrix b (Algebra.traceForm F K) = 1 := by
    rw [← Algebra.traceMatrix_of_basis b]
    ext i j
    simpa [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Matrix.one_apply] using hself i j
  calc
    Algebra.trace F K (x * y) = Algebra.traceForm F K x y := rfl
    _ = b.repr x ⬝ᵥ
        (LinearMap.BilinForm.toMatrix b (Algebra.traceForm F K)) *ᵥ b.repr y :=
      LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec b
        (Algebra.traceForm F K) x y
    _ = dotProduct (b.equivFun x) (b.equivFun y) := by
      simp [htraceMatrix, Module.Basis.equivFun_apply]

/-- The binary Frobenius automorphism preserves the field trace, as used in
`lem:one`, paper `04_preliminaries.tex:739-747`. -/
private theorem trace_sq_eq_trace {K : Type*} [Field K] [Finite K]
    [Algebra (ZMod 2) K] (x : K) :
    Algebra.trace (ZMod 2) K (x ^ 2) = Algebra.trace (ZMod 2) K x := by
  simpa [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, ZMod.card] using
    (Algebra.trace_eq_of_algEquiv
      (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K) x)

-- The finite carrier is part of the fixed source-aligned interface for the binary field model.
set_option linter.unusedFintypeInType false in
/-- The trace-one assertion of `lem:one`, blueprint
`ch11_qpbt_algebra.tex:290-311`, paper `04_preliminaries.tex:730-765`. -/
theorem trace_basis_eq_one_of_selfDual_normal {K : Type*} [Field K] [Fintype K]
    [Algebra (ZMod 2) K] {k : ℕ} (hk : Odd k)
    (b : Module.Basis (Fin k) (ZMod 2) K)
    (hself : Basis.IsSelfDual b) (hnormal : Basis.IsNormal b) (i : Fin k) :
    Algebra.trace (ZMod 2) K (b i) = 1 := by
  obtain ⟨α, hα⟩ := hnormal
  have htrace_pow (j : ℕ) :
      Algebra.trace (ZMod 2) K (α ^ (2 ^ j)) = Algebra.trace (ZMod 2) K α := by
    induction j with
    | zero => simp
    | succ j ih =>
        rw [pow_succ, pow_mul, trace_sq_eq_trace, ih]
  let c : ZMod 2 := Algebra.trace (ZMod 2) K α
  have htrace_basis (j : Fin k) : Algebra.trace (ZMod 2) K (b j) = c := by
    rw [hα j]
    simpa [ZMod.card, c] using htrace_pow j.1
  have hc : c ≠ 0 := by
    intro hc
    have htrace_zero (z : K) : Algebra.trace (ZMod 2) K z = 0 := by
      rw [← b.sum_equivFun z, map_sum]
      simp [htrace_basis, hc]
    let i₀ : Fin k := ⟨0, hk.pos⟩
    have h := hself i₀ i₀
    rw [htrace_zero] at h
    simp at h
  have hc_one : c = 1 := by
    exact Fin.eq_one_of_ne_zero c hc
  exact (htrace_basis i).trans hc_one

-- The finite carrier is part of the fixed source-aligned interface for the binary field model.
set_option linter.unusedFintypeInType false in
/-- The all-ones coordinate assertion of `lem:one`, blueprint
`ch11_qpbt_algebra.tex:290-311`, paper `04_preliminaries.tex:730-765`. -/
theorem basisCoord_one_of_selfDual_normal {K : Type*} [Field K] [Fintype K]
    [Algebra (ZMod 2) K] {k : ℕ} (hk : Odd k)
    (b : Module.Basis (Fin k) (ZMod 2) K)
    (hself : Basis.IsSelfDual b) (hnormal : Basis.IsNormal b) :
    b.equivFun 1 = fun _ => 1 := by
  ext i
  rw [basisCoord_apply_eq_trace b hself]
  simpa using trace_basis_eq_one_of_selfDual_normal hk b hself hnormal i

/-- Fixed-model specialization of the trace-one assertion in `lem:one`,
blueprint `ch11_qpbt_algebra.tex:290-311`, paper `04_preliminaries.tex:730-765`. -/
theorem fixedFieldModel_trace_basis_eq_one {q : ℕ} (F : FixedFieldModel q)
    (i : Fin F.basisDim) : Algebra.trace (ZMod 2) F.K (F.basis i) = 1 := by
  apply trace_basis_eq_one_of_selfDual_normal F.basisDimOdd F.basis
  · simpa [Basis.IsSelfDual, IsDualBasisPair] using F.selfDual
  · simpa [Basis.IsNormal, ZMod.card] using F.normal

/-- Fixed-model specialization of the all-ones assertion in `lem:one`, blueprint
`ch11_qpbt_algebra.tex:290-311`, paper `04_preliminaries.tex:730-765`. -/
theorem fixedFieldModel_basisCoord_one {q : ℕ} (F : FixedFieldModel q) :
    F.binaryCoordinates 1 = fun _ => 1 := by
  apply basisCoord_one_of_selfDual_normal F.basisDimOdd F.basis
  · simpa [Basis.IsSelfDual, IsDualBasisPair] using F.selfDual
  · simpa [Basis.IsNormal, ZMod.card] using F.normal

/-- Fixed-model specialization of item 1 of `lem:downsize_field`, blueprint
`ch11_qpbt_algebra.tex:259-277`, paper `04_preliminaries.tex:509-550`. -/
theorem basisCoord_apply_eq_fixedBinTrace {q : ℕ} (F : FixedFieldModel q)
    (x : F.K) (i : Fin F.basisDim) :
    F.basis.equivFun x i = fixedBinTrace F (x * F.basis i) := by
  apply basisCoord_apply_eq_trace F.basis
  simpa [Basis.IsSelfDual, IsDualBasisPair] using F.selfDual

/-- Canonical binary-trace spelling of item 1 of `lem:downsize_field`, blueprint
`ch11_qpbt_algebra.tex:259-277`, paper `04_preliminaries.tex:509-550`. -/
theorem kappa_apply_eq_binTrace {q : ℕ} (F : FixedFieldModel q)
    (x : F.K) (i : Fin F.basisDim) :
    F.binaryCoordinates x i = binTrace F.K (x * F.basis i) := by
  exact basisCoord_apply_eq_fixedBinTrace F x i

/-- Canonical specialization of item 2 of `lem:downsize_field`, blueprint
`ch11_qpbt_algebra.tex:259-277`, paper `04_preliminaries.tex:509-550`. -/
theorem binTrace_mul_eq_dotProduct {q : ℕ} (F : FixedFieldModel q)
    (x y : F.K) :
    binTrace F.K (x * y) = dotProduct (F.binaryCoordinates x) (F.binaryCoordinates y) := by
  apply trace_mul_eq_dotProduct_basisCoord F.basis
  simpa [Basis.IsSelfDual, IsDualBasisPair] using F.selfDual

/-- Fixed-model coordinate vector for item 3 of
`lem:downsize_field`, blueprint `ch11_qpbt_algebra.tex:259-277`, paper
`04_preliminaries.tex:509-550`. -/
noncomputable def kappaVec {q : ℕ} {ι : Type*} (F : FixedFieldModel q)
    (v : ι → F.K) : ι × Fin F.basisDim → ZMod 2 :=
  basisCoordVec F.basis v

-- The fixed interface supplies decidable basis indices for the multiplication-table calculation.
set_option linter.unusedDecidableInType false in
/-- Basis-generic item 3 of `lem:downsize_field`, with no self-duality
hypothesis; blueprint `ch11_qpbt_algebra.tex:259-277`, paper
`04_preliminaries.tex:509-550`. -/
theorem chi_mulVec_basisCoord {F K : Type*} [Field F] [Field K] [Algebra F K]
    {κ : Type*} [Fintype κ] [DecidableEq κ] {s t : ℕ}
    (b : Module.Basis κ F K) (M : Matrix (Fin s) (Fin t) K) (v : Fin t → K) :
    chiOfBasis b M *ᵥ basisCoordVec b v = basisCoordVec b (M *ᵥ v) := by
  ext p
  rcases p with ⟨i, r⟩
  simp only [chiOfBasis, basisCoordVec, Matrix.mulVec_apply_eq_sum,
    Fintype.sum_prod_type, Module.Basis.equivFun_apply, map_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  have h := congrFun (Algebra.leftMulMatrix_mulVec_repr b (M i j) (v j)) r
  simpa [Matrix.mulVec_apply_eq_sum, Algebra.leftMulMatrix_eq_repr_mul] using h

/-- Fixed-model specialization of item 3 of `lem:downsize_field`, blueprint
`ch11_qpbt_algebra.tex:259-277`, paper `04_preliminaries.tex:509-550`. -/
theorem fixedFieldModel_chi_mulVec_basisCoord {q s t : ℕ} (F : FixedFieldModel q)
    (M : Matrix (Fin s) (Fin t) F.K) (v : Fin t → F.K) :
    chi F M *ᵥ kappaVec F v = kappaVec F (M *ᵥ v) := by
  exact chi_mulVec_basisCoord F.basis M v

/-- The identity `chi_mulVec_kappa` expressing compatibility of `chi` and `kappa`;
`lem:downsize_field`, blueprint `ch11_qpbt_algebra.tex:259-277`, paper
`04_preliminaries.tex:509-550`. -/
theorem chi_mulVec_kappa {q s t : ℕ} (F : FixedFieldModel q)
    (M : Matrix (Fin s) (Fin t) F.K) (v : Fin t → F.K) :
    chi F M *ᵥ kappaVec F v = kappaVec F (M *ᵥ v) := by
  exact fixedFieldModel_chi_mulVec_basisCoord F M v

end MIPStarRE.QPBT
