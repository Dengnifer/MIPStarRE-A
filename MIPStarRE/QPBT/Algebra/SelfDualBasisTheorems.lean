import MIPStarRE.QPBT.Algebra.SelfDualBasis

/-! # Trace and coordinate identities for self-dual bases

Source `lem:downsize_field` and `lem:one`; blueprint
`blueprint/src/chapter/ch11_qpbt_algebra.tex:247-297`; paper
`references/qpbt-paper/04_preliminaries.tex:505-550,744-765`.
-/

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

/-- Item 1 of `lem:downsize_field`, blueprint `ch11_qpbt_algebra.tex:248-264`,
paper `04_preliminaries.tex:509-550`. -/
theorem basisCoord_apply_eq_trace {F K ι : Type*} [Field F] [Field K]
    [Algebra F K] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F K)
    (hself : Basis.IsSelfDual b) (x : K) (i : ι) :
    b.equivFun x i = Algebra.trace F K (x * b i) := by
  sorry

/-- Item 2 of `lem:downsize_field`, blueprint `ch11_qpbt_algebra.tex:248-264`,
paper `04_preliminaries.tex:509-550`. -/
theorem trace_mul_eq_dotProduct_basisCoord {F K ι : Type*} [Field F] [Field K]
    [Algebra F K] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F K)
    (hself : Basis.IsSelfDual b) (x y : K) :
    Algebra.trace F K (x * y) = dotProduct (b.equivFun x) (b.equivFun y) := by
  sorry

/-- The trace-one assertion of `lem:one`, blueprint
`ch11_qpbt_algebra.tex:277-296`, paper `04_preliminaries.tex:730-765`. -/
theorem trace_basis_eq_one_of_selfDual_normal {K : Type*} [Field K] [Fintype K]
    [Algebra (ZMod 2) K] {k : ℕ} (hk : Odd k)
    (b : Module.Basis (Fin k) (ZMod 2) K)
    (hself : Basis.IsSelfDual b) (hnormal : Basis.IsNormal b 2) (i : Fin k) :
    Algebra.trace (ZMod 2) K (b i) = 1 := by
  sorry

/-- The all-ones coordinate assertion of `lem:one`, blueprint
`ch11_qpbt_algebra.tex:277-296`, paper `04_preliminaries.tex:730-765`. -/
theorem basisCoord_one_of_selfDual_normal {K : Type*} [Field K] [Fintype K]
    [Algebra (ZMod 2) K] {k : ℕ} (hk : Odd k)
    (b : Module.Basis (Fin k) (ZMod 2) K)
    (hself : Basis.IsSelfDual b) (hnormal : Basis.IsNormal b 2) :
    b.equivFun 1 = fun _ => 1 := by
  sorry

/-- Fixed-model specialization of the trace-one assertion in `lem:one`,
blueprint `ch11_qpbt_algebra.tex:277-296`, paper `04_preliminaries.tex:730-765`. -/
theorem fixedFieldModel_trace_basis_eq_one {q : ℕ} (F : FixedFieldModel q)
    (i : Fin F.basisDim) : Algebra.trace (ZMod 2) F.K (F.basis i) = 1 := by
  sorry

/-- Fixed-model specialization of the all-ones assertion in `lem:one`, blueprint
`ch11_qpbt_algebra.tex:277-296`, paper `04_preliminaries.tex:730-765`. -/
theorem fixedFieldModel_basisCoord_one {q : ℕ} (F : FixedFieldModel q) :
    F.binaryCoordinates 1 = fun _ => 1 := by
  sorry

/-- Fixed-model specialization of item 1 of `lem:downsize_field`, blueprint
`ch11_qpbt_algebra.tex:248-264`, paper `04_preliminaries.tex:509-550`. -/
theorem basisCoord_apply_eq_fixedBinTrace {q : ℕ} (F : FixedFieldModel q)
    (x : F.K) (i : Fin F.basisDim) :
    F.basis.equivFun x i = fixedBinTrace F (x * F.basis i) := by
  sorry

/-- Canonical binary-trace spelling of item 1 of `lem:downsize_field`, blueprint
`ch11_qpbt_algebra.tex:248-264`, paper `04_preliminaries.tex:509-550`. -/
theorem kappa_apply_eq_binTrace {q : ℕ} (F : FixedFieldModel q)
    (x : F.K) (i : Fin F.basisDim) :
    F.binaryCoordinates x i = binTrace F.K (x * F.basis i) := by
  sorry

/-- Canonical specialization of item 2 of `lem:downsize_field`, blueprint
`ch11_qpbt_algebra.tex:248-264`, paper `04_preliminaries.tex:509-550`. -/
theorem binTrace_mul_eq_dotProduct {q : ℕ} (F : FixedFieldModel q)
    (x y : F.K) :
    binTrace F.K (x * y) = dotProduct (F.binaryCoordinates x) (F.binaryCoordinates y) := by
  sorry

/-- Fixed-model coordinate vector for item 3 of
`lem:downsize_field`, blueprint `ch11_qpbt_algebra.tex:260-274`, paper
`04_preliminaries.tex:509-550`. -/
noncomputable def kappaVec {q : ℕ} {ι : Type*} (F : FixedFieldModel q)
    (v : ι → F.K) : ι × Fin F.basisDim → ZMod 2 :=
  basisCoordVec F.basis v

/-- Basis-generic item 3 of `lem:downsize_field`, with no self-duality
hypothesis; blueprint `ch11_qpbt_algebra.tex:260-274`, paper
`04_preliminaries.tex:509-550`. -/
theorem chi_mulVec_basisCoord {F K : Type*} [Field F] [Field K] [Algebra F K]
    {κ : Type*} [Fintype κ] [DecidableEq κ] {s t : ℕ}
    (b : Module.Basis κ F K) (M : Matrix (Fin s) (Fin t) K) (v : Fin t → K) :
    chiOfBasis b M *ᵥ basisCoordVec b v = basisCoordVec b (M *ᵥ v) := by
  sorry

/-- Fixed-model specialization of item 3 of `lem:downsize_field`, blueprint
`ch11_qpbt_algebra.tex:260-274`, paper `04_preliminaries.tex:509-550`. -/
theorem fixedFieldModel_chi_mulVec_basisCoord {q s t : ℕ} (F : FixedFieldModel q)
    (M : Matrix (Fin s) (Fin t) F.K) (v : Fin t → F.K) :
    chi F M *ᵥ kappaVec F v = kappaVec F (M *ᵥ v) := by
  sorry

/-- The identity `chi_mulVec_kappa` expressing compatibility of `chi` and `kappa`;
`lem:downsize_field`, blueprint `ch11_qpbt_algebra.tex:260-274`, paper
`04_preliminaries.tex:509-550`. -/
theorem chi_mulVec_kappa {q s t : ℕ} (F : FixedFieldModel q)
    (M : Matrix (Fin s) (Fin t) F.K) (v : Fin t → F.K) :
    chi F M *ᵥ kappaVec F v = kappaVec F (M *ᵥ v) := by
  exact fixedFieldModel_chi_mulVec_basisCoord F M v

end MIPStarRE.QPBT
