import MIPStarRE.QPBT.Algebra.SelfDualBasis

/-! # Trace and coordinate identities for self-dual bases

Source `lem:downsize_field` and `lem:one`; blueprint
`blueprint/src/chapter/ch11_qpbt_algebra.tex:247-297`; paper
`references/qpbt-paper/04_preliminaries.tex:505-550,744-765`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

theorem basisCoord_apply_eq_trace {F K ι : Type*} [Field F] [Field K]
    [Algebra F K] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F K)
    (hself : Basis.IsSelfDual b) (x : K) (i : ι) :
    b.equivFun x i = Algebra.trace F K (x * b i) := by
  sorry

theorem trace_mul_eq_dotProduct_basisCoord {F K ι : Type*} [Field F] [Field K]
    [Algebra F K] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F K)
    (hself : Basis.IsSelfDual b) (x y : K) :
    Algebra.trace F K (x * y) = dotProduct (b.equivFun x) (b.equivFun y) := by
  sorry

theorem trace_basis_eq_one_of_selfDual_normal {K : Type*} [Field K] [Fintype K]
    [Algebra (ZMod 2) K] {k : ℕ} (b : Module.Basis (Fin k) (ZMod 2) K)
    (hself : Basis.IsSelfDual b) (hnormal : Basis.IsNormal b 2) (i : Fin k) :
    Algebra.trace (ZMod 2) K (b i) = 1 := by
  sorry

theorem basisCoord_one_of_selfDual_normal {K : Type*} [Field K] [Fintype K]
    [Algebra (ZMod 2) K] {k : ℕ} (b : Module.Basis (Fin k) (ZMod 2) K)
    (hself : Basis.IsSelfDual b) (hnormal : Basis.IsNormal b 2) :
    b.equivFun 1 = fun _ => 1 := by
  sorry

theorem basisCoord_apply_eq_fixedBinTrace {q : ℕ} (F : FixedFieldModel q)
    (x : F.K) (i : Fin F.basisDim) :
    F.basis.equivFun x i = fixedBinTrace F (x * F.basis i) := by
  sorry

end MIPStarRE.QPBT
