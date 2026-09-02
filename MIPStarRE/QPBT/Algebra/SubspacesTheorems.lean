import MIPStarRE.QPBT.Algebra.Subspaces

/-! # Orthogonal-complement algebra

Source labels `lem:perp_perp`, `def:Lperp`, and `lem:L_perp_perp`; blueprint
`blueprint/src/chapter/ch11_qpbt_algebra.tex:49-64,149-175`; paper
`references/qpbt-paper/04_preliminaries.tex:263-281,386-415`.
-/

namespace MIPStarRE.QPBT

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- The dimension identity in `lem:perp_perp`, blueprint
`ch11_qpbt_algebra.tex:49-64`, paper `04_preliminaries.tex:263-281`. -/
theorem finrank_add_finrank_dotOrthogonal (W : Submodule K (ι → K)) :
    Module.finrank K W + Module.finrank K (dotOrthogonal W) = Fintype.card ι := by
  sorry

/-- The double-orthogonal identity in `lem:perp_perp`, blueprint
`ch11_qpbt_algebra.tex:49-64`, paper `04_preliminaries.tex:263-281`. -/
theorem dotOrthogonal_dotOrthogonal (W : Submodule K (ι → K)) :
    dotOrthogonal (dotOrthogonal W) = W := by
  sorry

/-- The map of `def:Lperp`, blueprint `ch11_qpbt_algebra.tex:149-158`, paper
`04_preliminaries.tex:386-392`. The source chooses a basis of `ker(L)^perp`;
`canonicalProjOfKernel` depends only on its span, so the basis argument is
elided in this encoding. -/
noncomputable def canonicalProjPerp {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]
    (L : (Fin n → K) →ₗ[K] (Fin n → K)) :
    (Fin n → K) →ₗ[K] (Fin n → K) :=
  canonicalProjOfKernel (dotOrthogonal (LinearMap.ker L))

/-- The kernel identity `lem:L_perp_perp`, blueprint
`ch11_qpbt_algebra.tex:160-175`, paper `04_preliminaries.tex:394-415`. -/
theorem ker_canonicalProjPerp {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]
    (L : (Fin n → K) →ₗ[K] (Fin n → K)) :
    LinearMap.ker (canonicalProjPerp L) = dotOrthogonal (LinearMap.ker L) := by
  sorry

end MIPStarRE.QPBT
