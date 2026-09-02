import MIPStarRE.QPBT.Algebra.Subspaces

/-! # Orthogonal-complement algebra

Source labels `lem:perp_perp`, `def:Lperp`, and `lem:L_perp_perp`; blueprint
`blueprint/src/chapter/ch11_qpbt_algebra.tex:31-42,386-400`; paper
`references/qpbt-paper/04_preliminaries.tex:261-267,386-400`.
-/

namespace MIPStarRE.QPBT

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

theorem finrank_add_finrank_dotOrthogonal (W : Submodule K (ι → K)) :
    Module.finrank K W + Module.finrank K (dotOrthogonal W) = Fintype.card ι := by
  sorry

theorem dotOrthogonal_dotOrthogonal (W : Submodule K (ι → K)) :
    dotOrthogonal (dotOrthogonal W) = W := by
  sorry

/-- Canonical projector with kernel the dot-product orthogonal complement. -/
noncomputable def canonicalProjPerp {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]
    (L : (Fin n → K) →ₗ[K] (Fin n → K)) :
    (Fin n → K) →ₗ[K] (Fin n → K) :=
  canonicalProjOfKernel (dotOrthogonal (LinearMap.ker L))

theorem ker_canonicalProjPerp {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]
    (L : (Fin n → K) →ₗ[K] (Fin n → K)) :
    LinearMap.ker (canonicalProjPerp L) = dotOrthogonal (LinearMap.ker L) := by
  sorry

end MIPStarRE.QPBT
