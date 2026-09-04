import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import MIPStarRE.QPBT.Algebra.Subspaces

/-! # Orthogonal-complement algebra

Source labels `lem:perp_perp`, `def:Lperp`, and `lem:L_perp_perp`; blueprint
`blueprint/src/chapter/ch11_qpbt_algebra.tex:49-64,149-175`; paper
`references/qpbt-paper/04_preliminaries.tex:263-281,386-415`.
-/

namespace MIPStarRE.QPBT

variable {K ι : Type*} [Field K] [Fintype ι]

/-- The coordinate dot product regarded as a bilinear form. -/
private def coordinateDotProduct : LinearMap.BilinForm K (ι → K) :=
  dotProductBilin K K

/-- The coordinate dot-product bilinear form is reflexive. -/
private lemma coordinateDotProduct_isRefl :
    (coordinateDotProduct : LinearMap.BilinForm K (ι → K)).IsRefl := by
  intro u v huv
  simpa [coordinateDotProduct, dotProduct_comm] using huv

/-- The coordinate dot-product bilinear form is nondegenerate over every field. -/
private lemma coordinateDotProduct_nondegenerate :
    (coordinateDotProduct : LinearMap.BilinForm K (ι → K)).Nondegenerate := by
  classical
  apply LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
  intro u hu
  funext i
  simpa [coordinateDotProduct] using hu (Pi.single i 1)

/-- Mathlib's right orthogonal for the coordinate form is the project dot orthogonal. -/
private lemma coordinateDotProduct_orthogonal (W : Submodule K (ι → K)) :
    (coordinateDotProduct : LinearMap.BilinForm K (ι → K)).orthogonal W =
      dotOrthogonal W := by
  ext u
  constructor
  · intro hu v hv
    simpa [coordinateDotProduct, dotProduct_comm] using hu v hv
  · intro hu v hv
    simpa [coordinateDotProduct, dotProduct_comm] using hu v hv

-- The decidable-equality parameter is retained in the next two declarations to
-- preserve their existing public signatures.
set_option linter.unusedDecidableInType false in
/-- The dimension identity in `lem:perp_perp`, blueprint
`ch11_qpbt_algebra.tex:49-64`, paper `04_preliminaries.tex:263-281`. -/
theorem finrank_add_finrank_dotOrthogonal [DecidableEq ι]
    (W : Submodule K (ι → K)) :
    Module.finrank K W + Module.finrank K (dotOrthogonal W) = Fintype.card ι := by
  rw [← coordinateDotProduct_orthogonal W]
  have hker :
      LinearMap.ker (coordinateDotProduct : LinearMap.BilinForm K (ι → K)) = ⊥ :=
    coordinateDotProduct_nondegenerate.ker_eq_bot
  have h := LinearMap.BilinForm.finrank_add_finrank_orthogonal'
    (B := (coordinateDotProduct : LinearMap.BilinForm K (ι → K))) W
  rw [hker, inf_bot_eq, finrank_bot, add_zero, Module.finrank_pi] at h
  exact h

set_option linter.unusedDecidableInType false in
/-- The double-orthogonal identity in `lem:perp_perp`, blueprint
`ch11_qpbt_algebra.tex:49-64`, paper `04_preliminaries.tex:263-281`. -/
theorem dotOrthogonal_dotOrthogonal [DecidableEq ι]
    (W : Submodule K (ι → K)) :
    dotOrthogonal (dotOrthogonal W) = W := by
  rw [← coordinateDotProduct_orthogonal W,
    ← coordinateDotProduct_orthogonal
      ((coordinateDotProduct : LinearMap.BilinForm K (ι → K)).orthogonal W)]
  exact LinearMap.BilinForm.orthogonal_orthogonal
    coordinateDotProduct_nondegenerate coordinateDotProduct_isRefl W

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
  ext x
  simp [canonicalProjPerp, canonicalProjOfKernel, LinearMap.mem_ker]

end MIPStarRE.QPBT
