import MIPStarRE.QPBT.Extraction.EPRProjection
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.JointState

/-!
# The auxiliary vector from the EPR projection

Taking the partial inner product with the EPR vector constructs the
unnormalized auxiliary vector. Tensoring it with EPR gives exactly the
orthogonal projection of the original vector onto the EPR subspace.

## References

Blueprint `lem:qld-unitary`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1769-1783`.
-/

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum

noncomputable section

/-- Move each extracted register before its auxiliary registers. This
permutation puts the ideal state in the order used by
`MagicSquareRigidity.exists_unit_residual`. -/
def extractionEprFirstEquiv (P : AdmissibleParams) (ιA ιB : Type*) :
    SixReg P ιA ιB ≃
      (PauliRegister P × (ιA × PauliRegister P)) ×
        (PauliRegister P × (ιB × PauliRegister P)) :=
  (sixRegExtractionEquiv P ιA ιB).trans
    (Equiv.prodCongr (Equiv.prodComm _ _) (Equiv.prodComm _ _))

namespace Extraction

/-- Partial inner product with the EPR vector, leaving the auxiliary index.
This is the coordinate form of the vector defined at paper line 1769. -/
def eprPartialInner {R V : Type*} [Fintype R] [DecidableEq R]
    [Fintype V] [DecidableEq V] [Nonempty V]
    (ψ : EuclideanSpace ℂ (R × (V × V))) : EuclideanSpace ℂ R :=
  (EuclideanSpace.equiv R ℂ).symm
    (fun r => ∑ p : V × V, star (eprState V p) * ψ (r, p))

/-- Tensoring the EPR partial inner product with EPR gives the rank-one
projection on the second tensor factor. This is the projection equality in
paper lines 1776-1779; no normalization of the auxiliary vector is assumed. -/
theorem vecTensor_eprPartialInner {R V : Type*} [Fintype R] [DecidableEq R]
    [Fintype V] [DecidableEq V] [Nonempty V]
    (ψ : EuclideanSpace ℂ (R × (V × V))) :
    vecTensor (eprPartialInner ψ) (eprState V) =
      applyOperatorToState
        (heteroKron (1 : Op R) (Matrix.vecMulVec (fun x => eprState V x)
          (fun y => star (eprState V y)))) ψ := by
  ext x
  change (∑ p : V × V, star (eprState V p) * ψ (x.1, p)) * eprState V x.2 =
    ∑ j : R × (V × V),
      ((1 : Op R) x.1 j.1 * (eprState V x.2 * star (eprState V j.2))) * ψ j
  conv_rhs => rw [Fintype.sum_prod_type]
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul]
  conv_rhs => rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p _
  ring

end Extraction

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε)

open scoped Classical

/-- In EPR-first local coordinates, the ideal extraction state is the target
of the existing auxiliary-state normalization theorem. -/
theorem reindexState_idealExpState
    (aux : EuclideanSpace ℂ
      (ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB)) :
    reindexState (extractionEprFirstEquiv P S.toStrategy.ιA S.toStrategy.ιB)
        (S.idealExpState aux) =
      reindexState prodShuffle (vecTensor (eprState (PauliRegister P)) aux) := by
  ext index
  change aux ((index.1.2.1, index.1.2.2), (index.2.2.1, index.2.2.2)) *
      eprState (PauliRegister P) (index.1.1, index.2.1) =
    eprState (PauliRegister P) (index.1.1, index.2.1) * aux (index.1.2, index.2.2)
  exact mul_comm _ _

/-- Tensoring an auxiliary vector with EPR preserves its norm. -/
theorem idealExpState_norm
    (aux : EuclideanSpace ℂ
      (ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB)) :
    ‖S.idealExpState aux‖ = ‖aux‖ := by
  rw [idealExpState, reindexState_norm_eq, vecTensor_norm_eq, eprState_norm, mul_one]

/-- A normalized reference vector on `AA'BB'`, formed from the original state
and one EPR pair. It is used when the EPR projection of the given state vanishes. -/
def extractionAuxReference : EuclideanSpace ℂ
    (ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB) :=
  reindexState prodShuffle (vecTensor S.toStrategy.ψ (eprState (PauliRegister P)))

/-- The reference auxiliary vector has norm one. -/
theorem extractionAuxReference_norm : ‖S.extractionAuxReference‖ = 1 := by
  rw [extractionAuxReference, reindexState_norm_eq, vecTensor_norm_eq, eprState_norm,
    S.toStrategy.ψ_norm, one_mul]

/-- The EPR projection on registers `A''B''`, with identity on `AA'BB'`.
Paper lines 1766-1769 use this projection to select the auxiliary vector. -/
def extractionEprProjection : Op (SixReg P S.toStrategy.ιA S.toStrategy.ιB) :=
  reindexOp (extractionIdealShuffle P S.toStrategy.ιA S.toStrategy.ιB).symm
    (heteroKron (1 : Op (ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB))
      (Matrix.vecMulVec (fun x => eprState (PauliRegister P) x)
        (fun y => star (eprState (PauliRegister P) y))))

/-- The auxiliary vector before normalization, obtained by contracting the
extracted registers against EPR. This is `aux_0` at paper line 1769. -/
def extractionAux0
    (θ : EuclideanSpace ℂ (SixReg P S.toStrategy.ιA S.toStrategy.ιB)) :
    EuclideanSpace ℂ (ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB) :=
  Extraction.eprPartialInner
    (reindexState (extractionIdealShuffle P S.toStrategy.ιA S.toStrategy.ιB).symm θ)

/-- The unnormalized ideal extraction state is the EPR projection of the
given six-register state. This identifies the actual auxiliary construction
with the projection in paper lines 1776-1779, retaining the heterogeneous
player spaces of blueprint `lem:qld-unitary`. -/
theorem idealExpState_extractionAux0
    (θ : EuclideanSpace ℂ (SixReg P S.toStrategy.ιA S.toStrategy.ιB)) :
    S.idealExpState (S.extractionAux0 θ) =
      applyOperatorToState S.extractionEprProjection θ := by
  unfold idealExpState extractionAux0
  rw [Extraction.vecTensor_eprPartialInner]
  ext x
  let e := (extractionIdealShuffle P S.toStrategy.ιA S.toStrategy.ιB).symm
  let T := heteroKron
    (1 : Op (ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB))
    (Matrix.vecMulVec (fun x => eprState (PauliRegister P) x)
      (fun y => star (eprState (PauliRegister P) y)))
  change (T *ᵥ (fun j => θ (e.symm j))) (e x) =
    ((T.submatrix e e) *ᵥ (fun j => θ j)) x
  exact (congrFun (Matrix.submatrix_mulVec_equiv T (fun j => θ j) e e) x).symm

/-- Normalize the projected auxiliary vector, at twice the projection error.
This is the normalization step at paper lines 1773-1783. The existing
normalization theorem also covers a zero projection, using the reference
vector above; no nonvanishing assumption is added. -/
theorem exists_unit_aux_near_eprProjection
    (θ : EuclideanSpace ℂ (SixReg P S.toStrategy.ιA S.toStrategy.ιB)) (hθ : ‖θ‖ = 1) :
    ∃ aux : EuclideanSpace ℂ (ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB),
      ‖aux‖ = 1 ∧ ‖θ - S.idealExpState aux‖ ≤
        2 * ‖θ - applyOperatorToState S.extractionEprProjection θ‖ := by
  let e := extractionEprFirstEquiv P S.toStrategy.ιA S.toStrategy.ιB
  have hdist (aux : EuclideanSpace ℂ
      (ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB)) :
      ‖reindexState e θ -
        reindexState prodShuffle (vecTensor (eprState (PauliRegister P)) aux)‖ =
          ‖θ - S.idealExpState aux‖ := by
    rw [← S.reindexState_idealExpState]
    exact (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).norm_map (θ - S.idealExpState aux)
  obtain ⟨aux, haux, hclose⟩ := MagicSquareRigidity.exists_unit_residual
    (reindexState e θ) (by rwa [reindexState_norm_eq])
    S.extractionAuxReference S.extractionAuxReference_norm
    ‖θ - applyOperatorToState S.extractionEprProjection θ‖ (S.extractionAux0 θ)
    (((hdist (S.extractionAux0 θ)).trans
      (congrArg (fun v => ‖θ - v‖) (S.idealExpState_extractionAux0 θ))).le)
  exact ⟨aux, haux, (hdist aux).symm.trans_le hclose⟩

end ProjectiveSetting

end

end MIPStarRE.QPBT
