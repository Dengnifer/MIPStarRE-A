import MIPStarRE.QPBT.Extraction.Defs
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.GroundSlice

/-!
# Register transport for extraction

These formalization-only identities relate the six-register presentation, the
two local extraction blocks, and the EPR-first register order of the existing
auxiliary-state normalization theorem. State reindexing is covariant, whereas
operator reindexing is contravariant. Their action identity gives exact transport
of quadratic forms and state-dependent distances without a normalization or
consistency hypothesis.

The permutation to EPR-first order permits direct reuse of
`MagicSquareRigidity.exists_unit_residual`; no normalization theorem or extraction
witness is constructed here. The block identities apply to arbitrary operators,
independently of the controlled-unitary calculations.

## References

Blueprint `lem:qld-unitary` and
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1666-1858`,
especially the auxiliary-state construction at lines 1769-1784 and the register
placements in Equations `eq:qld-unitary-6` through `eq:qld-unitary-9`.
-/

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum

noncomputable section

section Reindex

variable {dom cod : Type*} [Fintype dom] [DecidableEq dom]
  [Fintype cod] [DecidableEq cod]

/-- Coordinate reindexing is Mathlib's linear isometric permutation of a finite
Euclidean space. -/
theorem reindexState_eq_piLpCongrLeft (equiv : dom ≃ cod)
    (state : EuclideanSpace ℂ dom) :
    reindexState equiv state = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ equiv state :=
  rfl

/-- Reindexing by the inverse permutation cancels state transport. -/
@[simp] theorem reindexState_symm_apply (equiv : dom ≃ cod)
    (state : EuclideanSpace ℂ dom) :
    reindexState equiv.symm (reindexState equiv state) = state := by
  simp only [reindexState_eq_piLpCongrLeft, ← LinearIsometryEquiv.piLpCongrLeft_symm,
    LinearIsometryEquiv.symm_apply_apply]

/-- Reindexing cancels transport by the inverse permutation. -/
@[simp] theorem reindexState_apply_symm (equiv : dom ≃ cod)
    (state : EuclideanSpace ℂ cod) :
    reindexState equiv (reindexState equiv.symm state) = state := by
  simpa using reindexState_symm_apply equiv.symm state

/-- Coordinate transport commutes with subtraction of state vectors. -/
theorem reindexState_sub (equiv : dom ≃ cod) (left right : EuclideanSpace ℂ dom) :
    reindexState equiv (left - right) =
      reindexState equiv left - reindexState equiv right := by
  simp only [reindexState_eq_piLpCongrLeft, map_sub]

/-- State-vector distance is invariant under a register permutation. -/
theorem reindexState_norm_sub (equiv : dom ≃ cod) (left right : EuclideanSpace ℂ dom) :
    ‖reindexState equiv left - reindexState equiv right‖ = ‖left - right‖ := by
  rw [← reindexState_sub, reindexState_norm_eq]

/-- The action of a reindexed operator is obtained by transporting the state
forward, acting, and transporting the result back. No property of the operator
or state is assumed. -/
theorem applyOperatorToState_reindexOp (equiv : dom ≃ cod) (operator : Op cod)
    (state : EuclideanSpace ℂ dom) :
    applyOperatorToState (reindexOp equiv operator) state =
      reindexState equiv.symm
        (applyOperatorToState operator (reindexState equiv state)) := by
  ext index
  change ((operator.submatrix equiv equiv) *ᵥ (fun entry => state entry)) index =
    (operator *ᵥ (fun entry => state (equiv.symm entry))) (equiv index)
  exact congrFun (Matrix.submatrix_mulVec_equiv operator
    (fun entry => state entry) equiv equiv) index

/-- State reindexing intertwines the reindexed operator with the original
operator. -/
theorem reindexState_applyOperatorToState (equiv : dom ≃ cod) (operator : Op cod)
    (state : EuclideanSpace ℂ dom) :
    reindexState equiv (applyOperatorToState (reindexOp equiv operator) state) =
      applyOperatorToState operator (reindexState equiv state) := by
  rw [applyOperatorToState_reindexOp, reindexState_apply_symm]

/-- Quadratic forms are unchanged by simultaneous state and operator transport. -/
theorem stateQForm_reindexState (equiv : dom ≃ cod) (operator : Op cod)
    (state : EuclideanSpace ℂ dom) :
    DistanceCalculus.stateQForm (reindexState equiv state) operator =
      DistanceCalculus.stateQForm state (reindexOp equiv operator) := by
  unfold DistanceCalculus.stateQForm
  rw [← reindexState_applyOperatorToState]
  simp only [reindexState_eq_piLpCongrLeft, LinearIsometryEquiv.inner_map_map]

/-- Reindexing the Hilbert-space carrier preserves the averaged squared
distance of arbitrary operator families, with no answer-cardinality factor. -/
theorem opFamilyDistSq_reindexState {questions answers : Type*} [Fintype answers]
    (equiv : dom ≃ cod) (distribution : MIPStarRE.LDT.Distribution questions)
    (left right : questions → answers → Op cod) (state : EuclideanSpace ℂ dom) :
    opFamilyDistSq distribution left right (reindexState equiv state) =
      opFamilyDistSq distribution
        (fun question answer => reindexOp equiv (left question answer))
        (fun question answer => reindexOp equiv (right question answer)) state := by
  unfold opFamilyDistSq
  congr 1
  funext question
  apply Finset.sum_congr rfl
  intro answer _
  change ‖applyOperatorToState (left question answer - right question answer)
      (reindexState equiv state)‖ ^ 2 =
    ‖applyOperatorToState (reindexOp equiv (left question answer - right question answer))
      state‖ ^ 2
  rw [applyOperatorToState_reindexOp, reindexState_norm_eq]

end Reindex

/-- Move the extracted registers to the front of their respective local blocks:
`AA'A'' | BB'B''` becomes `A''AA' | B''BB'`. This is the concrete permutation
needed to use `MagicSquareRigidity.exists_unit_residual` for the auxiliary state
of `lem:qld-unitary`, without identifying the players' original spaces. -/
def extractionEprFirstEquiv (params : AdmissibleParams) (ιA ιB : Type*) :
    SixReg params ιA ιB ≃
      (PauliRegister params × (ιA × PauliRegister params)) ×
        (PauliRegister params × (ιB × PauliRegister params)) :=
  (sixRegExtractionEquiv params ιA ιB).trans
    (Equiv.prodCongr (Equiv.prodComm _ _) (Equiv.prodComm _ _))

/-- The extraction-register permutation as a linear isometric equivalence.
This is a coordinate isometry, not the local swap unitary of the paper. -/
def extractionEprFirstIsometry (params : AdmissibleParams) (ιA ιB : Type*)
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] :
    EuclideanSpace ℂ (SixReg params ιA ιB) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ ((PauliRegister params × (ιA × PauliRegister params)) ×
        (PauliRegister params × (ιB × PauliRegister params))) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (extractionEprFirstEquiv params ιA ιB)

namespace ProjectiveSetting

open scoped Classical

variable {params : AdmissibleParams} {epsilon : ℝ} (setting : ProjectiveSetting params epsilon)

/-- In EPR-first local coordinates, the ideal extraction state is exactly the
target used by the existing auxiliary-state normalization theorem. -/
theorem reindexState_idealExpState
    (aux : EuclideanSpace ℂ
      (ExtractionAuxRegisters params setting.toStrategy.ιA setting.toStrategy.ιB)) :
    reindexState (extractionEprFirstEquiv params setting.toStrategy.ιA setting.toStrategy.ιB)
        (setting.idealExpState aux) =
      reindexState prodShuffle (vecTensor (eprState (PauliRegister params)) aux) := by
  ext index
  change aux ((index.1.2.1, index.1.2.2), (index.2.2.1, index.2.2.2)) *
      eprState (PauliRegister params) (index.1.1, index.2.1) =
    eprState (PauliRegister params) (index.1.1, index.2.1) * aux (index.1.2, index.2.2)
  exact mul_comm _ _

/-- The distance to an ideal extraction state is precisely the residual
distance in EPR-first coordinates. This permits reuse of
`MagicSquareRigidity.exists_unit_residual` in either direction. -/
theorem norm_sub_idealExpState_eq
    (state : EuclideanSpace ℂ (SixReg params setting.toStrategy.ιA setting.toStrategy.ιB))
    (aux : EuclideanSpace ℂ
      (ExtractionAuxRegisters params setting.toStrategy.ιA setting.toStrategy.ιB)) :
    ‖state - setting.idealExpState aux‖ =
      ‖reindexState
          (extractionEprFirstEquiv params setting.toStrategy.ιA setting.toStrategy.ιB) state -
        reindexState prodShuffle (vecTensor (eprState (PauliRegister params)) aux)‖ := by
  rw [← setting.reindexState_idealExpState, reindexState_norm_sub]

/-- The initial six-register state is normalized, since both adjoined EPR
vectors and the original strategy state have norm one. -/
theorem psiHat_norm : ‖setting.psiHat‖ = 1 := by
  simp only [psiHat, reindexState_norm_eq, vecTensor_norm_eq, eprState_norm,
    setting.toStrategy.ψ_norm, one_mul]

/-- Tensoring an auxiliary vector with the extracted EPR state preserves its
norm, even when the auxiliary vector is not normalized. -/
theorem idealExpState_norm
    (aux : EuclideanSpace ℂ
      (ExtractionAuxRegisters params setting.toStrategy.ιA setting.toStrategy.ιB)) :
    ‖setting.idealExpState aux‖ = ‖aux‖ := by
  rw [idealExpState, reindexState_norm_eq, vecTensor_norm_eq, eprState_norm, mul_one]

/-- A concrete normalized vector on `AA'BB'`, obtained from the original
strategy state and one EPR pair. It supplies the reference vector required by
`MagicSquareRigidity.exists_unit_residual`, including its zero-residual case. -/
def extractionAuxReference : EuclideanSpace ℂ
    (ExtractionAuxRegisters params setting.toStrategy.ιA setting.toStrategy.ιB) :=
  reindexState prodShuffle (vecTensor setting.toStrategy.ψ (eprState (PauliRegister params)))

/-- The reference auxiliary vector is a unit vector, without any choice of a
basis vector on either player's original space. -/
theorem extractionAuxReference_norm : ‖setting.extractionAuxReference‖ = 1 := by
  rw [extractionAuxReference, reindexState_norm_eq, vecTensor_norm_eq, eprState_norm,
    setting.toStrategy.ψ_norm, one_mul]

/-- Simultaneous block placement respects multiplication. This identity is
independent of the construction of the local swap operators. -/
theorem placeBoth_mul
    (aliceLeft aliceRight : Op (ExtractionBlock params setting.toStrategy.ιA))
    (bobLeft bobRight : Op (ExtractionBlock params setting.toStrategy.ιB)) :
    setting.placeBoth aliceLeft bobLeft * setting.placeBoth aliceRight bobRight =
      setting.placeBoth (aliceLeft * aliceRight) (bobLeft * bobRight) := by
  unfold placeBoth reindexOp
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv, heteroKron_mul]

/-- Simultaneous block placement respects adjoints. -/
theorem placeBoth_conjTranspose
    (aliceOp : Op (ExtractionBlock params setting.toStrategy.ιA))
    (bobOp : Op (ExtractionBlock params setting.toStrategy.ιB)) :
    (setting.placeBoth aliceOp bobOp)ᴴ = setting.placeBoth aliceOpᴴ bobOpᴴ := by
  unfold placeBoth reindexOp heteroKron Matrix.kronecker
  rw [Matrix.conjTranspose_reindex, Matrix.conjTranspose_kronecker]

/-- Placing the identity on each extraction block gives the six-register
identity operator. -/
theorem placeBoth_one_one : setting.placeBoth 1 1 = 1 := by
  simp [placeBoth, heteroKron_one_one, reindexOp, Matrix.reindex_apply]

/-- Conjugation by block operators acts separately on the two tensor factors.
No unitarity is needed for this algebraic identity. -/
theorem conjBy_placeBoth
    (aliceConjugator aliceOp : Op (ExtractionBlock params setting.toStrategy.ιA))
    (bobConjugator bobOp : Op (ExtractionBlock params setting.toStrategy.ιB)) :
    conjBy (setting.placeBoth aliceConjugator bobConjugator)
        (setting.placeBoth aliceOp bobOp) =
      setting.placeBoth (conjBy aliceConjugator aliceOp) (conjBy bobConjugator bobOp) := by
  simp only [conjBy, setting.placeBoth_conjTranspose, setting.placeBoth_mul]

/-- The original-player placement agrees with block placement after adjoining
identities on that player's two Pauli registers. This identifies the concrete
measurement placements in `lem:qld-unitary`. -/
theorem placePlayer_eq_placeSide (side : PlayerSide)
    (operator : Op (setting.LocalSpace side)) :
    setting.placePlayer side operator =
      setting.placeSide side (setting.onPlayer side operator) := by
  cases side <;> ext row column <;>
    simp only [placePlayer, placeSide, onPlayer, place, reindexOp, Matrix.reindex_apply,
      Equiv.symm_symm, Matrix.submatrix_apply, sixRegExtractionEquiv, Equiv.coe_fn_mk,
      ← heteroKron_one_one, heteroKron, Matrix.kronecker, Matrix.kroneckerMap_apply] <;> ring

/-- The crossed six-register placement of an extracted-register operator
agrees with its local extraction-block placement. No property of the operator
is needed; in particular this applies to every canonical Pauli projector. -/
theorem placeExtractedRegister_eq_placeSide (side : PlayerSide)
    (operator : Op (PauliRegister params)) :
    setting.placeExtractedRegister side operator =
      setting.placeSide side (heteroKron 1 operator) := by
  cases side with
  | alice =>
      ext row column
      change
        (1 : Op setting.toStrategy.ιA) row.1.1 column.1.1 *
            (1 : Op (PauliRegister params)) row.1.2.1 column.1.2.1 *
            ((1 : Op setting.toStrategy.ιB) row.2.1 column.2.1 *
              operator row.1.2.2 column.1.2.2) *
            (1 : Op (PauliRegister params)) row.2.2.1 column.2.2.1 *
            (1 : Op (PauliRegister params)) row.2.2.2 column.2.2.2 =
          (1 : Op (setting.toStrategy.ιA × PauliRegister params))
              (row.1.1, row.1.2.1) (column.1.1, column.1.2.1) *
            operator row.1.2.2 column.1.2.2 *
            (1 : Op (ExtractionBlock params setting.toStrategy.ιB))
              ((row.2.1, row.2.2.1), row.2.2.2) ((column.2.1, column.2.2.1), column.2.2.2)
      simp only [← heteroKron_one_one, heteroKron, Matrix.kronecker, Matrix.kroneckerMap_apply]
      ring
  | bob =>
      ext row column
      change
        ((1 : Op setting.toStrategy.ιA) row.1.1 column.1.1 *
              operator row.2.2.2 column.2.2.2) *
            (1 : Op (PauliRegister params)) row.1.2.1 column.1.2.1 *
            (1 : Op (PauliRegister params)) row.1.2.2 column.1.2.2 *
            (1 : Op setting.toStrategy.ιB) row.2.1 column.2.1 *
            (1 : Op (PauliRegister params)) row.2.2.1 column.2.2.1 =
          (1 : Op (ExtractionBlock params setting.toStrategy.ιA))
              ((row.1.1, row.1.2.1), row.1.2.2) ((column.1.1, column.1.2.1), column.1.2.2) *
            ((1 : Op (setting.toStrategy.ιB × PauliRegister params))
                (row.2.1, row.2.2.1) (column.2.1, column.2.2.1) *
              operator row.2.2.2 column.2.2.2)
      simp only [← heteroKron_one_one, heteroKron, Matrix.kronecker, Matrix.kroneckerMap_apply]
      ring

/-- Conjugating two operators on the same side is local block conjugation.
This does not assume that the conjugating operator is unitary. -/
theorem conjBy_placeSide (side : PlayerSide)
    (conjugator operator : Op (ExtractionBlock params (setting.LocalSpace side))) :
    conjBy (setting.placeSide side conjugator) (setting.placeSide side operator) =
      setting.placeSide side (conjBy conjugator operator) := by
  cases side with
  | alice =>
      change conjBy (setting.placeBoth conjugator 1) (setting.placeBoth operator 1) = _
      rw [setting.conjBy_placeBoth]
      simp [conjBy, placeBoth, placeSide]
      rfl
  | bob =>
      change conjBy (setting.placeBoth 1 conjugator) (setting.placeBoth 1 operator) = _
      rw [setting.conjBy_placeBoth]
      simp [conjBy, placeBoth, placeSide]
      rfl

/-- Simultaneous unitary conjugation of a one-side operator equals conjugation
on that side alone. The only hypotheses are the explicit right-unitary
identities for arbitrary local block operators, not consistency assumptions or
claims about the concrete controlled swaps. -/
theorem conjBy_placeBoth_placeSide
    (operators : (side : PlayerSide) → Op (ExtractionBlock params (setting.LocalSpace side)))
    (right_unitary : ∀ side, operators side * (operators side)ᴴ = 1)
    (side : PlayerSide) (operator : Op (ExtractionBlock params (setting.LocalSpace side))) :
    conjBy (setting.placeBoth (operators .alice) (operators .bob))
        (setting.placeSide side operator) =
      conjBy (setting.placeSide side (operators side)) (setting.placeSide side operator) := by
  rw [setting.conjBy_placeSide]
  dsimp only [LocalSpace, localSpaceFintype, localSpaceDecidableEq] at operators right_unitary ⊢
  cases side with
  | alice =>
      change conjBy (setting.placeBoth (operators .alice) (operators .bob))
        (setting.placeBoth operator 1) = _
      rw [setting.conjBy_placeBoth]
      have other : conjBy (operators .bob)
          (1 : Op (ExtractionBlock params setting.toStrategy.ιB)) = 1 := by
        rw [conjBy, Matrix.mul_one]
        exact right_unitary .bob
      rw [other]
      rfl
  | bob =>
      change conjBy (setting.placeBoth (operators .alice) (operators .bob))
        (setting.placeBoth 1 operator) = _
      rw [setting.conjBy_placeBoth]
      have other : conjBy (operators .alice)
          (1 : Op (ExtractionBlock params setting.toStrategy.ιA)) = 1 := by
        rw [conjBy, Matrix.mul_one]
        exact right_unitary .alice
      rw [other]
      rfl

/-- Applying the two block operators in six-register coordinates is exactly
their tensor action after reassociation to the two extraction blocks. -/
theorem reindexState_applyBoth
    (aliceOp : Op (ExtractionBlock params setting.toStrategy.ιA))
    (bobOp : Op (ExtractionBlock params setting.toStrategy.ιB))
    (state : EuclideanSpace ℂ (SixReg params setting.toStrategy.ιA setting.toStrategy.ιB)) :
    reindexState (sixRegExtractionEquiv params setting.toStrategy.ιA setting.toStrategy.ιB)
        (setting.applyBoth aliceOp bobOp state) =
      applyOperatorToState (heteroKron aliceOp bobOp)
        (reindexState (sixRegExtractionEquiv params setting.toStrategy.ιA setting.toStrategy.ιB)
          state) :=
  reindexState_applyOperatorToState _ _ _

/-- The six-register block action of two local isometries agrees with the
already established heterogeneous tensor-isometry action. -/
theorem applyBoth_eq_isometryTensor
    (aliceIsometry : EuclideanSpace ℂ (ExtractionBlock params setting.toStrategy.ιA) →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ExtractionBlock params setting.toStrategy.ιA))
    (bobIsometry : EuclideanSpace ℂ (ExtractionBlock params setting.toStrategy.ιB) →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ExtractionBlock params setting.toStrategy.ιB))
    (state : EuclideanSpace ℂ (SixReg params setting.toStrategy.ιA setting.toStrategy.ιB)) :
    setting.applyBoth (MagicSquareRigidity.isometryMatrix aliceIsometry)
        (MagicSquareRigidity.isometryMatrix bobIsometry) state =
      reindexState
        (sixRegExtractionEquiv params setting.toStrategy.ιA setting.toStrategy.ιB).symm
        (isometryTensor aliceIsometry bobIsometry
          (reindexState
            (sixRegExtractionEquiv params setting.toStrategy.ιA setting.toStrategy.ιB) state)) := by
  rw [MagicSquareRigidity.isometryTensor_eq_toEuclideanLin]
  exact applyOperatorToState_reindexOp _ _ _

/-- Applying local matrix isometries to the two extraction blocks preserves
the state norm. The rectangular matrix-isometry norm theorem is reused; the
unitarity of the concrete swap operators is a separate calculation. -/
theorem applyBoth_norm
    (aliceOp : Op (ExtractionBlock params setting.toStrategy.ιA))
    (bobOp : Op (ExtractionBlock params setting.toStrategy.ιB))
    (alice_isometry : aliceOpᴴ * aliceOp = 1) (bob_isometry : bobOpᴴ * bobOp = 1)
    (state : EuclideanSpace ℂ (SixReg params setting.toStrategy.ιA setting.toStrategy.ιB)) :
    ‖setting.applyBoth aliceOp bobOp state‖ = ‖state‖ := by
  apply MagicSquareRigidity.norm_toEuclideanLin_of_conjTranspose_mul_eq_one
  rw [setting.placeBoth_conjTranspose, setting.placeBoth_mul, alice_isometry, bob_isometry,
    setting.placeBoth_one_one]

end ProjectiveSetting

end

end MIPStarRE.QPBT
