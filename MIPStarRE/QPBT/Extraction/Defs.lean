import MIPStarRE.QPBT.Observables.ExpandedDefs

/-!
# Extraction foundations

This module defines the register identifications used to pull the Pauli
measurements apart. It retains the distinct local spaces of a
heterogeneous strategy, coarse-grains the generalized Pauli projectors by a
dot product, and records the state and error expressions needed by the later
extraction witness.

The binary phases use the existing `phaseSign`; the fixed field basis remains
the basis stored in `P.model` and is not re-quantified here.

## References

The Pauli dot-product projectors formalize blueprint
`def:tau-dot-product-projector`, from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1426-1429`.
The register and state helpers support blueprint `def:tilde-m-measurement`,
`def:v-swap-unitary`, and `lem:qld-unitary`, from paper lines 1429-1435 and
1666-1713.
-/

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum

noncomputable section

/-! ## Heterogeneous extraction registers -/

/-- One player's registers after adjoining the two generalized-Pauli
registers: `AA'A''` or `BB'B''`. This identifies the register order and spaces for
paper `14_analysis_of_the_pauli_basis_test.tex:1429-1435,1687-1713` and
blueprint `def:tilde-m-measurement` and `def:v-swap-unitary`. -/
abbrev ExtractionBlock (P : AdmissibleParams) (ι : Type*) :=
  (ι × PauliRegister P) × PauliRegister P

/-- The two heterogeneous extraction blocks in the order
`AA'A'' | BB'B''`. This is the block presentation of the existing `SixReg`
space used in blueprint
`lem:qld-unitary`, paper
`14_analysis_of_the_pauli_basis_test.tex:1666-1685`. -/
abbrev ExtractionRegisters (P : AdmissibleParams) (ιA ιB : Type*) :=
  ExtractionBlock P ιA × ExtractionBlock P ιB

/-- The auxiliary registers `AA'BB'` occurring before the extracted EPR
factor in blueprint `lem:qld-unitary`,
paper `14_analysis_of_the_pauli_basis_test.tex:1666-1685`. -/
abbrev ExtractionAuxRegisters (P : AdmissibleParams) (ιA ιB : Type*) :=
  (ιA × PauliRegister P) × (ιB × PauliRegister P)

/-- Reassociate the six-register order with the two extraction blocks.
This equivalence identifies the register order in paper
`14_analysis_of_the_pauli_basis_test.tex:1429-1435,1687-1713`. -/
def sixRegExtractionEquiv (P : AdmissibleParams) (ιA ιB : Type*) :
    SixReg P ιA ιB ≃ ExtractionRegisters P ιA ιB where
  toFun p := (((p.1.1, p.1.2.1), p.1.2.2),
    ((p.2.1, p.2.2.1), p.2.2.2))
  invFun p := ((p.1.1.1, (p.1.1.2, p.1.2)),
    (p.2.1.1, (p.2.1.2, p.2.2)))
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

/-- Shuffle `AA'BB' | A''B''` into the six-register order. This equivalence
places the ideal state in the order used in blueprint
`lem:qld-unitary`, paper
`14_analysis_of_the_pauli_basis_test.tex:1666-1685`. -/
def extractionIdealShuffle (P : AdmissibleParams) (ιA ιB : Type*) :
    (ExtractionAuxRegisters P ιA ιB ×
      (PauliRegister P × PauliRegister P)) ≃ SixReg P ιA ιB where
  toFun p := ((p.1.1.1, (p.1.1.2, p.2.1)),
    (p.1.2.1, (p.1.2.2, p.2.2)))
  invFun p := (((p.1.1, p.1.2.1), (p.2.1, p.2.2.1)),
    (p.1.2.2, p.2.2.2))
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

/-- Place an operator on one complete extraction block, with the identity on
the other player's block, as in the side-qualified operators of paper
`14_analysis_of_the_pauli_basis_test.tex:1429-1435,1687-1713`. -/
noncomputable def placeSide (S : ProjectiveSetting P ε) (side : PlayerSide)
    (O : Op (ExtractionBlock P (S.LocalSpace side))) :
    Op (SixReg P S.toStrategy.ιA S.toStrategy.ιB) := by
  cases side with
  | alice =>
      exact reindexOp
        (sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB)
        (heteroKron O 1)
  | bob =>
      exact reindexOp
        (sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB)
        (heteroKron 1 O)

/-- Lift an operator on a player's original strategy register to that player's
full extraction block. This places the Pauli and point measurements appearing
in blueprint `lem:qld-construct-the-paulis` and `lem:qld-unitary`. -/
noncomputable def onPlayer (S : ProjectiveSetting P ε) (side : PlayerSide)
    (O : Op (S.LocalSpace side)) :
    Op (ExtractionBlock P (S.LocalSpace side)) :=
  heteroKron (heteroKron O 1) 1

/-- Place an operator on the original strategy register of the selected
player. This is the player-side placement used in blueprint
`lem:qld-unitary`. -/
noncomputable def placePlayer (S : ProjectiveSetting P ε) (side : PlayerSide)
    (O : Op (S.LocalSpace side)) :
    Op (SixReg P S.toStrategy.ιA S.toStrategy.ιB) := by
  cases side with
  | alice => exact S.place .AA' (heteroKron O 1)
  | bob => exact S.place .BB' (heteroKron O 1)

/-- Place an operator on the selected extracted register `A''` or `B''`.
The unused strategy register in the crossed placement is assigned the
identity. This is the placement of the ideal Pauli operators in
blueprint `lem:qld-unitary`, paper
`14_analysis_of_the_pauli_basis_test.tex:1666-1685`. -/
noncomputable def placeExtractedRegister (S : ProjectiveSetting P ε)
    (side : PlayerSide) (O : Op (PauliRegister P)) :
    Op (SixReg P S.toStrategy.ιA S.toStrategy.ιB) := by
  cases side with
  | alice =>
      exact S.place .BA'' (heteroKron (1 : Op S.toStrategy.ιB) O)
  | bob =>
      exact S.place .AB'' (heteroKron (1 : Op S.toStrategy.ιA) O)

/-- Place a pair of block operators simultaneously on `AA'A''` and
`BB'B''`. This is the simultaneous placement used for the transformed state in
blueprint `lem:qld-unitary`, paper
`14_analysis_of_the_pauli_basis_test.tex:1666-1685`. -/
noncomputable def placeBoth (S : ProjectiveSetting P ε)
    (VA : Op (ExtractionBlock P S.toStrategy.ιA))
    (VB : Op (ExtractionBlock P S.toStrategy.ιB)) :
    Op (SixReg P S.toStrategy.ιA S.toStrategy.ιB) :=
  reindexOp (sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB)
    (heteroKron VA VB)

/-- Apply one operator to each heterogeneous extraction block. This is the
witness-independent state transformation used for `V_A tensor V_B` in
blueprint `lem:qld-unitary`, paper
`14_analysis_of_the_pauli_basis_test.tex:1666-1685`. -/
noncomputable def applyBoth (S : ProjectiveSetting P ε)
    (VA : Op (ExtractionBlock P S.toStrategy.ιA))
    (VB : Op (ExtractionBlock P S.toStrategy.ιB))
    (ψ : EuclideanSpace ℂ
      (SixReg P S.toStrategy.ιA S.toStrategy.ιB)) :
    EuclideanSpace ℂ (SixReg P S.toStrategy.ιA S.toStrategy.ιB) :=
  applyOperatorToState (S.placeBoth VA VB) ψ

/-- The state `aux tensor EPR_q^{tensor M}` in the six-register order.
This is the ideal state in Item 1 of blueprint
`lem:qld-unitary`, paper
`14_analysis_of_the_pauli_basis_test.tex:1666-1685`. -/
noncomputable def idealExpState (S : ProjectiveSetting P ε)
    (aux : EuclideanSpace ℂ
      (ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB)) :
    EuclideanSpace ℂ (SixReg P S.toStrategy.ιA S.toStrategy.ιB) := by
  classical
  exact
    reindexState (extractionIdealShuffle P S.toStrategy.ιA S.toStrategy.ιB)
      (vecTensor aux (eprState (PauliRegister P)))

end ProjectiveSetting

/-! ## Coarse-grained Pauli projectors -/

/-- Coarse-grain a finite operator family along a map of outcomes. This is the
operator-valued sum corresponding to `Measurement.postprocess`, used by
blueprint
`def:tau-dot-product-projector`. -/
noncomputable def bracketOp {α β ι : Type*} [Fintype α] [DecidableEq β]
    (N : α → Op ι) (f : α → β) (b : β) : Op ι :=
  ∑ a ∈ Finset.univ.filter (fun a => f a = b), N a

/-- The effect of a postprocessed measurement is the corresponding
coarse-grained operator sum. This equality is used by blueprint `def:bracket`
and `def:tau-dot-product-projector`. -/
theorem postprocess_effect_eq_bracketOp {α β ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype ι] [DecidableEq ι] (M : Measurement α ι) (f : α → β) (b : β) :
    (M.postprocess f).effect b = bracketOp M.effect f b :=
  rfl

/-- The projector obtained by measuring in basis `W` and retaining outcomes
whose dot product with `u` is `a`. This is Equation `eq:def-tauwu` in
blueprint
`def:tau-dot-product-projector`, paper
`14_analysis_of_the_pauli_basis_test.tex:1426-1429`. -/
noncomputable def tauDotProj {P : AdmissibleParams} (W : PauliKind)
    (u : PauliRegister P) (a : PauliScalar P) : Op (PauliRegister P) :=
  bracketOp (pauliProj W) (fun h => dotProduct h u) a

/-- Each dot-product coarse-graining is a projector, as asserted in
blueprint
`lem:tau-dot-product-projective`, paper
`14_analysis_of_the_pauli_basis_test.tex:1426-1429`.

Completeness makes the matrix of Pauli basis vectors unitary. The coarse-grained
operator is the conjugate of the diagonal projector onto the specified outcomes. -/
theorem tauDotProj_isProj {P : AdmissibleParams} (W : PauliKind)
    (u : PauliRegister P) (a : PauliScalar P) :
    IsProj (tauDotProj W u a) := by
  classical
  let basisMatrix : Op (PauliRegister P) := fun row label => pauliVec W label row
  have hbasis : basisMatrix * basisMatrixᴴ = 1 := by
    calc
      basisMatrix * basisMatrixᴴ = ∑ label : PauliRegister P, pauliProj W label := by
        ext row column
        simp [basisMatrix, Matrix.mul_apply, pauliProj, Matrix.sum_apply,
          Matrix.vecMulVec_apply]
      _ = 1 := sum_pauliProj_eq_one W
  let diagonalProj : Op (PauliRegister P) :=
    Matrix.diagonal (fun label => if dotProduct label u = a then (1 : ℂ) else 0)
  have hdiagonal : IsProj diagonalProj := by
    constructor
    · change Matrix.diagonal _ * Matrix.diagonal _ = Matrix.diagonal _
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      funext label
      split_ifs <;> simp
    · change diagonalProjᴴ = diagonalProj
      simp [diagonalProj, Matrix.diagonal_conjTranspose]
  have hcoarse : tauDotProj W u a = basisMatrix * diagonalProj * basisMatrixᴴ := by
    ext row column
    simp only [tauDotProj, bracketOp, Matrix.sum_apply, pauliProj, Matrix.vecMulVec_apply]
    rw [Matrix.mul_apply]
    simp only [diagonalProj, Matrix.mul_diagonal]
    simp [basisMatrix, Finset.sum_filter, mul_ite, ite_mul]
  rw [hcoarse]
  exact hdiagonal.map (Unitary.conjStarAlgAut ℂ (Op (PauliRegister P))
    ⟨basisMatrix, Matrix.mem_unitaryGroup_iff.mpr hbasis⟩)

/-- For fixed `W` and `u`, the dot-product projectors sum to the identity.
This is the completeness assertion of blueprint
`lem:tau-dot-product-projective`, paper
`14_analysis_of_the_pauli_basis_test.tex:1426-1429`.

The dot-product fibers partition the complete Pauli outcome family. -/
theorem sum_tauDotProj_eq_one {P : AdmissibleParams} (W : PauliKind)
    (u : PauliRegister P) :
    ∑ a : PauliScalar P, tauDotProj W u a = 1 := by
  classical
  unfold tauDotProj bracketOp
  rw [Finset.sum_fiberwise]
  exact sum_pauliProj_eq_one W

/-! ## Conjugation and extraction error -/

/-- Conjugation of an operator by a square matrix, as used in the exact
conjugation equations in blueprint
`lem:v-swap-conjugation`, paper
`14_analysis_of_the_pauli_basis_test.tex:1687-1713`. -/
noncomputable def conjBy {ι : Type*} [Fintype ι]
    (V N : Op ι) : Op ι :=
  V * N * Vᴴ

/-- The common error scale for constructing the pulled-apart measurements from
a global polynomial-pair witness. Here `deltaG` is its consistency error. The
remaining terms record the point-measurement transfer
and the Schwartz--Zippel loss; when `0 ≤ epsilon ≤ 1`, `sqrt epsilon` also
dominates terms of order `epsilon`.

This makes explicit the enlargement of the error called `deltaS` in
blueprint
`lem:qld-construct-the-paulis`, paper
`14_analysis_of_the_pauli_basis_test.tex:1458-1605`. -/
noncomputable def deltaConstructPaulis (C epsilon deltaG : ℝ)
    (m d q : ℕ) : ℝ :=
  C * (deltaG + Real.sqrt epsilon +
    ((m * d : ℕ) : ℝ) / (q : ℝ))

/-- The explicit extraction scale
`C * (deltaS^(1/4) + md/q)` from blueprint
`lem:qld-unitary`, paper
`14_analysis_of_the_pauli_basis_test.tex:1666-1685`. -/
noncomputable def deltaExtract (C deltaS : ℝ) (m d q : ℕ) : ℝ :=
  C * (Real.rpow deltaS (1 / 4 : ℝ) + ((m * d : ℕ) : ℝ) / (q : ℝ))

end

end MIPStarRE.QPBT
