import MIPStarRE.QPBT.Observables.ExpandedDefs
import MIPStarRE.QPBT.Observables.WinImplications

/-!
# Placing operators on the expanded state

The four register placements of `def:symmetric-equivalents` put an operator of
one player's expanded local space on one of the register pairs `AA'`, `BA''`,
`BB'` and `AB''` of the expanded state `psiHat`.  This module records how such
a placement acts on `psiHat`: after the shuffle of `eq:def-psihat` the placed
operator is a threefold tensor product, so a factorized operator whose Pauli
factor is an isometry has the same state-dependent norm as its strategy factor
placed on the original state.  No symmetry between the two players is used;
each of the four placements is treated explicitly.

## References

The declarations support `def:symmetric-equivalents` and `lem:qld-comm-cons`
in `blueprint/src/chapter/ch14_qpbt_observables.tex:876-922` and
`blueprint/src/chapter/ch14_qpbt_observables.tex:932-1032`.  Their paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:420-505`.
-/

-- The unshuffled six-register index type of `eq:def-psihat` is a fourfold
-- iterated product; instance search for its `Fintype` and `DecidableEq`
-- structure needs a larger budget than the default.
set_option synthInstance.maxSize 400
set_option synthInstance.maxHeartbeats 1000000

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-! ## Coordinate tensors -/

/-- The coordinate tensor of two vectors has the product norm.
Formalization-only support for `def:expanded-state`, blueprint
`ch14_qpbt_observables.tex:760-781`. -/
theorem norm_vecTensor {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (u : EuclideanSpace ℂ ι) (v : EuclideanSpace ℂ κ) :
    ‖vecTensor u v‖ = ‖u‖ * ‖v‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp ?_
  rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  show ‖u.ofLp i * v.ofLp j‖ ^ 2 = ‖u.ofLp i‖ ^ 2 * ‖v.ofLp j‖ ^ 2
  rw [norm_mul, mul_pow]

/-- A Kronecker product of operators acts factorwise on a coordinate tensor.
Formalization-only support for `def:expanded-state`, blueprint
`ch14_qpbt_observables.tex:760-781`. -/
theorem applyOperatorToState_heteroKron_vecTensor {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Op ι) (B : Op κ) (u : EuclideanSpace ℂ ι) (v : EuclideanSpace ℂ κ) :
    applyOperatorToState (heteroKron A B) (vecTensor u v) =
      vecTensor (applyOperatorToState A u) (applyOperatorToState B v) := by
  classical
  ext p
  obtain ⟨i, j⟩ := p
  show (Matrix.mulVec (heteroKron A B) (vecTensor u v).ofLp) (i, j) =
    (Matrix.mulVec A u.ofLp) i * (Matrix.mulVec B v.ofLp) j
  rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.mulVec,
    Matrix.mulVec, dotProduct, dotProduct, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro l _
  show heteroKron A B (i, j) (k, l) * (vecTensor u v).ofLp (k, l) =
    A i k * u.ofLp k * (B j l * v.ofLp l)
  show A i k * B j l * (u.ofLp k * v.ofLp l) =
    A i k * u.ofLp k * (B j l * v.ofLp l)
  ring

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

/-! ## The strategy factor of a placement -/

/-- Place a strategy-local operator on the player side that supplies the local
space of a register placement. Paper
`14_analysis_of_the_pauli_basis_test.tex:420-450`, blueprint
`ch14_qpbt_observables.tex:876-922`. -/
noncomputable def placeStrategySide (S : ProjectiveSetting P ε) :
    (side : PlayerSide) → Op (S.LocalSpace side) →
      Op (S.toStrategy.ιA × S.toStrategy.ιB)
  | .alice, T => heteroKron T 1
  | .bob, T => heteroKron 1 T

/-- The placement of a difference is the difference of the placements. Paper
`14_analysis_of_the_pauli_basis_test.tex:420-450`, blueprint
`ch14_qpbt_observables.tex:876-922`. -/
theorem place_sub (S : ProjectiveSetting P ε) (p : Placement)
    (O₁ O₂ : Op (S.ExpandedLocalSpace p.side)) :
    S.place p (O₁ - O₂) = S.place p O₁ - S.place p O₂ := by
  ext i j
  cases p <;> simp only [place, Matrix.sub_apply, sub_mul, mul_sub]

/-! ## The action of a placement on the expanded state -/

/-- The expanded state is the shuffle of the coordinate tensor of the strategy
state with the two EPR ancillas. This is `eq:def-psihat`, paper
`14_analysis_of_the_pauli_basis_test.tex:367-372`, blueprint
`ch14_qpbt_observables.tex:760-781`. -/
theorem psiHat_eq_reindexState (S : ProjectiveSetting P ε) :
    S.psiHat = reindexState (sixRegShuffle P S.toStrategy.ιA S.toStrategy.ιB)
      (vecTensor (vecTensor S.toStrategy.ψ (eprState (PauliRegister P)))
        (eprState (PauliRegister P))) := rfl

/-! ## The four placements -/

/-- Placing a factorized operator on the register pair `AA'`. Paper
`14_analysis_of_the_pauli_basis_test.tex:420-450`, blueprint
`ch14_qpbt_observables.tex:876-922`. -/
theorem norm_place_AA'_heteroKron_psiHat (S : ProjectiveSetting P ε)
    (T : Op S.toStrategy.ιA) (V : Op (PauliRegister P)) (hV : Vᴴ * V = 1) :
    ‖applyOperatorToState (S.place .AA' (heteroKron T V)) S.psiHat‖ =
      ‖applyOperatorToState
        (heteroKron T (1 : Op S.toStrategy.ιB)) S.toStrategy.ψ‖ := by
  classical
  have hop : reindexOp (sixRegShuffle P S.toStrategy.ιA S.toStrategy.ιB)
      (S.place .AA' (heteroKron T V)) =
      heteroKron (heteroKron (heteroKron T (1 : Op S.toStrategy.ιB))
          (heteroKron V (1 : Op (PauliRegister P))))
        (heteroKron (1 : Op (PauliRegister P))
          (1 : Op (PauliRegister P))) := by
    ext i j
    obtain ⟨⟨⟨iA, iB⟩, iA', iA''⟩, iB', iB''⟩ := i
    obtain ⟨⟨⟨jA, jB⟩, jA', jA''⟩, jB', jB''⟩ := j
    simp only [reindexOp, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_symm, place, sixRegShuffle, Equiv.coe_fn_mk, heteroKron,
      Matrix.kronecker, Matrix.kroneckerMap_apply]
    ring
  rw [psiHat_eq_reindexState,
    WinImplications.norm_applyOperatorToState_reindexState, hop,
    applyOperatorToState_heteroKron_vecTensor,
    applyOperatorToState_heteroKron_vecTensor, norm_vecTensor, norm_vecTensor,
    heteroKron_one_one, WinImplications.applyOperatorToState_one,
    WinImplications.norm_applyOperatorToState_of_isometry
      (WinImplications.heteroKron_left_isometry (ιB := PauliRegister P) V hV),
    eprState_norm]
  ring

/-- Placing a factorized operator on the register pair `BA''`. Paper
`14_analysis_of_the_pauli_basis_test.tex:420-450`, blueprint
`ch14_qpbt_observables.tex:876-922`. -/
theorem norm_place_BA''_heteroKron_psiHat (S : ProjectiveSetting P ε)
    (T : Op S.toStrategy.ιB) (V : Op (PauliRegister P)) (hV : Vᴴ * V = 1) :
    ‖applyOperatorToState (S.place .BA'' (heteroKron T V)) S.psiHat‖ =
      ‖applyOperatorToState
        (heteroKron (1 : Op S.toStrategy.ιA) T) S.toStrategy.ψ‖ := by
  classical
  have hop : reindexOp (sixRegShuffle P S.toStrategy.ιA S.toStrategy.ιB)
      (S.place .BA'' (heteroKron T V)) =
      heteroKron (heteroKron (heteroKron (1 : Op S.toStrategy.ιA) T)
          (heteroKron (1 : Op (PauliRegister P)) V))
        (heteroKron (1 : Op (PauliRegister P))
          (1 : Op (PauliRegister P))) := by
    ext i j
    obtain ⟨⟨⟨iA, iB⟩, iA', iA''⟩, iB', iB''⟩ := i
    obtain ⟨⟨⟨jA, jB⟩, jA', jA''⟩, jB', jB''⟩ := j
    simp only [reindexOp, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_symm, place, sixRegShuffle, Equiv.coe_fn_mk, heteroKron,
      Matrix.kronecker, Matrix.kroneckerMap_apply]
    ring
  rw [psiHat_eq_reindexState,
    WinImplications.norm_applyOperatorToState_reindexState, hop,
    applyOperatorToState_heteroKron_vecTensor,
    applyOperatorToState_heteroKron_vecTensor, norm_vecTensor, norm_vecTensor,
    heteroKron_one_one, WinImplications.applyOperatorToState_one,
    WinImplications.norm_applyOperatorToState_of_isometry
      (WinImplications.heteroKron_right_isometry (ιA := PauliRegister P) V hV),
    eprState_norm]
  ring

/-- Placing a factorized operator on the register pair `BB'`. Paper
`14_analysis_of_the_pauli_basis_test.tex:420-450`, blueprint
`ch14_qpbt_observables.tex:876-922`. -/
theorem norm_place_BB'_heteroKron_psiHat (S : ProjectiveSetting P ε)
    (T : Op S.toStrategy.ιB) (V : Op (PauliRegister P)) (hV : Vᴴ * V = 1) :
    ‖applyOperatorToState (S.place .BB' (heteroKron T V)) S.psiHat‖ =
      ‖applyOperatorToState
        (heteroKron (1 : Op S.toStrategy.ιA) T) S.toStrategy.ψ‖ := by
  classical
  have hop : reindexOp (sixRegShuffle P S.toStrategy.ιA S.toStrategy.ιB)
      (S.place .BB' (heteroKron T V)) =
      heteroKron (heteroKron (heteroKron (1 : Op S.toStrategy.ιA) T)
          (heteroKron (1 : Op (PauliRegister P))
            (1 : Op (PauliRegister P))))
        (heteroKron V (1 : Op (PauliRegister P))) := by
    ext i j
    obtain ⟨⟨⟨iA, iB⟩, iA', iA''⟩, iB', iB''⟩ := i
    obtain ⟨⟨⟨jA, jB⟩, jA', jA''⟩, jB', jB''⟩ := j
    simp only [reindexOp, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_symm, place, sixRegShuffle, Equiv.coe_fn_mk, heteroKron,
      Matrix.kronecker, Matrix.kroneckerMap_apply]
    ring
  rw [psiHat_eq_reindexState,
    WinImplications.norm_applyOperatorToState_reindexState, hop,
    applyOperatorToState_heteroKron_vecTensor,
    applyOperatorToState_heteroKron_vecTensor, norm_vecTensor, norm_vecTensor,
    heteroKron_one_one, WinImplications.applyOperatorToState_one,
    WinImplications.norm_applyOperatorToState_of_isometry
      (WinImplications.heteroKron_left_isometry (ιB := PauliRegister P) V hV),
    eprState_norm]
  ring

/-- Placing a factorized operator on the register pair `AB''`. Paper
`14_analysis_of_the_pauli_basis_test.tex:420-450`, blueprint
`ch14_qpbt_observables.tex:876-922`. -/
theorem norm_place_AB''_heteroKron_psiHat (S : ProjectiveSetting P ε)
    (T : Op S.toStrategy.ιA) (V : Op (PauliRegister P)) (hV : Vᴴ * V = 1) :
    ‖applyOperatorToState (S.place .AB'' (heteroKron T V)) S.psiHat‖ =
      ‖applyOperatorToState
        (heteroKron T (1 : Op S.toStrategy.ιB)) S.toStrategy.ψ‖ := by
  classical
  have hop : reindexOp (sixRegShuffle P S.toStrategy.ιA S.toStrategy.ιB)
      (S.place .AB'' (heteroKron T V)) =
      heteroKron (heteroKron (heteroKron T (1 : Op S.toStrategy.ιB))
          (heteroKron (1 : Op (PauliRegister P))
            (1 : Op (PauliRegister P))))
        (heteroKron (1 : Op (PauliRegister P)) V) := by
    ext i j
    obtain ⟨⟨⟨iA, iB⟩, iA', iA''⟩, iB', iB''⟩ := i
    obtain ⟨⟨⟨jA, jB⟩, jA', jA''⟩, jB', jB''⟩ := j
    simp only [reindexOp, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_symm, place, sixRegShuffle, Equiv.coe_fn_mk, heteroKron,
      Matrix.kronecker, Matrix.kroneckerMap_apply]
    ring
  rw [psiHat_eq_reindexState,
    WinImplications.norm_applyOperatorToState_reindexState, hop,
    applyOperatorToState_heteroKron_vecTensor,
    applyOperatorToState_heteroKron_vecTensor, norm_vecTensor, norm_vecTensor,
    heteroKron_one_one, WinImplications.applyOperatorToState_one,
    WinImplications.norm_applyOperatorToState_of_isometry
      (WinImplications.heteroKron_right_isometry (ιA := PauliRegister P) V hV),
    eprState_norm]
  ring

/-- A factorized operator placed on one of the four register pairs has, on the
expanded state, the state-dependent norm of its strategy factor on the original
state, provided its Pauli factor is an isometry. This is the placement
bookkeeping behind `lem:qld-comm-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:420-505`, blueprint
`ch14_qpbt_observables.tex:876-922`. -/
theorem norm_place_heteroKron_psiHat (S : ProjectiveSetting P ε)
    (p : Placement) (T : Op (S.LocalSpace p.side)) (V : Op (PauliRegister P))
    (hV : Vᴴ * V = 1) :
    ‖applyOperatorToState (S.place p (heteroKron T V)) S.psiHat‖ =
      ‖applyOperatorToState (S.placeStrategySide p.side T) S.toStrategy.ψ‖ := by
  cases p with
  | AA' => exact norm_place_AA'_heteroKron_psiHat S T V hV
  | BA'' => exact norm_place_BA''_heteroKron_psiHat S T V hV
  | BB' => exact norm_place_BB'_heteroKron_psiHat S T V hV
  | AB'' => exact norm_place_AB''_heteroKron_psiHat S T V hV

end ProjectiveSetting

end

end MIPStarRE.QPBT
