import MIPStarRE.QPBT.Observables.WinImplications.Consistency

/-!
# Interchange of the tensor factors in the winning implications

This module collects the statements shared by the operator-distance companions
of the winning implications and by their factor-interchanged forms: transport of
the state-dependent distance along the interchange of the two tensor factors,
the constant-factor passage from consistency to distance, the reversed
verifier edges, and the clause-by-clause symmetry of the Pauli win predicate
on the ordered type pairs that the implications use.

## References

The declarations support the trailing clause of `lem:qld-win-implications` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:616-706`. Their paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:192-267`,
whose closing sentences at lines 227 and 263-264 state both companions.
-/

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace WinImplications

/-! ## Transport of the distance functional along the factor interchange -/

/-- The identity operator acts trivially on a state. Formalization-only support
for `def:strategy-observables`, blueprint `ch14_qpbt_observables.tex:573-610`.
`MagicSquareRigidity.applyOperatorToState_one` states the same identity; that
module is not in the import closure of this file, so the copy is kept here.
Consolidating the two is issue #204. -/
theorem applyOperatorToState_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) : applyOperatorToState (1 : Op ι) ψ = ψ := by
  ext i
  simp [applyOperatorToState]

/-- Reindexing an operator is computed entrywise, hence commutes with
subtraction. Formalization-only support for the interchanged conclusions of
`lem:qld-win-implications`, blueprint `ch14_qpbt_observables.tex:701-703`. -/
theorem reindexOp_sub {ι ι' : Type*} (e : ι ≃ ι') (M N : Op ι') :
    reindexOp e (M - N) = reindexOp e M - reindexOp e N := rfl

/-- Interchanging the two tensor factors turns a Kronecker product into the
product of the exchanged factors. Formalization-only support for the
interchanged conclusions of `lem:qld-win-implications`, blueprint
`ch14_qpbt_observables.tex:701-703`. -/
theorem reindexOp_prodComm_heteroKron {ιA ιB : Type*}
    (A : Op ιA) (B : Op ιB) :
    reindexOp (Equiv.prodComm ιA ιB) (heteroKron B A) = heteroKron A B := by
  ext i j
  simp [reindexOp, heteroKron, Matrix.kronecker, Matrix.kroneckerMap,
    Matrix.reindex_apply, mul_comm]

/-- Coordinates of an operator applied to a reindexed state. Formalization-only
support for the interchanged conclusions of `lem:qld-win-implications`,
blueprint `ch14_qpbt_observables.tex:701-703`. -/
theorem applyOperatorToState_reindexState_ofLp {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (T : Op κ) (ψ : EuclideanSpace ℂ ι) (k : κ) :
    (applyOperatorToState T (reindexState e ψ)).ofLp k =
      (applyOperatorToState (reindexOp e T) ψ).ofLp (e.symm k) := by
  change (T *ᵥ (reindexState e ψ).ofLp) k = (reindexOp e T *ᵥ ψ.ofLp) (e.symm k)
  rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct,
    ← e.sum_comp (fun l : κ => T k l * (reindexState e ψ).ofLp l)]
  apply Finset.sum_congr rfl
  intro j _
  simp [reindexState, reindexOp]

/-- Reindexing a state and its operator preserves the length of the image.
Formalization-only support for the interchanged conclusions of
`lem:qld-win-implications`, blueprint `ch14_qpbt_observables.tex:701-703`. -/
theorem norm_applyOperatorToState_reindexState {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (T : Op κ) (ψ : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState T (reindexState e ψ)‖ =
      ‖applyOperatorToState (reindexOp e T) ψ‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    ← e.symm.sum_comp (fun i : ι =>
      ‖(applyOperatorToState (reindexOp e T) ψ).ofLp i‖ ^ 2)]
  apply Finset.sum_congr rfl
  intro k _
  rw [applyOperatorToState_reindexState_ofLp]

/-- The state-dependent distance of two oppositely placed operator families is
unchanged by interchanging the tensor factors of both the families and the
state. Formalization-only support for the interchanged clause of
`lem:qld-win-implications`, blueprint `ch14_qpbt_observables.tex:699-701`,
paper `14_analysis_of_the_pauli_basis_test.tex:227`. -/
theorem opFamilyDistSq_swappedState {X α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : Distribution X) (M : X → α → Op ιA) (N : X → α → Op ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    opFamilyDistSq μ (fun x a => heteroKron (N x a) 1)
        (fun x a => heteroKron 1 (M x a))
        (reindexState (Equiv.prodComm ιA ιB) ψ) =
      opFamilyDistSq μ (fun x a => heteroKron (M x a) 1)
        (fun x a => heteroKron 1 (N x a)) ψ := by
  unfold opFamilyDistSq avgOver
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [norm_applyOperatorToState_reindexState]
  have hop : reindexOp (Equiv.prodComm ιA ιB)
      (heteroKron (N x a) 1 - heteroKron 1 (M x a)) =
      -(heteroKron (M x a) 1 - heteroKron 1 (N x a)) := by
    rw [reindexOp_sub, reindexOp_prodComm_heteroKron,
      reindexOp_prodComm_heteroKron, neg_sub]
  rw [hop]
  simp only [applyOperatorToState, map_neg, LinearMap.neg_apply, norm_neg]

/-- Consistency bounds the state-dependent distance of two oppositely placed
measurement families. This is the first item of `fact:agreement`, blueprint
`ch12_qpbt_games.tex:260-276`, in the placed form used by the trailing clause
of `lem:qld-win-implications`, blueprint `ch14_qpbt_observables.tex:699-701`,
paper `14_analysis_of_the_pauli_basis_test.tex:263-264`. -/
theorem opFamilyDistSq_placed_le_two_mul_consistencyDefect
    {X α ιA ιB : Type*} [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : Distribution X) (A : X → Measurement α ιA) (B : X → Measurement α ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    opFamilyDistSq μ (fun x a => heteroKron ((A x).effect a) 1)
        (fun x a => heteroKron 1 ((B x).effect a)) ψ ≤
      2 * consistencyDefect μ (fun x a => heteroKron ((A x).effect a) 1)
        (fun x a => heteroKron 1 ((B x).effect a)) ψ :=
  opFamilyDistSq_le_two_mul_consistencyDefect μ
    (fun x => DistanceCalculus.leftPlacedMeasurement (A x))
    (fun x => DistanceCalculus.rightPlacedMeasurement (B x)) ψ

/-- Consistency at level `c` gives operator distance at level `2 * c` for two
oppositely placed measurement families. This is the quantitative form of
`fact:agreement`, blueprint `ch12_qpbt_games.tex:260-276`, used by the trailing
clause of `lem:qld-win-implications`, blueprint
`ch14_qpbt_observables.tex:699-701`, paper
`14_analysis_of_the_pauli_basis_test.tex:263-264`. -/
theorem opFamilyDistSq_placed_le_of_consistencyDefect_le
    {X α ιA ιB : Type*} [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : Distribution X) (A : X → Measurement α ιA) (B : X → Measurement α ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) {c : ℝ}
    (h : consistencyDefect μ (fun x a => heteroKron ((A x).effect a) 1)
      (fun x a => heteroKron 1 ((B x).effect a)) ψ ≤ c) :
    opFamilyDistSq μ (fun x a => heteroKron ((A x).effect a) 1)
      (fun x a => heteroKron 1 ((B x).effect a)) ψ ≤ 2 * c := by
  have hstep := opFamilyDistSq_placed_le_two_mul_consistencyDefect μ A B ψ
  linarith

/-! ## Reversed verifier edges

The Pauli type graph is a set of unordered pairs, so every ordered edge used by
the exact implications has its reverse in the graph. The reversed edges carry
the interchanged conclusions of `lem:qld-win-implications`, blueprint
`ch14_qpbt_observables.tex:701-703`. -/

/-- The point/axis-line verifier edge, reversing `alinePointEdge`. -/
def pointAlineEdge (W : PauliKind) : PauliEdge :=
  ⟨(.point W, .aline W), by simp [pauliEdges]⟩

/-- The point/diagonal-line verifier edge, reversing `dlinePointEdge`. -/
def pointDlineEdge (W : PauliKind) : PauliEdge :=
  ⟨(.point W, .dline W), by simp [pauliEdges]⟩

/-- The Pauli/point verifier edge, reversing `pointPauliEdge`. -/
def pauliPointEdge (W : PauliKind) : PauliEdge :=
  ⟨(.pauli W, .point W), by simp [pauliEdges]⟩

/-- The Pair/Pair-W verifier edge, reversing `pairWPairEdge`. -/
def pairPairWEdge (W : PauliKind) : PauliEdge :=
  ⟨(.pair, .pairW W), by simp [pauliEdges]⟩

/-- The Pair-W/point verifier edge, reversing `pointPairWEdge`. -/
def pairWPointEdge (W : PauliKind) : PauliEdge :=
  ⟨(.pairW W, .point W), by simp [pauliEdges]⟩

/-- The variable/point verifier edge, reversing `pointMsImplicationEdge`. -/
def msVarPointEdge : PauliKind → PauliEdge
  | .X => ⟨(.ms (.var 0), .point .X), by simp [pauliEdges]⟩
  | .Z => ⟨(.ms (.var 4), .point .Z), by simp [pauliEdges]⟩

/-! ## Symmetry of the win predicate on the subtests used here

`def:pauli-win-predicate` lists every clause together with its mirror image, so
on each ordered type pair occurring in `lem:qld-win-implications` exchanging the
two questions and the two answers leaves the predicate unchanged. Paper
`08_classical_and_quantum_low_degree_tests.tex:1126-1225`, blueprint
`ch13_qpbt_test.tex:410-449`. -/

/-- Point/axis-line clause symmetry. -/
theorem win_symm_point_aline (P : AdmissibleParams) (W : PauliKind)
    (x y : PauliSpace P) (A B : PauliAnswer P) :
    pauliWinPredicate P (.point W, x) (.aline W, y) A B =
      pauliWinPredicate P (.aline W, y) (.point W, x) B A := by
  cases A <;> cases B <;>
    simp [pauliWinPredicate, validPauliAnswer, eq_comm]

/-- Point/diagonal-line clause symmetry. -/
theorem win_symm_point_dline (P : AdmissibleParams) (W : PauliKind)
    (x y : PauliSpace P) (A B : PauliAnswer P) :
    pauliWinPredicate P (.point W, x) (.dline W, y) A B =
      pauliWinPredicate P (.dline W, y) (.point W, x) B A := by
  cases A <;> cases B <;>
    simp [pauliWinPredicate, validPauliAnswer, eq_comm]

/-- Pauli/point clause symmetry. -/
theorem win_symm_pauli_point (P : AdmissibleParams) (W : PauliKind)
    (x y : PauliSpace P) (A B : PauliAnswer P) :
    pauliWinPredicate P (.pauli W, x) (.point W, y) A B =
      pauliWinPredicate P (.point W, y) (.pauli W, x) B A := by
  cases A <;> cases B <;>
    simp [pauliWinPredicate, validPauliAnswer, eq_comm]

/-- Pair/Pair-W clause symmetry. -/
theorem win_symm_pair_pairW (P : AdmissibleParams) (W : PauliKind)
    (x y : PauliSpace P) (A B : PauliAnswer P) :
    pauliWinPredicate P (.pair, x) (.pairW W, y) A B =
      pauliWinPredicate P (.pairW W, y) (.pair, x) B A := by
  cases A <;> cases B <;>
    simp [pauliWinPredicate, validPauliAnswer, eq_comm]

/-- Pair-W/point clause symmetry. -/
theorem win_symm_pairW_point (P : AdmissibleParams) (W : PauliKind)
    (x y : PauliSpace P) (A B : PauliAnswer P) :
    pauliWinPredicate P (.pairW W, x) (.point W, y) A B =
      pauliWinPredicate P (.point W, y) (.pairW W, x) B A := by
  cases A <;> cases B <;>
    simp [pauliWinPredicate, validPauliAnswer, eq_comm]

/-- Variable/point clause symmetry. -/
theorem win_symm_msvar_point (P : AdmissibleParams) (W : PauliKind)
    (j : Fin 9) (x y : PauliSpace P) (A B : PauliAnswer P) :
    pauliWinPredicate P (.ms (.var j), x) (.point W, y) A B =
      pauliWinPredicate P (.point W, y) (.ms (.var j), x) B A := by
  cases A <;> cases B <;>
    simp [pauliWinPredicate, validPauliAnswer, eq_comm]

/-! ## Numeric bookkeeping -/

/-- Enlarging the constant of a distance bound proved with the first of two
admissible constants. Formalization-only support for the trailing clause of
`lem:qld-win-implications`, blueprint `ch14_qpbt_observables.tex:699-701`. -/
theorem approxBound_of_left {C₁ C₂ ε x : ℝ} (hC₂ : 1 ≤ C₂) (hε : 0 ≤ ε)
    (h : x ≤ 2 * (C₁ * ε)) : x ≤ 2 * (C₁ + C₂) * ε := by
  nlinarith

/-- Enlarging the constant of a distance bound proved with the second of two
admissible constants. Formalization-only support for the trailing clause of
`lem:qld-win-implications`, blueprint `ch14_qpbt_observables.tex:699-701`. -/
theorem approxBound_of_right {C₁ C₂ ε x : ℝ} (hC₁ : 1 ≤ C₁) (hε : 0 ≤ ε)
    (h : x ≤ 2 * (C₂ * ε)) : x ≤ 2 * (C₁ + C₂) * ε := by
  nlinarith

end WinImplications

end

end MIPStarRE.QPBT
