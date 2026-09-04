import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Questions
import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.SeedFiber

/-!
# Strategy transport for the directly indexed low-degree game

This module reads one coordinate of a projective directly indexed strategy as
a two-space mature low individual degree strategy.  The question and answer
transport of `Transport.Questions` supplies the canonical direct question of
every mature line, with the reversed coordinate order and the leading index
of the decoded diagonal direction, together with answer readouts that are
covariant under line rebasing; this establishes all four covariance
conditions of `ProjStrat`.  The module also records exact Born-weight
formulas for both directions of strategy transport.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-458`
- `references/ldt-paper/test_definition.tex:49-151`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.Quantum

noncomputable section

/-! ## From a direct strategy to a mature LDT strategy -/

/-- Regard a matrix-valued projective measurement as a projective measurement
in the mature LDT interface. -/
noncomputable def matrixMeasurementToLDTProjMeas
    {alpha iota : Type*} [Fintype alpha] [Fintype iota] [DecidableEq iota]
    (M : MIPStarRE.Quantum.Measurement alpha iota)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) :
    MIPStarRE.LDT.ProjMeas alpha iota where
  toMeasurement := {
    toSubMeas := {
      outcome := M.effect
      total := 1
      outcome_pos := M.pos
      sum_eq_total := M.sum_eq_one
      total_le_one := le_rfl
    }
    total_eq_one := rfl
  }
  proj a := (hM a).isIdempotentElem.eq

@[simp] theorem matrixMeasurementToLDTProjMeas_outcome
    {alpha iota : Type*} [Fintype alpha] [Fintype iota] [DecidableEq iota]
    (M : MIPStarRE.Quantum.Measurement alpha iota)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) (a : alpha) :
    (matrixMeasurementToLDTProjMeas M hM).outcome a = M.effect a :=
  rfl

/-- Point measurements obtained by querying the direct strategy and reading
one simultaneous coordinate. -/
noncomputable def directCoordinatePointMeasurement
    (D : DirectLdParams) (r : Fin D.k)
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (M : DirectLdQuestion D →
      MIPStarRE.Quantum.Measurement (DirectLdAnswer D) iota)
    (hM : ∀ q, MIPStarRE.QPBT.Measurement.IsProjective (M q)) :
    letI := D.toLDTFieldModel
    IdxProjMeas (Point D.toLDTParameters) (Fq D.toLDTParameters) iota := by
  letI := D.toLDTFieldModel
  intro u
  exact ProjMeas.postprocess
    (matrixMeasurementToLDTProjMeas (M (directPointQuestionOf D u))
      (hM (directPointQuestionOf D u)))
    (directPointAnswerReadout D r)

/-- Axis-line measurements obtained by querying the canonical direct line and
rebasing one coordinate polynomial to the mature line parametrization. -/
noncomputable def directCoordinateAxisMeasurement
    (D : DirectLdParams) (r : Fin D.k)
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (M : DirectLdQuestion D →
      MIPStarRE.Quantum.Measurement (DirectLdAnswer D) iota)
    (hM : ∀ q, MIPStarRE.QPBT.Measurement.IsProjective (M q)) :
    letI := D.toLDTFieldModel
    IdxProjMeas (AxisParallelLine D.toLDTParameters)
      (AxisLinePolynomial D.toLDTParameters) iota := by
  letI := D.toLDTFieldModel
  intro line
  exact ProjMeas.postprocess
    (matrixMeasurementToLDTProjMeas (M (directAxisQuestionOf D line))
      (hM (directAxisQuestionOf D line)))
    (directAxisAnswerReadout D r line)

/-- Diagonal-line measurements obtained by querying the canonical direct line
and rebasing one coordinate polynomial to the mature line parametrization. -/
noncomputable def directCoordinateDiagonalMeasurement
    (D : DirectLdParams) (r : Fin D.k)
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (M : DirectLdQuestion D →
      MIPStarRE.Quantum.Measurement (DirectLdAnswer D) iota)
    (hM : ∀ q, MIPStarRE.QPBT.Measurement.IsProjective (M q)) :
    letI := D.toLDTFieldModel
    IdxProjMeas (DiagonalLine D.toLDTParameters)
      (DiagonalLinePolynomial D.toLDTParameters) iota := by
  letI := D.toLDTFieldModel
  intro line
  exact ProjMeas.postprocess
    (matrixMeasurementToLDTProjMeas (M (directDiagonalQuestionOf D line))
      (hM (directDiagonalQuestionOf D line)))
    (directDiagonalAnswerReadout D r line)

/-- The coordinate axis-line family is independent of the chosen affine
parametrization of a mature line. -/
theorem directCoordinateAxisMeasurement_reparam
    (D : DirectLdParams) (r : Fin D.k)
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (M : DirectLdQuestion D →
      MIPStarRE.Quantum.Measurement (DirectLdAnswer D) iota)
    (hM : ∀ q, MIPStarRE.QPBT.Measurement.IsProjective (M q)) :
    letI := D.toLDTFieldModel
    AxisParallelMeasurementReparamInvariant D.toLDTParameters
      (directCoordinateAxisMeasurement D r M hM) := by
  letI := D.toLDTFieldModel
  classical
  intro line t f
  simp only [directCoordinateAxisMeasurement, ProjMeas.postprocess,
    SubMeas.postprocess_outcome, matrixMeasurementToLDTProjMeas_outcome]
  rw [directAxisQuestionOf_rebase]
  have hfiber :
      Finset.univ.filter (fun answer =>
        directAxisAnswerReadout D r (line.rebaseAt t) answer =
          AxisLinePolynomial.reparamAt f t) =
        Finset.univ.filter (fun answer =>
          directAxisAnswerReadout D r line answer = f) := by
    ext answer
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [directAxisAnswerReadout_rebase]
    exact (AxisLinePolynomial.reparamAtEquiv t).injective.eq_iff
  rw [hfiber]

/-- The coordinate diagonal-line family is independent of the chosen affine
parametrization, including the zero-direction convention. -/
theorem directCoordinateDiagonalMeasurement_reparam
    (D : DirectLdParams) (r : Fin D.k)
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (M : DirectLdQuestion D →
      MIPStarRE.Quantum.Measurement (DirectLdAnswer D) iota)
    (hM : ∀ q, MIPStarRE.QPBT.Measurement.IsProjective (M q)) :
    letI := D.toLDTFieldModel
    DiagonalMeasurementReparamInvariant D.toLDTParameters
      (directCoordinateDiagonalMeasurement D r M hM) := by
  letI := D.toLDTFieldModel
  classical
  intro line t f
  simp only [directCoordinateDiagonalMeasurement, ProjMeas.postprocess,
    SubMeas.postprocess_outcome, matrixMeasurementToLDTProjMeas_outcome]
  rw [directDiagonalQuestionOf_rebase]
  have hfiber :
      Finset.univ.filter (fun answer =>
        directDiagonalAnswerReadout D r (line.rebaseAt t) answer =
          DiagonalLinePolynomial.reparamAt f t) =
        Finset.univ.filter (fun answer =>
          directDiagonalAnswerReadout D r line answer = f) := by
    ext answer
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [directDiagonalAnswerReadout_rebase]
    exact (DiagonalLinePolynomial.reparamAtEquiv t).injective.eq_iff
  rw [hfiber]

private theorem strategy_carrier_nonempty {G : Game} (S : Strategy G) :
    Nonempty (S.ιA × S.ιB) := by
  by_contra h
  rw [not_nonempty_iff] at h
  letI := h
  have hzero : S.ψ = 0 := Subsingleton.elim _ _
  have hnorm := S.ψ_norm
  rw [hzero, norm_zero] at hnorm
  exact zero_ne_one hnorm

/-- The pure LDT state represented by a game's unit strategy vector. -/
noncomputable def strategyPureState {G : Game} (S : Strategy G)
    [Nonempty (S.ιA × S.ιB)] : PureState (S.ιA × S.ιB) where
  vector := S.ψ
  unit := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
      inner_self_eq_norm_sq_to_K, S.ψ_norm]
    norm_num

/-- The mature density-matrix state represented by a game's unit strategy
vector. -/
noncomputable def strategyQuantumState {G : Game} (S : Strategy G) :
    QuantumState (S.ιA × S.ιB) := by
  letI : Nonempty (S.ιA × S.ιB) := strategy_carrier_nonempty S
  exact PureState.toQuantumState (strategyPureState S)

/-- The density-matrix state associated with a game strategy is normalized. -/
theorem strategyQuantumState_isNormalized {G : Game} (S : Strategy G) :
    (strategyQuantumState S).IsNormalized := by
  letI : Nonempty (S.ιA × S.ιB) := strategy_carrier_nonempty S
  simpa [strategyQuantumState] using
    PureState.toQuantumState_isNormalized (strategyPureState S)

/-- The complex Born amplitude of a vector and two local effects. -/
private noncomputable def vectorBornAmplitude
    {iotaA iotaB : Type*}
    [Fintype iotaA] [DecidableEq iotaA]
    [Fintype iotaB] [DecidableEq iotaB]
    (psi : EuclideanSpace ℂ (iotaA × iotaB))
    (A : Op iotaA) (B : Op iotaB) : ℂ :=
  inner ℂ psi (applyOperatorToState (heteroKron A B) psi)

/-- The real Born quadratic form of a vector and two local effects. -/
private noncomputable def vectorBornWeight
    {iotaA iotaB : Type*}
    [Fintype iotaA] [DecidableEq iotaA]
    [Fintype iotaB] [DecidableEq iotaB]
    (psi : EuclideanSpace ℂ (iotaA × iotaB))
    (A : Op iotaA) (B : Op iotaB) : ℝ :=
  (vectorBornAmplitude psi A B).re

private theorem vectorBornAmplitude_add_left
    {iotaA iotaB : Type*}
    [Fintype iotaA] [DecidableEq iotaA]
    [Fintype iotaB] [DecidableEq iotaB]
    (psi : EuclideanSpace ℂ (iotaA × iotaB))
    (A₁ A₂ : Op iotaA) (B : Op iotaB) :
    vectorBornAmplitude psi (A₁ + A₂) B =
      vectorBornAmplitude psi A₁ B + vectorBornAmplitude psi A₂ B := by
  unfold vectorBornAmplitude applyOperatorToState heteroKron Matrix.kronecker
  rw [Matrix.add_kronecker]
  simp

private theorem vectorBornAmplitude_add_right
    {iotaA iotaB : Type*}
    [Fintype iotaA] [DecidableEq iotaA]
    [Fintype iotaB] [DecidableEq iotaB]
    (psi : EuclideanSpace ℂ (iotaA × iotaB))
    (A : Op iotaA) (B₁ B₂ : Op iotaB) :
    vectorBornAmplitude psi A (B₁ + B₂) =
      vectorBornAmplitude psi A B₁ + vectorBornAmplitude psi A B₂ := by
  unfold vectorBornAmplitude applyOperatorToState heteroKron Matrix.kronecker
  rw [Matrix.kronecker_add]
  simp

private theorem vectorBornAmplitude_zero_left
    {iotaA iotaB : Type*}
    [Fintype iotaA] [DecidableEq iotaA]
    [Fintype iotaB] [DecidableEq iotaB]
    (psi : EuclideanSpace ℂ (iotaA × iotaB)) (B : Op iotaB) :
    vectorBornAmplitude psi 0 B = 0 := by
  unfold vectorBornAmplitude applyOperatorToState heteroKron Matrix.kronecker
  rw [Matrix.zero_kronecker]
  simp

private theorem vectorBornAmplitude_zero_right
    {iotaA iotaB : Type*}
    [Fintype iotaA] [DecidableEq iotaA]
    [Fintype iotaB] [DecidableEq iotaB]
    (psi : EuclideanSpace ℂ (iotaA × iotaB)) (A : Op iotaA) :
    vectorBornAmplitude psi A 0 = 0 := by
  unfold vectorBornAmplitude applyOperatorToState heteroKron Matrix.kronecker
  rw [Matrix.kronecker_zero]
  simp

private theorem vectorBornWeight_add_left
    {iotaA iotaB : Type*}
    [Fintype iotaA] [DecidableEq iotaA]
    [Fintype iotaB] [DecidableEq iotaB]
    (psi : EuclideanSpace ℂ (iotaA × iotaB))
    (A₁ A₂ : Op iotaA) (B : Op iotaB) :
    vectorBornWeight psi (A₁ + A₂) B =
      vectorBornWeight psi A₁ B + vectorBornWeight psi A₂ B := by
  unfold vectorBornWeight
  rw [vectorBornAmplitude_add_left, Complex.add_re]

private theorem vectorBornWeight_add_right
    {iotaA iotaB : Type*}
    [Fintype iotaA] [DecidableEq iotaA]
    [Fintype iotaB] [DecidableEq iotaB]
    (psi : EuclideanSpace ℂ (iotaA × iotaB))
    (A : Op iotaA) (B₁ B₂ : Op iotaB) :
    vectorBornWeight psi A (B₁ + B₂) =
      vectorBornWeight psi A B₁ + vectorBornWeight psi A B₂ := by
  unfold vectorBornWeight
  rw [vectorBornAmplitude_add_right, Complex.add_re]

private theorem vectorBornWeight_finset_sum_left
    {alpha iotaA iotaB : Type*}
    [Fintype iotaA] [DecidableEq iotaA]
    [Fintype iotaB] [DecidableEq iotaB]
    (psi : EuclideanSpace ℂ (iotaA × iotaB))
    (s : Finset alpha) (A : alpha → Op iotaA) (B : Op iotaB) :
    vectorBornWeight psi (∑ a ∈ s, A a) B =
      ∑ a ∈ s, vectorBornWeight psi (A a) B := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [vectorBornWeight, vectorBornAmplitude_zero_left]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        vectorBornWeight_add_left, ih]

private theorem vectorBornWeight_finset_sum_right
    {beta iotaA iotaB : Type*}
    [Fintype iotaA] [DecidableEq iotaA]
    [Fintype iotaB] [DecidableEq iotaB]
    (psi : EuclideanSpace ℂ (iotaA × iotaB))
    (A : Op iotaA) (s : Finset beta) (B : beta → Op iotaB) :
    vectorBornWeight psi A (∑ b ∈ s, B b) =
      ∑ b ∈ s, vectorBornWeight psi A (B b) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [vectorBornWeight, vectorBornAmplitude_zero_right]
  | @insert b s hb ih =>
      rw [Finset.sum_insert hb, Finset.sum_insert hb,
        vectorBornWeight_add_right, ih]

/-- Expectations in the density state associated with a strategy agree with
the strategy's vector Born quadratic form. -/
private theorem strategyQuantumState_ev_eq_vectorBornWeight
    {G : Game} (S : Strategy G) (A : Op S.ιA) (B : Op S.ιB) :
    ev (strategyQuantumState S) (opTensor A B) =
      vectorBornWeight S.ψ A B := by
  letI : Nonempty (S.ιA × S.ιB) := strategy_carrier_nonempty S
  rw [show strategyQuantumState S =
      PureState.toQuantumState (strategyPureState S) by
        simp [strategyQuantumState],
    PureState.ev_eq_re_inner]
  unfold vectorBornWeight vectorBornAmplitude applyOperatorToState heteroKron opTensor
  simp_rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (star S.ψ ⬝ᵥ
      (Matrix.kronecker A B *ᵥ S.ψ)).re =
    ((Matrix.kronecker A B *ᵥ S.ψ) ⬝ᵥ star S.ψ).re
  rw [dotProduct_comm]

/-- Postprocessing both local measurements gives the exact double sum of the
original Born weights over the two answer fibers. -/
theorem directPostprocessBornWeight
    (D : DirectLdParams) (S : Strategy (directLdGame D))
    (hS : S.IsProjective)
    {alpha beta : Type*} [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    (x y : DirectLdQuestion D)
    (readA : DirectLdAnswer D → alpha)
    (readB : DirectLdAnswer D → beta)
    (a : alpha) (b : beta) :
    ev (strategyQuantumState S)
        (opTensor
          ((ProjMeas.postprocess
            (matrixMeasurementToLDTProjMeas (S.A x) (hS.1 x)) readA).outcome a)
          ((ProjMeas.postprocess
            (matrixMeasurementToLDTProjMeas (S.B y) (hS.2 y)) readB).outcome b)) =
      ∑ directA ∈ Finset.univ.filter (fun answer => readA answer = a),
        ∑ directB ∈ Finset.univ.filter (fun answer => readB answer = b),
          outcomeWeight S x y directA directB := by
  rw [strategyQuantumState_ev_eq_vectorBornWeight]
  simp only [ProjMeas.postprocess, SubMeas.postprocess_outcome,
    matrixMeasurementToLDTProjMeas_outcome]
  rw [vectorBornWeight_finset_sum_left]
  apply Finset.sum_congr rfl
  intro directA _
  rw [vectorBornWeight_finset_sum_right]
  rfl

/-- Correlated residue registers turn two block-diagonal effects into the
uniform average of their matching source-block Born weights. -/
private theorem seedFiberBlockBornAmplitude
    {G : Game} (S : Strategy G) (L : LdParams)
    (A : Fin (L.q / L.m) → Op S.ιA)
    (B : Fin (L.q / L.m) → Op S.ιB) :
    vectorBornAmplitude (seedFiberLiftedState S L)
        (Matrix.blockDiagonal A) (Matrix.blockDiagonal B) =
      (Fintype.card (Fin (L.q / L.m)) : ℂ)⁻¹ *
        ∑ residue, vectorBornAmplitude S.ψ (A residue) (B residue) := by
  classical
  letI : Nonempty (Fin (L.q / L.m)) :=
    Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  unfold vectorBornAmplitude applyOperatorToState heteroKron Matrix.kronecker
  simp_rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    dotProduct, Matrix.mulVec]
  simp_rw [← Finset.univ_product_univ, Finset.sum_product]
  simp [seedFiberLiftedState_apply, Matrix.blockDiagonal_apply,
    mul_assoc, mul_comm]
  ring_nf
  simp_rw [mul_assoc, ← Finset.mul_sum]
  ring_nf
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [← mul_assoc]
  congr 1
  rw [← pow_two, inv_pow, ← Complex.ofReal_pow,
    Real.sq_sqrt (Nat.cast_nonneg (L.q / L.m))]
  norm_cast
  exact Complex.ofReal_inv _

/-- Correlated residue registers give the uniform average of the source-block
Born weights. -/
private theorem seedFiberBlockBornWeight
    {G : Game} (S : Strategy G) (L : LdParams)
    (A : Fin (L.q / L.m) → Op S.ιA)
    (B : Fin (L.q / L.m) → Op S.ιB) :
    vectorBornWeight (seedFiberLiftedState S L)
        (Matrix.blockDiagonal A) (Matrix.blockDiagonal B) =
      (Fintype.card (Fin (L.q / L.m)) : ℝ)⁻¹ *
        ∑ residue, vectorBornWeight S.ψ (A residue) (B residue) := by
  unfold vectorBornWeight
  rw [seedFiberBlockBornAmplitude]
  simp [Complex.mul_re, Complex.inv_re, Complex.inv_im]

/-- The Born weight of the seed-bearing direct adapter is the uniform average
of the original seed-dependent Born weights over the correlated residue. -/
theorem ldStrategyToDirect_bornWeight
    (L : LdParams) (S : Strategy (ldGame L))
    (x y : DirectLdQuestion L.toDirectLdParams)
    (a b : DirectLdAnswer L.toDirectLdParams) :
    outcomeWeight (ldStrategyToDirect L S) x y a b =
      (Fintype.card (Fin (L.q / L.m)) : ℝ)⁻¹ *
        ∑ residue,
          outcomeWeight S
            (seededLdQuestion L x residue)
            (seededLdQuestion L y residue)
            ((ldDirectAnswerEquiv L).symm a)
            ((ldDirectAnswerEquiv L).symm b) := by
  change vectorBornWeight (seedFiberLiftedState S L)
      (Matrix.blockDiagonal fun residue =>
        (S.A (seededLdQuestion L x residue)).effect
          ((ldDirectAnswerEquiv L).symm a))
      (Matrix.blockDiagonal fun residue =>
        (S.B (seededLdQuestion L y residue)).effect
          ((ldDirectAnswerEquiv L).symm b)) = _
  exact seedFiberBlockBornWeight S L _ _

/-- Read coordinate `r` of a projective direct-game strategy as a two-space
projective strategy for the mature low individual degree interface. -/
noncomputable def directCoordinateProjStrat
    (D : DirectLdParams) (S : Strategy (directLdGame D))
    (hS : S.IsProjective) (r : Fin D.k) :
    letI := D.toLDTFieldModel
    ProjStrat D.toLDTParameters S.ιA S.ιB := by
  letI := D.toLDTFieldModel
  exact {
    state := strategyQuantumState S
    isNormalized := strategyQuantumState_isNormalized S
    pointMeasurementA := directCoordinatePointMeasurement D r S.A hS.1
    axisParallelMeasurementA := directCoordinateAxisMeasurement D r S.A hS.1
    axisParallelReparamInvariantA :=
      directCoordinateAxisMeasurement_reparam D r S.A hS.1
    diagonalMeasurementA := directCoordinateDiagonalMeasurement D r S.A hS.1
    diagonalReparamInvariantA :=
      directCoordinateDiagonalMeasurement_reparam D r S.A hS.1
    pointMeasurementB := directCoordinatePointMeasurement D r S.B hS.2
    axisParallelMeasurementB := directCoordinateAxisMeasurement D r S.B hS.2
    axisParallelReparamInvariantB :=
      directCoordinateAxisMeasurement_reparam D r S.B hS.2
    diagonalMeasurementB := directCoordinateDiagonalMeasurement D r S.B hS.2
    diagonalReparamInvariantB :=
      directCoordinateDiagonalMeasurement_reparam D r S.B hS.2
  }

/-- Point Born weights of the coordinate strategy are exactly the sums over
the corresponding direct-answer readout fibers. -/
theorem directCoordinateProjStrat_point_bornWeight
    (D : DirectLdParams) (S : Strategy (directLdGame D))
    (hS : S.IsProjective) (r : Fin D.k)
    (u v : Point D.toLDTParameters)
    (a b : Fq D.toLDTParameters) :
    letI := D.toLDTFieldModel
    ev (directCoordinateProjStrat D S hS r).state
        (opTensor
          (((directCoordinateProjStrat D S hS r).pointMeasurementA u).outcome a)
          (((directCoordinateProjStrat D S hS r).pointMeasurementB v).outcome b)) =
      ∑ directA ∈ Finset.univ.filter (fun answer =>
          directPointAnswerReadout D r answer = a),
        ∑ directB ∈ Finset.univ.filter (fun answer =>
            directPointAnswerReadout D r answer = b),
          outcomeWeight S (directPointQuestionOf D u)
            (directPointQuestionOf D v) directA directB := by
  letI := D.toLDTFieldModel
  change ev (strategyQuantumState S)
      (opTensor
        ((ProjMeas.postprocess
          (matrixMeasurementToLDTProjMeas
            (S.A (directPointQuestionOf D u))
            (hS.1 (directPointQuestionOf D u)))
          (directPointAnswerReadout D r)).outcome a)
        ((ProjMeas.postprocess
          (matrixMeasurementToLDTProjMeas
            (S.B (directPointQuestionOf D v))
            (hS.2 (directPointQuestionOf D v)))
          (directPointAnswerReadout D r)).outcome b)) = _
  exact directPostprocessBornWeight D S hS
    (directPointQuestionOf D u) (directPointQuestionOf D v)
    (directPointAnswerReadout D r) (directPointAnswerReadout D r) a b

/-- Axis-line Born weights of the coordinate strategy are exactly the sums
over the corresponding rebased direct-answer fibers. -/
theorem directCoordinateProjStrat_axis_bornWeight
    (D : DirectLdParams) (S : Strategy (directLdGame D))
    (hS : S.IsProjective) (r : Fin D.k) :
    letI := D.toLDTFieldModel
    ∀ (lineA lineB : AxisParallelLine D.toLDTParameters)
      (f g : AxisLinePolynomial D.toLDTParameters),
    ev (directCoordinateProjStrat D S hS r).state
        (opTensor
          (((directCoordinateProjStrat D S hS r).axisParallelMeasurementA
            lineA).outcome f)
          (((directCoordinateProjStrat D S hS r).axisParallelMeasurementB
            lineB).outcome g)) =
      ∑ directA ∈ Finset.univ.filter (fun answer =>
          directAxisAnswerReadout D r lineA answer = f),
        ∑ directB ∈ Finset.univ.filter (fun answer =>
            directAxisAnswerReadout D r lineB answer = g),
          outcomeWeight S (directAxisQuestionOf D lineA)
            (directAxisQuestionOf D lineB) directA directB := by
  letI := D.toLDTFieldModel
  classical
  intro lineA lineB f g
  change ev (strategyQuantumState S)
      (opTensor
        ((ProjMeas.postprocess
          (matrixMeasurementToLDTProjMeas
            (S.A (directAxisQuestionOf D lineA))
            (hS.1 (directAxisQuestionOf D lineA)))
          (directAxisAnswerReadout D r lineA)).outcome f)
        ((ProjMeas.postprocess
          (matrixMeasurementToLDTProjMeas
            (S.B (directAxisQuestionOf D lineB))
            (hS.2 (directAxisQuestionOf D lineB)))
          (directAxisAnswerReadout D r lineB)).outcome g)) = _
  exact directPostprocessBornWeight D S hS
    (directAxisQuestionOf D lineA) (directAxisQuestionOf D lineB)
    (directAxisAnswerReadout D r lineA)
    (directAxisAnswerReadout D r lineB) f g

open Classical in
/-- Diagonal-line Born weights of the coordinate strategy are exactly the
sums over the corresponding rebased direct-answer fibers. -/
theorem directCoordinateProjStrat_diagonal_bornWeight
    (D : DirectLdParams) (S : Strategy (directLdGame D))
    (hS : S.IsProjective) (r : Fin D.k) :
    letI := D.toLDTFieldModel
    ∀ (lineA lineB : DiagonalLine D.toLDTParameters)
      (f g : DiagonalLinePolynomial D.toLDTParameters),
    ev (directCoordinateProjStrat D S hS r).state
        (opTensor
          (((directCoordinateProjStrat D S hS r).diagonalMeasurementA
            lineA).outcome f)
          (((directCoordinateProjStrat D S hS r).diagonalMeasurementB
            lineB).outcome g)) =
      ∑ directA ∈ Finset.univ.filter (fun answer =>
          directDiagonalAnswerReadout D r lineA answer = f),
        ∑ directB ∈ Finset.univ.filter (fun answer =>
            directDiagonalAnswerReadout D r lineB answer = g),
          outcomeWeight S (directDiagonalQuestionOf D lineA)
            (directDiagonalQuestionOf D lineB) directA directB := by
  letI := D.toLDTFieldModel
  classical
  intro lineA lineB f g
  change ev (strategyQuantumState S)
      (opTensor
        ((ProjMeas.postprocess
          (matrixMeasurementToLDTProjMeas
            (S.A (directDiagonalQuestionOf D lineA))
            (hS.1 (directDiagonalQuestionOf D lineA)))
          (directDiagonalAnswerReadout D r lineA)).outcome f)
        ((ProjMeas.postprocess
          (matrixMeasurementToLDTProjMeas
            (S.B (directDiagonalQuestionOf D lineB))
            (hS.2 (directDiagonalQuestionOf D lineB)))
          (directDiagonalAnswerReadout D r lineB)).outcome g)) = _
  exact directPostprocessBornWeight D S hS
    (directDiagonalQuestionOf D lineA) (directDiagonalQuestionOf D lineB)
    (directDiagonalAnswerReadout D r lineA)
    (directDiagonalAnswerReadout D r lineB) f g

end

end MIPStarRE.QPBT
