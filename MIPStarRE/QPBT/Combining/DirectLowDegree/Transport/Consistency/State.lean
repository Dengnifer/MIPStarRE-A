import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Consistency.Measurements

/-!
# State conversion and direct point readout

This module contains the pure-state conversion and direct point-readout
portion of the low-degree consistency transport.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:393-458`
- `references/ldt-paper/test_definition.tex:180-202`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.Quantum

noncomputable section

/-! ## Equality of the two consistency formulations -/

/-- View the coordinate function of an LDT pure state as a Euclidean vector. -/
noncomputable def pureStateEuclideanVector
    {iota : Type*} [Fintype iota] [DecidableEq iota] [Nonempty iota]
    (psi : PureState iota) : EuclideanSpace ℂ iota :=
  (EuclideanSpace.equiv iota ℂ).symm psi.vector

@[simp] theorem pureStateEuclideanVector_apply
    {iota : Type*} [Fintype iota] [DecidableEq iota] [Nonempty iota]
    (psi : PureState iota) (i : iota) :
    pureStateEuclideanVector psi i = psi.vector i :=
  rfl

/-- The Euclidean vector associated with an LDT pure state has norm one. -/
theorem pureStateEuclideanVector_norm
    {iota : Type*} [Fintype iota] [DecidableEq iota] [Nonempty iota]
    (psi : PureState iota) : ‖pureStateEuclideanVector psi‖ = 1 := by
  have hsquareComplex :
      ((‖pureStateEuclideanVector psi‖ ^ 2 : ℝ) : ℂ) = 1 := by
    calc
      ((‖pureStateEuclideanVector psi‖ ^ 2 : ℝ) : ℂ) =
          (‖pureStateEuclideanVector psi‖ : ℂ) ^ 2 := by norm_cast
      _ = inner ℂ (pureStateEuclideanVector psi)
          (pureStateEuclideanVector psi) :=
        (inner_self_eq_norm_sq_to_K (pureStateEuclideanVector psi)).symm
      _ = dotProduct psi.vector (star psi.vector) :=
        EuclideanSpace.inner_eq_star_dotProduct _ _
      _ = dotProduct (star psi.vector) psi.vector := dotProduct_comm _ _
      _ = 1 := psi.unit
  have hsquare : ‖pureStateEuclideanVector psi‖ ^ 2 = (1 : ℝ) := by
    exact_mod_cast hsquareComplex
  nlinarith [norm_nonneg (pureStateEuclideanVector psi)]

/-- Evaluation in a pure LDT density state is the quadratic form of its
Euclidean vector. -/
theorem pureState_stateQForm_eq_ev
    {iota : Type*} [Fintype iota] [DecidableEq iota] [Nonempty iota]
    (psi : PureState iota) (T : Op iota) :
    DistanceCalculus.stateQForm (pureStateEuclideanVector psi) T =
      ev (psi : QuantumState iota) T := by
  rw [PureState.ev_eq_re_inner]
  unfold DistanceCalculus.stateQForm applyOperatorToState
  change (inner ℂ (pureStateEuclideanVector psi)
      (WithLp.toLp 2 (T *ᵥ psi.vector))).re =
    (dotProduct (star psi.vector) (T *ᵥ psi.vector)).re
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rfl

/-- For complete projective families and a pure bipartite state, the mature
LDT consistency relation is exactly the QPBT off-diagonal defect.  In
particular, changing between the density and vector formulations incurs no
loss in the error parameter. -/
theorem consRel_iff_consistencyDefect
    {Question Outcome iotaA iotaB : Type*}
    [Fintype Question] [DecidableEq Question]
    [Fintype Outcome] [DecidableEq Outcome]
    [Fintype iotaA] [DecidableEq iotaA]
    [Fintype iotaB] [DecidableEq iotaB]
    [Nonempty (iotaA × iotaB)]
    (psi : PureState (iotaA × iotaB))
    (mu : Distribution Question) (hmu : mu.IsProbability)
    (A : Question → ProjMeas Outcome iotaA)
    (B : Question → ProjMeas Outcome iotaB) (delta : ℝ) :
    ConsRel (psi : QuantumState (iotaA × iotaB)) mu
        (fun x => (A x).toSubMeas) (fun x => (B x).toSubMeas) delta ↔
      consistencyDefect mu
        (fun x a => heteroKron ((A x).outcome a) 1)
        (fun x a => heteroKron 1 ((B x).outcome a))
        (pureStateEuclideanVector psi) ≤ delta := by
  let AM : Question → MIPStarRE.Quantum.Measurement Outcome (iotaA × iotaB) :=
    fun x => DistanceCalculus.leftPlacedMeasurement
      (ldtMeasurementToMatrixMeasurement (A x).toMeasurement)
  let BM : Question → MIPStarRE.Quantum.Measurement Outcome (iotaA × iotaB) :=
    fun x => DistanceCalculus.rightPlacedMeasurement
      (ldtMeasurementToMatrixMeasurement (B x).toMeasurement)
  have hAM (x : Question) (a : Outcome) :
      (AM x).effect a = heteroKron ((A x).outcome a) 1 := rfl
  have hBM (x : Question) (a : Outcome) :
      (BM x).effect a = heteroKron 1 ((B x).outcome a) := rfl
  have hdefect :
      consistencyDefect mu
          (fun x a => heteroKron ((A x).outcome a) 1)
          (fun x a => heteroKron 1 ((B x).outcome a))
          (pureStateEuclideanVector psi) =
        bipartiteConsError (psi : QuantumState (iotaA × iotaB)) mu
          (fun x => (A x).toSubMeas) (fun x => (B x).toSubMeas) := by
    calc
      consistencyDefect mu
          (fun x a => heteroKron ((A x).outcome a) 1)
          (fun x a => heteroKron 1 ((B x).outcome a))
          (pureStateEuclideanVector psi) =
          1 - avgOver mu (fun x => ∑ a,
            DistanceCalculus.stateQForm (pureStateEuclideanVector psi)
              ((AM x).effect a * (BM x).effect a)) := by
            simpa only [hAM, hBM] using
              DistanceCalculus.consistencyDefect_eq_one_sub_overlap
                mu AM BM (pureStateEuclideanVector psi) hmu
                  (pureStateEuclideanVector_norm psi)
      _ = avgOver mu (fun x => 1 - ∑ a,
            DistanceCalculus.stateQForm (pureStateEuclideanVector psi)
              ((AM x).effect a * (BM x).effect a)) := by
            rw [avgOver_sub, avgOver_const_of_isProbability mu hmu]
      _ = bipartiteConsError (psi : QuantumState (iotaA × iotaB)) mu
          (fun x => (A x).toSubMeas) (fun x => (B x).toSubMeas) := by
            unfold bipartiteConsError
            apply avgOver_congr
            intro x
            rw [qBipartiteConsDefect_of_measurements
              (psi : QuantumState (iotaA × iotaB))
              (A x).toMeasurement (B x).toMeasurement]
            rw [ev_one_of_isNormalized (psi : QuantumState (iotaA × iotaB))
              psi.toQuantumState_isNormalized]
            congr 1
            apply Finset.sum_congr rfl
            intro a _
            rw [hAM, hBM]
            rw [DistanceCalculus.placed_product_stateQForm_eq]
            exact pureState_stateQForm_eq_ev psi
              (opTensor ((A x).outcome a) ((B x).outcome a))
  constructor
  · intro h
    rw [hdefect]
    exact h.offDiagonalBound
  · intro h
    refine ⟨?_⟩
    rw [← hdefect]
    exact h

/-! ## Direct-strategy state and point readout -/

private theorem quantumState_ext
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    {rho sigma : QuantumState iota} (h : rho.density = sigma.density) : rho = sigma := by
  cases rho with
  | mk rho hrho =>
      cases sigma with
      | mk sigma hsigma =>
          simp only at h
          subst sigma
          rfl

/-- The pure state carried by a game strategy, expressed in the mature LDT
state interface. -/
noncomputable def gameStrategyPureState {G : Game} (S : Strategy G) :
    letI : Nonempty (S.ιA × S.ιB) :=
      (strategyQuantumState_isNormalized S).nonempty
    PureState (S.ιA × S.ιB) := by
  letI : Nonempty (S.ιA × S.ιB) :=
    (strategyQuantumState_isNormalized S).nonempty
  exact
    { vector := S.ψ
      unit := by
        rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
          inner_self_eq_norm_sq_to_K, S.ψ_norm]
        norm_num }

@[simp] theorem gameStrategyPureState_vector {G : Game} (S : Strategy G) :
    letI : Nonempty (S.ιA × S.ιB) :=
      (strategyQuantumState_isNormalized S).nonempty
    (gameStrategyPureState S).vector = S.ψ := by
  letI : Nonempty (S.ιA × S.ιB) :=
    (strategyQuantumState_isNormalized S).nonempty
  rfl

/-- The density state used by `directCoordinateProjStrat` is the density of
the strategy's displayed pure state. -/
theorem strategyQuantumState_eq_gameStrategyPureState
    {G : Game} (S : Strategy G) :
    letI : Nonempty (S.ιA × S.ιB) :=
      (strategyQuantumState_isNormalized S).nonempty
    strategyQuantumState S =
      (gameStrategyPureState S : QuantumState (S.ιA × S.ιB)) := by
  letI : Nonempty (S.ιA × S.ιB) :=
    (strategyQuantumState_isNormalized S).nonempty
  apply quantumState_ext
  rfl

/-- The Euclidean vector of the strategy's pure-state presentation is the
original game vector. -/
@[simp] theorem gameStrategyPureState_euclideanVector
    {G : Game} (S : Strategy G) :
    letI : Nonempty (S.ιA × S.ιB) :=
      (strategyQuantumState_isNormalized S).nonempty
    pureStateEuclideanVector (gameStrategyPureState S) = S.ψ := by
  letI : Nonempty (S.ιA × S.ιB) :=
    (strategyQuantumState_isNormalized S).nonempty
  apply (EuclideanSpace.equiv (S.ιA × S.ιB) ℂ).injective
  rfl

/-- A mature consistency relation on the density state associated with a game
strategy gives the identical QPBT defect bound on the strategy vector. -/
theorem strategyConsRel_consistencyDefect_le
    {G : Game} (S : Strategy G)
    {Question Outcome : Type*}
    [Fintype Question] [DecidableEq Question]
    [Fintype Outcome] [DecidableEq Outcome]
    (mu : Distribution Question) (hmu : mu.IsProbability)
    (A : Question → ProjMeas Outcome S.ιA)
    (B : Question → ProjMeas Outcome S.ιB) (delta : ℝ)
    (h : ConsRel (strategyQuantumState S) mu
      (fun x => (A x).toSubMeas) (fun x => (B x).toSubMeas) delta) :
    consistencyDefect mu
      (fun x a => heteroKron ((A x).outcome a) 1)
      (fun x a => heteroKron 1 ((B x).outcome a)) S.ψ ≤ delta := by
  letI : Nonempty (S.ιA × S.ιB) :=
    (strategyQuantumState_isNormalized S).nonempty
  let pure : PureState (S.ιA × S.ιB) := gameStrategyPureState S
  have hpure :
      ConsRel (pure : QuantumState (S.ιA × S.ιB)) mu
        (fun x => (A x).toSubMeas) (fun x => (B x).toSubMeas) delta := by
    rw [← strategyQuantumState_eq_gameStrategyPureState S]
    exact h
  have hconverted := (consRel_iff_consistencyDefect pure mu hmu A B delta).mp hpure
  have hv : pureStateEuclideanVector pure = S.ψ := by
    exact gameStrategyPureState_euclideanVector S
  rw [hv] at hconverted
  exact hconverted

@[simp] theorem directPointQuestionOf_directPointEquiv
    (D : DirectLdParams) (u : Fin D.m → DirectScalarQ D) :
    directPointQuestionOf D (directPointEquiv D u) =
      directLdPointQuestionOf D u := by
  unfold directPointQuestionOf ldtPointToDirect
  rw [(directPointEquiv D).symm_apply_apply]

/-- Mature points associated with direct parameters have a canonical zero
witness. -/
instance directMaturePointNonempty (D : DirectLdParams) :
    Nonempty (Point D.toLDTParameters) :=
  ⟨fun _ => ⟨0, D.toLDTParameters.hq⟩⟩

/-- Direct points are nonempty because they are equivalent to mature points. -/
noncomputable instance directPointNonempty (D : DirectLdParams) :
    Nonempty (Fin D.m → DirectScalarQ D) :=
  Nonempty.map (directPointEquiv D).symm (directMaturePointNonempty D)

/-- The mature scalar readout is the direct coordinate readout followed by
the scalar coding equivalence. -/
@[simp] theorem directPointAnswerReadout_eq
    (D : DirectLdParams) (r : Fin D.k) (answer : DirectLdAnswer D) :
    letI := D.toLDTFieldModel
    directPointAnswerReadout D r answer =
      directScalarEquiv D (directLdPointValuesOrZero D answer r) := by
  letI := D.toLDTFieldModel
  cases answer <;> rfl

/-- At corresponding points and scalar outcomes, the mature point effect is
the effect of the direct point measurement followed by coordinate projection. -/
theorem directCoordinatePointMeasurement_effect_transport
    (D : DirectLdParams) (S : Strategy (directLdGame D))
    (hS : S.IsProjective) (r : Fin D.k)
    (u : Fin D.m → DirectScalarQ D) (a : DirectScalarQ D) :
    letI := D.toLDTFieldModel
    (((directCoordinateProjStrat D S hS r).pointMeasurementA
      (directPointEquiv D u)).outcome (directScalarEquiv D a)) =
      ((S.A (directLdPointQuestionOf D u)).postprocess
        (fun answer => directLdPointValuesOrZero D answer r)).effect a := by
  letI := D.toLDTFieldModel
  classical
  simp only [directCoordinateProjStrat, directCoordinatePointMeasurement,
    directLdGame,
    ProjMeas.postprocess, SubMeas.postprocess_outcome,
    matrixMeasurementToLDTProjMeas_outcome,
    directPointQuestionOf_directPointEquiv,
    MIPStarRE.Quantum.Measurement.postprocess_effect]
  congr 1
  ext answer
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  simpa only [directPointAnswerReadout_eq] using
    (directScalarEquiv D).injective.eq_iff

/-- Bob's point effects satisfy the same direct-to-mature readout identity. -/
theorem directCoordinatePointMeasurementB_effect_transport
    (D : DirectLdParams) (S : Strategy (directLdGame D))
    (hS : S.IsProjective) (r : Fin D.k)
    (u : Fin D.m → DirectScalarQ D) (a : DirectScalarQ D) :
    letI := D.toLDTFieldModel
    (((directCoordinateProjStrat D S hS r).pointMeasurementB
      (directPointEquiv D u)).outcome (directScalarEquiv D a)) =
      ((S.B (directLdPointQuestionOf D u)).postprocess
        (fun answer => directLdPointValuesOrZero D answer r)).effect a := by
  letI := D.toLDTFieldModel
  classical
  simp only [directCoordinateProjStrat, directCoordinatePointMeasurement,
    directLdGame,
    ProjMeas.postprocess, SubMeas.postprocess_outcome,
    matrixMeasurementToLDTProjMeas_outcome,
    directPointQuestionOf_directPointEquiv,
    MIPStarRE.Quantum.Measurement.postprocess_effect]
  congr 1
  ext answer
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  simpa only [directPointAnswerReadout_eq] using
    (directScalarEquiv D).injective.eq_iff

/-- Alice's direct point measurement followed by projection to coordinate
`r`. -/
noncomputable def directPointCoordinateMeasurementA
    (D : DirectLdParams) (S : Strategy (directLdGame D))
    (r : Fin D.k) (u : Fin D.m → DirectScalarQ D) :
    MIPStarRE.Quantum.Measurement (DirectScalarQ D) S.ιA :=
  (S.A (directLdPointQuestionOf D u)).postprocess
    (fun answer => directLdPointValuesOrZero D answer r)

/-- Bob's direct point measurement followed by projection to coordinate
`r`. -/
noncomputable def directPointCoordinateMeasurementB
    (D : DirectLdParams) (S : Strategy (directLdGame D))
    (r : Fin D.k) (u : Fin D.m → DirectScalarQ D) :
    MIPStarRE.Quantum.Measurement (DirectScalarQ D) S.ιB :=
  (S.B (directLdPointQuestionOf D u)).postprocess
    (fun answer => directLdPointValuesOrZero D answer r)

/-- Evaluate a transported mature polynomial measurement at a direct point. -/
noncomputable def directPolynomialEvaluationMeasurement
    (D : DirectLdParams) :
    letI := D.toLDTFieldModel
    {iota : Type*} → [Fintype iota] → [DecidableEq iota] →
      ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) iota →
        (Fin D.m → DirectScalarQ D) →
          MIPStarRE.Quantum.Measurement (DirectScalarQ D) iota := by
  letI := D.toLDTFieldModel
  intro iota _ _ G u
  exact (directPolynomialMeasurement D G).postprocess
    (fun g => MvPolynomial.eval u g.1)

/-- Alice's mature point family obtained from direct coordinate `r`. -/
noncomputable def matureCoordinatePointMeasurementA
    (D : DirectLdParams) (S : Strategy (directLdGame D))
    (hS : S.IsProjective) (r : Fin D.k) :
    letI := D.toLDTFieldModel
    IdxProjMeas (Point D.toLDTParameters) (Fq D.toLDTParameters) S.ιA := by
  letI := D.toLDTFieldModel
  exact (directCoordinateProjStrat D S hS r).pointMeasurementA

/-- Bob's mature point family obtained from direct coordinate `r`. -/
noncomputable def matureCoordinatePointMeasurementB
    (D : DirectLdParams) (S : Strategy (directLdGame D))
    (hS : S.IsProjective) (r : Fin D.k) :
    letI := D.toLDTFieldModel
    IdxProjMeas (Point D.toLDTParameters) (Fq D.toLDTParameters) S.ιB := by
  letI := D.toLDTFieldModel
  exact (directCoordinateProjStrat D S hS r).pointMeasurementB

/-- The mature projective evaluation family associated with a global
polynomial projective measurement. -/
noncomputable def maturePolynomialEvaluationMeasurement
    (D : DirectLdParams) :
    letI := D.toLDTFieldModel
    {iota : Type*} → [Fintype iota] → [DecidableEq iota] →
      ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) iota →
        IdxProjMeas (Point D.toLDTParameters) (Fq D.toLDTParameters) iota := by
  letI := D.toLDTFieldModel
  intro iota _ _ G u
  exact ProjMeas.postprocess G (fun g => g u)

/-- Left placement of Alice's mature point family. -/
noncomputable def maturePointAPlaced
    (D : DirectLdParams) (S : Strategy (directLdGame D))
    (hS : S.IsProjective) (r : Fin D.k) :
    letI := D.toLDTFieldModel
    Point D.toLDTParameters → Fq D.toLDTParameters → Op (S.ιA × S.ιB) := by
  letI := D.toLDTFieldModel
  intro u a
  exact heteroKron ((matureCoordinatePointMeasurementA D S hS r u).outcome a) 1

/-- Right placement of Bob's mature point family. -/
noncomputable def maturePointBPlaced
    (D : DirectLdParams) (S : Strategy (directLdGame D))
    (hS : S.IsProjective) (r : Fin D.k) :
    letI := D.toLDTFieldModel
    Point D.toLDTParameters → Fq D.toLDTParameters → Op (S.ιA × S.ιB) := by
  letI := D.toLDTFieldModel
  intro u a
  exact heteroKron 1 ((matureCoordinatePointMeasurementB D S hS r u).outcome a)

/-- Left placement of a mature polynomial evaluation family. -/
noncomputable def maturePolynomialEvaluationLeft
    (D : DirectLdParams) {iotaA iotaB : Type*}
    [Fintype iotaA] [DecidableEq iotaA]
    [Fintype iotaB] [DecidableEq iotaB] :
    letI := D.toLDTFieldModel
    ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) iotaA →
      Point D.toLDTParameters → Fq D.toLDTParameters → Op (iotaA × iotaB) := by
  letI := D.toLDTFieldModel
  intro G u a
  exact heteroKron ((maturePolynomialEvaluationMeasurement D G u).outcome a) 1

/-- Right placement of a mature polynomial evaluation family. -/
noncomputable def maturePolynomialEvaluationRight
    (D : DirectLdParams) {iotaA iotaB : Type*}
    [Fintype iotaA] [DecidableEq iotaA]
    [Fintype iotaB] [DecidableEq iotaB] :
    letI := D.toLDTFieldModel
    ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) iotaB →
      Point D.toLDTParameters → Fq D.toLDTParameters → Op (iotaA × iotaB) := by
  letI := D.toLDTFieldModel
  intro G u a
  exact heteroKron 1 ((maturePolynomialEvaluationMeasurement D G u).outcome a)

/-- Left placement of a mature global polynomial measurement. -/
noncomputable def maturePolynomialLeftPlaced
    (D : DirectLdParams) {iotaA iotaB : Type*}
    [Fintype iotaA] [DecidableEq iotaA]
    [Fintype iotaB] [DecidableEq iotaB] :
    letI := D.toLDTFieldModel
    ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) iotaA →
      MIPStarRE.LDT.Polynomial D.toLDTParameters → Op (iotaA × iotaB) := by
  letI := D.toLDTFieldModel
  intro G g
  exact heteroKron (G.outcome g) 1

/-- Right placement of a mature global polynomial measurement. -/
noncomputable def maturePolynomialRightPlaced
    (D : DirectLdParams) {iotaA iotaB : Type*}
    [Fintype iotaA] [DecidableEq iotaA]
    [Fintype iotaB] [DecidableEq iotaB] :
    letI := D.toLDTFieldModel
    ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) iotaB →
      MIPStarRE.LDT.Polynomial D.toLDTParameters → Op (iotaA × iotaB) := by
  letI := D.toLDTFieldModel
  intro G g
  exact heteroKron 1 (G.outcome g)

end

end MIPStarRE.QPBT
