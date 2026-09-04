import MIPStarRE.LDT.Test.MainTheorem.MainFormal
import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Strategy
import MIPStarRE.QPBT.Games.DistanceTheorems.TensorSupport

/-!
# Low-degree consistency transport

This module identifies the mature low individual degree polynomial outcomes
with the bounded polynomial representatives used by the directly indexed QPBT
game.  It also transports complete measurements and their evaluation
postprocessings without changing either coordinate order or consistency error.

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

/-! ## Polynomial outcomes -/

private theorem directPolynomialRename_degreeOf_le
    (D : DirectLdParams) (p : MvPolynomial (Fin D.m) (DirectScalarQ D))
    (hp : ∀ i, MvPolynomial.degreeOf i p ≤ D.d) (i : Fin D.m) :
    MvPolynomial.degreeOf i (MvPolynomial.rename Fin.rev p) ≤ D.d := by
  rw [← Fin.rev_rev i,
    MvPolynomial.degreeOf_rename_of_injective Fin.rev_injective]
  exact hp (Fin.rev i)

private theorem ldtPolynomial_ext
    {params : Parameters} [FieldModel params.q]
    {g h : MIPStarRE.LDT.Polynomial params} (hpoly : g.poly = h.poly) : g = h := by
  cases g with
  | mk gp hg =>
      cases h with
      | mk hp hh =>
          simp only at hpoly
          subst hp
          rfl

/-- Bounded QPBT polynomial representatives are equivalent to mature LDT
polynomial outcomes.  The variable renaming is the same coordinate reversal
as `directPointEquiv`, so evaluation retains the direct coordinate order. -/
noncomputable def directPolyEquivPolynomial (D : DirectLdParams) :
    letI := D.toLDTFieldModel
    PolyIndex D.m (DirectScalarQ D) D.d ≃
      MIPStarRE.LDT.Polynomial D.toLDTParameters := by
  letI := D.toLDTFieldModel
  refine
    { toFun := fun g =>
        { poly := MvPolynomial.rename Fin.rev g.1
          lowIndividualDegree := directPolynomialRename_degreeOf_le D g.1
            (degreeOf_le_of_mem_polyFunc g.2) }
      invFun := fun g =>
        ⟨MvPolynomial.rename Fin.rev g.poly, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [MvPolynomial.mem_restrictDegree]
    intro s hs i
    exact (MvPolynomial.degreeOf_le_iff.mp
      (directPolynomialRename_degreeOf_le D g.poly g.lowIndividualDegree i)) s hs
  · intro g
    apply Subtype.ext
    change MvPolynomial.rename Fin.rev
      (MvPolynomial.rename Fin.rev g.1) = g.1
    rw [MvPolynomial.rename_rename]
    rw [show Fin.rev ∘ Fin.rev = id by funext i; simp]
    exact MvPolynomial.rename_id_apply g.1
  · intro g
    cases g with
    | mk p hp =>
        have hpoly : MvPolynomial.rename Fin.rev
            (MvPolynomial.rename Fin.rev p) = p := by
          rw [MvPolynomial.rename_rename]
          rw [show Fin.rev ∘ Fin.rev = id by funext i; simp]
          exact MvPolynomial.rename_id_apply p
        apply ldtPolynomial_ext
        exact hpoly

@[simp] theorem directPolyEquivPolynomial_poly
    (D : DirectLdParams) (g : PolyIndex D.m (DirectScalarQ D) D.d) :
    letI := D.toLDTFieldModel
    (directPolyEquivPolynomial D g).poly = MvPolynomial.rename Fin.rev g.1 := by
  letI := D.toLDTFieldModel
  rfl

/-- The polynomial equivalence commutes with evaluation after the direct point
and scalar codings. -/
@[simp] theorem directPolyEquivPolynomial_apply
    (D : DirectLdParams) (g : PolyIndex D.m (DirectScalarQ D) D.d)
    (u : Fin D.m → DirectScalarQ D) :
    letI := D.toLDTFieldModel
    directPolyEquivPolynomial D g (directPointEquiv D u) =
      directScalarEquiv D (MvPolynomial.eval u g.1) := by
  letI := D.toLDTFieldModel
  unfold MIPStarRE.LDT.Polynomial.toFun evalPolynomialModel
  rw [directPolyEquivPolynomial_poly]
  unfold decodePoint
  rw [MvPolynomial.eval_rename]
  congr 1
  apply congrArg (fun v : Fin D.m → DirectScalarQ D =>
    MvPolynomial.eval v g.1)
  funext i
  simp only [Function.comp_apply, directPointEquiv_apply, Fin.rev_rev]
  change (directScalarEquiv D).symm (directScalarEquiv D (u i)) = u i
  exact (directScalarEquiv D).symm_apply_apply (u i)

/-! ## Complete measurements -/

/-- Regard a complete mature LDT measurement as a matrix-valued QPBT
measurement, with exactly the same effects. -/
noncomputable def ldtMeasurementToMatrixMeasurement
    {alpha iota : Type*} [Fintype alpha] [Fintype iota] [DecidableEq iota]
    (M : MIPStarRE.LDT.Measurement alpha iota) :
    MIPStarRE.Quantum.Measurement alpha iota :=
  MIPStarRE.Quantum.Measurement.ofSumEqOne M.outcome M.outcome_pos (by
    rw [M.sum_eq_total, M.total_eq_one])

@[simp] theorem ldtMeasurementToMatrixMeasurement_effect
    {alpha iota : Type*} [Fintype alpha] [Fintype iota] [DecidableEq iota]
    (M : MIPStarRE.LDT.Measurement alpha iota) (a : alpha) :
    (ldtMeasurementToMatrixMeasurement M).effect a = M.outcome a :=
  rfl

private theorem matrixMeasurement_ext
    {alpha iota : Type*} [Fintype alpha] [Fintype iota] [DecidableEq iota]
    {M N : MIPStarRE.Quantum.Measurement alpha iota}
    (h : ∀ a, M.effect a = N.effect a) : M = N := by
  cases M with
  | mk M hM =>
      cases N with
      | mk N hN =>
          cases M with
          | mk effectM posM leM =>
              cases N with
              | mk effectN posN leN =>
                  simp only at h
                  have heffect : effectM = effectN := funext h
                  subst effectN
                  rfl

/-- Postprocessing matrix-valued measurements is functorial. -/
theorem matrixMeasurement_postprocess_comp
    {alpha beta gamma iota : Type*}
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    [Fintype gamma] [DecidableEq gamma]
    [Fintype iota] [DecidableEq iota]
    (M : MIPStarRE.Quantum.Measurement alpha iota)
    (f : alpha → beta) (g : beta → gamma) :
    (M.postprocess f).postprocess g = M.postprocess (fun a => g (f a)) := by
  classical
  apply matrixMeasurement_ext
  intro c
  calc
    ((M.postprocess f).postprocess g).effect c =
        ∑ b : beta, if g b = c then
          ∑ a : alpha, if f a = b then M.effect a else 0
        else 0 := by
          change (∑ b ∈ Finset.univ.filter (fun b : beta => g b = c),
            ∑ a ∈ Finset.univ.filter (fun a : alpha => f a = b), M.effect a) = _
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro b _
          by_cases hgb : g b = c
          · simp only [hgb, if_true]
            rw [Finset.sum_filter]
          · simp [hgb]
    _ = ∑ b : beta, ∑ a : alpha,
        if g b = c ∧ f a = b then M.effect a else 0 := by
          apply Finset.sum_congr rfl
          intro b _
          by_cases hgc : g b = c <;> simp [hgc]
    _ = ∑ a : alpha, ∑ b : beta,
        if g b = c ∧ f a = b then M.effect a else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ a : alpha,
        if g (f a) = c then M.effect a else 0 := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases hgc : g (f a) = c
          · rw [Finset.sum_eq_single (f a)]
            · simp [hgc]
            · intro b _ hba
              by_cases hfa : f a = b
              · exact (hba hfa.symm).elim
              · simp [hfa]
            · simp
          · have hzero :
                (∑ b : beta,
                  if g b = c ∧ f a = b then M.effect a else 0) = 0 := by
              apply Finset.sum_eq_zero
              intro b _
              by_cases hfa : f a = b
              · subst b
                simp [hgc]
              · simp [hfa]
            simp [hgc, hzero]
    _ = (M.postprocess (fun a => g (f a))).effect c := by
          change _ = ∑ a ∈ Finset.univ.filter
            (fun a : alpha => g (f a) = c), M.effect a
          rw [Finset.sum_filter]

/-- Relabel a mature polynomial projective measurement by direct QPBT
polynomial representatives. -/
noncomputable def directPolynomialMeasurement
    (D : DirectLdParams) :
    letI := D.toLDTFieldModel
    {iota : Type*} → [Fintype iota] → [DecidableEq iota] →
      ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) iota →
        PolyMeas D.m (DirectScalarQ D) D.d iota := by
  letI := D.toLDTFieldModel
  intro iota _ _ G
  exact matrixMeasurementTransport (directPolyEquivPolynomial D).symm
    (ldtMeasurementToMatrixMeasurement G.toMeasurement)

@[simp] theorem directPolynomialMeasurement_effect
    (D : DirectLdParams) :
    letI := D.toLDTFieldModel
    ∀ {iota : Type*} [Fintype iota] [DecidableEq iota]
      (G : ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) iota)
      (g : PolyIndex D.m (DirectScalarQ D) D.d),
      (directPolynomialMeasurement D G).effect g =
        G.outcome (directPolyEquivPolynomial D g) := by
  letI := D.toLDTFieldModel
  intro iota _ _ G g
  rfl

/-- Extract one polynomial coordinate from a direct polynomial-tuple POVM. -/
noncomputable def directPolyMeasTupleMarginal
    (D : DirectLdParams) {iota : Type*} [Fintype iota] [DecidableEq iota]
    (G : DirectPolyMeasTuple D iota) (r : Fin D.k) :
    PolyMeas D.m (DirectScalarQ D) D.d iota :=
  G.postprocess (fun tuple => tuple r)

/-- Extract one polynomial coordinate from a seed-indexed polynomial-tuple
POVM. -/
noncomputable def polyMeasTupleMarginal
    (L : LdParams) {iota : Type*} [Fintype iota] [DecidableEq iota]
    (G : PolyMeasTuple L iota) (r : Fin L.k) :
    PolyMeas L.m (ScalarQ L) L.d iota :=
  G.postprocess (fun tuple => tuple r)

/-- Evaluating a direct polynomial tuple and then selecting coordinate `r`
agrees with evaluating the `r`-th polynomial marginal. -/
theorem directPolyMeasTuple_evaluation_marginal
    (D : DirectLdParams) {iota : Type*} [Fintype iota] [DecidableEq iota]
    (G : DirectPolyMeasTuple D iota) (r : Fin D.k)
    (u : Fin D.m → DirectScalarQ D) :
    (G.postprocess (evalDirectPolyTupleAt u)).postprocess (fun values => values r) =
      (directPolyMeasTupleMarginal D G r).postprocess
        (fun g => MvPolynomial.eval u g.1) := by
  unfold directPolyMeasTupleMarginal
  rw [matrixMeasurement_postprocess_comp, matrixMeasurement_postprocess_comp]
  rfl

/-- Evaluating a seed-indexed polynomial tuple and then selecting coordinate
`r` agrees with evaluating the `r`-th polynomial marginal. -/
theorem polyMeasTuple_evaluation_marginal
    (L : LdParams) {iota : Type*} [Fintype iota] [DecidableEq iota]
    (G : PolyMeasTuple L iota) (r : Fin L.k)
    (u : Fin L.m → ScalarQ L) :
    (G.postprocess (evalPolyTupleAt u)).postprocess (fun values => values r) =
      (polyMeasTupleMarginal L G r).postprocess
        (fun g => MvPolynomial.eval u g.1) := by
  unfold polyMeasTupleMarginal
  rw [matrixMeasurement_postprocess_comp, matrixMeasurement_postprocess_comp]
  rfl

/-- Evaluating the transported polynomial measurement is the relabeling of
the mature evaluation postprocessing through `directScalarEquiv`. -/
theorem directPolynomialMeasurement_evaluation_effect
    (D : DirectLdParams) :
    letI := D.toLDTFieldModel
    ∀ {iota : Type*} [Fintype iota] [DecidableEq iota]
      (G : ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) iota)
      (u : Fin D.m → DirectScalarQ D) (a : DirectScalarQ D),
      ((directPolynomialMeasurement D G).postprocess
        (fun g => MvPolynomial.eval u g.1)).effect a =
        (ldtMeasurementToMatrixMeasurement
          (ProjMeas.postprocess G
            (fun g => g (directPointEquiv D u))).toMeasurement).effect
            (directScalarEquiv D a) := by
  letI := D.toLDTFieldModel
  intro iota _ _ G u a
  classical
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
  rw [ldtMeasurementToMatrixMeasurement_effect,
    ProjMeas.postprocess, SubMeas.postprocess_outcome]
  apply Finset.sum_bij (fun g _ => directPolyEquivPolynomial D g)
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    simpa only [directPolyEquivPolynomial_apply] using
      congrArg (directScalarEquiv D) hg
  · intro g₁ _ g₂ _ h
    exact (directPolyEquivPolynomial D).injective h
  · intro g hg
    refine ⟨(directPolyEquivPolynomial D).symm g, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
      have heval := directPolyEquivPolynomial_apply D
        ((directPolyEquivPolynomial D).symm g) u
      rw [(directPolyEquivPolynomial D).apply_symm_apply] at heval
      exact (directScalarEquiv D).injective (heval.symm.trans hg)
    · exact (directPolyEquivPolynomial D).apply_symm_apply g
  · intro g _
    rw [directPolynomialMeasurement_effect]

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

/-! ## Reindexing the QPBT defect -/

/-- A uniform consistency defect is invariant under a bijective relabeling of
its question type. -/
theorem consistencyDefect_uniform_question_equiv
    {X Y Outcome iota : Type*}
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype Outcome] [DecidableEq Outcome]
    [Fintype iota] [DecidableEq iota]
    (e : X ≃ Y) (A B : Y → Outcome → Op iota)
    (psi : EuclideanSpace ℂ iota) :
    consistencyDefect (uniformDistribution X)
        (fun x a => A (e x) a) (fun x a => B (e x) a) psi =
      consistencyDefect (uniformDistribution Y) A B psi := by
  unfold consistencyDefect
  simpa using avgOver_uniform_equiv e (fun x =>
    ∑ a : Outcome, ∑ b : Outcome,
      if a = b then 0 else
        (inner ℂ psi ((EuclideanSpace.equiv iota ℂ).symm
          (((A (e x) a) * (B (e x) b)).mulVec psi))).re)

/-- A consistency defect is invariant under a bijective relabeling of both
outcome families. -/
theorem consistencyDefect_outcome_equiv
    {X Alpha Beta iota : Type*}
    [Fintype X] [DecidableEq X]
    [Fintype Alpha] [DecidableEq Alpha]
    [Fintype Beta] [DecidableEq Beta]
    [Fintype iota] [DecidableEq iota]
    (mu : Distribution X) (e : Beta ≃ Alpha)
    (A B : X → Alpha → Op iota) (psi : EuclideanSpace ℂ iota) :
    consistencyDefect mu
        (fun x b => A x (e b)) (fun x b => B x (e b)) psi =
      consistencyDefect mu A B psi := by
  unfold consistencyDefect
  apply avgOver_congr
  intro x
  let term : Alpha → Alpha → ℝ := fun a b =>
    if a = b then 0 else
      (inner ℂ psi ((EuclideanSpace.equiv iota ℂ).symm
        (((A x a) * (B x b)).mulVec psi))).re
  calc
    _ = ∑ a : Beta, ∑ b : Beta, term (e a) (e b) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      unfold term
      by_cases hab : a = b
      · subst b
        simp
      · have heab : e a ≠ e b := fun h => hab (e.injective h)
        simp [hab, heab]
    _ =
        ∑ a : Beta, ∑ b : Alpha, term (e a) b := by
      apply Finset.sum_congr rfl
      intro a _
      exact Equiv.sum_comp e (fun b => term (e a) b)
    _ = ∑ a : Alpha, ∑ b : Alpha, term a b :=
      Equiv.sum_comp e (fun a => ∑ b : Alpha, term a b)
    _ = _ := rfl

/-- Simultaneous bijective relabeling of uniform questions and outcomes leaves
the consistency defect unchanged. -/
theorem consistencyDefect_uniform_question_outcome_equiv
    {X Y Alpha Beta iota : Type*}
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype Alpha] [DecidableEq Alpha]
    [Fintype Beta] [DecidableEq Beta]
    [Fintype iota] [DecidableEq iota]
    (questionEquiv : X ≃ Y) (outcomeEquiv : Beta ≃ Alpha)
    (A B : Y → Alpha → Op iota) (psi : EuclideanSpace ℂ iota) :
    consistencyDefect (uniformDistribution X)
        (fun x b => A (questionEquiv x) (outcomeEquiv b))
        (fun x b => B (questionEquiv x) (outcomeEquiv b)) psi =
      consistencyDefect (uniformDistribution Y) A B psi := by
  calc
    consistencyDefect (uniformDistribution X)
        (fun x b => A (questionEquiv x) (outcomeEquiv b))
        (fun x b => B (questionEquiv x) (outcomeEquiv b)) psi =
      consistencyDefect (uniformDistribution X)
        (fun x a => A (questionEquiv x) a)
        (fun x a => B (questionEquiv x) a) psi :=
      consistencyDefect_outcome_equiv (uniformDistribution X)
        outcomeEquiv _ _ psi
    _ = consistencyDefect (uniformDistribution Y) A B psi :=
      consistencyDefect_uniform_question_equiv questionEquiv A B psi

/-! ## The three mature LDT conclusions in direct coordinates -/

/-- Pointwise equality of both operator families gives equality of their
consistency defects. -/
theorem consistencyDefect_congr
    {X Outcome iota : Type*}
    [Fintype X] [DecidableEq X]
    [Fintype Outcome] [DecidableEq Outcome]
    [Fintype iota] [DecidableEq iota]
    (mu : Distribution X) (A A' B B' : X → Outcome → Op iota)
    (psi : EuclideanSpace ℂ iota)
    (hA : ∀ x a, A x a = A' x a) (hB : ∀ x a, B x a = B' x a) :
    consistencyDefect mu A B psi = consistencyDefect mu A' B' psi := by
  unfold consistencyDefect
  apply avgOver_congr
  intro x
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases hab : a = b
  · simp [hab]
  · simp only [hab, if_false]
    rw [hA x a, hB x b]

/-- The direct single-coordinate point/global defect is exactly the mature
defect after the polynomial, point, and scalar equivalences. -/
theorem directPointPolynomial_consistencyDefect_eq
    (D : DirectLdParams) (S : Strategy (directLdGame D))
    (hS : S.IsProjective) (r : Fin D.k) :
    letI := D.toLDTFieldModel
    ∀ (G : ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) S.ιB),
      consistencyDefect
          (uniformDistribution (Fin D.m → DirectScalarQ D))
          (fun u a => heteroKron
            ((directPointCoordinateMeasurementA D S r u).effect a) 1)
          (fun u a => heteroKron 1
            ((directPolynomialEvaluationMeasurement D G u).effect a)) S.ψ =
        consistencyDefect (uniformDistribution (Point D.toLDTParameters))
          (maturePointAPlaced D S hS r)
          (maturePolynomialEvaluationRight D G) S.ψ := by
  letI := D.toLDTFieldModel
  intro G
  calc
    consistencyDefect
        (uniformDistribution (Fin D.m → DirectScalarQ D))
        (fun u a => heteroKron
          ((directPointCoordinateMeasurementA D S r u).effect a) 1)
        (fun u a => heteroKron 1
          ((directPolynomialEvaluationMeasurement D G u).effect a)) S.ψ =
      consistencyDefect
        (uniformDistribution (Fin D.m → DirectScalarQ D))
        (fun u a => maturePointAPlaced D S hS r
          (directPointEquiv D u) (directScalarEquiv D a))
        (fun u a => maturePolynomialEvaluationRight D G
          (directPointEquiv D u) (directScalarEquiv D a)) S.ψ := by
          apply consistencyDefect_congr
          · intro u a
            unfold maturePointAPlaced
            congr 1
            exact (directCoordinatePointMeasurement_effect_transport
              D S hS r u a).symm
          · intro u a
            unfold maturePolynomialEvaluationRight
            congr 1
            exact directPolynomialMeasurement_evaluation_effect D G u a
    _ = consistencyDefect (uniformDistribution (Point D.toLDTParameters))
        (maturePointAPlaced D S hS r)
        (maturePolynomialEvaluationRight D G) S.ψ :=
      consistencyDefect_uniform_question_outcome_equiv
        (directPointEquiv D) (directScalarEquiv D)
        (maturePointAPlaced D S hS r)
        (maturePolynomialEvaluationRight D G) S.ψ

/-- Convert the mature point/global `ConsRel` conclusion to its vector-state
QPBT defect formulation. -/
theorem maturePointPolynomial_consistencyDefect_le
    (D : DirectLdParams) (S : Strategy (directLdGame D))
    (hS : S.IsProjective) (r : Fin D.k) :
    letI := D.toLDTFieldModel
    ∀ (G : ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) S.ιB)
      (delta : ℝ),
      ConsRel (strategyQuantumState S)
          (uniformDistribution (Point D.toLDTParameters))
          (fun u => (matureCoordinatePointMeasurementA D S hS r u).toSubMeas)
          (fun u => (maturePolynomialEvaluationMeasurement D G u).toSubMeas) delta →
        consistencyDefect (uniformDistribution (Point D.toLDTParameters))
          (maturePointAPlaced D S hS r)
          (maturePolynomialEvaluationRight D G) S.ψ ≤ delta := by
  letI := D.toLDTFieldModel
  intro G delta h
  letI : Nonempty (S.ιA × S.ιB) :=
    (strategyQuantumState_isNormalized S).nonempty
  let pure : PureState (S.ιA × S.ιB) := gameStrategyPureState S
  have hpure :
      ConsRel (pure : QuantumState (S.ιA × S.ιB))
        (uniformDistribution (Point D.toLDTParameters))
        (fun u => (matureCoordinatePointMeasurementA D S hS r u).toSubMeas)
        (fun u => (maturePolynomialEvaluationMeasurement D G u).toSubMeas) delta := by
    rw [← strategyQuantumState_eq_gameStrategyPureState S]
    exact h
  have hconverted := (consRel_iff_consistencyDefect pure
    (uniformDistribution (Point D.toLDTParameters))
    (uniformDistribution_isProbability (Point D.toLDTParameters))
    (matureCoordinatePointMeasurementA D S hS r)
    (maturePolynomialEvaluationMeasurement D G) delta).mp hpure
  have hv : pureStateEuclideanVector pure = S.ψ := by
    exact gameStrategyPureState_euclideanVector S
  rw [hv] at hconverted
  have heq := consistencyDefect_congr
    (uniformDistribution (Point D.toLDTParameters))
    (maturePointAPlaced D S hS r)
    (fun u a => heteroKron
      ((matureCoordinatePointMeasurementA D S hS r u).outcome a) 1)
    (maturePolynomialEvaluationRight D G)
    (fun u a => heteroKron 1
      ((maturePolynomialEvaluationMeasurement D G u).outcome a)) S.ψ
    (by intro u a; rfl) (by intro u a; rfl)
  rw [heq]
  exact hconverted

/-- Convert the point-on-Alice/global-on-Bob conclusion of `LDT.Test.mainFormal`
for one simultaneous coordinate to the direct QPBT defect, with the identical
numerical bound. -/
theorem directPointPolynomial_consistencyDefect_le
    (D : DirectLdParams) (S : Strategy (directLdGame D))
    (hS : S.IsProjective) (r : Fin D.k) :
    letI := D.toLDTFieldModel
    ∀ (G : ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) S.ιB)
      (delta : ℝ),
      ConsRel (directCoordinateProjStrat D S hS r).state
          (uniformDistribution (Point D.toLDTParameters))
          (IdxProjMeas.toIdxSubMeas
            (directCoordinateProjStrat D S hS r).pointMeasurementA)
          (polynomialEvaluationFamily D.toLDTParameters G.toSubMeas) delta →
        consistencyDefect
          (uniformDistribution (Fin D.m → DirectScalarQ D))
          (fun u a => heteroKron
            ((directPointCoordinateMeasurementA D S r u).effect a) 1)
          (fun u a => heteroKron 1
            ((directPolynomialEvaluationMeasurement D G u).effect a))
          S.ψ ≤ delta := by
  letI := D.toLDTFieldModel
  intro G delta h
  have hmature :
      consistencyDefect (uniformDistribution (Point D.toLDTParameters))
        (maturePointAPlaced D S hS r)
        (maturePolynomialEvaluationRight D G) S.ψ ≤ delta := by
    apply maturePointPolynomial_consistencyDefect_le D S hS r G delta
    change ConsRel (directCoordinateProjStrat D S hS r).state
      (uniformDistribution (Point D.toLDTParameters))
      (IdxProjMeas.toIdxSubMeas
        (directCoordinateProjStrat D S hS r).pointMeasurementA)
      (polynomialEvaluationFamily D.toLDTParameters G.toSubMeas) delta
    exact h
  rw [directPointPolynomial_consistencyDefect_eq D S hS r G]
  exact hmature

/-- The direct single-coordinate global/point defect is exactly the mature
defect after the polynomial, point, and scalar equivalences. -/
theorem directPolynomialPoint_consistencyDefect_eq
    (D : DirectLdParams) (S : Strategy (directLdGame D))
    (hS : S.IsProjective) (r : Fin D.k) :
    letI := D.toLDTFieldModel
    ∀ (G : ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) S.ιA),
      consistencyDefect
          (uniformDistribution (Fin D.m → DirectScalarQ D))
          (fun u a => heteroKron
            ((directPolynomialEvaluationMeasurement D G u).effect a) 1)
          (fun u a => heteroKron 1
            ((directPointCoordinateMeasurementB D S r u).effect a)) S.ψ =
        consistencyDefect (uniformDistribution (Point D.toLDTParameters))
          (maturePolynomialEvaluationLeft D G)
          (maturePointBPlaced D S hS r) S.ψ := by
  letI := D.toLDTFieldModel
  intro G
  calc
    consistencyDefect
        (uniformDistribution (Fin D.m → DirectScalarQ D))
        (fun u a => heteroKron
          ((directPolynomialEvaluationMeasurement D G u).effect a) 1)
        (fun u a => heteroKron 1
          ((directPointCoordinateMeasurementB D S r u).effect a)) S.ψ =
      consistencyDefect
        (uniformDistribution (Fin D.m → DirectScalarQ D))
        (fun u a => maturePolynomialEvaluationLeft D G
          (directPointEquiv D u) (directScalarEquiv D a))
        (fun u a => maturePointBPlaced D S hS r
          (directPointEquiv D u) (directScalarEquiv D a)) S.ψ := by
          apply consistencyDefect_congr
          · intro u a
            unfold maturePolynomialEvaluationLeft
            congr 1
            exact directPolynomialMeasurement_evaluation_effect D G u a
          · intro u a
            unfold maturePointBPlaced
            congr 1
            exact (directCoordinatePointMeasurementB_effect_transport
              D S hS r u a).symm
    _ = consistencyDefect (uniformDistribution (Point D.toLDTParameters))
        (maturePolynomialEvaluationLeft D G)
        (maturePointBPlaced D S hS r) S.ψ :=
      consistencyDefect_uniform_question_outcome_equiv
        (directPointEquiv D) (directScalarEquiv D)
        (maturePolynomialEvaluationLeft D G)
        (maturePointBPlaced D S hS r) S.ψ

/-- Convert the global-on-Alice/point-on-Bob conclusion of
`LDT.Test.mainFormal` for one simultaneous coordinate to the direct QPBT
defect, with the identical numerical bound. -/
theorem directPolynomialPoint_consistencyDefect_le
    (D : DirectLdParams) (S : Strategy (directLdGame D))
    (hS : S.IsProjective) (r : Fin D.k) :
    letI := D.toLDTFieldModel
    ∀ (G : ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) S.ιA)
      (delta : ℝ),
      ConsRel (directCoordinateProjStrat D S hS r).state
          (uniformDistribution (Point D.toLDTParameters))
          (polynomialEvaluationFamily D.toLDTParameters G.toSubMeas)
          (IdxProjMeas.toIdxSubMeas
            (directCoordinateProjStrat D S hS r).pointMeasurementB) delta →
        consistencyDefect
          (uniformDistribution (Fin D.m → DirectScalarQ D))
          (fun u a => heteroKron
            ((directPolynomialEvaluationMeasurement D G u).effect a) 1)
          (fun u a => heteroKron 1
            ((directPointCoordinateMeasurementB D S r u).effect a))
          S.ψ ≤ delta := by
  letI := D.toLDTFieldModel
  intro G delta h
  have hbase :
      ConsRel (strategyQuantumState S)
        (uniformDistribution (Point D.toLDTParameters))
        (fun u => (maturePolynomialEvaluationMeasurement D G u).toSubMeas)
        (fun u => (matureCoordinatePointMeasurementB D S hS r u).toSubMeas)
        delta := by
    change ConsRel (directCoordinateProjStrat D S hS r).state
      (uniformDistribution (Point D.toLDTParameters))
      (polynomialEvaluationFamily D.toLDTParameters G.toSubMeas)
      (IdxProjMeas.toIdxSubMeas
        (directCoordinateProjStrat D S hS r).pointMeasurementB) delta
    exact h
  have hmature := strategyConsRel_consistencyDefect_le S
    (uniformDistribution (Point D.toLDTParameters))
    (uniformDistribution_isProbability (Point D.toLDTParameters))
    (maturePolynomialEvaluationMeasurement D G)
    (matureCoordinatePointMeasurementB D S hS r) delta hbase
  have heq := consistencyDefect_congr
    (uniformDistribution (Point D.toLDTParameters))
    (maturePolynomialEvaluationLeft D G)
    (fun u a => heteroKron
      ((maturePolynomialEvaluationMeasurement D G u).outcome a) 1)
    (maturePointBPlaced D S hS r)
    (fun u a => heteroKron 1
      ((matureCoordinatePointMeasurementB D S hS r u).outcome a)) S.ψ
    (by intro u a; rfl) (by intro u a; rfl)
  rw [directPolynomialPoint_consistencyDefect_eq D S hS r G, heq]
  exact hmature

/-- Relabeling both global polynomial measurements identifies their direct
QPBT defect with the mature global/global defect. -/
theorem directPolynomialPolynomial_consistencyDefect_eq
    (D : DirectLdParams) (S : Strategy (directLdGame D)) :
    letI := D.toLDTFieldModel
    ∀ (GA : ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) S.ιA)
      (GB : ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) S.ιB),
      consistencyDefect (uniformDistribution Unit)
          (fun _ g => heteroKron ((directPolynomialMeasurement D GA).effect g) 1)
          (fun _ g => heteroKron 1 ((directPolynomialMeasurement D GB).effect g))
          S.ψ =
        consistencyDefect (uniformDistribution Unit)
          (fun _ g => maturePolynomialLeftPlaced D GA g)
          (fun _ g => maturePolynomialRightPlaced D GB g) S.ψ := by
  letI := D.toLDTFieldModel
  intro GA GB
  calc
    consistencyDefect (uniformDistribution Unit)
        (fun _ g => heteroKron ((directPolynomialMeasurement D GA).effect g) 1)
        (fun _ g => heteroKron 1 ((directPolynomialMeasurement D GB).effect g))
        S.ψ =
      consistencyDefect (uniformDistribution Unit)
        (fun _ g => maturePolynomialLeftPlaced D GA (directPolyEquivPolynomial D g))
        (fun _ g => maturePolynomialRightPlaced D GB (directPolyEquivPolynomial D g))
        S.ψ := by
          apply consistencyDefect_congr
          · intro _ g
            unfold maturePolynomialLeftPlaced
            rw [directPolynomialMeasurement_effect]
          · intro _ g
            unfold maturePolynomialRightPlaced
            rw [directPolynomialMeasurement_effect]
    _ = consistencyDefect (uniformDistribution Unit)
        (fun _ g => maturePolynomialLeftPlaced D GA g)
        (fun _ g => maturePolynomialRightPlaced D GB g) S.ψ :=
      consistencyDefect_outcome_equiv (uniformDistribution Unit)
        (directPolyEquivPolynomial D)
        (fun _ g => maturePolynomialLeftPlaced D GA g)
        (fun _ g => maturePolynomialRightPlaced D GB g) S.ψ

/-- Convert the global/global conclusion of `LDT.Test.mainFormal` to the direct
QPBT defect, with the identical numerical bound. -/
theorem directPolynomialPolynomial_consistencyDefect_le
    (D : DirectLdParams) (S : Strategy (directLdGame D)) :
    letI := D.toLDTFieldModel
    ∀ (GA : ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) S.ιA)
      (GB : ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) S.ιB)
      (delta : ℝ),
      ConsRel (strategyQuantumState S) (uniformDistribution Unit)
          (constSubMeasFamily GA.toSubMeas)
          (constSubMeasFamily GB.toSubMeas) delta →
        consistencyDefect (uniformDistribution Unit)
          (fun _ g => heteroKron ((directPolynomialMeasurement D GA).effect g) 1)
          (fun _ g => heteroKron 1 ((directPolynomialMeasurement D GB).effect g))
          S.ψ ≤ delta := by
  letI := D.toLDTFieldModel
  intro GA GB delta h
  have hmature := strategyConsRel_consistencyDefect_le S
    (uniformDistribution Unit) (uniformDistribution_isProbability Unit)
    (fun _ => GA) (fun _ => GB) delta h
  have heq := consistencyDefect_congr (uniformDistribution Unit)
    (fun _ g => maturePolynomialLeftPlaced D GA g)
    (fun _ g => heteroKron (GA.outcome g) 1)
    (fun _ g => maturePolynomialRightPlaced D GB g)
    (fun _ g => heteroKron 1 (GB.outcome g)) S.ψ
    (by intro _ g; rfl) (by intro _ g; rfl)
  rw [directPolynomialPolynomial_consistencyDefect_eq D S GA GB, heq]
  exact hmature

/-! ## Correlated-ancilla compression -/

/-!
The diagonal-block conditional expectation preserves either mixed defect
exactly because the point measurement on the opposite carrier is constant on
the residue register.  It does not yield a global/global compression theorem:
the lifted state pairs equal residues, whereas separately compressing both
polynomial measurements produces an independent double average over residues.
Neither quantity bounds the other in general.  This open obstruction is
recorded in `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.
-/

/-- The normalized diagonal-block average of an operator on a carrier with a
finite ancillary register.  This is the local conditional expectation used to
discard one half of the correlated seed-residue ancilla. -/
noncomputable def averageDiagonalBlock
    {iota block : Type*} [Fintype iota] [Fintype block]
    (A : Op (iota × block)) : Op iota := by
  classical
  exact (Fintype.card block : ℝ)⁻¹ •
    ∑ r, A.submatrix (fun i => (i, r)) (fun i => (i, r))

/-- Compress a POVM through the normalized diagonal-block average.  The
nonemptiness assumption says precisely that the normalized finite average is
defined over at least one ancillary basis element. -/
noncomputable def correlatedAncillaCompressMeasurement
    {alpha iota block : Type*}
    [Fintype alpha] [Fintype iota] [DecidableEq iota]
    [Fintype block] [DecidableEq block] [Nonempty block]
    (M : MIPStarRE.Quantum.Measurement alpha (iota × block)) :
    MIPStarRE.Quantum.Measurement alpha iota :=
  MIPStarRE.Quantum.Measurement.ofSumEqOne
    (fun a => averageDiagonalBlock (M.effect a))
    (fun a => by
      unfold averageDiagonalBlock
      apply smul_nonneg
      · positivity
      · exact Finset.sum_nonneg fun r _ =>
          Matrix.nonneg_iff_posSemidef.mpr
            ((Matrix.nonneg_iff_posSemidef.mp (M.pos a)).submatrix
              (fun i => (i, r))))
    (by
      classical
      ext i j
      simp only [averageDiagonalBlock, Matrix.sum_apply, Matrix.smul_apply,
        Matrix.submatrix_apply]
      calc
        ∑ a, (Fintype.card block : ℝ)⁻¹ •
              ∑ r, M.effect a (i, r) (j, r) =
            (Fintype.card block : ℝ)⁻¹ •
              ∑ a, ∑ r, M.effect a (i, r) (j, r) := by
                rw [Finset.smul_sum]
        _ = (Fintype.card block : ℝ)⁻¹ •
              ∑ r, ∑ a, M.effect a (i, r) (j, r) := by
                rw [Finset.sum_comm]
        _ = (Fintype.card block : ℝ)⁻¹ •
              ∑ r, (1 : Op (iota × block)) (i, r) (j, r) := by
                congr 1
                apply Finset.sum_congr rfl
                intro r _
                simpa only [Matrix.sum_apply] using
                  congrFun (congrFun M.sum_eq_one (i, r)) (j, r)
        _ = (1 : Op iota) i j := by
              simp [Matrix.one_apply, Fintype.card_ne_zero])

@[simp] theorem correlatedAncillaCompressMeasurement_effect
    {alpha iota block : Type*}
    [Fintype alpha] [Fintype iota] [DecidableEq iota]
    [Fintype block] [DecidableEq block] [Nonempty block]
    (M : MIPStarRE.Quantum.Measurement alpha (iota × block)) (a : alpha) :
    (correlatedAncillaCompressMeasurement M).effect a =
      averageDiagonalBlock (M.effect a) :=
  rfl

private theorem averageDiagonalBlock_finset_sum
    {alpha iota block : Type*} [Fintype iota] [Fintype block]
    (s : Finset alpha) (A : alpha → Op (iota × block)) :
    averageDiagonalBlock (∑ a ∈ s, A a) =
      ∑ a ∈ s, averageDiagonalBlock (A a) := by
  classical
  ext i j
  simp only [averageDiagonalBlock, Matrix.smul_apply, Matrix.sum_apply,
    Matrix.submatrix_apply]
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]

/-- Normalized diagonal-block compression commutes with deterministic outcome
postprocessing. -/
theorem correlatedAncillaCompressMeasurement_postprocess
    {alpha beta iota block : Type*}
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    [Fintype iota] [DecidableEq iota]
    [Fintype block] [DecidableEq block] [Nonempty block]
    (M : MIPStarRE.Quantum.Measurement alpha (iota × block))
    (f : alpha → beta) :
    correlatedAncillaCompressMeasurement (M.postprocess f) =
      (correlatedAncillaCompressMeasurement M).postprocess f := by
  classical
  apply matrixMeasurement_ext
  intro b
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect,
    correlatedAncillaCompressMeasurement_effect,
    MIPStarRE.Quantum.Measurement.postprocess_effect]
  exact averageDiagonalBlock_finset_sum
    (Finset.univ.filter (fun a => f a = b)) M.effect

/-- Specialize ancillary compression to the nonempty residue fiber supplied by
the divisibility data of `LdParams`. -/
noncomputable def seedFiberCompressMeasurement
    (L : LdParams) {alpha iota : Type*}
    [Fintype alpha] [Fintype iota] [DecidableEq iota]
    (M : MIPStarRE.Quantum.Measurement alpha
      (iota × Fin (L.q / L.m))) :
    MIPStarRE.Quantum.Measurement alpha iota := by
  letI : Nonempty (Fin (L.q / L.m)) :=
    Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  exact correlatedAncillaCompressMeasurement M

@[simp] theorem seedFiberCompressMeasurement_effect
    (L : LdParams) {alpha iota : Type*}
    [Fintype alpha] [Fintype iota] [DecidableEq iota]
    (M : MIPStarRE.Quantum.Measurement alpha
      (iota × Fin (L.q / L.m))) (a : alpha) :
    (seedFiberCompressMeasurement L M).effect a =
      averageDiagonalBlock (M.effect a) :=
  rfl

/-- Seed-fiber compression commutes with deterministic outcome
postprocessing. -/
theorem seedFiberCompressMeasurement_postprocess
    (L : LdParams) {alpha beta iota : Type*}
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    [Fintype iota] [DecidableEq iota]
    (M : MIPStarRE.Quantum.Measurement alpha
      (iota × Fin (L.q / L.m))) (f : alpha → beta) :
    seedFiberCompressMeasurement L (M.postprocess f) =
      (seedFiberCompressMeasurement L M).postprocess f := by
  letI : Nonempty (Fin (L.q / L.m)) :=
    Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  exact correlatedAncillaCompressMeasurement_postprocess M f

/-- Compress a direct polynomial-tuple POVM from the correlated seed-residue
carrier to the corresponding seed-indexed polynomial POVM. -/
noncomputable def seedFiberCompressPolyMeasTuple
    (L : LdParams) {iota : Type*} [Fintype iota] [DecidableEq iota]
    (G : DirectPolyMeasTuple L.toDirectLdParams
      (iota × Fin (L.q / L.m))) : PolyMeasTuple L iota := by
  exact seedFiberCompressMeasurement L G

@[simp] theorem seedFiberCompressPolyMeasTuple_effect
    (L : LdParams) {iota : Type*} [Fintype iota] [DecidableEq iota]
    (G : DirectPolyMeasTuple L.toDirectLdParams
      (iota × Fin (L.q / L.m))) (g : PolyTuple L) :
    (seedFiberCompressPolyMeasTuple L G).effect g =
      averageDiagonalBlock (G.effect g) :=
  rfl

/-- Polynomial evaluation commutes exactly with compression of the correlated
seed-residue carrier. -/
theorem seedFiberCompressPolyMeasTuple_evaluation
    (L : LdParams) {iota : Type*} [Fintype iota] [DecidableEq iota]
    (G : DirectPolyMeasTuple L.toDirectLdParams
      (iota × Fin (L.q / L.m))) (u : Fin L.m → ScalarQ L) :
    (seedFiberCompressPolyMeasTuple L G).postprocess (evalPolyTupleAt u) =
      seedFiberCompressMeasurement L
        (G.postprocess (evalDirectPolyTupleAt u)) := by
  exact (seedFiberCompressMeasurement_postprocess L G
    (evalDirectPolyTupleAt u)).symm

/-- Block-diagonal assembly commutes with deterministic outcome
postprocessing. -/
theorem blockDiagonalMeasurement_postprocess
    {alpha beta iota block : Type*}
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    [Fintype iota] [DecidableEq iota]
    [Fintype block] [DecidableEq block]
    (M : block → MIPStarRE.Quantum.Measurement alpha iota)
    (f : alpha → beta) :
    (blockDiagonalMeasurement M).postprocess f =
      blockDiagonalMeasurement (fun r => (M r).postprocess f) := by
  classical
  apply matrixMeasurement_ext
  intro b
  ext ⟨i, r⟩ ⟨j, s⟩
  simp only [MIPStarRE.Quantum.Measurement.postprocess_effect,
    blockDiagonalMeasurement_effect, Matrix.sum_apply,
    Matrix.blockDiagonal_apply]
  by_cases hrs : r = s
  · subst s
    simp only [if_pos]
  · simp [hrs]

private theorem matrixMeasurementTransport_eq_postprocess
    {alpha beta iota : Type*}
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    [Fintype iota] [DecidableEq iota]
    (e : alpha ≃ beta) (M : MIPStarRE.Quantum.Measurement alpha iota) :
    matrixMeasurementTransport e M = M.postprocess e := by
  classical
  apply matrixMeasurement_ext
  intro b
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
  rw [Finset.sum_eq_single (e.symm b)]
  · simp
  · intro a haMem ha
    have hea : e a = b := (Finset.mem_filter.mp haMem).2
    exact (ha (e.injective (hea.trans (e.apply_symm_apply b).symm))).elim
  · simp

/-- Relabeling along an outcome equivalence commutes with subsequent
postprocessing. -/
theorem matrixMeasurementTransport_postprocess
    {alpha beta gamma iota : Type*}
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    [Fintype gamma] [DecidableEq gamma]
    [Fintype iota] [DecidableEq iota]
    (e : alpha ≃ beta) (M : MIPStarRE.Quantum.Measurement alpha iota)
    (f : beta → gamma) :
    (matrixMeasurementTransport e M).postprocess f =
      M.postprocess (fun a => f (e a)) := by
  rw [matrixMeasurementTransport_eq_postprocess,
    matrixMeasurement_postprocess_comp]

/-- Reconstructing a seed-indexed point question in any residue block gives
the original point question. -/
@[simp] theorem seededLdQuestion_directLdPointQuestionOf
    (L : LdParams) (u : Fin L.m → ScalarQ L)
    (residue : Fin (L.q / L.m)) :
    seededLdQuestion L
        (directLdPointQuestionOf L.toDirectLdParams u) residue =
      ldPointQuestionOf L u :=
  rfl

/-- The direct point-answer readout agrees with the seed-indexed readout under
the constructor-preserving answer equivalence. -/
@[simp] theorem ldPointValuesOrZero_ldDirectAnswerEquiv_symm
    (L : LdParams) (a : DirectLdAnswer L.toDirectLdParams) :
    ldPointValuesOrZero L ((ldDirectAnswerEquiv L).symm a) =
      directLdPointValuesOrZero L.toDirectLdParams a := by
  cases a <;> rfl

private theorem seedFiberPointMeasurement
    (L : LdParams) {iota : Type*} [Fintype iota] [DecidableEq iota]
    (M : LdQuestion L →
      MIPStarRE.Quantum.Measurement (LdAnswer L) iota)
    (u : Fin L.m → ScalarQ L) :
    (blockDiagonalMeasurement fun residue =>
        matrixMeasurementTransport (ldDirectAnswerEquiv L)
          (M (seededLdQuestion L
            (directLdPointQuestionOf L.toDirectLdParams u) residue))).postprocess
        (directLdPointValuesOrZero L.toDirectLdParams) =
      blockDiagonalMeasurement fun _ =>
        (M (ldPointQuestionOf L u)).postprocess (ldPointValuesOrZero L) := by
  rw [blockDiagonalMeasurement_postprocess]
  apply congrArg blockDiagonalMeasurement
  funext residue
  rw [matrixMeasurementTransport_postprocess,
    seededLdQuestion_directLdPointQuestionOf]
  congr 1
  funext a
  cases a <;> rfl

/-- The point POVM of the correlated direct adapter is the block-diagonal
amplification of Alice's original seed-indexed point POVM. -/
theorem ldStrategyToDirect_pointMeasurementA
    (L : LdParams) (S : Strategy (ldGame L))
    (u : Fin L.m → ScalarQ L) :
    (((ldStrategyToDirect L S).A
        (directLdPointQuestionOf L.toDirectLdParams u)).postprocess
      (directLdPointValuesOrZero L.toDirectLdParams)) =
      blockDiagonalMeasurement fun _ =>
        (S.A (ldPointQuestionOf L u)).postprocess (ldPointValuesOrZero L) := by
  change (blockDiagonalMeasurement fun residue =>
      matrixMeasurementTransport (ldDirectAnswerEquiv L)
        (S.A (seededLdQuestion L
          (directLdPointQuestionOf L.toDirectLdParams u) residue))).postprocess
      (directLdPointValuesOrZero L.toDirectLdParams) = _
  exact seedFiberPointMeasurement L S.A u

/-- The point POVM of the correlated direct adapter is the block-diagonal
amplification of Bob's original seed-indexed point POVM. -/
theorem ldStrategyToDirect_pointMeasurementB
    (L : LdParams) (S : Strategy (ldGame L))
    (u : Fin L.m → ScalarQ L) :
    (((ldStrategyToDirect L S).B
        (directLdPointQuestionOf L.toDirectLdParams u)).postprocess
      (directLdPointValuesOrZero L.toDirectLdParams)) =
      blockDiagonalMeasurement fun _ =>
        (S.B (ldPointQuestionOf L u)).postprocess (ldPointValuesOrZero L) := by
  change (blockDiagonalMeasurement fun residue =>
      matrixMeasurementTransport (ldDirectAnswerEquiv L)
        (S.B (seededLdQuestion L
          (directLdPointQuestionOf L.toDirectLdParams u) residue))).postprocess
      (directLdPointValuesOrZero L.toDirectLdParams) = _
  exact seedFiberPointMeasurement L S.B u

private theorem mul_fintype_sum
    {alpha R : Type*} [Fintype alpha] [NonUnitalNonAssocSemiring R]
    (a : R) (f : alpha → R) :
    a * ∑ x, f x = ∑ x, a * f x := by
  classical
  simpa only using Finset.mul_sum Finset.univ f a

private theorem correlated_ancilla_scale
    (block : Type*) [Fintype block] [Nonempty block] :
    (Real.sqrt (Fintype.card block : ℝ) : ℂ)⁻¹ *
        (starRingEnd ℂ)
          (Real.sqrt (Fintype.card block : ℝ) : ℂ)⁻¹ =
      (Fintype.card block : ℂ)⁻¹ := by
  rw [show (starRingEnd ℂ)
      (Real.sqrt (Fintype.card block : ℝ) : ℂ)⁻¹ =
        (Real.sqrt (Fintype.card block : ℝ) : ℂ)⁻¹ by simp]
  rw [← pow_two, inv_pow, ← Complex.ofReal_pow,
    Real.sq_sqrt (Nat.cast_nonneg (Fintype.card block))]
  norm_cast
  exact Complex.ofReal_inv _

private theorem correlatedState_compress_left
    {iotaA iotaB block : Type*}
    [Fintype iotaA] [DecidableEq iotaA]
    [Fintype iotaB] [DecidableEq iotaB]
    [Fintype block] [DecidableEq block] [Nonempty block]
    (psi : EuclideanSpace ℂ (iotaA × iotaB))
    (phi : EuclideanSpace ℂ ((iotaA × block) × (iotaB × block)))
    (hphi : ∀ i j r s, phi ((i, r), (j, s)) =
      if r = s then
        psi (i, j) * (Real.sqrt (Fintype.card block : ℝ) : ℂ)⁻¹
      else 0)
    (A : Op (iotaA × block)) (B : Op iotaB) :
    DistanceCalculus.stateQForm phi
        (heteroKron A (Matrix.blockDiagonal fun _ => B)) =
      DistanceCalculus.stateQForm psi
        (heteroKron (averageDiagonalBlock A) B) := by
  classical
  unfold DistanceCalculus.stateQForm
  apply congrArg Complex.re
  unfold applyOperatorToState heteroKron Matrix.kronecker averageDiagonalBlock
  simp_rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, dotProduct,
    Matrix.mulVec]
  simp_rw [← Finset.univ_product_univ, Finset.sum_product]
  suffices h :
      (∑ i : iotaA, ∑ r : block, ∑ j : iotaB,
        ∑ i' : iotaA, ∑ j' : iotaB,
          (starRingEnd ℂ)
              (Real.sqrt (Fintype.card block : ℝ) : ℂ)⁻¹ *
            (starRingEnd ℂ) (psi (i, j)) *
              (B j j' * (A (i, r) (i', r) *
                ((Real.sqrt (Fintype.card block : ℝ) : ℂ)⁻¹ *
                  psi (i', j'))))) =
        ∑ i : iotaA, ∑ j : iotaB, ∑ i' : iotaA,
          ∑ j' : iotaB, ∑ r : block,
            (starRingEnd ℂ) (psi (i, j)) *
              (psi (i', j') * (B j j' *
                ((Fintype.card block : ℂ)⁻¹ * A (i, r) (i', r)))) by
    simpa [hphi, Matrix.blockDiagonal_apply, Matrix.kroneckerMap_apply,
      apply_ite, map_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, map_mul, Matrix.submatrix,
      Matrix.sum_apply, Matrix.of_apply, mul_fintype_sum, Finset.sum_mul,
      mul_assoc, mul_comm] using h
  apply Fintype.sum_congr
  intro i
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro j
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro i'
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro j'
  apply Fintype.sum_congr
  intro r
  ring_nf
  rw [correlated_ancilla_scale block]
  ring

private theorem correlatedState_compress_right
    {iotaA iotaB block : Type*}
    [Fintype iotaA] [DecidableEq iotaA]
    [Fintype iotaB] [DecidableEq iotaB]
    [Fintype block] [DecidableEq block] [Nonempty block]
    (psi : EuclideanSpace ℂ (iotaA × iotaB))
    (phi : EuclideanSpace ℂ ((iotaA × block) × (iotaB × block)))
    (hphi : ∀ i j r s, phi ((i, r), (j, s)) =
      if r = s then
        psi (i, j) * (Real.sqrt (Fintype.card block : ℝ) : ℂ)⁻¹
      else 0)
    (A : Op iotaA) (B : Op (iotaB × block)) :
    DistanceCalculus.stateQForm phi
        (heteroKron (Matrix.blockDiagonal fun _ => A) B) =
      DistanceCalculus.stateQForm psi
        (heteroKron A (averageDiagonalBlock B)) := by
  classical
  unfold DistanceCalculus.stateQForm
  apply congrArg Complex.re
  unfold applyOperatorToState heteroKron Matrix.kronecker averageDiagonalBlock
  simp_rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, dotProduct,
    Matrix.mulVec]
  simp_rw [← Finset.univ_product_univ, Finset.sum_product]
  suffices h :
      (∑ i : iotaA, ∑ r : block, ∑ j : iotaB,
        ∑ i' : iotaA, ∑ j' : iotaB,
          (starRingEnd ℂ)
              (Real.sqrt (Fintype.card block : ℝ) : ℂ)⁻¹ *
            (starRingEnd ℂ) (psi (i, j)) *
              (A i i' * (B (j, r) (j', r) *
                ((Real.sqrt (Fintype.card block : ℝ) : ℂ)⁻¹ *
                  psi (i', j'))))) =
        ∑ i : iotaA, ∑ j : iotaB, ∑ i' : iotaA,
          ∑ j' : iotaB, ∑ r : block,
            (starRingEnd ℂ) (psi (i, j)) *
              (psi (i', j') * (A i i' *
                ((Fintype.card block : ℂ)⁻¹ * B (j, r) (j', r)))) by
    simpa [hphi, Matrix.blockDiagonal_apply, Matrix.kroneckerMap_apply,
      apply_ite, map_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, map_mul, Matrix.submatrix,
      Matrix.sum_apply, Matrix.of_apply, mul_fintype_sum, Finset.sum_mul,
      mul_assoc, mul_comm] using h
  apply Fintype.sum_congr
  intro i
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro j
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro i'
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro j'
  apply Fintype.sum_congr
  intro r
  ring_nf
  rw [correlated_ancilla_scale block]
  ring

/-- Compressing Alice's ancillary register preserves every correlation against
an operator on Bob's original carrier. -/
theorem seedFiberLiftedState_compress_left
    {G : Game} (S : Strategy G) (L : LdParams)
    (A : Op (S.ιA × Fin (L.q / L.m))) (B : Op S.ιB) :
    DistanceCalculus.stateQForm (seedFiberLiftedState S L)
        (heteroKron A (Matrix.blockDiagonal fun _ => B)) =
      DistanceCalculus.stateQForm S.ψ
        (heteroKron (averageDiagonalBlock A) B) := by
  classical
  letI : Nonempty (Fin (L.q / L.m)) :=
    Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  apply correlatedState_compress_left S.ψ (seedFiberLiftedState S L)
  intro i j r s
  exact seedFiberLiftedState_apply S L i j r s

/-- Compressing Bob's ancillary register preserves every correlation against
an operator on Alice's original carrier. -/
theorem seedFiberLiftedState_compress_right
    {G : Game} (S : Strategy G) (L : LdParams)
    (A : Op S.ιA) (B : Op (S.ιB × Fin (L.q / L.m))) :
    DistanceCalculus.stateQForm (seedFiberLiftedState S L)
        (heteroKron (Matrix.blockDiagonal fun _ => A) B) =
      DistanceCalculus.stateQForm S.ψ
        (heteroKron A (averageDiagonalBlock B)) := by
  classical
  letI : Nonempty (Fin (L.q / L.m)) :=
    Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  apply correlatedState_compress_right S.ψ (seedFiberLiftedState S L)
  intro i j r s
  exact seedFiberLiftedState_apply S L i j r s

/-- Compressing an arbitrary Alice family preserves its defect against a Bob
family that is constant on the correlated residue register. -/
theorem consistencyDefect_seedFiber_compress_left
    {G : Game} (S : Strategy G) (L : LdParams)
    {X alpha : Type*} [Fintype X] [DecidableEq X]
    [Fintype alpha] [DecidableEq alpha]
    (mu : Distribution X)
    (A : X → alpha → Op (S.ιA × Fin (L.q / L.m)))
    (B : X → alpha → Op S.ιB) :
    consistencyDefect mu
        (fun x a => heteroKron (A x a) 1)
        (fun x a => heteroKron 1 (Matrix.blockDiagonal fun _ => B x a))
        (seedFiberLiftedState S L) =
      consistencyDefect mu
        (fun x a => heteroKron (averageDiagonalBlock (A x a)) 1)
        (fun x a => heteroKron 1 (B x a)) S.ψ := by
  classical
  letI : Nonempty (Fin (L.q / L.m)) :=
    Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  unfold consistencyDefect avgOver
  simp_rw [DistanceCalculus.consistency_term_eq_stateQForm,
    DistanceCalculus.placed_product_stateQForm_eq]
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  apply Fintype.sum_congr
  intro a
  apply Fintype.sum_congr
  intro b
  by_cases hab : a = b
  · simp [hab]
  · simp only [if_neg hab]
    exact seedFiberLiftedState_compress_left S L (A x a) (B x b)

/-- Compressing an arbitrary Bob family preserves its defect against an Alice
family that is constant on the correlated residue register. -/
theorem consistencyDefect_seedFiber_compress_right
    {G : Game} (S : Strategy G) (L : LdParams)
    {X alpha : Type*} [Fintype X] [DecidableEq X]
    [Fintype alpha] [DecidableEq alpha]
    (mu : Distribution X) (A : X → alpha → Op S.ιA)
    (B : X → alpha → Op (S.ιB × Fin (L.q / L.m))) :
    consistencyDefect mu
        (fun x a => heteroKron (Matrix.blockDiagonal fun _ => A x a) 1)
        (fun x a => heteroKron 1 (B x a)) (seedFiberLiftedState S L) =
      consistencyDefect mu
        (fun x a => heteroKron (A x a) 1)
        (fun x a => heteroKron 1 (averageDiagonalBlock (B x a))) S.ψ := by
  classical
  letI : Nonempty (Fin (L.q / L.m)) :=
    Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  unfold consistencyDefect avgOver
  simp_rw [DistanceCalculus.consistency_term_eq_stateQForm,
    DistanceCalculus.placed_product_stateQForm_eq]
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  apply Fintype.sum_congr
  intro a
  apply Fintype.sum_congr
  intro b
  by_cases hab : a = b
  · simp [hab]
  · simp only [if_neg hab]
    exact seedFiberLiftedState_compress_right S L (A x a) (B x b)

/-- The point-on-Alice/global-on-Bob defect of the correlated direct adapter is
exactly the defect of the compressed polynomial tuple on the original
seed-indexed strategy. -/
theorem ldStrategyToDirect_pointPolynomial_compression
    (L : LdParams) (S : Strategy (ldGame L))
    (GB : DirectPolyMeasTuple L.toDirectLdParams
      (S.ιB × Fin (L.q / L.m))) :
    consistencyDefect (uniformDistribution (Fin L.m → ScalarQ L))
        (fun u outcome =>
          heteroKron
            ((((ldStrategyToDirect L S).A
              (directLdPointQuestionOf L.toDirectLdParams u)).postprocess
                (directLdPointValuesOrZero L.toDirectLdParams)).effect outcome) 1)
        (fun u outcome => heteroKron 1
          ((GB.postprocess (evalDirectPolyTupleAt u)).effect outcome))
        (ldStrategyToDirect L S).ψ =
      consistencyDefect (uniformDistribution (Fin L.m → ScalarQ L))
        (fun u outcome => heteroKron
          (((S.A (ldPointQuestionOf L u)).postprocess
            (ldPointValuesOrZero L)).effect outcome) 1)
        (fun u outcome => heteroKron 1
          (((seedFiberCompressPolyMeasTuple L GB).postprocess
            (evalPolyTupleAt u)).effect outcome)) S.ψ := by
  rw [show (ldStrategyToDirect L S).ψ = seedFiberLiftedState S L by rfl]
  simp only [ldStrategyToDirect_pointMeasurementA,
    blockDiagonalMeasurement_effect,
    seedFiberCompressPolyMeasTuple_evaluation,
    seedFiberCompressMeasurement_effect]
  convert consistencyDefect_seedFiber_compress_right S L
    (X := Fin L.m → ScalarQ L) (alpha := Fin L.k → ScalarQ L)
    (uniformDistribution (Fin L.m → ScalarQ L))
    (fun u outcome =>
      ((S.A (ldPointQuestionOf L u)).postprocess
        (ldPointValuesOrZero L)).effect outcome)
    (fun u outcome =>
      (GB.postprocess (evalDirectPolyTupleAt u)).effect outcome) using 1
  apply consistencyDefect_congr <;> intros <;> rfl

/-- The global-on-Alice/point-on-Bob defect of the correlated direct adapter is
exactly the defect of the compressed polynomial tuple on the original
seed-indexed strategy. -/
theorem ldStrategyToDirect_polynomialPoint_compression
    (L : LdParams) (S : Strategy (ldGame L))
    (GA : DirectPolyMeasTuple L.toDirectLdParams
      (S.ιA × Fin (L.q / L.m))) :
    consistencyDefect (uniformDistribution (Fin L.m → ScalarQ L))
        (fun u outcome => heteroKron
          ((GA.postprocess (evalDirectPolyTupleAt u)).effect outcome) 1)
        (fun u outcome =>
          heteroKron 1
            ((((ldStrategyToDirect L S).B
              (directLdPointQuestionOf L.toDirectLdParams u)).postprocess
                (directLdPointValuesOrZero L.toDirectLdParams)).effect outcome))
        (ldStrategyToDirect L S).ψ =
      consistencyDefect (uniformDistribution (Fin L.m → ScalarQ L))
        (fun u outcome => heteroKron
          (((seedFiberCompressPolyMeasTuple L GA).postprocess
            (evalPolyTupleAt u)).effect outcome) 1)
        (fun u outcome => heteroKron 1
          (((S.B (ldPointQuestionOf L u)).postprocess
            (ldPointValuesOrZero L)).effect outcome)) S.ψ := by
  rw [show (ldStrategyToDirect L S).ψ = seedFiberLiftedState S L by rfl]
  simp only [ldStrategyToDirect_pointMeasurementB,
    blockDiagonalMeasurement_effect,
    seedFiberCompressPolyMeasTuple_evaluation,
    seedFiberCompressMeasurement_effect]
  convert consistencyDefect_seedFiber_compress_left S L
    (X := Fin L.m → ScalarQ L) (alpha := Fin L.k → ScalarQ L)
    (uniformDistribution (Fin L.m → ScalarQ L))
    (fun u outcome =>
      (GA.postprocess (evalDirectPolyTupleAt u)).effect outcome)
    (fun u outcome =>
      ((S.B (ldPointQuestionOf L u)).postprocess
        (ldPointValuesOrZero L)).effect outcome) using 1
  all_goals
    apply consistencyDefect_congr <;> intros <;> rfl

end

end MIPStarRE.QPBT
