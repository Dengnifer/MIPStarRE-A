import MIPStarRE.QPBT.Games.DistanceTheorems.TensorSupport
import MIPStarRE.LDT.MakingMeasurementsProjective.Orthonormalization
import MIPStarRE.LDT.Preliminaries.Completion
import MIPStarRE.LDT.Preliminaries.Triangles.Core
import MIPStarRE.LDT.Test.StrategyRole.Algebra

/-!
# Projective rounding for consistent POVMs

This module derives an explicit finite-dimensional projective rounding from the
Q/X/XHat construction used in the LDT orthonormalization theorem. The argument
keeps the original Alice space and completes the resulting projective
submeasurement after proving that its missing state mass is small.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:131-153`
- `blueprint/src/chapter/ch14_qpbt_observables.tex:356-383`
- `references/ldt-paper/orthonormalization.tex`
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus
open MIPStarRE.LDT.MakingMeasurementsProjective

noncomputable section

/-- The normalized pure state whose vector is the given unit Euclidean vector. -/
private noncomputable def roundPureState {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) : PureState ι where
  vector := ψ.ofLp
  unit := by
    calc
      star ψ.ofLp ⬝ᵥ ψ.ofLp = ψ.ofLp ⬝ᵥ star ψ.ofLp := dotProduct_comm _ _
      _ = inner ℂ ψ ψ := (EuclideanSpace.inner_eq_star_dotProduct ψ ψ).symm
      _ = (‖ψ‖ ^ 2 : ℂ) := inner_self_eq_norm_sq_to_K ψ
      _ = 1 := by rw [hψ]; norm_num

/-- The QPBT vector quadratic form equals evaluation in `roundPureState`. -/
private theorem round_stateQForm_eq_ev {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (T : Op ι) :
    stateQForm ψ T = ev (roundPureState ψ hψ : QuantumState ι) T := by
  rw [PureState.ev_eq_re_inner]
  simp only [roundPureState]
  change (inner ℂ ψ (WithLp.toLp 2 (T *ᵥ ψ.ofLp))).re =
    (star ψ.ofLp ⬝ᵥ T *ᵥ ψ.ofLp).re
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

/-- Evaluation of an operator square in `roundPureState` is the squared vector norm. -/
private theorem round_ev_adjoint_mul_self_eq_norm_sq {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (T : Op ι) :
    ev (roundPureState ψ hψ : QuantumState ι) (Tᴴ * T) =
      ‖applyOperatorToState T ψ‖ ^ 2 := by
  rw [← round_stateQForm_eq_ev]
  symm
  rw [@norm_sq_eq_re_inner ℂ]
  unfold stateQForm applyOperatorToState
  rw [Matrix.toEuclideanLin_conjTranspose_mul_self]
  change (inner ℂ (Matrix.toEuclideanLin T ψ) (Matrix.toEuclideanLin T ψ)).re =
    (inner ℂ ψ ((Matrix.toEuclideanLin T).adjoint (Matrix.toEuclideanLin T ψ))).re
  rw [LinearMap.adjoint_inner_right]

/-- Package a nonempty finite matrix index as an LDT finite Hilbert space. -/
private def roundFiniteHilbertSpace (ι : Type*) [Fintype ι] [DecidableEq ι]
    [Nonempty ι] : FiniteHilbertSpace :=
  { carrier := ι
    instFintype := inferInstance
    instDecidableEq := inferInstance
    instNonempty := inferInstance }

/-- The diagonal block of a bipartite operator at a fixed right index. -/
private def roundDiagBlock {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : Op (ιA × ιB)) (b : ιB) : Op ιA :=
  M.submatrix (fun i => (i, b)) (fun j => (j, b))

/-- The normalized left marginal density obtained by summing diagonal right blocks. -/
private def roundLeftMarginalDensity {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ρ : Op (ιA × ιB)) : Op ιA :=
  ((((Fintype.card ιB : Error) : Error)⁻¹ : Error) : ℂ) •
    ∑ b : ιB, roundDiagBlock ρ b

/-- Positivity passes from a bipartite density to its normalized left marginal. -/
private lemma roundLeftMarginalDensity_nonneg {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    {ρ : Op (ιA × ιB)} (hρ : 0 ≤ ρ) :
    0 ≤ roundLeftMarginalDensity ρ := by
  have hρpsd : ρ.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hρ
  have hsum : 0 ≤ ∑ b : ιB, roundDiagBlock ρ b := by
    refine Finset.sum_nonneg fun b _ => ?_
    refine Matrix.nonneg_iff_posSemidef.mpr ?_
    simpa [roundDiagBlock] using hρpsd.submatrix (fun i => (i, b))
  have hcoeff : 0 ≤ ((((Fintype.card ιB : Error) : Error)⁻¹ : Error) : ℂ) := by
    positivity
  simpa [roundLeftMarginalDensity] using smul_nonneg hcoeff hsum

/-- The local quantum state defined by the normalized left marginal density. -/
private def roundLeftMarginalState {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB)) : QuantumState ιA where
  density := roundLeftMarginalDensity ψ.density
  density_psd := roundLeftMarginalDensity_nonneg ψ.density_psd

/-- Left tensor placement is block diagonal with the same block at every right index. -/
private lemma round_leftTensor_eq_blockDiagonal_const {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (X : Op ιA) :
    leftTensor (ι₂ := ιB) X = Matrix.blockDiagonal (fun _ : ιB => X) := by
  ext x y
  rcases x with ⟨i, b⟩
  rcases y with ⟨j, c⟩
  by_cases h : b = c
  · subst c
    simp [leftTensor, Matrix.blockDiagonal_apply]
  · simp [leftTensor, Matrix.blockDiagonal_apply, h]

/-- The trace against a constant block-diagonal operator is the sum over diagonal blocks. -/
private lemma round_trace_blockDiagonal_const_mul_eq_sum_trace_diagBlock
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (X : Op ιA) (M : Op (ιA × ιB)) :
    Matrix.trace (Matrix.blockDiagonal (fun _ : ιB => X) * M) =
      ∑ b : ιB, Matrix.trace (X * roundDiagBlock M b) := by
  classical
  let e : ((ιA × ιB) × ιA) ≃ (ιB × (ιA × ιA)) :=
    { toFun := fun x => (x.1.2, (x.1.1, x.2))
      invFun := fun x => ((x.2.1, x.1), x.2.2)
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, ⟨_, _⟩⟩ => rfl }
  simpa [roundDiagBlock, Matrix.trace, Matrix.mul_apply, Matrix.blockDiagonal_apply,
    Fintype.sum_prod_type, Finset.sum_sigma', e] using
    (e.sum_comp (fun y : ιB × (ιA × ιA) =>
      X y.2.1 y.2.2 * M (y.2.2, y.1) (y.2.1, y.1)))

/-- Evaluating a local operator in the left marginal agrees with left tensor placement. -/
private lemma round_normalizedTrace_leftMarginalDensity_mul_eq
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ρ : Op (ιA × ιB)) (X : Op ιA) :
    normalizedTrace (roundLeftMarginalDensity ρ * X) =
      normalizedTrace (ρ * leftTensor (ι₂ := ιB) X) := by
  have hcard : ((Fintype.card ιB : Error) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold normalizedTrace roundLeftMarginalDensity
  rw [smul_mul_assoc, Matrix.trace_smul, Matrix.sum_mul, Matrix.trace_sum]
  have hswap :
      ∑ b : ιB, Matrix.trace (roundDiagBlock ρ b * X) =
        ∑ b : ιB, Matrix.trace (X * roundDiagBlock ρ b) := by
    refine Finset.sum_congr rfl ?_
    intro b _
    exact Matrix.trace_mul_comm _ _
  rw [hswap, Matrix.trace_mul_comm, round_leftTensor_eq_blockDiagonal_const]
  rw [round_trace_blockDiagonal_const_mul_eq_sum_trace_diagBlock]
  simp [Fintype.card_prod]
  ring

/-- The left marginal of a normalized bipartite state is normalized. -/
private lemma roundLeftMarginalState_isNormalized {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    {ψ : QuantumState (ιA × ιB)} (hψ : ψ.IsNormalized) :
    (roundLeftMarginalState ψ).IsNormalized := by
  unfold QuantumState.IsNormalized
  have hnorm : normalizedTrace (roundLeftMarginalDensity ψ.density) =
      normalizedTrace ψ.density := by
    simpa [leftTensor_one] using
      round_normalizedTrace_leftMarginalDensity_mul_eq (ρ := ψ.density)
        (X := (1 : Op ιA))
  simpa [roundLeftMarginalState] using hnorm.trans hψ

/-- Local evaluation in the left marginal equals bipartite evaluation after placement. -/
private lemma roundLeftMarginal_ev_eq {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB)) (X : Op ιA) :
    ev ψ (leftTensor (ι₂ := ιB) X) = ev (roundLeftMarginalState ψ) X := by
  unfold ev
  rw [← Complex.ofReal_inj]
  simp [round_normalizedTrace_leftMarginalDensity_mul_eq (ρ := ψ.density) (X := X),
    roundLeftMarginalState]

/-- A finite complex matrix of rank zero is the zero matrix. -/
private lemma round_matrix_eq_zero_of_rank_eq_zero {m n : Type*}
    [Finite m] [Fintype n] (A : Matrix m n ℂ) (hA : A.rank = 0) :
    A = 0 := by
  let _ : Fintype m := Fintype.ofFinite m
  classical
  have hrange : A.mulVecLin.range = ⊥ := by
    rw [Matrix.rank] at hA
    exact Submodule.finrank_eq_zero.mp hA
  ext i j
  have hv : A.mulVecLin (Pi.single j 1) ∈ A.mulVecLin.range := ⟨Pi.single j 1, rfl⟩
  have hv0 : A.mulVecLin (Pi.single j 1) = 0 := by
    simpa [hrange] using hv
  have hentry := congrArg (fun w => w i) hv0
  simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Finset.sum_ite_eq,
    Pi.single_apply] using hentry

/-- A complete measurement on a nonzero finite space has a nonempty outcome type. -/
private theorem round_measurement_outcome_nonempty {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : MIPStarRE.Quantum.Measurement α ι) : Nonempty α := by
  classical
  by_contra hα
  haveI : IsEmpty α := not_nonempty_iff.mp hα
  let i : ι := Classical.choice inferInstance
  have heq := congrArg (fun X : Op ι => X i i) M.sum_eq_one
  simp [Matrix.sum_apply] at heq

/-- QPBT vector consistency is the LDT bipartite consistency relation on the
associated pure state and concrete measurements. -/
private lemma round_consRel_of_consistencyDefect {ιA ιB α : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] [DecidableEq α] [Nonempty ιA] [Nonempty ιB]
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (hψ : ‖ψ‖ = 1)
    (Q : MIPStarRE.Quantum.Measurement α ιA)
    (R : MIPStarRE.Quantum.Measurement α ιB) (δ : Error)
    (hcons : consistencyDefect (uniformDistribution Unit)
      (fun _ a => heteroKron (Q.effect a) 1)
      (fun _ a => heteroKron 1 (R.effect a)) ψ ≤ δ) :
    let ψp : PureState (ιA × ιB) := roundPureState ψ hψ
    let HA : FiniteHilbertSpace := roundFiniteHilbertSpace ιA
    let HB : FiniteHilbertSpace := roundFiniteHilbertSpace ιB
    let A : MIPStarRE.LDT.Measurement α ιA :=
      MatrixMeasurement.toMeasurement (H := HA) Q
    let B : MIPStarRE.LDT.Measurement α ιB :=
      MatrixMeasurement.toMeasurement (H := HB) R
    ConsRel (ψp : QuantumState (ιA × ιB)) (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas) (constSubMeasFamily B.toSubMeas) δ := by
    dsimp
    constructor
    rw [show bipartiteConsError
        (roundPureState ψ hψ : QuantumState (ιA × ιB))
        (uniformDistribution Unit)
        (constSubMeasFamily
          (MatrixSubmeasurement.toSubMeas (H := roundFiniteHilbertSpace ιA)
            Q.toSubmeasurement))
        (constSubMeasFamily
          (MatrixSubmeasurement.toSubMeas (H := roundFiniteHilbertSpace ιB)
            R.toSubmeasurement)) =
        qBipartiteConsDefect
          (roundPureState ψ hψ : QuantumState (ιA × ιB))
          (MatrixSubmeasurement.toSubMeas (H := roundFiniteHilbertSpace ιA)
            Q.toSubmeasurement)
          (MatrixSubmeasurement.toSubMeas (H := roundFiniteHilbertSpace ιB)
            R.toSubmeasurement) by
      simp [bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily]]
    rw [show qBipartiteConsDefect
        (roundPureState ψ hψ : QuantumState (ιA × ιB))
        (MatrixSubmeasurement.toSubMeas (H := roundFiniteHilbertSpace ιA)
          Q.toSubmeasurement)
        (MatrixSubmeasurement.toSubMeas (H := roundFiniteHilbertSpace ιB)
          R.toSubmeasurement) =
        ev (roundPureState ψ hψ : QuantumState (ιA × ιB)) 1 -
          qBipartiteMatchMass
            (roundPureState ψ hψ : QuantumState (ιA × ιB))
            (MatrixSubmeasurement.toSubMeas (H := roundFiniteHilbertSpace ιA)
              Q.toSubmeasurement)
            (MatrixSubmeasurement.toSubMeas (H := roundFiniteHilbertSpace ιB)
              R.toSubmeasurement) by
      simpa using qBipartiteConsDefect_of_measurements
        (roundPureState ψ hψ : QuantumState (ιA × ιB))
        (MatrixMeasurement.toMeasurement (H := roundFiniteHilbertSpace ιA) Q)
        (MatrixMeasurement.toMeasurement (H := roundFiniteHilbertSpace ιB) R)]
    rw [ev_one_of_isNormalized _ (roundPureState ψ hψ).toQuantumState_isNormalized]
    rw [show qBipartiteMatchMass (roundPureState ψ hψ : QuantumState (ιA × ιB))
        (MatrixSubmeasurement.toSubMeas (H := roundFiniteHilbertSpace ιA)
          Q.toSubmeasurement)
        (MatrixSubmeasurement.toSubMeas (H := roundFiniteHilbertSpace ιB)
          R.toSubmeasurement) =
      ∑ a : α, stateQForm ψ (heteroKron (Q.effect a) (R.effect a)) by
      unfold qBipartiteMatchMass
      apply Finset.sum_congr rfl
      intro a _
      simpa [MIPStarRE.QPBT.heteroKron, MIPStarRE.LDT.opTensor] using
        (round_stateQForm_eq_ev ψ hψ (heteroKron (Q.effect a) (R.effect a))).symm]
    have hpoint := point_defect_eq
      (DistanceCalculus.leftPlacedMeasurement (ιB := ιB) Q)
      (DistanceCalculus.rightPlacedMeasurement (ιA := ιA) R) ψ
    have hdefect : consistencyDefect (uniformDistribution Unit)
        (fun _ a => heteroKron (Q.effect a) 1)
        (fun _ a => heteroKron 1 (R.effect a)) ψ =
        1 - ∑ a : α, stateQForm ψ (heteroKron (Q.effect a) (R.effect a)) := by
      unfold consistencyDefect
      simp_rw [consistency_term_eq_stateQForm]
      rw [show avgOver (uniformDistribution Unit)
          (fun _ => ∑ a : α, ∑ b : α, if a = b then 0 else
            stateQForm ψ
              (heteroKron (Q.effect a) 1 * heteroKron 1 (R.effect b))) =
          ∑ a : α, ∑ b : α, if a = b then 0 else
            stateQForm ψ
              (heteroKron (Q.effect a) 1 * heteroKron 1 (R.effect b)) by
        simp [avgOver, uniformDistribution]]
      rw [show (∑ a : α, ∑ b : α, if a = b then 0 else
            stateQForm ψ
              (heteroKron (Q.effect a) 1 * heteroKron 1 (R.effect b))) =
          ‖ψ‖ ^ 2 - ∑ a : α,
            stateQForm ψ (heteroKron (Q.effect a) (R.effect a)) by
        have hdiag :
            (∑ a : α,
                stateQForm ψ (heteroKron (Q.effect a) (R.effect a))) =
              ∑ a : α, stateQForm ψ
                ((DistanceCalculus.leftPlacedMeasurement (ιB := ιB) Q).effect a *
                  (DistanceCalculus.rightPlacedMeasurement (ιA := ιA) R).effect a) := by
          apply Finset.sum_congr rfl
          intro a _
          symm
          simpa [DistanceCalculus.leftPlacedMeasurement,
            DistanceCalculus.rightPlacedMeasurement,
            MIPStarRE.Quantum.Measurement.ofSumEqOne] using
              DistanceCalculus.placed_product_stateQForm_eq ψ (Q.effect a) (R.effect a)
        rw [hdiag]
        simpa [DistanceCalculus.leftPlacedMeasurement,
          DistanceCalculus.rightPlacedMeasurement,
          MIPStarRE.Quantum.Measurement.ofSumEqOne] using hpoint]
      rw [hψ]
      norm_num
    rw [← hdefect]
    exact hcons

/-- The Q/X/XHat repair and canonical completion give a projective measurement
on Alice's original space with error at most `220 * δ^(1/4)`. -/
private lemma round_projective_ldt {ιA ιB α : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] [DecidableEq α] [Nonempty ιA] [Nonempty ιB]
    (Ψ : QuantumState (ιA × ιB)) (hΨ : Ψ.IsNormalized)
    (A : MIPStarRE.LDT.Measurement α ιA)
    (B : MIPStarRE.LDT.Measurement α ιB) (a₀ : α) (δ : Error)
    (hδ : 0 ≤ δ)
    (hCons : ConsRel Ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas) (constSubMeasFamily B.toSubMeas) δ) :
    ∃ C : ProjMeas α ιA,
      qSDD Ψ (leftPlacedSubMeas (ιB := ιB) A.toSubMeas)
        (leftPlacedSubMeas (ιB := ιB) C.toSubMeas) ≤
          220 * zetaQuarterRoot δ := by
  classical
  let φ : QuantumState ιA := roundLeftMarginalState Ψ
  have hφ : φ.IsNormalized := roundLeftMarginalState_isNormalized hΨ
  let t : Error := zetaQuarterRoot δ
  have ht_nonneg : 0 ≤ t := zetaQuarterRoot_nonneg hδ
  by_cases ht_small : t ≤ 1 / (24 : Error)
  · have hδ_small : δ ≤ 1 / (4 : Error) := by
      have ht_four : t ^ (4 : Nat) = δ := by
        dsimp [t, zetaQuarterRoot]
        calc
          (Real.rpow δ (1 / (4 : Error))) ^ (4 : Nat) =
              Real.rpow δ ((1 / (4 : Error)) * 4) := by
                rw [← Real.rpow_natCast]
                simpa using
                  (Real.rpow_mul hδ (1 / (4 : Error)) (4 : Error)).symm
          _ = δ := by norm_num [Real.rpow_natCast]
      have hpow := pow_le_pow_left₀ ht_nonneg ht_small 4
      rw [ht_four] at hpow
      calc
        δ ≤ (1 / (24 : Error)) ^ (4 : Nat) := hpow
        _ ≤ 1 / (4 : Error) := by norm_num
    have hAlmost := consistencyToAlmostProjective
      (ψ := Ψ) (A := A) (B := B) (ζ := δ) hCons
    have hsourceLifted := hAlmost.sourceAlmostProjective
    have hterm : ∀ a : α,
        ev Ψ
          ((leftLiftedMeasurement (ιB := ιB) A).outcome a -
            (leftLiftedMeasurement (ιB := ιB) A).outcome a *
              (leftLiftedMeasurement (ιB := ιB) A).outcome a) =
        ev φ (A.outcome a - A.outcome a * A.outcome a) := by
      intro a
      simpa [φ, leftLiftedMeasurement, leftPlacedSubMeas, leftTensor_sub,
        leftTensor_mul_leftTensor] using
        (roundLeftMarginal_ev_eq Ψ (A.outcome a - A.outcome a * A.outcome a))
    have hsource :
        ∑ a, ev φ (A.outcome a - A.outcome a * A.outcome a) ≤ 2 * δ := by
      simpa [hterm, consistencyToAlmostProjectiveError] using hsourceLifted
    obtain ⟨qLayer, hRank⟩ :=
      projectiveLowRankSum φ A δ hφ hδ hδ_small hsource
    have hq_complete :
        ev φ (QTotal qLayer) ≥ 1 - 11 * t := by
      simpa [t] using qCompleteness φ A δ qLayer hφ hδ hδ_small hRank
    have hsigma : Nonempty (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : α => (qLayer.q.outcome a).rank)) := by
      by_contra hsigma
      have hzero_rank : ∀ a : α, (qLayer.q.outcome a).rank = 0 := by
        intro a
        by_contra hrank
        have hpos : 0 < (qLayer.q.outcome a).rank := Nat.pos_of_ne_zero hrank
        have : Nonempty (FiniteHilbertSpace.sigmaFinCarrier
            (fun a : α => (qLayer.q.outcome a).rank)) := by
          refine ⟨⟨Fintype.equivFin α a, ⟨0, ?_⟩⟩⟩
          simpa [Fintype.equivFin] using hpos
        exact hsigma this
      have hzero : ∀ a : α, qLayer.q.outcome a = 0 := by
        intro a
        exact round_matrix_eq_zero_of_rank_eq_zero
          (qLayer.q.outcome a) (hzero_rank a)
      have htotal_zero : QTotal qLayer = 0 := by
        calc
          QTotal qLayer = ∑ a, qLayer.q.outcome a := hRank.sum_eq_total.symm
          _ = 0 := Finset.sum_eq_zero fun a _ => hzero a
      have : ev φ (QTotal qLayer) = 0 := by simp [htotal_zero, ev]
      rw [this] at hq_complete
      nlinarith
    letI := hsigma
    obtain ⟨_xHat, _hxHat_coisometry, _hxHat_mixed, data, hq, _hx, _hxHat, hQP⟩ :=
      pQApprox_ofRankReductionSigmaRangePositiveGram φ A δ hRank hφ hδ hδ_small
    have hRankData : RankReductionWitness φ A δ data.qLayer := by
      exact hq.symm ▸ hRank.toSigmaRangeQLayer
    have hAQ :
        SDDOpRel φ (uniformDistribution Unit)
          (constOpFamily (A.toSubMeas : OpFamily α ιA))
          (constOpFamily data.qLayer.q) (roundingToProjectiveError δ) := by
      simpa [hq] using hRank.toSigmaRangeQLayer.closeness
    have hAP :
        SDDOpRel φ (uniformDistribution Unit)
          (constOpFamily (A.toSubMeas : OpFamily α ιA))
          (constOpFamily (PFamily data)) (84 * t) := by
      have htri := MIPStarRE.LDT.Preliminaries.sddOpRel_triangle φ
        (uniformDistribution Unit)
        (constOpFamily (A.toSubMeas : OpFamily α ιA))
        (constOpFamily data.qLayer.q) (constOpFamily (PFamily data))
        (roundingToProjectiveError δ) (30 * zetaQuarterRoot δ) hAQ hQP
      refine MIPStarRE.LDT.Preliminaries.sddOpRel_mono φ
        (uniformDistribution Unit)
        (constOpFamily (A.toSubMeas : OpFamily α ιA))
        (constOpFamily (PFamily data))
        (2 * (roundingToProjectiveError δ + 30 * zetaQuarterRoot δ))
        (84 * t) htri ?_
      have htrunc : spectralTruncationError δ ≤ zetaQuarterRoot δ :=
        spectralTruncationError_le_zetaQuarterRoot δ hδ hδ_small
      dsimp [roundingToProjectiveError, spectralTruncationError, t]
      dsimp [spectralTruncationError] at htrunc
      nlinarith
    let P : ProjSubMeas α ιA := qxpProjSubMeas data
    let pMass : Error := ev φ P.toSubMeas.total
    let qMass : Error := ev φ (QTotal data.qLayer)
    let sqrtMass : Error := ev φ (CFC.sqrt (QTotal data.qLayer))
    have hqtotal_nonneg : 0 ≤ QTotal data.qLayer := by
      rw [← hRankData.sum_eq_total]
      exact Finset.sum_nonneg fun a _ => hRankData.outcome_nonneg a
    have hq_nonneg : 0 ≤ qMass := by
      dsimp [qMass]
      exact ev_nonneg_of_psd φ _ hqtotal_nonneg
    have hp_nonneg : 0 ≤ pMass := by
      exact ev_nonneg_of_psd φ P.toSubMeas.total P.toSubMeas.total_nonneg
    have hp_le_one : pMass ≤ 1 := by
      calc
        pMass ≤ ev φ (1 : Op ιA) :=
          ev_mono φ _ _ P.toSubMeas.total_le_one
        _ = 1 := ev_one_of_isNormalized φ hφ
    have hsqrt_nonneg : 0 ≤ sqrtMass := by
      exact ev_nonneg_of_psd φ _ (CFC.sqrt_nonneg (QTotal data.qLayer))
    have hsqrt_complete : sqrtMass ≥ 1 - 12 * t := by
      simpa [sqrtMass, t] using
        sqrtQCompleteness φ A δ data.qLayer hφ hδ hδ_small hRankData
    have hsupport :
        CFC.sqrt (QTotal data.qLayer) * P.toSubMeas.total =
          CFC.sqrt (QTotal data.qLayer) := by
      rw [show P.toSubMeas.total = data.xHatᴴ * data.xHat by
        exact qxpProjSubMeas_total_eq_xHat_adjoint_mul_xHat data]
      rw [← data.xHat_mixed]
      calc
        data.xᴴ * data.xHat * (data.xHatᴴ * data.xHat) =
            data.xᴴ * (data.xHat * data.xHatᴴ) * data.xHat := by
              simp only [Matrix.mul_assoc]
        _ = data.xᴴ * data.xHat := by simp [data.xHat_coisometry]
    have hq_sqrt_sq :
        CFC.sqrt (QTotal data.qLayer) * (CFC.sqrt (QTotal data.qLayer))ᴴ =
          QTotal data.qLayer := by
      have hsqrt_herm : (CFC.sqrt (QTotal data.qLayer))ᴴ =
          CFC.sqrt (QTotal data.qLayer) :=
        (Matrix.nonneg_iff_posSemidef.mp
          (CFC.sqrt_nonneg (QTotal data.qLayer))).isHermitian.eq
      calc
        CFC.sqrt (QTotal data.qLayer) * (CFC.sqrt (QTotal data.qLayer))ᴴ =
            CFC.sqrt (QTotal data.qLayer) * CFC.sqrt (QTotal data.qLayer) := by
              rw [hsqrt_herm]
        _ = QTotal data.qLayer :=
          CFC.sqrt_mul_sqrt_self _ hqtotal_nonneg
    have hp_sq : P.toSubMeas.totalᴴ * P.toSubMeas.total =
        P.toSubMeas.total := by
      rw [(Matrix.nonneg_iff_posSemidef.mp P.toSubMeas.total_nonneg).isHermitian.eq]
      exact MIPStarRE.LDT.Preliminaries.projSubMeas_total_proj P
    have hcs : |sqrtMass| ≤ Real.sqrt qMass * Real.sqrt pMass := by
      have hcs0 :=
        ev_abs_mul_le_sqrt φ (CFC.sqrt (QTotal data.qLayer)) P.toSubMeas.total
      rw [hsupport, hq_sqrt_sq, hp_sq] at hcs0
      simpa [sqrtMass, qMass, pMass] using hcs0
    have hsquare : sqrtMass ^ 2 ≤ qMass * pMass := by
      have hsquare' : |sqrtMass| ^ 2 ≤
          (Real.sqrt qMass * Real.sqrt pMass) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg sqrtMass)
          (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).2 hcs
      simpa [sq_abs, mul_pow, Real.sq_sqrt hq_nonneg,
        Real.sq_sqrt hp_nonneg] using hsquare'
    have hq_le : qMass ≤ 1 + 2 * t := by
      have hbound := ev_mono φ _ _ hRankData.total_le
      have hbound' : qMass ≤ 1 + 2 * spectralTruncationError δ := by
        have hscale :=
          ev_scale φ (1 + 2 * spectralTruncationError δ) (1 : Op ιA)
        rw [ev_one_of_isNormalized φ hφ, mul_one] at hscale
        have hscalar :
            (((1 : Error) + 2 * spectralTruncationError δ : Error) : ℂ) =
              (1 : ℂ) + 2 * (spectralTruncationError δ : ℂ) := by
          norm_num
        rw [hscalar] at hscale
        dsimp [qMass]
        exact hbound.trans_eq hscale
      have htrunc := spectralTruncationError_le_zetaQuarterRoot δ hδ hδ_small
      dsimp [t]
      linarith
    have hbase_nonneg : 0 ≤ 1 - 12 * t := by linarith
    have hbase_sq : (1 - 12 * t) ^ 2 ≤ sqrtMass ^ 2 :=
      (sq_le_sq₀ hbase_nonneg hsqrt_nonneg).2 hsqrt_complete
    have hqpmass : qMass * pMass ≤ (1 + 2 * t) * pMass :=
      mul_le_mul_of_nonneg_right hq_le hp_nonneg
    have hp_lower : 1 - 26 * t ≤ pMass := by
      nlinarith [sq_nonneg t]
    have hresidual :
        ev φ ((1 - P.toSubMeas.total) * (1 - P.toSubMeas.total)) ≤ 26 * t := by
      have hresidual_eq :
          (1 - P.toSubMeas.total) * (1 - P.toSubMeas.total) =
            1 - P.toSubMeas.total := by
        calc
          (1 - P.toSubMeas.total) * (1 - P.toSubMeas.total) =
              1 - P.toSubMeas.total - P.toSubMeas.total +
                P.toSubMeas.total * P.toSubMeas.total := by noncomm_ring
          _ = 1 - P.toSubMeas.total := by
            rw [MIPStarRE.LDT.Preliminaries.projSubMeas_total_proj P]
            abel
      rw [hresidual_eq, ev_sub, ev_one_of_isNormalized φ hφ]
      dsimp [pMass] at hp_lower
      linarith
    let C : ProjMeas α ιA :=
      MIPStarRE.LDT.Preliminaries.completeAtOutcomeProj P a₀
    have hAPq : qSDD φ A.toSubMeas P.toSubMeas ≤ 84 * t := by
      have hraw : qSDDCore φ A.outcome (PFamily data).outcome ≤ 84 * t := by
        simpa [SDDOpRel, sddErrorOp, avgOver, uniformDistribution,
          constOpFamily, qSDDOp, SubMeas.toOpFamily] using hAP.squaredDistanceBound
      unfold qSDD qSDDCore
      unfold qSDDCore at hraw
      simpa [P, PFamily, pFamilyFromXHat, Pa, qxpProjSubMeas_outcome] using hraw
    have hPCq : qSDD φ P.toSubMeas C.toSubMeas ≤ 26 * t := by
      rw [show C.toSubMeas =
          (MIPStarRE.LDT.Preliminaries.completeAtOutcome P.toSubMeas a₀).toSubMeas by
        rfl]
      rw [MIPStarRE.LDT.Preliminaries.completion_self_distance]
      exact hresidual
    have hACq : qSDD φ A.toSubMeas C.toSubMeas ≤ 220 * t := by
      calc
        qSDD φ A.toSubMeas C.toSubMeas ≤
            2 * (qSDD φ A.toSubMeas P.toSubMeas +
              qSDD φ P.toSubMeas C.toSubMeas) :=
          MIPStarRE.LDT.Preliminaries.questionSDD_triangle
            φ A.toSubMeas P.toSubMeas C.toSubMeas
        _ ≤ 2 * (84 * t + 26 * t) := by gcongr
        _ = 220 * t := by ring
    refine ⟨C, ?_⟩
    have hlift :
        qSDD Ψ (leftPlacedSubMeas (ιB := ιB) A.toSubMeas)
          (leftPlacedSubMeas (ιB := ιB) C.toSubMeas) =
        qSDD φ A.toSubMeas C.toSubMeas := by
      unfold qSDD qSDDCore
      apply Finset.sum_congr rfl
      intro a _
      simpa [φ, leftPlacedSubMeas, leftTensor_sub, leftTensor_conjTranspose,
        leftTensor_mul_leftTensor] using
        roundLeftMarginal_ev_eq Ψ
          ((A.outcome a - C.outcome a)ᴴ * (A.outcome a - C.outcome a))
    rw [hlift]
    exact hACq
  · -- Outside the small-error range, the universal distance bound is below `220 * t`.
    let Z : ProjSubMeas α ιA := zeroProjSubMeas
    let C : ProjMeas α ιA :=
      MIPStarRE.LDT.Preliminaries.completeAtOutcomeProj Z a₀
    have hAZ :
        qSDD Ψ (leftPlacedSubMeas (ιB := ιB) A.toSubMeas)
          (leftPlacedSubMeas (ιB := ιB) Z.toSubMeas) ≤ 1 :=
      qSDD_leftPlaced_zeroProjSubMeas_le_one Ψ hΨ A.toSubMeas
    have hCZ :
        qSDD Ψ (leftPlacedSubMeas (ιB := ιB) C.toSubMeas)
          (leftPlacedSubMeas (ιB := ιB) Z.toSubMeas) ≤ 1 :=
      qSDD_leftPlaced_zeroProjSubMeas_le_one Ψ hΨ C.toSubMeas
    have hZC :
        qSDD Ψ (leftPlacedSubMeas (ιB := ιB) Z.toSubMeas)
          (leftPlacedSubMeas (ιB := ιB) C.toSubMeas) ≤ 1 := by
      simpa [MIPStarRE.LDT.Preliminaries.qSDD_symm] using hCZ
    refine ⟨C, ?_⟩
    calc
      qSDD Ψ (leftPlacedSubMeas (ιB := ιB) A.toSubMeas)
          (leftPlacedSubMeas (ιB := ιB) C.toSubMeas) ≤
          2 * (qSDD Ψ (leftPlacedSubMeas (ιB := ιB) A.toSubMeas)
              (leftPlacedSubMeas (ιB := ιB) Z.toSubMeas) +
            qSDD Ψ (leftPlacedSubMeas (ιB := ιB) Z.toSubMeas)
              (leftPlacedSubMeas (ιB := ιB) C.toSubMeas)) :=
        MIPStarRE.LDT.Preliminaries.questionSDD_triangle Ψ
          (leftPlacedSubMeas (ιB := ιB) A.toSubMeas)
          (leftPlacedSubMeas (ιB := ιB) Z.toSubMeas)
          (leftPlacedSubMeas (ιB := ιB) C.toSubMeas)
      _ ≤ 4 := by linarith
      _ ≤ 220 * t := by nlinarith

/-- A consistent pair of POVMs admits an Alice-side projective rounding with
the explicit dimension-independent error `220 * δ^(1/4)`. -/
theorem projective_rounding_with_explicit_constant {ιA ιB α : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] [DecidableEq α]
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (hψ : ‖ψ‖ = 1)
    (Q : MIPStarRE.Quantum.Measurement α ιA)
    (R : MIPStarRE.Quantum.Measurement α ιB) (δ : Error) (hδ : 0 ≤ δ)
    (hcons : consistencyDefect (uniformDistribution Unit)
      (fun _ a => heteroKron (Q.effect a) 1)
      (fun _ a => heteroKron 1 (R.effect a)) ψ ≤ δ) :
    ∃ Pm : MIPStarRE.Quantum.Measurement α ιA,
      MIPStarRE.QPBT.Measurement.IsProjective Pm ∧
      opFamilyDistSq (uniformDistribution Unit)
        (fun _ a => heteroKron (Pm.effect a) 1)
        (fun _ a => heteroKron (Q.effect a) 1) ψ ≤
          220 * Real.rpow δ (1 / 4 : Error) := by
  have hι : Nonempty (ιA × ιB) := by
    by_contra hempty
    letI : IsEmpty (ιA × ιB) := not_nonempty_iff.mp hempty
    have hzero : ψ = 0 := Subsingleton.elim _ _
    rw [hzero, norm_zero] at hψ
    norm_num at hψ
  haveI : Nonempty ιA := ⟨(Classical.choice hι).1⟩
  haveI : Nonempty ιB := ⟨(Classical.choice hι).2⟩
  have hα : Nonempty α := round_measurement_outcome_nonempty Q
  letI : Nonempty α := hα
  let a₀ : α := Classical.choice hα
  let Ψ : PureState (ιA × ιB) := roundPureState ψ hψ
  let HA : FiniteHilbertSpace := roundFiniteHilbertSpace ιA
  let HB : FiniteHilbertSpace := roundFiniteHilbertSpace ιB
  let A : MIPStarRE.LDT.Measurement α ιA :=
    MatrixMeasurement.toMeasurement (H := HA) Q
  let B : MIPStarRE.LDT.Measurement α ιB :=
    MatrixMeasurement.toMeasurement (H := HB) R
  have hCons : ConsRel (Ψ : QuantumState (ιA × ιB)) (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas) (constSubMeasFamily B.toSubMeas) δ := by
    simpa [Ψ, HA, HB, A, B] using
      round_consRel_of_consistencyDefect ψ hψ Q R δ hcons
  obtain ⟨C, hC⟩ := round_projective_ldt (Ψ : QuantumState (ιA × ιB))
    Ψ.toQuantumState_isNormalized A B a₀ δ hδ hCons
  let Pm : MIPStarRE.Quantum.Measurement α ιA :=
    MIPStarRE.Quantum.Measurement.ofSumEqOne C.outcome C.outcome_pos <| by
      rw [C.sum_eq_total, C.total_eq_one]
  have hPm_projective : MIPStarRE.QPBT.Measurement.IsProjective Pm := by
    intro a
    change IsProj (C.outcome a)
    exact
      { isIdempotentElem := C.proj a
        isSelfAdjoint :=
          (Matrix.nonneg_iff_posSemidef.mp (C.outcome_pos a)).isHermitian.eq }
  refine ⟨Pm, hPm_projective, ?_⟩
  have hdist :
      opFamilyDistSq (uniformDistribution Unit)
          (fun _ a => heteroKron (Pm.effect a) 1)
          (fun _ a => heteroKron (Q.effect a) 1) ψ =
        qSDD (Ψ : QuantumState (ιA × ιB))
          (leftPlacedSubMeas (ιB := ιB) C.toSubMeas)
          (leftPlacedSubMeas (ιB := ιB) A.toSubMeas) := by
    unfold opFamilyDistSq
    rw [show avgOver (uniformDistribution Unit)
        (fun _ => ∑ a : α,
          ‖applyOperatorToState
            (heteroKron (Pm.effect a) 1 - heteroKron (Q.effect a) 1) ψ‖ ^ 2) =
        ∑ a : α,
          ‖applyOperatorToState
            (heteroKron (Pm.effect a) 1 - heteroKron (Q.effect a) 1) ψ‖ ^ 2 by
      simp [avgOver, uniformDistribution]]
    unfold qSDD qSDDCore
    apply Finset.sum_congr rfl
    intro a _
    rw [round_ev_adjoint_mul_self_eq_norm_sq ψ hψ]
    simp only [Pm, A, HA, leftPlacedSubMeas, mkLeftPlacedSubMeas_outcome,
      MatrixMeasurement.toMeasurement_outcome,
      MIPStarRE.Quantum.Measurement.ofSumEqOne]
    rfl
  rw [hdist]
  rw [MIPStarRE.LDT.Preliminaries.qSDD_symm]
  simpa [zetaQuarterRoot] using hC

end

end MIPStarRE.QPBT
