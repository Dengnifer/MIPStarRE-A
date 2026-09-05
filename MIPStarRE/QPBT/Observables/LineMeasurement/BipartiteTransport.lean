import MIPStarRE.QPBT.Observables.LineMeasurement.LinePointOverlap

/-!
# Bipartite estimates and transport for the expanded line measurements

This module collects the generic distance estimates used by items 2 and 3 of
the expanded-line consistency lemma, and the bookkeeping that transports the
placed families of the six-register expanded state to the two opposite-
placement bipartitions. The generic estimates are: the distance between two
oppositely placed complete measurements is at most twice the complement of
their diagonal overlap (`fact:agreement`), and a projective family compared
with itself followed by an effect selected through a coarse-graining is at
most as far as the coarse-grained families are from each other
(`fact:add-a-proj2` for a projective refinement).

## References

Items 2 and 3 of `lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:569-679`,
blueprint `blueprint/src/chapter/ch14_qpbt_observables.tex:1103-1210`, and
`fact:agreement`, `fact:add-a-proj2` in
`blueprint/src/chapter/ch12_qpbt_games.tex:245-313`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-! ## Generic bipartite estimates -/

namespace DistanceCalculus

/-- A projective effect is absorbed by the postprocessed effect of its own
fiber. -/
theorem effect_mul_postprocess_effect_self {α β ι : Type*} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι]
    (M : MIPStarRE.Quantum.Measurement α ι)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) (g : α → β) (a : α) :
    M.effect a * (M.postprocess g).effect (g a) = M.effect a := by
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect, Finset.mul_sum,
    Finset.sum_eq_single a]
  · exact (hM a).isIdempotentElem.eq
  · intro b _ hba
    exact projective_effect_mul_effect_eq_zero M hM (Ne.symm hba)
  · intro hnot
    exact absurd (Finset.mem_filter.mpr
      (⟨Finset.mem_univ a, rfl⟩ : a ∈ Finset.univ ∧ g a = g a)) hnot

/-- The distance between two oppositely placed complete measurements is at
most twice their inconsistency, expressed through the diagonal overlap. This
is `fact:agreement` combined with the overlap form of the consistency defect,
blueprint `ch12_qpbt_games.tex:245-254`. -/
theorem opFamilyDistSq_placed_le_two_mul_one_sub_overlap {X α ιA ιB : Type*}
    [Finite X] [Fintype α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : Distribution X) (hμ : μ.IsProbability)
    (A : X → MIPStarRE.Quantum.Measurement α ιA)
    (B : X → MIPStarRE.Quantum.Measurement α ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (hψ : ‖ψ‖ = 1) :
    opFamilyDistSq μ (fun x a => heteroKron ((A x).effect a) 1)
        (fun x a => heteroKron 1 ((B x).effect a)) ψ ≤
      2 * (1 - avgOver μ (fun x => ∑ a,
        stateQForm ψ (heteroKron ((A x).effect a) 1 *
          heteroKron 1 ((B x).effect a)))) := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  refine (WinImplications.opFamilyDistSq_placed_le_two_mul_consistencyDefect
    μ A B ψ).trans (le_of_eq ?_)
  congr 1
  exact consistencyDefect_eq_one_sub_overlap μ
    (fun x => leftPlacedMeasurement (A x))
    (fun x => rightPlacedMeasurement (B x)) ψ hμ hψ

/-- A left-placed projective family, compared with itself followed by a
right-placed effect selected through a coarse-graining, is at most as far
from it as the coarse-grained families are from each other. This is the
projective refinement step (`fact:add-a-proj2`) used to derive item 2 of
`lem:qld-comm-line-cons` from item 3, paper
`14_analysis_of_the_pauli_basis_test.tex:569-620`. -/
theorem opFamilyDistSq_left_refine_le {X α β ιA ιB : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : Distribution X) (M : X → MIPStarRE.Quantum.Measurement α ιA)
    (hM : ∀ x, MIPStarRE.QPBT.Measurement.IsProjective (M x))
    (ev : X → α → β) (B : X → MIPStarRE.Quantum.Measurement β ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    opFamilyDistSq μ (fun x a => heteroKron ((M x).effect a) 1)
        (fun x a => heteroKron ((M x).effect a) 1 *
          heteroKron 1 ((B x).effect (ev x a))) ψ ≤
      opFamilyDistSq μ
        (fun x b => heteroKron (((M x).postprocess (ev x)).effect b) 1)
        (fun x b => heteroKron 1 ((B x).effect b)) ψ := by
  unfold opFamilyDistSq
  apply avgOver_mono
  intro x
  have hrw : ∀ a : α,
      heteroKron ((M x).effect a) (1 : Op ιB) -
          heteroKron ((M x).effect a) 1 * heteroKron 1 ((B x).effect (ev x a)) =
        heteroKron ((M x).effect a) 1 *
          (heteroKron (((M x).postprocess (ev x)).effect (ev x a)) 1 -
            heteroKron 1 ((B x).effect (ev x a))) := by
    intro a
    rw [mul_sub]
    congr 1
    rw [heteroKron_mul, Matrix.mul_one,
      effect_mul_postprocess_effect_self (M x) (hM x) (ev x) a]
  simp_rw [hrw]
  exact sum_norm_mul_funIndexed_apply_le (fun a => ev x a)
    (fun a => heteroKron ((M x).effect a) (1 : Op ιB))
    (fun b => heteroKron (((M x).postprocess (ev x)).effect b) 1 -
      heteroKron 1 ((B x).effect b)) ψ
    (leftPlaced_sum_adjoint_mul_le_one (M x))

/-- The right-placed form of the projective refinement step. -/
theorem opFamilyDistSq_right_refine_le {X α β ιA ιB : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : Distribution X) (M : X → MIPStarRE.Quantum.Measurement α ιB)
    (hM : ∀ x, MIPStarRE.QPBT.Measurement.IsProjective (M x))
    (ev : X → α → β) (B : X → MIPStarRE.Quantum.Measurement β ιA)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    opFamilyDistSq μ (fun x a => heteroKron 1 ((M x).effect a))
        (fun x a => heteroKron 1 ((M x).effect a) *
          heteroKron ((B x).effect (ev x a)) 1) ψ ≤
      opFamilyDistSq μ
        (fun x b => heteroKron ((B x).effect b) 1)
        (fun x b => heteroKron 1 (((M x).postprocess (ev x)).effect b)) ψ := by
  unfold opFamilyDistSq
  apply avgOver_mono
  intro x
  have hrw : ∀ a : α,
      heteroKron (1 : Op ιA) ((M x).effect a) -
          heteroKron 1 ((M x).effect a) * heteroKron ((B x).effect (ev x a)) 1 =
        heteroKron 1 ((M x).effect a) *
          (heteroKron 1 (((M x).postprocess (ev x)).effect (ev x a)) -
            heteroKron ((B x).effect (ev x a)) 1) := by
    intro a
    rw [mul_sub]
    congr 1
    rw [heteroKron_mul, Matrix.mul_one,
      effect_mul_postprocess_effect_self (M x) (hM x) (ev x) a]
  simp_rw [hrw]
  refine (sum_norm_mul_funIndexed_apply_le (fun a => ev x a)
    (fun a => heteroKron (1 : Op ιA) ((M x).effect a))
    (fun b => heteroKron 1 (((M x).postprocess (ev x)).effect b) -
      heteroKron ((B x).effect b) 1) ψ
    (rightPlaced_sum_adjoint_mul_le_one (M x))).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← norm_neg, ← neg_sub]
  congr 2
  simp [applyOperatorToState]

end DistanceCalculus

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

/-! ## Transport between the six registers and the bipartitions -/

set_option synthInstance.maxSize 400 in
/-- On the `AA' | BA''(B'B'')` bipartition, an `AA'` placement followed by
the product with a `BA''` placement acts on the expanded state as the
corresponding left and right tensor placements. -/
theorem norm_place_AA'_sub_mul_place_BA'' (S : ProjectiveSetting P ε)
    (X : Op (S.toStrategy.ιA × PauliRegister P))
    (Y : Op (S.toStrategy.ιB × PauliRegister P)) :
    ‖applyOperatorToState (S.place .AA' X - S.place .AA' X * S.place .BA'' Y)
        S.psiHat‖ =
      ‖applyOperatorToState
        (heteroKron X (1 : Op ((S.toStrategy.ιB × PauliRegister P) ×
            (PauliRegister P × PauliRegister P))) -
          heteroKron X 1 *
            heteroKron (1 : Op (S.toStrategy.ιA × PauliRegister P))
              (heteroKron Y (1 : Op (PauliRegister P × PauliRegister P))))
        (reindexState (aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
          S.psiHat)‖ := by
  rw [WinImplications.norm_applyOperatorToState_reindexState,
    WinImplications.reindexOp_sub, WinImplications.reindexOp_mul,
    reindexOp_aaBaBipartition_left, reindexOp_aaBaBipartition_right]

set_option synthInstance.maxSize 400 in
/-- The `BA''`-first analogue of the previous transport. -/
theorem norm_place_BA''_sub_mul_place_AA' (S : ProjectiveSetting P ε)
    (X : Op (S.toStrategy.ιA × PauliRegister P))
    (Y : Op (S.toStrategy.ιB × PauliRegister P)) :
    ‖applyOperatorToState (S.place .BA'' Y - S.place .BA'' Y * S.place .AA' X)
        S.psiHat‖ =
      ‖applyOperatorToState
        (heteroKron (1 : Op (S.toStrategy.ιA × PauliRegister P))
            (heteroKron Y (1 : Op (PauliRegister P × PauliRegister P))) -
          heteroKron (1 : Op (S.toStrategy.ιA × PauliRegister P))
              (heteroKron Y (1 : Op (PauliRegister P × PauliRegister P))) *
            heteroKron X (1 : Op ((S.toStrategy.ιB × PauliRegister P) ×
              (PauliRegister P × PauliRegister P))))
        (reindexState (aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
          S.psiHat)‖ := by
  rw [WinImplications.norm_applyOperatorToState_reindexState,
    WinImplications.reindexOp_sub, WinImplications.reindexOp_mul,
    reindexOp_aaBaBipartition_left, reindexOp_aaBaBipartition_right]

set_option synthInstance.maxSize 400 in
/-- On the `AA' | BA''(B'B'')` bipartition, the overlap of left and right
tensor placements is the overlap of the `AA'` and `BA''` placements. -/
theorem stateQForm_aaBa_mul_eq (S : ProjectiveSetting P ε)
    (X : Op (S.toStrategy.ιA × PauliRegister P))
    (Y : Op (S.toStrategy.ιB × PauliRegister P)) :
    DistanceCalculus.stateQForm
        (reindexState (aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
          S.psiHat)
        (heteroKron X (1 : Op ((S.toStrategy.ιB × PauliRegister P) ×
            (PauliRegister P × PauliRegister P))) *
          heteroKron (1 : Op (S.toStrategy.ιA × PauliRegister P))
            (heteroKron Y (1 : Op (PauliRegister P × PauliRegister P)))) =
      DistanceCalculus.stateQForm S.psiHat (S.place .AA' X * S.place .BA'' Y) := by
  rw [WinImplications.stateQForm_reindexState, WinImplications.reindexOp_mul,
    reindexOp_aaBaBipartition_left, reindexOp_aaBaBipartition_right]

set_option synthInstance.maxSize 400 in
/-- On the `AB'' | BB'(A'A'')` bipartition, an `AB''` placement followed by
the product with a `BB'` placement acts on the expanded state as the
corresponding left and right tensor placements. -/
theorem norm_place_AB''_sub_mul_place_BB' (S : ProjectiveSetting P ε)
    (X : Op (S.toStrategy.ιA × PauliRegister P))
    (Y : Op (S.toStrategy.ιB × PauliRegister P)) :
    ‖applyOperatorToState (S.place .AB'' X - S.place .AB'' X * S.place .BB' Y)
        S.psiHat‖ =
      ‖applyOperatorToState
        (heteroKron X (1 : Op ((S.toStrategy.ιB × PauliRegister P) ×
            (PauliRegister P × PauliRegister P))) -
          heteroKron X 1 *
            heteroKron (1 : Op (S.toStrategy.ιA × PauliRegister P))
              (heteroKron Y (1 : Op (PauliRegister P × PauliRegister P))))
        (reindexState (abBbBipartition P S.toStrategy.ιA S.toStrategy.ιB)
          S.psiHat)‖ := by
  rw [WinImplications.norm_applyOperatorToState_reindexState,
    WinImplications.reindexOp_sub, WinImplications.reindexOp_mul,
    reindexOp_abBbBipartition_left, reindexOp_abBbBipartition_right]

set_option synthInstance.maxSize 400 in
/-- The `BB'`-first analogue of the previous transport. -/
theorem norm_place_BB'_sub_mul_place_AB'' (S : ProjectiveSetting P ε)
    (X : Op (S.toStrategy.ιA × PauliRegister P))
    (Y : Op (S.toStrategy.ιB × PauliRegister P)) :
    ‖applyOperatorToState (S.place .BB' Y - S.place .BB' Y * S.place .AB'' X)
        S.psiHat‖ =
      ‖applyOperatorToState
        (heteroKron (1 : Op (S.toStrategy.ιA × PauliRegister P))
            (heteroKron Y (1 : Op (PauliRegister P × PauliRegister P))) -
          heteroKron (1 : Op (S.toStrategy.ιA × PauliRegister P))
              (heteroKron Y (1 : Op (PauliRegister P × PauliRegister P))) *
            heteroKron X (1 : Op ((S.toStrategy.ιB × PauliRegister P) ×
              (PauliRegister P × PauliRegister P))))
        (reindexState (abBbBipartition P S.toStrategy.ιA S.toStrategy.ιB)
          S.psiHat)‖ := by
  rw [WinImplications.norm_applyOperatorToState_reindexState,
    WinImplications.reindexOp_sub, WinImplications.reindexOp_mul,
    reindexOp_abBbBipartition_left, reindexOp_abBbBipartition_right]

set_option synthInstance.maxSize 400 in
/-- On the `AB'' | BB'(A'A'')` bipartition, the overlap of left and right
tensor placements is the overlap of the `AB''` and `BB'` placements. -/
theorem stateQForm_abBb_mul_eq (S : ProjectiveSetting P ε)
    (X : Op (S.toStrategy.ιA × PauliRegister P))
    (Y : Op (S.toStrategy.ιB × PauliRegister P)) :
    DistanceCalculus.stateQForm
        (reindexState (abBbBipartition P S.toStrategy.ιA S.toStrategy.ιB)
          S.psiHat)
        (heteroKron X (1 : Op ((S.toStrategy.ιB × PauliRegister P) ×
            (PauliRegister P × PauliRegister P))) *
          heteroKron (1 : Op (S.toStrategy.ιA × PauliRegister P))
            (heteroKron Y (1 : Op (PauliRegister P × PauliRegister P)))) =
      DistanceCalculus.stateQForm S.psiHat (S.place .AB'' X * S.place .BB' Y) := by
  rw [WinImplications.stateQForm_reindexState, WinImplications.reindexOp_mul,
    reindexOp_abBbBipartition_left, reindexOp_abBbBipartition_right]

end ProjectiveSetting

end

end MIPStarRE.QPBT
