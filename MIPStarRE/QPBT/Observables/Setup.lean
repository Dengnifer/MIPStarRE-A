import MIPStarRE.QPBT.Games.StrategyClasses
import MIPStarRE.QPBT.State
import MIPStarRE.LDT.MakingMeasurementsProjective.NaimarkFull
import MIPStarRE.LDT.Preliminaries.Completion
import MIPStarRE.LDT.Test.StrategyBiProj.DirectSum

/-!
# Projective strategy setup

This module records the finite-dimensional projective dilation used before
the observable analysis and gives its explicit zero-padding isometries.

## References

The setup is `lem:projective-strategy-setup` and
`def:projective-strategy-general` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:385-475`, with paper origin
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:155-172`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.Preliminaries

noncomputable section

/-- Embed a finite Euclidean space into an equivalently indexed space by
placing its coordinates in the all-zero ancilla sector. This is the
zero-padding isometry in `lem:projective-strategy-setup`, blueprint
`ch14_qpbt_observables.tex:412-475`, paper
`14_analysis_of_the_pauli_basis_test.tex:155-172`. -/
noncomputable def padWithZeros {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {n : ℕ}
    (e : κ ≃ ι × (Fin n → Bool)) :
    EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ := by
  let L : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ κ :=
    { toFun := fun ψ => (EuclideanSpace.equiv κ ℂ).symm fun j =>
        if (e j).2 = 0 then (EuclideanSpace.equiv ι ℂ ψ) (e j).1 else 0
      map_add' := by
        intro ψ φ
        apply (EuclideanSpace.equiv κ ℂ).injective
        change (fun j => if (e j).2 = 0 then
          (EuclideanSpace.equiv ι ℂ (ψ + φ)) (e j).1 else 0) = _
        ext j
        simp only [map_add, Pi.add_apply]
        split_ifs with h <;> simp [h]
      map_smul' := by
        intro c ψ
        apply (EuclideanSpace.equiv κ ℂ).injective
        change (fun j => if (e j).2 = 0 then
          (EuclideanSpace.equiv ι ℂ (c • ψ)) (e j).1 else 0) = _
        ext j
        simp only [map_smul, Pi.smul_apply]
        split_ifs with h <;> simp [h] }
  refine { toLinearMap := L, norm_map' := fun ψ => ?_ }
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  change (∑ j : κ, ‖if (e j).2 = 0 then ψ (e j).1 else 0‖ ^ 2) = _
  change (∑ j : κ, (fun p : ι × (Fin n → Bool) =>
    ‖if p.2 = 0 then ψ p.1 else 0‖ ^ 2) (e j)) = _
  calc
    _ = ∑ p : ι × (Fin n → Bool),
        ‖if p.2 = 0 then ψ p.1 else 0‖ ^ 2 := e.sum_comp _
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single (0 : Fin n → Bool)]
      · simp
      · intro b _ hb
        simp [hb]
      · intro h
        exact (h (Finset.mem_univ _)).elim

/-- Reindex the product of two padded local spaces into the source bipartite
space followed by the two ancilla spaces. This is the explicit shuffle in
`lem:projective-strategy-setup`, blueprint
`ch14_qpbt_observables.tex:412-475`. -/
def paddedProdShuffle {ιA ιB κA κB : Type*} {nA nB : ℕ}
    (eA : κA ≃ ιA × (Fin nA → Bool))
    (eB : κB ≃ ιB × (Fin nB → Bool)) :
    κA × κB ≃ (ιA × ιB) × ((Fin nA → Bool) × (Fin nB → Bool)) :=
  (Equiv.prodCongr eA eB).trans prodShuffle

/-- Embed `Option α` into a Boolean cube, sending `none` to the zero word and
each `some a` to a one-hot word. -/
private def optionBoolEmbedding (α : Type*) [Fintype α] [DecidableEq α] :
    Option α ↪ (Fin (Fintype.card α + 1) → Bool) where
  toFun
    | none => 0
    | some a => fun i => decide (i = (Fintype.equivFin α a).castSucc)
  inj' := by
    intro x y hxy
    cases x with
    | none =>
        cases y with
        | none => rfl
        | some y =>
            have h := congrFun hxy (Fintype.equivFin α y).castSucc
            simp at h
    | some x =>
        cases y with
        | none =>
            have h := congrFun hxy (Fintype.equivFin α x).castSucc
            simp at h
        | some y =>
            have h := congrFun hxy (Fintype.equivFin α x).castSucc
            have heq : (Fintype.equivFin α x).castSucc =
                (Fintype.equivFin α y).castSucc := by
              apply of_decide_eq_true
              simpa using h.symm
            exact congrArg some ((Fintype.equivFin α).injective
              (Fin.castSucc_injective _ heq))

/-- The distinguished `none` coordinate maps to the zero Boolean word. -/
private theorem optionBoolEmbedding_none (α : Type*)
    [Fintype α] [DecidableEq α] :
    optionBoolEmbedding α none = 0 := rfl

/-- The Boolean words outside the image of the `Option` encoding. -/
private abbrev BoolAncillaCompl (α : Type*) [Fintype α] [DecidableEq α] :=
  {b : Fin (Fintype.card α + 1) → Bool //
    b ∉ Set.range (optionBoolEmbedding α)}

/-- Split the Boolean cube into the encoded `Option` coordinates and their
complement. -/
private noncomputable def optionSumComplEquiv (α : Type*)
    [Fintype α] [DecidableEq α] :
    Option α ⊕ BoolAncillaCompl α ≃ (Fin (Fintype.card α + 1) → Bool) :=
  (Equiv.sumCongr
      (Equiv.ofInjective (optionBoolEmbedding α) (optionBoolEmbedding α).injective)
      (Equiv.refl (BoolAncillaCompl α))).trans
    (Equiv.sumCompl (fun b => b ∈ Set.range (optionBoolEmbedding α)))

/-- Distribute the local Hilbert-space index over the encoded Boolean-cube
coordinates and their complement. -/
private noncomputable def paddedLocalEquiv (I α : Type*)
    [Fintype α] [DecidableEq α] :
    (I × Option α) ⊕ (I × BoolAncillaCompl α) ≃
      I × (Fin (Fintype.card α + 1) → Bool) :=
  (Equiv.prodSumDistrib I (Option α) (BoolAncillaCompl α)).symm.trans
    (Equiv.prodCongr (Equiv.refl I) (optionSumComplEquiv α))

/-- The distinguished Naimark coordinate is carried to the zero Boolean
ancilla by `paddedLocalEquiv`. -/
private theorem paddedLocalEquiv_inl_none (I α : Type*)
    [Fintype α] [DecidableEq α] (i : I) :
    paddedLocalEquiv I α (Sum.inl (i, none)) = (i, 0) := by
  simp [paddedLocalEquiv, optionSumComplEquiv, optionBoolEmbedding_none]

/-- Tensoring the two local zero-padding isometries gives the coordinate-wise
Boolean-padded state. -/
private theorem isometryTensor_padWithZeros_refl
    {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] {nA nB : ℕ}
    (ψ : EuclideanSpace ℂ (I × J)) :
    isometryTensor
        (padWithZeros (Equiv.refl (I × (Fin nA → Bool))))
        (padWithZeros (Equiv.refl (J × (Fin nB → Bool)))) ψ =
      padState (0 : Fin nA → Bool) (0 : Fin nB → Bool) ψ := by
  apply (EuclideanSpace.equiv
    ((I × (Fin nA → Bool)) × (J × (Fin nB → Bool))) ℂ).injective
  funext p
  simp only [isometryTensor, ContinuousLinearEquiv.apply_symm_apply]
  change (∑ i : I, ∑ j : J,
      (if p.1.2 = 0 then (Pi.single i 1 : I → ℂ) p.1.1 else 0) *
        (if p.2.2 = 0 then (Pi.single j 1 : J → ℂ) p.2.1 else 0) *
        ψ.ofLp (i, j)) = _
  by_cases hA : p.1.2 = 0 <;> by_cases hB : p.2.2 = 0
  · simp only [hA, hB, if_true, padState,
      ContinuousLinearEquiv.apply_symm_apply]
    rw [Finset.sum_eq_single p.1.1]
    · rw [Pi.single_eq_same, Finset.sum_eq_single p.2.1]
      · simp
      · intro j hj hjne
        rw [Pi.single_eq_of_ne hjne.symm]
        simp
      · intro h
        exact (h (Finset.mem_univ _)).elim
    · intro i hi hine
      rw [Pi.single_eq_of_ne hine.symm]
      simp
    · intro h
      exact (h (Finset.mem_univ _)).elim
  · simp [padState, hA, hB]
  · simp [padState, hA, hB]
  · simp [padState, hA, hB]

/-- A projective POVM supported on a single distinguished outcome. -/
private def trivialProjectiveMeasurement
    {α I : Type} [Fintype α] [Fintype I] [DecidableEq I]
    (a0 : α) : MIPStarRE.Quantum.Measurement α I :=
  let P : ProjMeas α I := ProjMeas.trivialDistinguishedOutcome a0
  MIPStarRE.Quantum.Measurement.ofSumEqOne P.outcome P.outcome_pos <| by
    rw [P.sum_eq_total, P.total_eq_one]

/-- The distinguished-outcome POVM is projective. -/
private theorem trivialProjectiveMeasurement_isProjective
    {α I : Type} [Fintype α] [Fintype I] [DecidableEq I]
    (a0 : α) : Measurement.IsProjective
      (trivialProjectiveMeasurement (I := I) a0) := by
  intro a
  let P : ProjMeas α I := ProjMeas.trivialDistinguishedOutcome a0
  change IsProj (P.outcome a)
  exact
    { isIdempotentElem := P.proj a
      isSelfAdjoint :=
        (Matrix.nonneg_iff_posSemidef.mp (P.outcome_pos a)).isHermitian.eq }

/-- Extend a Naimark POVM to the requested Boolean cube by a projective
measurement on the complementary coordinates. -/
private def paddedMeasurement
    {α I : Type} [Fintype α] [DecidableEq α]
    [Fintype I] [DecidableEq I]
    (a0 : α) (M : MIPStarRE.Quantum.Measurement α I) :
    MIPStarRE.Quantum.Measurement α
      (I × (Fin (Fintype.card α + 1) → Bool)) :=
  reindexMeasurement (paddedLocalEquiv I α).symm
    (blockMeasurement (dilatedMeasurement a0 M)
      (trivialProjectiveMeasurement (I := I × BoolAncillaCompl α) a0))

/-- The Boolean-cube extension of a Naimark POVM is projective. -/
private theorem paddedMeasurement_isProjective
    {α I : Type} [Fintype α] [DecidableEq α]
    [Fintype I] [DecidableEq I]
    (a0 : α) (M : MIPStarRE.Quantum.Measurement α I) :
    Measurement.IsProjective (paddedMeasurement a0 M) := by
  apply reindexMeasurement_isProjective
  apply blockMeasurement_isProjective
  · exact dilatedMeasurement_isProjective a0 M
  · exact trivialProjectiveMeasurement_isProjective a0

/-- Compressing a Boolean-cube padded effect to its zero ancilla coordinate
recovers the original POVM effect. -/
private theorem paddedMeasurement_compression
    {α I : Type} [Fintype α] [DecidableEq α]
    [Fintype I] [DecidableEq I]
    (a0 a : α) (M : MIPStarRE.Quantum.Measurement α I) (i j : I) :
    (paddedMeasurement a0 M).effect a (i, 0) (j, 0) = M.effect a i j := by
  classical
  have hi : (paddedLocalEquiv I α).symm (i, 0) = Sum.inl (i, none) := by
    apply (paddedLocalEquiv I α).injective
    simp [paddedLocalEquiv_inl_none]
  have hj : (paddedLocalEquiv I α).symm (j, 0) = Sum.inl (j, none) := by
    apply (paddedLocalEquiv I α).injective
    simp [paddedLocalEquiv_inl_none]
  change (blockMeasurement (dilatedMeasurement a0 M)
      (trivialProjectiveMeasurement (I := I × BoolAncillaCompl α) a0)).effect a
        ((paddedLocalEquiv I α).symm (i, 0))
        ((paddedLocalEquiv I α).symm (j, 0)) = M.effect a i j
  rw [hi, hj]
  change (dilatedMeasurement a0 M).effect a (i, none) (j, none) = M.effect a i j
  exact dilatedMeasurement_compression a0 a M i j

/-- Dilate each local POVM family into the Boolean-cube ancilla space and pad
the shared state at the zero ancilla coordinates. -/
private def paddedProjectiveStrategy {G : Game} (S : Strategy G)
    (a0 : G.AnswerA) (b0 : G.AnswerB) : Strategy G :=
  paddedStrategy S
    (0 : Fin (Fintype.card G.AnswerA + 1) → Bool)
    (0 : Fin (Fintype.card G.AnswerB + 1) → Bool)
    (fun x => paddedMeasurement a0 (S.A x))
    (fun y => paddedMeasurement b0 (S.B y))

/-- The locally padded strategy has projective measurements. -/
private theorem paddedProjectiveStrategy_isProjective {G : Game}
    (S : Strategy G) (a0 : G.AnswerA) (b0 : G.AnswerB) :
    (paddedProjectiveStrategy S a0 b0).IsProjective :=
  paddedStrategy_isProjective S
    (0 : Fin (Fintype.card G.AnswerA + 1) → Bool)
    (0 : Fin (Fintype.card G.AnswerB + 1) → Bool)
    (fun x => paddedMeasurement a0 (S.A x))
    (fun y => paddedMeasurement b0 (S.B y))
    (fun x => paddedMeasurement_isProjective a0 (S.A x))
    (fun y => paddedMeasurement_isProjective b0 (S.B y))

/-- Local Naimark dilation and Boolean padding preserve every game
correlation, hence the strategy value. -/
private theorem paddedProjectiveStrategy_value {G : Game} (S : Strategy G)
    (a0 : G.AnswerA) (b0 : G.AnswerB) :
    (paddedProjectiveStrategy S a0 b0).value = S.value :=
  paddedStrategy_value S
    (0 : Fin (Fintype.card G.AnswerA + 1) → Bool)
    (0 : Fin (Fintype.card G.AnswerB + 1) → Bool)
    (fun x => paddedMeasurement a0 (S.A x))
    (fun y => paddedMeasurement b0 (S.B y))
    (fun x a => paddedMeasurement_compression a0 a (S.A x))
    (fun y b => paddedMeasurement_compression b0 b (S.B y))

/-- Every finite tensor-product strategy has an equal-value projective
dilation whose state is obtained by local zero padding. This is
`lem:projective-strategy-setup`, blueprint
`blueprint/src/chapter/ch14_qpbt_observables.tex:412-475`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:155-172`.
The proof route is Naimark dilation followed by residual-projector completion. -/
theorem exists_projective_padded_strategy (G : Game) (S : Strategy G) :
    ∃ (nA nB : ℕ) (T : Strategy G)
      (eA : T.ιA ≃ S.ιA × (Fin nA → Bool))
      (eB : T.ιB ≃ S.ιB × (Fin nB → Bool)),
      T.IsProjective ∧
        reindexState (paddedProdShuffle eA eB) T.ψ =
          reindexState (paddedProdShuffle eA eB)
            (isometryTensor (padWithZeros eA) (padWithZeros eB) S.ψ) ∧
        T.value = S.value := by
  classical
  have hlocal := nonempty_of_unit_vector S.ψ S.ψ_norm
  letI : Nonempty S.ιA := hlocal.map Prod.fst
  letI : Nonempty S.ιB := hlocal.map Prod.snd
  have hquestions := nonempty_of_probability G.μ G.μ_prob
  have ha := measurement_outcome_nonempty (S.A hquestions.some.1)
  have hb := measurement_outcome_nonempty (S.B hquestions.some.2)
  let a0 : G.AnswerA := Classical.choice ha
  let b0 : G.AnswerB := Classical.choice hb
  let T : Strategy G := paddedProjectiveStrategy S a0 b0
  let eA : T.ιA ≃ S.ιA ×
      (Fin (Fintype.card G.AnswerA + 1) → Bool) := Equiv.refl _
  let eB : T.ιB ≃ S.ιB ×
      (Fin (Fintype.card G.AnswerB + 1) → Bool) := Equiv.refl _
  refine ⟨Fintype.card G.AnswerA + 1, Fintype.card G.AnswerB + 1,
    T, eA, eB, paddedProjectiveStrategy_isProjective S a0 b0, ?_,
    paddedProjectiveStrategy_value S a0 b0⟩
  apply congrArg (reindexState (paddedProdShuffle eA eB))
  change padState (0 : Fin (Fintype.card G.AnswerA + 1) → Bool)
      (0 : Fin (Fintype.card G.AnswerB + 1) → Bool) S.ψ =
    isometryTensor
      (padWithZeros (Equiv.refl (S.ιA ×
        (Fin (Fintype.card G.AnswerA + 1) → Bool))))
      (padWithZeros (Equiv.refl (S.ιB ×
        (Fin (Fintype.card G.AnswerB + 1) → Bool)))) S.ψ
  exact (isometryTensor_padWithZeros_refl S.ψ).symm

end

end MIPStarRE.QPBT
