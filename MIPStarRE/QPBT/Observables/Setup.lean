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

/-- Pad a bipartite state by zero on every nonzero Boolean ancilla
coordinate. -/
private def boolPaddedState
    {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] {nA nB : ℕ}
    (ψ : EuclideanSpace ℂ (I × J)) :
    EuclideanSpace ℂ ((I × (Fin nA → Bool)) × (J × (Fin nB → Bool))) :=
  (EuclideanSpace.equiv
    ((I × (Fin nA → Bool)) × (J × (Fin nB → Bool))) ℂ).symm
    (fun p => if p.1.2 = 0 then
      if p.2.2 = 0 then ψ.ofLp (p.1.1, p.2.1) else 0 else 0)

/-- Boolean-cube zero padding preserves the norm of a bipartite state. -/
private theorem boolPaddedState_norm
    {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] {nA nB : ℕ}
    (ψ : EuclideanSpace ℂ (I × J)) :
    ‖boolPaddedState (nA := nA) (nB := nB) ψ‖ = ‖ψ‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp only [boolPaddedState, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single (0 : Fin nA → Bool)]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_eq_single (0 : Fin nB → Bool)]
    · simp
    · intro b hb hb0
      simp [hb0]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  · intro a ha ha0
    simp [ha0]
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- Tensoring the two local zero-padding isometries gives the coordinate-wise
Boolean-padded state. -/
private theorem isometryTensor_padWithZeros_refl
    {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] {nA nB : ℕ}
    (ψ : EuclideanSpace ℂ (I × J)) :
    isometryTensor
        (padWithZeros (Equiv.refl (I × (Fin nA → Bool))))
        (padWithZeros (Equiv.refl (J × (Fin nB → Bool)))) ψ =
      boolPaddedState (nA := nA) (nB := nB) ψ := by
  apply (EuclideanSpace.equiv
    ((I × (Fin nA → Bool)) × (J × (Fin nB → Bool))) ℂ).injective
  funext p
  simp only [isometryTensor, ContinuousLinearEquiv.apply_symm_apply]
  change (∑ i : I, ∑ j : J,
      (if p.1.2 = 0 then (Pi.single i 1 : I → ℂ) p.1.1 else 0) *
        (if p.2.2 = 0 then (Pi.single j 1 : J → ℂ) p.2.1 else 0) *
        ψ.ofLp (i, j)) = _
  by_cases hA : p.1.2 = 0 <;> by_cases hB : p.2.2 = 0
  · simp only [hA, hB, if_true, boolPaddedState,
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
  · simp [boolPaddedState, hA, hB]
  · simp [boolPaddedState, hA, hB]
  · simp [boolPaddedState, hA, hB]

/-- The real quadratic form of a finite-dimensional operator. -/
private def vectorQForm {I : Type*} [Fintype I] [DecidableEq I]
    (ψ : EuclideanSpace ℂ I) (A : Op I) : ℝ :=
  (inner ℂ ψ (Matrix.toEuclideanLin A ψ)).re

/-- The quadratic form of a Boolean-padded state depends only on the
zero-ancilla compression of each local operator. -/
private theorem vectorQForm_boolPaddedState
    {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] {nA nB : ℕ}
    (ψ : EuclideanSpace ℂ (I × J))
    (A : Op I) (B : Op J)
    (A' : Op (I × (Fin nA → Bool)))
    (B' : Op (J × (Fin nB → Bool)))
    (hA : ∀ i j, A' (i, 0) (j, 0) = A i j)
    (hB : ∀ i j, B' (i, 0) (j, 0) = B i j) :
    vectorQForm (boolPaddedState (nA := nA) (nB := nB) ψ)
        (heteroKron A' B') =
      vectorQForm ψ (heteroKron A B) := by
  unfold vectorQForm
  apply congrArg Complex.re
  rw [EuclideanSpace.inner_eq_star_dotProduct,
    EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ p : (I × (Fin nA → Bool)) × (J × (Fin nB → Bool)),
      (∑ q : (I × (Fin nA → Bool)) × (J × (Fin nB → Bool)),
        heteroKron A' B' p q *
          (boolPaddedState (nA := nA) (nB := nB) ψ).ofLp q) *
        star (boolPaddedState (nA := nA) (nB := nB) ψ).ofLp p) =
    (∑ p : I × J,
      (∑ q : I × J, heteroKron A B p q * ψ.ofLp q) * star ψ.ofLp p)
  suffices hExpanded :
      (∑ i : I, ∑ a : Fin nA → Bool, ∑ j : J, ∑ b : Fin nB → Bool,
        (∑ k : I, ∑ l : J,
          A' (i, a) (k, 0) * B' (j, b) (l, 0) * ψ.ofLp (k, l)) *
            star (if a = 0 then if b = 0 then ψ.ofLp (i, j) else 0 else 0)) =
        ∑ i : I, ∑ j : J,
          (∑ k : I, ∑ l : J, A i k * B j l * ψ.ofLp (k, l)) *
            star (ψ.ofLp (i, j)) by
    simpa [boolPaddedState, heteroKron, Matrix.kronecker,
      Fintype.sum_prod_type] using hExpanded
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single (0 : Fin nA → Bool)]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_eq_single (0 : Fin nB → Bool)]
    · simp_rw [hA, hB]
      simp
    · intro b hb hb0
      simp [hb0]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  · intro a ha ha0
    simp [ha0]
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- Choose the one-measurement Naimark data associated with a POVM. -/
private def oneMeasData
    {α I : Type} [Fintype α] [DecidableEq α]
    [Fintype I] [DecidableEq I]
    (M : MIPStarRE.Quantum.Measurement α I) : OneMeasNaimarkData α I :=
  Classical.choose (oneMeasNaimark M.toSubmeasurement)

/-- The source effect family of the chosen Naimark data is the original POVM
effect family. -/
private theorem oneMeasData_source_effect
    {α I : Type} [Fintype α] [DecidableEq α]
    [Fintype I] [DecidableEq I]
    (M : MIPStarRE.Quantum.Measurement α I) :
    (oneMeasData M).source.effect = M.effect := by
  exact congrArg MIPStarRE.Quantum.Submeasurement.effect
    (Classical.choose_spec (oneMeasNaimark M.toSubmeasurement))

/-- Complete the Naimark projectors at one distinguished outcome to obtain a
projective POVM. -/
private def dilatedMeasurement
    {α I : Type} [Fintype α] [DecidableEq α]
    [Fintype I] [DecidableEq I]
    (a0 : α) (M : MIPStarRE.Quantum.Measurement α I) :
    MIPStarRE.Quantum.Measurement α (I × Option α) :=
  let P := completeAtOutcomeProj (oneMeasData M).toProjSubMeas a0
  MIPStarRE.Quantum.Measurement.ofSumEqOne P.outcome P.outcome_pos <| by
    rw [P.sum_eq_total, P.total_eq_one]

/-- Every effect of the completed Naimark measurement is a projection. -/
private theorem dilatedMeasurement_isProjective
    {α I : Type} [Fintype α] [DecidableEq α]
    [Fintype I] [DecidableEq I]
    (a0 : α) (M : MIPStarRE.Quantum.Measurement α I) :
    Measurement.IsProjective (dilatedMeasurement a0 M) := by
  intro a
  let P := completeAtOutcomeProj (oneMeasData M).toProjSubMeas a0
  change IsProj (P.outcome a)
  exact
    { isIdempotentElem := P.proj a
      isSelfAdjoint :=
        (Matrix.nonneg_iff_posSemidef.mp (P.outcome_pos a)).isHermitian.eq }

/-- Compressing a completed Naimark effect to the distinguished ancilla
coordinate recovers the original effect. -/
private theorem dilatedMeasurement_compression
    {α I : Type} [Fintype α] [DecidableEq α]
    [Fintype I] [DecidableEq I]
    (a0 a : α) (M : MIPStarRE.Quantum.Measurement α I) (i j : I) :
    (dilatedMeasurement a0 M).effect a (i, none) (j, none) = M.effect a i j := by
  let D := oneMeasData M
  let P := D.toProjSubMeas
  have hcompress (b : α) : P.outcome b (i, none) (j, none) = M.effect b i j := by
    change D.liftedEffect (some b) (i, none) (j, none) = M.effect b i j
    rw [D.compression_none_none]
    exact congrArg (fun X : Op I => X i j)
      (congrFun (oneMeasData_source_effect M) b)
  have htotal : P.total (i, none) (j, none) = (1 : Op I) i j := by
    rw [← P.sum_eq_total]
    simp_rw [Matrix.sum_apply, hcompress]
    simpa [Matrix.sum_apply] using
      congrArg (fun X : Op I => X i j) M.sum_eq_one
  simp only [dilatedMeasurement, MIPStarRE.Quantum.Measurement.ofSumEqOne]
  change ((completeAtOutcomeProj P a0).toMeasurement).outcome a
      (i, none) (j, none) = M.effect a i j
  rw [completeAtOutcomeProj_toMeasurement]
  simp only [completeAtOutcome]
  by_cases ha : a = a0
  · subst a
    rw [dif_pos rfl]
    rw [Matrix.add_apply, hcompress, Matrix.sub_apply, Matrix.one_apply, htotal]
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply]
  · rw [dif_neg ha]
    exact hcompress a

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

/-- Form the block-diagonal direct sum of two POVMs with a shared outcome
type. -/
private def blockMeasurement
    {α I J : Type} [Fintype α] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J]
    (A : MIPStarRE.Quantum.Measurement α I)
    (B : MIPStarRE.Quantum.Measurement α J) :
    MIPStarRE.Quantum.Measurement α (Sum I J) :=
  MIPStarRE.Quantum.Measurement.ofSumEqOne
    (fun a => ProjStrat.localDirectSumBlock (A.effect a) (B.effect a))
    (fun a => ProjStrat.localDirectSumBlock_nonneg (A.pos a) (B.pos a))
    (by
      calc
        (∑ a : α, ProjStrat.localDirectSumBlock (A.effect a) (B.effect a)) =
          ProjStrat.localDirectSumBlock (∑ a : α, A.effect a)
            (∑ a : α, B.effect a) := by
              simpa using ProjStrat.localDirectSumBlock_finset_sum
                Finset.univ A.effect B.effect
        _ = 1 := by
          rw [A.sum_eq_one, B.sum_eq_one, ProjStrat.localDirectSumBlock_one])

/-- A direct sum of projective POVMs is projective. -/
private theorem blockMeasurement_isProjective
    {α I J : Type} [Fintype α] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J]
    (A : MIPStarRE.Quantum.Measurement α I)
    (B : MIPStarRE.Quantum.Measurement α J)
    (hA : Measurement.IsProjective A) (hB : Measurement.IsProjective B) :
    Measurement.IsProjective (blockMeasurement A B) := by
  intro a
  change IsProj (ProjStrat.localDirectSumBlock (A.effect a) (B.effect a))
  refine { isIdempotentElem := ?_, isSelfAdjoint := ?_ }
  · change ProjStrat.localDirectSumBlock (A.effect a) (B.effect a) *
        ProjStrat.localDirectSumBlock (A.effect a) (B.effect a) = _
    rw [ProjStrat.localDirectSumBlock_mul,
      (hA a).isIdempotentElem.eq, (hB a).isIdempotentElem.eq]
  · change (ProjStrat.localDirectSumBlock (A.effect a) (B.effect a))ᴴ = _
    rw [ProjStrat.localDirectSumBlock_conjTranspose,
      (hA a).isSelfAdjoint.isHermitian.eq,
      (hB a).isSelfAdjoint.isHermitian.eq]

/-- Transport a POVM along an equivalence of finite coordinate types. -/
private noncomputable def reindexMeasurement
    {α I J : Type} [Fintype α]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ≃ J) (M : MIPStarRE.Quantum.Measurement α J) :
    MIPStarRE.Quantum.Measurement α I :=
  MIPStarRE.Quantum.Measurement.ofSumEqOne
    (fun a => reindexOp e (M.effect a))
    (fun a => MIPStarRE.Quantum.reindex_nonneg e.symm (M.pos a))
    (by
      change ∑ a : α, (Matrix.reindexAlgEquiv ℂ ℂ e.symm) (M.effect a) = 1
      rw [← map_sum, M.sum_eq_one, map_one])

/-- Reindexing a projective POVM preserves projectivity. -/
private theorem reindexMeasurement_isProjective
    {α I J : Type} [Fintype α]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ≃ J) (M : MIPStarRE.Quantum.Measurement α J)
    (hM : Measurement.IsProjective M) :
    Measurement.IsProjective (reindexMeasurement e M) := by
  intro a
  change IsProj (reindexOp e (M.effect a))
  refine { isIdempotentElem := ?_, isSelfAdjoint := ?_ }
  · change (Matrix.reindexAlgEquiv ℂ ℂ e.symm) (M.effect a) *
        (Matrix.reindexAlgEquiv ℂ ℂ e.symm) (M.effect a) =
      (Matrix.reindexAlgEquiv ℂ ℂ e.symm) (M.effect a)
    rw [← map_mul, (hM a).isIdempotentElem.eq]
  · exact (Matrix.IsHermitian.ext fun i j => by
      simp [reindexOp, Matrix.reindex_apply,
        (hM a).isSelfAdjoint.isHermitian.apply]).isSelfAdjoint

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

/-- A unit vector has a nonempty coordinate type. -/
private theorem nonempty_of_unit_vector
    {I : Type} [Fintype I]
    (ψ : EuclideanSpace ℂ I) (hψ : ‖ψ‖ = 1) : Nonempty I := by
  classical
  by_contra hI
  haveI : IsEmpty I := not_nonempty_iff.mp hI
  have hzero : ψ = 0 := Subsingleton.elim _ _
  rw [hzero, norm_zero] at hψ
  norm_num at hψ

/-- A POVM on a nonzero finite-dimensional space has an outcome. -/
private theorem measurement_outcome_nonempty
    {α I : Type} [Fintype α] [Fintype I] [DecidableEq I] [Nonempty I]
    (M : MIPStarRE.Quantum.Measurement α I) : Nonempty α := by
  classical
  by_contra hα
  haveI : IsEmpty α := not_nonempty_iff.mp hα
  let i : I := Classical.choice inferInstance
  have heq := congrArg (fun X : Op I => X i i) M.sum_eq_one
  simp [Matrix.sum_apply] at heq

/-- A probability distribution has a nonempty ambient sample type. -/
private theorem nonempty_of_probability {α : Type}
    (μ : Distribution α) (hμ : μ.IsProbability) : Nonempty α := by
  classical
  by_contra hα
  haveI : IsEmpty α := not_nonempty_iff.mp hα
  have hs : μ.support = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a
    exact isEmptyElim a
  have hsum := hμ.weight_sum_eq_one
  rw [hs] at hsum
  norm_num at hsum

/-- Dilate each local POVM family into the Boolean-cube ancilla space and pad
the shared state at the zero ancilla coordinates. -/
private def paddedProjectiveStrategy {G : Game} (S : Strategy G)
    (a0 : G.AnswerA) (b0 : G.AnswerB) : Strategy G where
  ιA := S.ιA × (Fin (Fintype.card G.AnswerA + 1) → Bool)
  ιB := S.ιB × (Fin (Fintype.card G.AnswerB + 1) → Bool)
  ψ := boolPaddedState S.ψ
  ψ_norm := (boolPaddedState_norm S.ψ).trans S.ψ_norm
  A := fun x => paddedMeasurement a0 (S.A x)
  B := fun y => paddedMeasurement b0 (S.B y)

/-- The locally padded strategy has projective measurements. -/
private theorem paddedProjectiveStrategy_isProjective {G : Game}
    (S : Strategy G) (a0 : G.AnswerA) (b0 : G.AnswerB) :
    (paddedProjectiveStrategy S a0 b0).IsProjective := by
  constructor
  · intro x
    exact paddedMeasurement_isProjective a0 (S.A x)
  · intro y
    exact paddedMeasurement_isProjective b0 (S.B y)

/-- Local Naimark dilation and Boolean padding preserve every game
correlation, hence the strategy value. -/
private theorem paddedProjectiveStrategy_value {G : Game} (S : Strategy G)
    (a0 : G.AnswerA) (b0 : G.AnswerB) :
    (paddedProjectiveStrategy S a0 b0).value = S.value := by
  unfold Strategy.value
  apply avgOver_congr
  intro xy
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hw : G.decide xy.1 xy.2 a b
  · simp only [hw, if_true]
    exact vectorQForm_boolPaddedState S.ψ
      ((S.A xy.1).effect a) ((S.B xy.2).effect b)
      ((paddedMeasurement a0 (S.A xy.1)).effect a)
      ((paddedMeasurement b0 (S.B xy.2)).effect b)
      (paddedMeasurement_compression a0 a (S.A xy.1))
      (paddedMeasurement_compression b0 b (S.B xy.2))
  · simp [hw]

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
  change boolPaddedState S.ψ =
    isometryTensor
      (padWithZeros (Equiv.refl (S.ιA ×
        (Fin (Fintype.card G.AnswerA + 1) → Bool))))
      (padWithZeros (Equiv.refl (S.ιB ×
        (Fin (Fintype.card G.AnswerB + 1) → Bool)))) S.ψ
  exact (isometryTensor_padWithZeros_refl S.ψ).symm

end

end MIPStarRE.QPBT
