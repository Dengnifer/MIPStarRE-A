import MIPStarRE.QPBT.Observables.LineMeasurement.SelfConsistency

/-!
# Overlap of expanded line and expanded point measurements

This module computes the diagonal overlap, on the expanded state, between an
expanded line measurement on one placement and the expanded point effects
selected by evaluation at the sampled point on the opposite placement. Each
product of convolution terms factorizes into a strategy overlap and an EPR
overlap; the EPR overlap of a Pauli line projector with a Pauli point projector
vanishes unless the line polynomial evaluates to the point value, and then
equals the EPR overlap of the line projector alone. Summing over the
convolution fibers identifies the expanded overlap with the overlap of the
strategy's evaluation classes and its completed point measurement. This is the
computation displayed in items 2 and 3 of the expanded-line consistency lemma.

## References

Items 2 and 3 of `lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:569-679`,
blueprint `blueprint/src/chapter/ch14_qpbt_observables.tex:1103-1210`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-! ## Linearity of the state quadratic form and of tensor placements -/

namespace DistanceCalculus

/-- The state quadratic form is additive over finite sums of operators. -/
theorem stateQForm_finset_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) {γ : Type*} (s : Finset γ) (M : γ → Op ι) :
    stateQForm ψ (∑ g ∈ s, M g) = ∑ g ∈ s, stateQForm ψ (M g) := by
  simp [stateQForm, applyOperatorToState]

/-- The state quadratic form of the zero operator vanishes. -/
theorem stateQForm_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) : stateQForm ψ (0 : Op ι) = 0 := by
  simp [stateQForm, applyOperatorToState]

end DistanceCalculus

/-- The tensor placement respects finite sums in the left factor. A public
form of this identity lives in the Magic Square rigidity development, outside
the import closure of this file. -/
private theorem heteroKron_finset_sum_left {γ ι κ : Type*} (s : Finset γ)
    (A : γ → Op ι) (B : Op κ) :
    heteroKron (∑ g ∈ s, A g) B = ∑ g ∈ s, heteroKron (A g) B := by
  ext ⟨i, k⟩ ⟨j, l⟩
  unfold heteroKron Matrix.kronecker Matrix.kroneckerMap
  simp only [Matrix.of_apply, Matrix.sum_apply]
  rw [Finset.sum_mul]

/-- The tensor placement respects finite sums in the right factor. -/
private theorem heteroKron_finset_sum_right {γ ι κ : Type*} (A : Op ι)
    (s : Finset γ) (B : γ → Op κ) :
    heteroKron A (∑ g ∈ s, B g) = ∑ g ∈ s, heteroKron A (B g) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  unfold heteroKron Matrix.kronecker Matrix.kroneckerMap
  simp only [Matrix.of_apply, Matrix.sum_apply]
  rw [Finset.mul_sum]

/-- The tensor placement of a zero right factor vanishes. -/
private theorem heteroKron_zero_right {ι κ : Type*} (A : Op ι) :
    heteroKron A (0 : Op κ) = 0 := by
  unfold heteroKron
  exact Matrix.kronecker_zero A

/-- The tensor placement of a zero left factor vanishes. -/
private theorem heteroKron_zero_left {ι κ : Type*} (B : Op κ) :
    heteroKron (0 : Op ι) B = 0 := by
  unfold heteroKron
  exact Matrix.zero_kronecker B

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

/-- A register placement respects finite sums of operators. Paper
`14_analysis_of_the_pauli_basis_test.tex:420-450`, blueprint
`ch14_qpbt_observables.tex:876-922`. -/
theorem place_finset_sum (S : ProjectiveSetting P ε) (p : Placement)
    {γ : Type*} (s : Finset γ) (O : γ → Op (S.ExpandedLocalSpace p.side)) :
    S.place p (∑ g ∈ s, O g) = ∑ g ∈ s, S.place p (O g) := by
  ext i j
  cases p <;> simp only [place, Matrix.sum_apply, Finset.sum_mul, Finset.mul_sum]

/-- A register placement of the zero operator is zero. -/
theorem place_zero (S : ProjectiveSetting P ε) (p : Placement) :
    S.place p (0 : Op (S.ExpandedLocalSpace p.side)) = 0 := by
  ext i j
  cases p <;> simp [place]

/-- The `AA'` placement respects finite sums. -/
theorem place_AA'_finset_sum (S : ProjectiveSetting P ε) {γ : Type*}
    (s : Finset γ) (O : γ → Op (S.ExpandedLocalSpace .alice)) :
    S.place .AA' (∑ g ∈ s, O g : Op (S.ExpandedLocalSpace .alice)) =
      ∑ g ∈ s, S.place .AA' (O g) :=
  place_finset_sum S .AA' s O

/-- The `BA''` placement respects finite sums. -/
theorem place_BA''_finset_sum (S : ProjectiveSetting P ε) {γ : Type*}
    (s : Finset γ) (O : γ → Op (S.ExpandedLocalSpace .bob)) :
    S.place .BA'' (∑ g ∈ s, O g : Op (S.ExpandedLocalSpace .bob)) =
      ∑ g ∈ s, S.place .BA'' (O g) :=
  place_finset_sum S .BA'' s O

/-- The `AB''` placement respects finite sums. -/
theorem place_AB''_finset_sum (S : ProjectiveSetting P ε) {γ : Type*}
    (s : Finset γ) (O : γ → Op (S.ExpandedLocalSpace .alice)) :
    S.place .AB'' (∑ g ∈ s, O g : Op (S.ExpandedLocalSpace .alice)) =
      ∑ g ∈ s, S.place .AB'' (O g) :=
  place_finset_sum S .AB'' s O

/-- The `BB'` placement respects finite sums. -/
theorem place_BB'_finset_sum (S : ProjectiveSetting P ε) {γ : Type*}
    (s : Finset γ) (O : γ → Op (S.ExpandedLocalSpace .bob)) :
    S.place .BB' (∑ g ∈ s, O g : Op (S.ExpandedLocalSpace .bob)) =
      ∑ g ∈ s, S.place .BB' (O g) :=
  place_finset_sum S .BB' s O

/-- The `AA'` placement of zero is zero. -/
theorem place_AA'_zero (S : ProjectiveSetting P ε) :
    S.place .AA' (0 : Op (S.ExpandedLocalSpace .alice)) = 0 :=
  place_zero S .AA'

/-- The `BA''` placement of zero is zero. -/
theorem place_BA''_zero (S : ProjectiveSetting P ε) :
    S.place .BA'' (0 : Op (S.ExpandedLocalSpace .bob)) = 0 :=
  place_zero S .BA''

/-- The `AB''` placement of zero is zero. -/
theorem place_AB''_zero (S : ProjectiveSetting P ε) :
    S.place .AB'' (0 : Op (S.ExpandedLocalSpace .alice)) = 0 :=
  place_zero S .AB''

/-- The `BB'` placement of zero is zero. -/
theorem place_BB'_zero (S : ProjectiveSetting P ε) :
    S.place .BB' (0 : Op (S.ExpandedLocalSpace .bob)) = 0 :=
  place_zero S .BB'

/-! ## Effects of the option-valued families -/

/-- The completed point measurement agrees with the point measurement on
proper values. -/
theorem pointMeasOption_effect_some (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (u : Fin P.m → PauliScalar P)
    (b : PauliScalar P) :
    (S.pointMeasOption side W u).effect (some b) =
      (S.pointMeas side W u).effect b := by
  unfold pointMeasOption
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
  simp [Finset.filter_eq']

/-- The completed point measurement assigns zero to the `none` outcome. -/
theorem pointMeasOption_effect_none (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (u : Fin P.m → PauliScalar P) :
    (S.pointMeasOption side W u).effect none = 0 := by
  unfold pointMeasOption
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
  apply Finset.sum_eq_zero
  intro a ha
  exact absurd (Finset.mem_filter.mp ha).2 (by simp)

/-- The completed expanded point measurement agrees with the expanded point
measurement on proper values. -/
theorem pointMeasExpOption_effect_some (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (u : Fin P.m → PauliScalar P)
    (b : PauliScalar P) :
    (S.pointMeasExpOption side W u).effect (some b) =
      (S.pointMeasExp side W u).effect b := by
  unfold pointMeasExpOption
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
  simp [Finset.filter_eq']

/-- The completed expanded point measurement assigns zero to `none`. -/
theorem pointMeasExpOption_effect_none (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (u : Fin P.m → PauliScalar P) :
    (S.pointMeasExpOption side W u).effect none = 0 := by
  unfold pointMeasExpOption
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
  apply Finset.sum_eq_zero
  intro a ha
  exact absurd (Finset.mem_filter.mp ha).2 (by simp)

/-- The expanded point effect selected by a line answer is the completed
expanded point effect at the partial evaluation of the answer. This
identifies the two presentations of item 2 and item 3 of
`lem:qld-comm-line-cons`, blueprint `ch14_qpbt_observables.tex:1098-1140`. -/
theorem pointMeasExpOption_effect_evalOpt (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (line : LineDesc P.toLdParams)
    (u : Fin P.m → PauliScalar P) (f : DegPoly P.toLdParams (P.m * P.d)) :
    (S.pointMeasExpOption side W u).effect (evalOpt line u f) =
      S.expPointEffectAtLineAnswer side W line u f := by
  unfold expPointEffectAtLineAnswer
  cases evalOpt line u f with
  | none => exact S.pointMeasExpOption_effect_none side W u
  | some a => exact S.pointMeasExpOption_effect_some side W u a

/-- The expanded point effect selected by a line answer, written through the
convolution form of the expanded point measurement. -/
theorem expPointEffectAtLineAnswer_eq_elim (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (line : LineDesc P.toLdParams)
    (u : Fin P.m → PauliScalar P) (f : DegPoly P.toLdParams (P.m * P.d)) :
    S.expPointEffectAtLineAnswer side W line u f =
      (evalOpt line u f).elim 0 (fun a =>
        ∑ q ∈ Finset.univ.filter
          (fun q : PauliScalar P × PauliScalar P => q.1 + q.2 = a),
          heteroKron ((S.pointMeas side W u).effect q.1)
            (tauPointProj W u q.2)) := by
  unfold expPointEffectAtLineAnswer
  cases evalOpt line u f with
  | none => rfl
  | some a => exact S.expPointOp_eq_convolution side W u a

/-- Effects of the expanded evaluation classes are the fiber sums of expanded
line effects. -/
theorem lineEvalMeasExp_effect (S : ProjectiveSetting P ε) (side : PlayerSide)
    (W : PauliKind) (line : LineDesc P.toLdParams)
    (u : Fin P.m → PauliScalar P) (o : Option (PauliScalar P)) :
    (S.lineEvalMeasExp side W line u).effect o =
      ∑ f ∈ Finset.univ.filter
        (fun f : DegPoly P.toLdParams (P.m * P.d) => evalOpt line u f = o),
        S.expLineOp side W line f := by
  unfold lineEvalMeasExp
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
  rfl

/-! ## Factorization of opposite placements with distinct Pauli factors -/

set_option synthInstance.maxSize 400 in
/-- The product of opposite `AA'` and `BA''` placements with distinct Pauli
factors separates into the strategy product, the first EPR-pair product, and
the identity on the second EPR pair. -/
theorem reindexOp_sixRegShuffle_place_AA'_mul_BA''_two
    (S : ProjectiveSetting P ε) (A : Op S.toStrategy.ιA)
    (B : Op S.toStrategy.ιB) (T T' : Op (PauliRegister P)) :
    reindexOp (sixRegShuffle P S.toStrategy.ιA S.toStrategy.ιB)
        (S.place .AA' (heteroKron A T) * S.place .BA'' (heteroKron B T')) =
      heteroKron (heteroKron (heteroKron A B) (heteroKron T T'))
        (1 : Op (PauliRegister P × PauliRegister P)) := by
  rw [WinImplications.reindexOp_mul,
    reindexOp_sixRegShuffle_place_AA'_heteroKron,
    reindexOp_sixRegShuffle_place_BA''_heteroKron]
  simp only [heteroKron_mul, Matrix.mul_one, Matrix.one_mul,
    heteroKron_one_one]

set_option synthInstance.maxSize 400 in
/-- The product of opposite `AB''` and `BB'` placements with distinct Pauli
factors separates into the strategy product, the identity on the first EPR
pair, and the second EPR-pair product. -/
theorem reindexOp_sixRegShuffle_place_AB''_mul_BB'_two
    (S : ProjectiveSetting P ε) (A : Op S.toStrategy.ιA)
    (B : Op S.toStrategy.ιB) (T T' : Op (PauliRegister P)) :
    reindexOp (sixRegShuffle P S.toStrategy.ιA S.toStrategy.ιB)
        (S.place .AB'' (heteroKron A T) * S.place .BB' (heteroKron B T')) =
      heteroKron (heteroKron (heteroKron A B)
          (1 : Op (PauliRegister P × PauliRegister P)))
        (heteroKron T' T) := by
  rw [WinImplications.reindexOp_mul,
    reindexOp_sixRegShuffle_place_AB''_heteroKron,
    reindexOp_sixRegShuffle_place_BB'_heteroKron]
  simp only [heteroKron_mul, Matrix.mul_one, Matrix.one_mul,
    heteroKron_one_one]

set_option synthInstance.maxSize 400 in
/-- The diagonal quadratic form for the `AA'`--`BA''` product with distinct
Pauli factors factors into the strategy overlap and the first EPR-pair
overlap. This is the factorization behind the ancillary consistency in items
2 and 3 of `lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:569-620`. -/
theorem stateQForm_place_AA'_mul_BA''_two (S : ProjectiveSetting P ε)
    (A : Op S.toStrategy.ιA) (B : Op S.toStrategy.ιB)
    (T T' : Op (PauliRegister P)) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hT : T.IsHermitian) (hT' : T'.IsHermitian) :
    DistanceCalculus.stateQForm S.psiHat
        (S.place .AA' (heteroKron A T) * S.place .BA'' (heteroKron B T')) =
      DistanceCalculus.stateQForm S.toStrategy.ψ (heteroKron A B) *
        DistanceCalculus.stateQForm (eprState (PauliRegister P))
          (heteroKron T T') := by
  have hAB : (heteroKron A B).IsHermitian :=
    heteroKron_isHermitian A B hA hB
  have hTT : (heteroKron T T').IsHermitian :=
    heteroKron_isHermitian T T' hT hT'
  have hactive :
      (heteroKron (heteroKron A B) (heteroKron T T')).IsHermitian :=
    heteroKron_isHermitian _ _ hAB hTT
  rw [psiHat_eq_reindexState, WinImplications.stateQForm_reindexState,
    reindexOp_sixRegShuffle_place_AA'_mul_BA''_two,
    stateQForm_vecTensor_heteroKron _ _ _ _ hactive Matrix.isHermitian_one,
    stateQForm_vecTensor_heteroKron _ _ _ _ hAB hTT,
    stateQForm_one_eq_norm_sq, eprState_norm]
  ring

set_option synthInstance.maxSize 400 in
/-- The diagonal quadratic form for the `AB''`--`BB'` product with distinct
Pauli factors factors into the strategy overlap and the second EPR-pair
overlap, the Pauli factor of `BB'` acting on the first half of the pair.
Paper `14_analysis_of_the_pauli_basis_test.tex:569-620`. -/
theorem stateQForm_place_AB''_mul_BB'_two (S : ProjectiveSetting P ε)
    (A : Op S.toStrategy.ιA) (B : Op S.toStrategy.ιB)
    (T T' : Op (PauliRegister P)) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hT : T.IsHermitian) (hT' : T'.IsHermitian) :
    DistanceCalculus.stateQForm S.psiHat
        (S.place .AB'' (heteroKron A T) * S.place .BB' (heteroKron B T')) =
      DistanceCalculus.stateQForm S.toStrategy.ψ (heteroKron A B) *
        DistanceCalculus.stateQForm (eprState (PauliRegister P))
          (heteroKron T' T) := by
  have hAB : (heteroKron A B).IsHermitian :=
    heteroKron_isHermitian A B hA hB
  have hpassive :
      (heteroKron (heteroKron A B)
        (1 : Op (PauliRegister P × PauliRegister P))).IsHermitian :=
    heteroKron_isHermitian _ _ hAB Matrix.isHermitian_one
  have hTT : (heteroKron T' T).IsHermitian :=
    heteroKron_isHermitian T' T hT' hT
  rw [psiHat_eq_reindexState, WinImplications.stateQForm_reindexState,
    reindexOp_sixRegShuffle_place_AB''_mul_BB'_two,
    stateQForm_vecTensor_heteroKron _ _ _ _ hpassive hTT,
    stateQForm_vecTensor_heteroKron _ _ _ _ hAB Matrix.isHermitian_one,
    stateQForm_one_eq_norm_sq, eprState_norm]
  ring

set_option synthInstance.maxSize 400 in
/-- Operators placed on `AA'` and on `BA''` commute. -/
theorem place_AA'_mul_place_BA''_comm (S : ProjectiveSetting P ε)
    (X : Op (S.ExpandedLocalSpace .alice))
    (Y : Op (S.ExpandedLocalSpace .bob)) :
    S.place .AA' X * S.place .BA'' Y = S.place .BA'' Y * S.place .AA' X := by
  have key : ∀ (X' : Op (S.toStrategy.ιA × PauliRegister P))
      (Y' : Op (S.toStrategy.ιB × PauliRegister P)),
      S.place .AA' X' * S.place .BA'' Y' = S.place .BA'' Y' * S.place .AA' X' := by
    intro X' Y'
    rw [← reindexOp_aaBaBipartition_left S X', ← reindexOp_aaBaBipartition_right S Y',
      ← WinImplications.reindexOp_mul, ← WinImplications.reindexOp_mul]
    congr 1
    rw [heteroKron_mul, heteroKron_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_one, Matrix.one_mul]
  exact key X Y

set_option synthInstance.maxSize 400 in
/-- Operators placed on `AB''` and on `BB'` commute. -/
theorem place_AB''_mul_place_BB'_comm (S : ProjectiveSetting P ε)
    (X : Op (S.ExpandedLocalSpace .alice))
    (Y : Op (S.ExpandedLocalSpace .bob)) :
    S.place .AB'' X * S.place .BB' Y = S.place .BB' Y * S.place .AB'' X := by
  have key : ∀ (X' : Op (S.toStrategy.ιA × PauliRegister P))
      (Y' : Op (S.toStrategy.ιB × PauliRegister P)),
      S.place .AB'' X' * S.place .BB' Y' = S.place .BB' Y' * S.place .AB'' X' := by
    intro X' Y'
    rw [← reindexOp_abBbBipartition_left S X', ← reindexOp_abBbBipartition_right S Y',
      ← WinImplications.reindexOp_mul, ← WinImplications.reindexOp_mul]
    congr 1
    rw [heteroKron_mul, heteroKron_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_one, Matrix.one_mul]
  exact key X Y

end ProjectiveSetting

/-! ## The overlap identity -/

/-- The convolution-fiber rearrangement behind items 2 and 3 of
`lem:qld-comm-line-cons`, at a point of the line. Here `Φ` is the expanded
overlap of two product operators on opposite placements, `Ψ` is the strategy
overlap, and `Φ` on a line term and a point term factorizes through the
ancillary consistency `tau^{W,line}_{f''}` versus `tau^{W,u}_{f''(u)}`.
Summing over the convolution fibers of the expanded line and point effects
yields the overlap of the strategy's evaluation classes with its completed
point measurement. Paper `14_analysis_of_the_pauli_basis_test.tex:569-620`,
blueprint `ch14_qpbt_observables.tex:1103-1210`. -/
theorem overlap_identity_of_mem (P : AdmissibleParams) (W : PauliKind)
    {ιL ιP : Type*} [Fintype ιL] [DecidableEq ιL] [Fintype ιP] [DecidableEq ιP]
    (LM : Measurement (DegPoly P.toLdParams (P.m * P.d)) ιL)
    (PM : Measurement (ScalarQ P.toLdParams) ιP)
    (Φ : Op (ιL × PauliRegister P) → Op (ιP × PauliRegister P) → ℝ)
    (Ψ : Op ιL → Op ιP → ℝ)
    (line : LineDesc P.toLdParams) (u : Fin P.m → ScalarQ P.toLdParams)
    (hu : u ∈ line.pointSet)
    (hΦ0 : ∀ X, Φ X 0 = 0)
    (hΦl : ∀ (s : Finset (DegPoly P.toLdParams (P.m * P.d) ×
        DegPoly P.toLdParams (P.m * P.d)))
      (X : DegPoly P.toLdParams (P.m * P.d) × DegPoly P.toLdParams (P.m * P.d) →
        Op (ιL × PauliRegister P)) (Y : Op (ιP × PauliRegister P)),
      Φ (∑ i ∈ s, X i) Y = ∑ i ∈ s, Φ (X i) Y)
    (hΦr : ∀ (X : Op (ιL × PauliRegister P))
      (t : Finset (ScalarQ P.toLdParams × ScalarQ P.toLdParams))
      (Y : ScalarQ P.toLdParams × ScalarQ P.toLdParams → Op (ιP × PauliRegister P)),
      Φ X (∑ j ∈ t, Y j) = ∑ j ∈ t, Φ X (Y j))
    (hΦfact : ∀ (f' f'' : DegPoly P.toLdParams (P.m * P.d)) (b' b'' : ScalarQ P.toLdParams),
      Φ (heteroKron (LM.effect f') (tauLineProj P W line f''))
          (heteroKron (PM.effect b') (ProjectiveSetting.tauPointProj W u b'')) =
        Ψ (LM.effect f') (PM.effect b') *
          (if evalOpt line u f'' = some b'' then
            DistanceCalculus.stateQForm (eprState (PauliRegister P))
              (heteroKron (tauLineProj P W line f'') (1 : Op (PauliRegister P)))
          else 0))
    (hΨl : ∀ (s : Finset (DegPoly P.toLdParams (P.m * P.d)))
      (A : DegPoly P.toLdParams (P.m * P.d) → Op ιL) (B : Op ιP),
      Ψ (∑ i ∈ s, A i) B = ∑ i ∈ s, Ψ (A i) B)
    (hΨ0 : ∀ A, Ψ A 0 = 0) :
    (∑ f : DegPoly P.toLdParams (P.m * P.d),
      Φ (∑ p ∈ Finset.univ.filter
          (fun p : DegPoly P.toLdParams (P.m * P.d) ×
            DegPoly P.toLdParams (P.m * P.d) => p.1 + p.2 = f),
          heteroKron (LM.effect p.1) (tauLineProj P W line p.2))
        ((evalOpt line u f).elim 0 (fun a =>
          ∑ q ∈ Finset.univ.filter
            (fun q : ScalarQ P.toLdParams × ScalarQ P.toLdParams => q.1 + q.2 = a),
            heteroKron (PM.effect q.1) (ProjectiveSetting.tauPointProj W u q.2)))) =
      ∑ o : Option (ScalarQ P.toLdParams),
        Ψ ((LM.postprocess (evalOpt line u)).effect o)
          ((PM.postprocess some).effect o) := by
  let c : DegPoly P.toLdParams (P.m * P.d) → ℝ := fun f'' =>
    DistanceCalculus.stateQForm (eprState (PauliRegister P))
      (heteroKron (tauLineProj P W line f'') (1 : Op (PauliRegister P)))
  let Pt : Option (ScalarQ P.toLdParams) → Op ιP := fun o => (PM.postprocess some).effect o
  have hPt_none : Pt none = 0 := by
    simp only [Pt]
    rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
    apply Finset.sum_eq_zero
    intro a ha
    exact absurd (Finset.mem_filter.mp ha).2 (by simp)
  have hPt_some (b : ScalarQ P.toLdParams) : Pt (some b) = PM.effect b := by
    simp only [Pt]
    rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
    simp [Finset.filter_eq']
  have hc : ∑ f'', c f'' = 1 := sum_stateQForm_eprState_tauLineProj_one P W line
  have hc0 : ∀ f'', evalOpt line u f'' = none → c f'' = 0 := by
    intro f'' h
    simp only [c]
    rw [tauLineProj_eq_zero_of_evalOpt_none P W line u hu f'' h,
      heteroKron_zero_left, DistanceCalculus.stateQForm_zero]
  have hterm : ∀ (f : DegPoly P.toLdParams (P.m * P.d))
      (p : DegPoly P.toLdParams (P.m * P.d) × DegPoly P.toLdParams (P.m * P.d)),
      p.1 + p.2 = f →
      Φ (heteroKron (LM.effect p.1) (tauLineProj P W line p.2))
          ((evalOpt line u f).elim 0 (fun a =>
            ∑ q ∈ Finset.univ.filter
              (fun q : ScalarQ P.toLdParams × ScalarQ P.toLdParams => q.1 + q.2 = a),
              heteroKron (PM.effect q.1) (ProjectiveSetting.tauPointProj W u q.2))) =
        Ψ (LM.effect p.1) (Pt (evalOpt line u p.1)) * c p.2 := by
    intro f p hp
    rcases hf : evalOpt line u f with _ | a
    · rw [Option.elim_none, hΦ0]
      rcases h1 : evalOpt line u p.1 with _ | a'
      · rw [hPt_none, hΨ0, zero_mul]
      · have h2 : evalOpt line u p.2 = none := by
          rcases h2 : evalOpt line u p.2 with _ | b
          · rfl
          · exfalso
            have hsum := evalOpt_add_of_some h1 h2
            rw [hp, hf] at hsum
            exact absurd hsum (by simp)
        rw [hc0 p.2 h2, mul_zero]
    · rw [Option.elim_some, hΦr]
      simp_rw [hΦfact]
      rcases h2 : evalOpt line u p.2 with _ | c''
      · have h1 : evalOpt line u p.1 = none := by
          rcases h1 : evalOpt line u p.1 with _ | a'
          · rfl
          · exfalso
            have hsum : evalOpt line u (p.2 + p.1) = some a := by
              rw [add_comm, hp, hf]
            have h2' := evalOpt_left_of_add_some hsum h1
            rw [h2] at h2'
            exact absurd h2' (by simp)
        rw [h1, hPt_none, hΨ0, zero_mul]
        refine Finset.sum_eq_zero fun q _ => ?_
        rw [if_neg (by simp), mul_zero]
      · have hsum : evalOpt line u (p.1 + p.2) = some a := by rw [hp, hf]
        have h1 : evalOpt line u p.1 = some (a - c'') :=
          evalOpt_left_of_add_some hsum h2
        rw [h1, hPt_some]
        rw [Finset.sum_eq_single (a - c'', c'')]
        · change Ψ (LM.effect p.1) (PM.effect (a - c'')) *
            (if some c'' = some c'' then c p.2 else 0) =
              Ψ (LM.effect p.1) (PM.effect (a - c'')) * c p.2
          rw [if_pos rfl]
        · intro q hq hne
          rw [if_neg, mul_zero]
          intro heq
          apply hne
          have hq2 : q.2 = c'' := (Option.some_inj.mp heq).symm
          have hq1 : q.1 + q.2 = a := (Finset.mem_filter.mp hq).2
          ext
          · change q.1 = a - c''
            rw [← hq1, hq2, add_sub_cancel_right]
          · exact hq2
        · intro hnot
          exfalso
          exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, sub_add_cancel a c''⟩)
  calc
    _ = ∑ f : DegPoly P.toLdParams (P.m * P.d),
        ∑ p ∈ Finset.univ.filter
          (fun p : DegPoly P.toLdParams (P.m * P.d) ×
            DegPoly P.toLdParams (P.m * P.d) => p.1 + p.2 = f),
          Ψ (LM.effect p.1) (Pt (evalOpt line u p.1)) * c p.2 := by
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [hΦl]
      exact Finset.sum_congr rfl fun p hp => hterm f p (Finset.mem_filter.mp hp).2
    _ = ∑ p : DegPoly P.toLdParams (P.m * P.d) × DegPoly P.toLdParams (P.m * P.d),
        Ψ (LM.effect p.1) (Pt (evalOpt line u p.1)) * c p.2 :=
      Finset.sum_fiberwise Finset.univ
        (fun p : DegPoly P.toLdParams (P.m * P.d) ×
          DegPoly P.toLdParams (P.m * P.d) => p.1 + p.2)
        (fun p => Ψ (LM.effect p.1) (Pt (evalOpt line u p.1)) * c p.2)
    _ = ∑ f' : DegPoly P.toLdParams (P.m * P.d),
        Ψ (LM.effect f') (Pt (evalOpt line u f')) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun f' _ => ?_
      change ∑ y, Ψ (LM.effect f') (Pt (evalOpt line u f')) * c y =
        Ψ (LM.effect f') (Pt (evalOpt line u f'))
      rw [← Finset.mul_sum, hc, mul_one]
    _ = ∑ o : Option (ScalarQ P.toLdParams),
        ∑ f' ∈ Finset.univ.filter
          (fun f' : DegPoly P.toLdParams (P.m * P.d) => evalOpt line u f' = o),
          Ψ (LM.effect f') (Pt o) := by
      rw [← Finset.sum_fiberwise Finset.univ (fun f' => evalOpt line u f')
        (fun f' => Ψ (LM.effect f') (Pt (evalOpt line u f')))]
      refine Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun f' hf' => ?_
      rw [(Finset.mem_filter.mp hf').2]
    _ = ∑ o : Option (ScalarQ P.toLdParams),
        Ψ ((LM.postprocess (evalOpt line u)).effect o) (Pt o) := by
      refine Finset.sum_congr rfl fun o _ => ?_
      rw [MIPStarRE.Quantum.Measurement.postprocess_effect, hΨl]

/-- Off the line, both sides of the overlap identity vanish: no line
polynomial evaluates, so the selected point effects are zero and the
evaluation classes with a proper value are empty. -/
theorem overlap_identity_of_not_mem (P : AdmissibleParams) (W : PauliKind)
    {ιL ιP : Type*} [Fintype ιL] [DecidableEq ιL] [Fintype ιP] [DecidableEq ιP]
    (LM : Measurement (DegPoly P.toLdParams (P.m * P.d)) ιL)
    (PM : Measurement (ScalarQ P.toLdParams) ιP)
    (Φ : Op (ιL × PauliRegister P) → Op (ιP × PauliRegister P) → ℝ)
    (Ψ : Op ιL → Op ιP → ℝ)
    (line : LineDesc P.toLdParams) (u : Fin P.m → ScalarQ P.toLdParams)
    (hu : u ∉ line.pointSet)
    (hΦ0 : ∀ X, Φ X 0 = 0)
    (hΨl : ∀ (s : Finset (DegPoly P.toLdParams (P.m * P.d)))
      (A : DegPoly P.toLdParams (P.m * P.d) → Op ιL) (B : Op ιP),
      Ψ (∑ i ∈ s, A i) B = ∑ i ∈ s, Ψ (A i) B)
    (hΨ0 : ∀ A, Ψ A 0 = 0) :
    (∑ f : DegPoly P.toLdParams (P.m * P.d),
      Φ (∑ p ∈ Finset.univ.filter
          (fun p : DegPoly P.toLdParams (P.m * P.d) ×
            DegPoly P.toLdParams (P.m * P.d) => p.1 + p.2 = f),
          heteroKron (LM.effect p.1) (tauLineProj P W line p.2))
        ((evalOpt line u f).elim 0 (fun a =>
          ∑ q ∈ Finset.univ.filter
            (fun q : ScalarQ P.toLdParams × ScalarQ P.toLdParams => q.1 + q.2 = a),
            heteroKron (PM.effect q.1) (ProjectiveSetting.tauPointProj W u q.2)))) =
      ∑ o : Option (ScalarQ P.toLdParams),
        Ψ ((LM.postprocess (evalOpt line u)).effect o)
          ((PM.postprocess some).effect o) := by
  have hnone : ∀ f : DegPoly P.toLdParams (P.m * P.d), evalOpt line u f = none :=
    fun f => evalOpt_eq_none_of_not_mem hu f
  rw [Finset.sum_eq_zero fun f _ => by rw [hnone f, Option.elim_none, hΦ0]]
  symm
  refine Finset.sum_eq_zero fun o _ => ?_
  rcases o with _ | b
  · have hPt : (PM.postprocess some).effect none = 0 := by
      rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
      apply Finset.sum_eq_zero
      intro a ha
      exact absurd (Finset.mem_filter.mp ha).2 (by simp)
    rw [hPt, hΨ0]
  · have hempty : Finset.univ.filter
        (fun f' : DegPoly P.toLdParams (P.m * P.d) => evalOpt line u f' = some b) =
          ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro f' _ h
      rw [hnone f'] at h
      exact absurd h (by simp)
    rw [MIPStarRE.Quantum.Measurement.postprocess_effect, hempty, Finset.sum_empty]
    simpa using hΨl ∅ (fun _ => 0) ((PM.postprocess some).effect (some b))

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

/-! ## The four placement pairs -/

/-- Hermitian-ness of a strategy line effect. -/
private theorem lineMeas_effect_isHermitian (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (line : LineDesc P.toLdParams)
    (f : DegPoly P.toLdParams (P.m * P.d)) :
    ((S.lineMeas side W line).effect f).IsHermitian :=
  (Matrix.nonneg_iff_posSemidef.mp ((S.lineMeas side W line).pos f)).isHermitian

/-- Hermitian-ness of a strategy point effect. -/
private theorem pointMeas_effect_isHermitian (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (u : Fin P.m → PauliScalar P)
    (b : PauliScalar P) :
    ((S.pointMeas side W u).effect b).IsHermitian :=
  (Matrix.nonneg_iff_posSemidef.mp ((S.pointMeas side W u).pos b)).isHermitian

/-- Hermitian-ness of a Pauli line projector. -/
private theorem tauLineProj_isHermitian (W : PauliKind)
    (line : LineDesc P.toLdParams) (f : DegPoly P.toLdParams (P.m * P.d)) :
    (tauLineProj P W line f).IsHermitian :=
  (Matrix.nonneg_iff_posSemidef.mp (tauLineProj_nonneg P W line f)).isHermitian

/-- Hermitian-ness of a Pauli point projector. -/
private theorem tauPointProj_isHermitian (W : PauliKind)
    (u : Fin P.m → PauliScalar P) (b : PauliScalar P) :
    (tauPointProj W u b).IsHermitian :=
  (Matrix.nonneg_iff_posSemidef.mp ((tauPointMeas W u).pos b)).isHermitian

set_option synthInstance.maxSize 400 in
/-- The expanded overlap of Alice's line measurement on `AA'` with Bob's
selected point effects on `BA''` is the strategy overlap of Alice's
evaluation classes with Bob's completed point measurement. This is the
computation `eq:qld-mhat-line-1`--`eq:qld-comm-line-pt-cons-eps` of
`lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:569-620`. -/
theorem overlap_AA'_BA''_eq (S : ProjectiveSetting P ε) (W : PauliKind)
    (line : LineDesc P.toLdParams) (u : Fin P.m → PauliScalar P) :
    ∑ f : DegPoly P.toLdParams (P.m * P.d),
        DistanceCalculus.stateQForm S.psiHat
          (S.place .AA' (S.expLineOp .alice W line f) *
            S.place .BA'' (S.expPointEffectAtLineAnswer .bob W line u f)) =
      ∑ o : Option (PauliScalar P),
        DistanceCalculus.stateQForm S.toStrategy.ψ
          (heteroKron ((S.lineEvalMeas .alice W line u).effect o)
            ((S.pointMeasOption .bob W u).effect o)) := by
  let Φ : Op (S.ExpandedLocalSpace .alice) →
      Op (S.ExpandedLocalSpace .bob) → ℝ := fun X Y =>
    DistanceCalculus.stateQForm S.psiHat (S.place .AA' X * S.place .BA'' Y)
  let Ψ : Op S.toStrategy.ιA → Op S.toStrategy.ιB → ℝ := fun L Q =>
    DistanceCalculus.stateQForm S.toStrategy.ψ (heteroKron L Q)
  have hΦ0 : ∀ X, Φ X 0 = 0 := by
    intro X
    simp only [Φ]
    rw [place_BA''_zero, mul_zero, DistanceCalculus.stateQForm_zero]
  have hΦl : ∀ (s : Finset (DegPoly P.toLdParams (P.m * P.d) ×
        DegPoly P.toLdParams (P.m * P.d)))
      (X : DegPoly P.toLdParams (P.m * P.d) × DegPoly P.toLdParams (P.m * P.d) →
        Op (S.ExpandedLocalSpace .alice))
      (Y : Op (S.ExpandedLocalSpace .bob)),
      Φ (∑ i ∈ s, X i) Y = ∑ i ∈ s, Φ (X i) Y := by
    intro s X Y
    simp only [Φ]
    rw [place_AA'_finset_sum, Finset.sum_mul,
      DistanceCalculus.stateQForm_finset_sum]
  have hΦr : ∀ (X : Op (S.ExpandedLocalSpace .alice))
      (t : Finset (PauliScalar P × PauliScalar P))
      (Y : PauliScalar P × PauliScalar P → Op (S.ExpandedLocalSpace .bob)),
      Φ X (∑ j ∈ t, Y j) = ∑ j ∈ t, Φ X (Y j) := by
    intro X t Y
    simp only [Φ]
    rw [place_BA''_finset_sum, Finset.mul_sum,
      DistanceCalculus.stateQForm_finset_sum]
  have hΨl : ∀ (s : Finset (DegPoly P.toLdParams (P.m * P.d)))
      (A : DegPoly P.toLdParams (P.m * P.d) → Op S.toStrategy.ιA)
      (B : Op S.toStrategy.ιB), Ψ (∑ i ∈ s, A i) B = ∑ i ∈ s, Ψ (A i) B := by
    intro s A B
    simp only [Ψ]
    rw [heteroKron_finset_sum_left, DistanceCalculus.stateQForm_finset_sum]
  have hΨ0 : ∀ A, Ψ A 0 = 0 := by
    intro A
    simp only [Ψ]
    rw [heteroKron_zero_right, DistanceCalculus.stateQForm_zero]
  change ∑ f, Φ (S.expLineOp .alice W line f)
      (S.expPointEffectAtLineAnswer .bob W line u f) =
    ∑ o, Ψ (((S.lineMeas .alice W line).postprocess (evalOpt line u)).effect o)
      (((S.pointMeas .bob W u).postprocess some).effect o)
  simp_rw [expPointEffectAtLineAnswer_eq_elim]
  by_cases hu : u ∈ line.pointSet
  · have hΦfact : ∀ (f' f'' : DegPoly P.toLdParams (P.m * P.d))
        (b' b'' : PauliScalar P),
        Φ (heteroKron ((S.lineMeas .alice W line).effect f')
            (tauLineProj P W line f''))
          (heteroKron ((S.pointMeas .bob W u).effect b') (tauPointProj W u b'')) =
        Ψ ((S.lineMeas .alice W line).effect f') ((S.pointMeas .bob W u).effect b') *
          (if evalOpt line u f'' = some b'' then
            DistanceCalculus.stateQForm (eprState (PauliRegister P))
              (heteroKron (tauLineProj P W line f'') (1 : Op (PauliRegister P)))
          else 0) := by
      intro f' f'' b' b''
      simp only [Φ, Ψ]
      have hfac := stateQForm_place_AA'_mul_BA''_two S
        ((S.lineMeas .alice W line).effect f') ((S.pointMeas .bob W u).effect b')
        (tauLineProj P W line f'') (tauPointProj W u b'')
        (lineMeas_effect_isHermitian S .alice W line f')
        (pointMeas_effect_isHermitian S .bob W u b')
        (tauLineProj_isHermitian W line f'') (tauPointProj_isHermitian W u b'')
      rw [stateQForm_eprState_tauLineProj_tauPointProj P W line u hu f'' b''] at hfac
      exact hfac
    exact overlap_identity_of_mem P W (S.lineMeas .alice W line)
      (S.pointMeas .bob W u) Φ Ψ line u hu hΦ0 hΦl hΦr hΦfact hΨl hΨ0
  · exact overlap_identity_of_not_mem P W (S.lineMeas .alice W line)
      (S.pointMeas .bob W u) Φ Ψ line u hu hΦ0 hΨl hΨ0

set_option synthInstance.maxSize 400 in
/-- The expanded overlap of Bob's line measurement on `BA''` with Alice's
selected point effects on `AA'` is the strategy overlap of Alice's completed
point measurement with Bob's evaluation classes. This is the interchanged
form of the computation in items 2 and 3 of `lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:569-620`. -/
theorem overlap_BA''_AA'_eq (S : ProjectiveSetting P ε) (W : PauliKind)
    (line : LineDesc P.toLdParams) (u : Fin P.m → PauliScalar P) :
    ∑ f : DegPoly P.toLdParams (P.m * P.d),
        DistanceCalculus.stateQForm S.psiHat
          (S.place .BA'' (S.expLineOp .bob W line f) *
            S.place .AA' (S.expPointEffectAtLineAnswer .alice W line u f)) =
      ∑ o : Option (PauliScalar P),
        DistanceCalculus.stateQForm S.toStrategy.ψ
          (heteroKron ((S.pointMeasOption .alice W u).effect o)
            ((S.lineEvalMeas .bob W line u).effect o)) := by
  let Φ : Op (S.ExpandedLocalSpace .bob) →
      Op (S.ExpandedLocalSpace .alice) → ℝ := fun X Y =>
    DistanceCalculus.stateQForm S.psiHat (S.place .BA'' X * S.place .AA' Y)
  let Ψ : Op S.toStrategy.ιB → Op S.toStrategy.ιA → ℝ := fun L Q =>
    DistanceCalculus.stateQForm S.toStrategy.ψ (heteroKron Q L)
  have hΦ0 : ∀ X, Φ X 0 = 0 := by
    intro X
    simp only [Φ]
    rw [place_AA'_zero, mul_zero, DistanceCalculus.stateQForm_zero]
  have hΦl : ∀ (s : Finset (DegPoly P.toLdParams (P.m * P.d) ×
        DegPoly P.toLdParams (P.m * P.d)))
      (X : DegPoly P.toLdParams (P.m * P.d) × DegPoly P.toLdParams (P.m * P.d) →
        Op (S.ExpandedLocalSpace .bob))
      (Y : Op (S.ExpandedLocalSpace .alice)),
      Φ (∑ i ∈ s, X i) Y = ∑ i ∈ s, Φ (X i) Y := by
    intro s X Y
    simp only [Φ]
    rw [place_BA''_finset_sum, Finset.sum_mul,
      DistanceCalculus.stateQForm_finset_sum]
  have hΦr : ∀ (X : Op (S.ExpandedLocalSpace .bob))
      (t : Finset (PauliScalar P × PauliScalar P))
      (Y : PauliScalar P × PauliScalar P → Op (S.ExpandedLocalSpace .alice)),
      Φ X (∑ j ∈ t, Y j) = ∑ j ∈ t, Φ X (Y j) := by
    intro X t Y
    simp only [Φ]
    rw [place_AA'_finset_sum, Finset.mul_sum,
      DistanceCalculus.stateQForm_finset_sum]
  have hΨl : ∀ (s : Finset (DegPoly P.toLdParams (P.m * P.d)))
      (A : DegPoly P.toLdParams (P.m * P.d) → Op S.toStrategy.ιB)
      (B : Op S.toStrategy.ιA), Ψ (∑ i ∈ s, A i) B = ∑ i ∈ s, Ψ (A i) B := by
    intro s A B
    simp only [Ψ]
    rw [heteroKron_finset_sum_right, DistanceCalculus.stateQForm_finset_sum]
  have hΨ0 : ∀ A, Ψ A 0 = 0 := by
    intro A
    simp only [Ψ]
    rw [heteroKron_zero_left, DistanceCalculus.stateQForm_zero]
  change ∑ f, Φ (S.expLineOp .bob W line f)
      (S.expPointEffectAtLineAnswer .alice W line u f) =
    ∑ o, Ψ (((S.lineMeas .bob W line).postprocess (evalOpt line u)).effect o)
      (((S.pointMeas .alice W u).postprocess some).effect o)
  simp_rw [expPointEffectAtLineAnswer_eq_elim]
  by_cases hu : u ∈ line.pointSet
  · have hΦfact : ∀ (f' f'' : DegPoly P.toLdParams (P.m * P.d))
        (b' b'' : PauliScalar P),
        Φ (heteroKron ((S.lineMeas .bob W line).effect f')
            (tauLineProj P W line f''))
          (heteroKron ((S.pointMeas .alice W u).effect b') (tauPointProj W u b'')) =
        Ψ ((S.lineMeas .bob W line).effect f') ((S.pointMeas .alice W u).effect b') *
          (if evalOpt line u f'' = some b'' then
            DistanceCalculus.stateQForm (eprState (PauliRegister P))
              (heteroKron (tauLineProj P W line f'') (1 : Op (PauliRegister P)))
          else 0) := by
      intro f' f'' b' b''
      simp only [Φ, Ψ]
      have hfac := stateQForm_place_AA'_mul_BA''_two S
        ((S.pointMeas .alice W u).effect b') ((S.lineMeas .bob W line).effect f')
        (tauPointProj W u b'') (tauLineProj P W line f'')
        (pointMeas_effect_isHermitian S .alice W u b')
        (lineMeas_effect_isHermitian S .bob W line f')
        (tauPointProj_isHermitian W u b'') (tauLineProj_isHermitian W line f'')
      rw [stateQForm_eprState_tauPointProj_tauLineProj P W line u hu f'' b''] at hfac
      have hcomm := place_AA'_mul_place_BA''_comm S
        (heteroKron ((S.pointMeas .alice W u).effect b') (tauPointProj W u b''))
        (heteroKron ((S.lineMeas .bob W line).effect f') (tauLineProj P W line f''))
      exact (congrArg (DistanceCalculus.stateQForm S.psiHat) hcomm.symm).trans hfac
    exact overlap_identity_of_mem P W (S.lineMeas .bob W line)
      (S.pointMeas .alice W u) Φ Ψ line u hu hΦ0 hΦl hΦr hΦfact hΨl hΨ0
  · exact overlap_identity_of_not_mem P W (S.lineMeas .bob W line)
      (S.pointMeas .alice W u) Φ Ψ line u hu hΦ0 hΨl hΨ0

set_option synthInstance.maxSize 400 in
/-- The expanded overlap of Alice's line measurement on `AB''` with Bob's
selected point effects on `BB'`, on the second bipartition. Paper
`14_analysis_of_the_pauli_basis_test.tex:569-620`. -/
theorem overlap_AB''_BB'_eq (S : ProjectiveSetting P ε) (W : PauliKind)
    (line : LineDesc P.toLdParams) (u : Fin P.m → PauliScalar P) :
    ∑ f : DegPoly P.toLdParams (P.m * P.d),
        DistanceCalculus.stateQForm S.psiHat
          (S.place .AB'' (S.expLineOp .alice W line f) *
            S.place .BB' (S.expPointEffectAtLineAnswer .bob W line u f)) =
      ∑ o : Option (PauliScalar P),
        DistanceCalculus.stateQForm S.toStrategy.ψ
          (heteroKron ((S.lineEvalMeas .alice W line u).effect o)
            ((S.pointMeasOption .bob W u).effect o)) := by
  let Φ : Op (S.ExpandedLocalSpace .alice) →
      Op (S.ExpandedLocalSpace .bob) → ℝ := fun X Y =>
    DistanceCalculus.stateQForm S.psiHat (S.place .AB'' X * S.place .BB' Y)
  let Ψ : Op S.toStrategy.ιA → Op S.toStrategy.ιB → ℝ := fun L Q =>
    DistanceCalculus.stateQForm S.toStrategy.ψ (heteroKron L Q)
  have hΦ0 : ∀ X, Φ X 0 = 0 := by
    intro X
    simp only [Φ]
    rw [place_BB'_zero, mul_zero, DistanceCalculus.stateQForm_zero]
  have hΦl : ∀ (s : Finset (DegPoly P.toLdParams (P.m * P.d) ×
        DegPoly P.toLdParams (P.m * P.d)))
      (X : DegPoly P.toLdParams (P.m * P.d) × DegPoly P.toLdParams (P.m * P.d) →
        Op (S.ExpandedLocalSpace .alice))
      (Y : Op (S.ExpandedLocalSpace .bob)),
      Φ (∑ i ∈ s, X i) Y = ∑ i ∈ s, Φ (X i) Y := by
    intro s X Y
    simp only [Φ]
    rw [place_AB''_finset_sum, Finset.sum_mul,
      DistanceCalculus.stateQForm_finset_sum]
  have hΦr : ∀ (X : Op (S.ExpandedLocalSpace .alice))
      (t : Finset (PauliScalar P × PauliScalar P))
      (Y : PauliScalar P × PauliScalar P → Op (S.ExpandedLocalSpace .bob)),
      Φ X (∑ j ∈ t, Y j) = ∑ j ∈ t, Φ X (Y j) := by
    intro X t Y
    simp only [Φ]
    rw [place_BB'_finset_sum, Finset.mul_sum,
      DistanceCalculus.stateQForm_finset_sum]
  have hΨl : ∀ (s : Finset (DegPoly P.toLdParams (P.m * P.d)))
      (A : DegPoly P.toLdParams (P.m * P.d) → Op S.toStrategy.ιA)
      (B : Op S.toStrategy.ιB), Ψ (∑ i ∈ s, A i) B = ∑ i ∈ s, Ψ (A i) B := by
    intro s A B
    simp only [Ψ]
    rw [heteroKron_finset_sum_left, DistanceCalculus.stateQForm_finset_sum]
  have hΨ0 : ∀ A, Ψ A 0 = 0 := by
    intro A
    simp only [Ψ]
    rw [heteroKron_zero_right, DistanceCalculus.stateQForm_zero]
  change ∑ f, Φ (S.expLineOp .alice W line f)
      (S.expPointEffectAtLineAnswer .bob W line u f) =
    ∑ o, Ψ (((S.lineMeas .alice W line).postprocess (evalOpt line u)).effect o)
      (((S.pointMeas .bob W u).postprocess some).effect o)
  simp_rw [expPointEffectAtLineAnswer_eq_elim]
  by_cases hu : u ∈ line.pointSet
  · have hΦfact : ∀ (f' f'' : DegPoly P.toLdParams (P.m * P.d))
        (b' b'' : PauliScalar P),
        Φ (heteroKron ((S.lineMeas .alice W line).effect f')
            (tauLineProj P W line f''))
          (heteroKron ((S.pointMeas .bob W u).effect b') (tauPointProj W u b'')) =
        Ψ ((S.lineMeas .alice W line).effect f') ((S.pointMeas .bob W u).effect b') *
          (if evalOpt line u f'' = some b'' then
            DistanceCalculus.stateQForm (eprState (PauliRegister P))
              (heteroKron (tauLineProj P W line f'') (1 : Op (PauliRegister P)))
          else 0) := by
      intro f' f'' b' b''
      simp only [Φ, Ψ]
      have hfac := stateQForm_place_AB''_mul_BB'_two S
        ((S.lineMeas .alice W line).effect f') ((S.pointMeas .bob W u).effect b')
        (tauLineProj P W line f'') (tauPointProj W u b'')
        (lineMeas_effect_isHermitian S .alice W line f')
        (pointMeas_effect_isHermitian S .bob W u b')
        (tauLineProj_isHermitian W line f'') (tauPointProj_isHermitian W u b'')
      rw [stateQForm_eprState_tauPointProj_tauLineProj P W line u hu f'' b''] at hfac
      exact hfac
    exact overlap_identity_of_mem P W (S.lineMeas .alice W line)
      (S.pointMeas .bob W u) Φ Ψ line u hu hΦ0 hΦl hΦr hΦfact hΨl hΨ0
  · exact overlap_identity_of_not_mem P W (S.lineMeas .alice W line)
      (S.pointMeas .bob W u) Φ Ψ line u hu hΦ0 hΨl hΨ0

set_option synthInstance.maxSize 400 in
/-- The expanded overlap of Bob's line measurement on `BB'` with Alice's
selected point effects on `AB''`, on the second bipartition. Paper
`14_analysis_of_the_pauli_basis_test.tex:569-620`. -/
theorem overlap_BB'_AB''_eq (S : ProjectiveSetting P ε) (W : PauliKind)
    (line : LineDesc P.toLdParams) (u : Fin P.m → PauliScalar P) :
    ∑ f : DegPoly P.toLdParams (P.m * P.d),
        DistanceCalculus.stateQForm S.psiHat
          (S.place .BB' (S.expLineOp .bob W line f) *
            S.place .AB'' (S.expPointEffectAtLineAnswer .alice W line u f)) =
      ∑ o : Option (PauliScalar P),
        DistanceCalculus.stateQForm S.toStrategy.ψ
          (heteroKron ((S.pointMeasOption .alice W u).effect o)
            ((S.lineEvalMeas .bob W line u).effect o)) := by
  let Φ : Op (S.ExpandedLocalSpace .bob) →
      Op (S.ExpandedLocalSpace .alice) → ℝ := fun X Y =>
    DistanceCalculus.stateQForm S.psiHat (S.place .BB' X * S.place .AB'' Y)
  let Ψ : Op S.toStrategy.ιB → Op S.toStrategy.ιA → ℝ := fun L Q =>
    DistanceCalculus.stateQForm S.toStrategy.ψ (heteroKron Q L)
  have hΦ0 : ∀ X, Φ X 0 = 0 := by
    intro X
    simp only [Φ]
    rw [place_AB''_zero, mul_zero, DistanceCalculus.stateQForm_zero]
  have hΦl : ∀ (s : Finset (DegPoly P.toLdParams (P.m * P.d) ×
        DegPoly P.toLdParams (P.m * P.d)))
      (X : DegPoly P.toLdParams (P.m * P.d) × DegPoly P.toLdParams (P.m * P.d) →
        Op (S.ExpandedLocalSpace .bob))
      (Y : Op (S.ExpandedLocalSpace .alice)),
      Φ (∑ i ∈ s, X i) Y = ∑ i ∈ s, Φ (X i) Y := by
    intro s X Y
    simp only [Φ]
    rw [place_BB'_finset_sum, Finset.sum_mul,
      DistanceCalculus.stateQForm_finset_sum]
  have hΦr : ∀ (X : Op (S.ExpandedLocalSpace .bob))
      (t : Finset (PauliScalar P × PauliScalar P))
      (Y : PauliScalar P × PauliScalar P → Op (S.ExpandedLocalSpace .alice)),
      Φ X (∑ j ∈ t, Y j) = ∑ j ∈ t, Φ X (Y j) := by
    intro X t Y
    simp only [Φ]
    rw [place_AB''_finset_sum, Finset.mul_sum,
      DistanceCalculus.stateQForm_finset_sum]
  have hΨl : ∀ (s : Finset (DegPoly P.toLdParams (P.m * P.d)))
      (A : DegPoly P.toLdParams (P.m * P.d) → Op S.toStrategy.ιB)
      (B : Op S.toStrategy.ιA), Ψ (∑ i ∈ s, A i) B = ∑ i ∈ s, Ψ (A i) B := by
    intro s A B
    simp only [Ψ]
    rw [heteroKron_finset_sum_right, DistanceCalculus.stateQForm_finset_sum]
  have hΨ0 : ∀ A, Ψ A 0 = 0 := by
    intro A
    simp only [Ψ]
    rw [heteroKron_zero_left, DistanceCalculus.stateQForm_zero]
  change ∑ f, Φ (S.expLineOp .bob W line f)
      (S.expPointEffectAtLineAnswer .alice W line u f) =
    ∑ o, Ψ (((S.lineMeas .bob W line).postprocess (evalOpt line u)).effect o)
      (((S.pointMeas .alice W u).postprocess some).effect o)
  simp_rw [expPointEffectAtLineAnswer_eq_elim]
  by_cases hu : u ∈ line.pointSet
  · have hΦfact : ∀ (f' f'' : DegPoly P.toLdParams (P.m * P.d))
        (b' b'' : PauliScalar P),
        Φ (heteroKron ((S.lineMeas .bob W line).effect f')
            (tauLineProj P W line f''))
          (heteroKron ((S.pointMeas .alice W u).effect b') (tauPointProj W u b'')) =
        Ψ ((S.lineMeas .bob W line).effect f') ((S.pointMeas .alice W u).effect b') *
          (if evalOpt line u f'' = some b'' then
            DistanceCalculus.stateQForm (eprState (PauliRegister P))
              (heteroKron (tauLineProj P W line f'') (1 : Op (PauliRegister P)))
          else 0) := by
      intro f' f'' b' b''
      simp only [Φ, Ψ]
      have hfac := stateQForm_place_AB''_mul_BB'_two S
        ((S.pointMeas .alice W u).effect b') ((S.lineMeas .bob W line).effect f')
        (tauPointProj W u b'') (tauLineProj P W line f'')
        (pointMeas_effect_isHermitian S .alice W u b')
        (lineMeas_effect_isHermitian S .bob W line f')
        (tauPointProj_isHermitian W u b'') (tauLineProj_isHermitian W line f'')
      rw [stateQForm_eprState_tauLineProj_tauPointProj P W line u hu f'' b''] at hfac
      have hcomm := place_AB''_mul_place_BB'_comm S
        (heteroKron ((S.pointMeas .alice W u).effect b') (tauPointProj W u b''))
        (heteroKron ((S.lineMeas .bob W line).effect f') (tauLineProj P W line f''))
      exact (congrArg (DistanceCalculus.stateQForm S.psiHat) hcomm.symm).trans hfac
    exact overlap_identity_of_mem P W (S.lineMeas .bob W line)
      (S.pointMeas .alice W u) Φ Ψ line u hu hΦ0 hΦl hΦr hΦfact hΨl hΨ0
  · exact overlap_identity_of_not_mem P W (S.lineMeas .bob W line)
      (S.pointMeas .alice W u) Φ Ψ line u hu hΦ0 hΨl hΨ0

end ProjectiveSetting

end

end MIPStarRE.QPBT
