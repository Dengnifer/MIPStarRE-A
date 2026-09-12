import MIPStarRE.QPBT.Observables.LineMeasurement.BipartiteTransport

/-!
# Consistency of expanded evaluation classes with expanded points

This module proves item 3 of the expanded-line consistency lemma on the four
directed opposite-placement pairs. On each bipartition the distance between
the evaluation classes of the expanded line measurement and the completed
expanded point measurement is at most twice their inconsistency, which by the
overlap identity equals the inconsistency of the strategy's evaluation classes
with its completed point measurement. The trivial bound `4` on the same
distance supplies the large-`ε` case of the common square-root error.

## References

Item 3 of `lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:540-545`,
blueprint `eq:qld-comm-line-pt-cons2`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

/-! ## Overlaps of the evaluation classes -/

/-- Summed over outcomes, the overlap of Alice's expanded evaluation classes
with Bob's completed expanded point measurement on the expanded state equals
the corresponding overlap of the strategy's own evaluation classes with its
completed point measurement on the strategy state. The ancillary Pauli
projectors cancel because they agree exactly on the EPR pairs. This is the
identity behind `eq:qld-comm-line-pt-cons2`, paper
`14_analysis_of_the_pauli_basis_test.tex:540-545`. -/
theorem sum_stateQForm_evalClass_AA'_BA''_eq (S : ProjectiveSetting P ε)
    (W : PauliKind) (line : LineDesc P.toLdParams)
    (u : Fin P.m → PauliScalar P) :
    ∑ o : Option (PauliScalar P),
        DistanceCalculus.stateQForm S.psiHat
          (S.place .AA' ((S.lineEvalMeasExp .alice W line u).effect o) *
            S.place .BA'' ((S.pointMeasExpOption .bob W u).effect o)) =
      ∑ o : Option (PauliScalar P),
        DistanceCalculus.stateQForm S.toStrategy.ψ
          (heteroKron ((S.lineEvalMeas .alice W line u).effect o)
            ((S.pointMeasOption .bob W u).effect o)) := by
  rw [← overlap_AA'_BA''_eq]
  calc
    _ = ∑ o : Option (PauliScalar P),
        ∑ f ∈ Finset.univ.filter
          (fun f : DegPoly P.toLdParams (P.m * P.d) => evalOpt line u f = o),
          DistanceCalculus.stateQForm S.psiHat
            (S.place .AA' (S.expLineOp .alice W line f) *
              S.place .BA'' ((S.pointMeasExpOption .bob W u).effect
                (evalOpt line u f))) := by
      refine Finset.sum_congr rfl fun o _ => ?_
      rw [lineEvalMeasExp_effect, place_AA'_finset_sum, Finset.sum_mul,
        DistanceCalculus.stateQForm_finset_sum]
      refine Finset.sum_congr rfl fun f hf => ?_
      rw [(Finset.mem_filter.mp hf).2]
    _ = ∑ f : DegPoly P.toLdParams (P.m * P.d),
        DistanceCalculus.stateQForm S.psiHat
          (S.place .AA' (S.expLineOp .alice W line f) *
            S.place .BA'' ((S.pointMeasExpOption .bob W u).effect
              (evalOpt line u f))) :=
      Finset.sum_fiberwise Finset.univ (fun f => evalOpt line u f) _
    _ = _ := by
      simp_rw [pointMeasExpOption_effect_evalOpt]

/-- The identity of `sum_stateQForm_evalClass_AA'_BA''_eq` with the two
placements exchanged, so that the evaluation classes are carried by the `BA''`
registers and the completed point measurement by `AA'`. This is the symmetric equivalent
of `eq:qld-comm-line-pt-cons2` on the reversed directed pair, paper
`14_analysis_of_the_pauli_basis_test.tex:540-548`. -/
theorem sum_stateQForm_evalClass_BA''_AA'_eq (S : ProjectiveSetting P ε)
    (W : PauliKind) (line : LineDesc P.toLdParams)
    (u : Fin P.m → PauliScalar P) :
    ∑ o : Option (PauliScalar P),
        DistanceCalculus.stateQForm S.psiHat
          (S.place .AA' ((S.pointMeasExpOption .alice W u).effect o) *
            S.place .BA'' ((S.lineEvalMeasExp .bob W line u).effect o)) =
      ∑ o : Option (PauliScalar P),
        DistanceCalculus.stateQForm S.toStrategy.ψ
          (heteroKron ((S.pointMeasOption .alice W u).effect o)
            ((S.lineEvalMeas .bob W line u).effect o)) := by
  rw [← overlap_BA''_AA'_eq]
  calc
    _ = ∑ o : Option (PauliScalar P),
        ∑ f ∈ Finset.univ.filter
          (fun f : DegPoly P.toLdParams (P.m * P.d) => evalOpt line u f = o),
          DistanceCalculus.stateQForm S.psiHat
            (S.place .BA'' (S.expLineOp .bob W line f) *
              S.place .AA' ((S.pointMeasExpOption .alice W u).effect
                (evalOpt line u f))) := by
      refine Finset.sum_congr rfl fun o _ => ?_
      rw [place_AA'_mul_place_BA''_comm, lineEvalMeasExp_effect,
        place_BA''_finset_sum, Finset.sum_mul,
        DistanceCalculus.stateQForm_finset_sum]
      refine Finset.sum_congr rfl fun f hf => ?_
      rw [(Finset.mem_filter.mp hf).2]
    _ = ∑ f : DegPoly P.toLdParams (P.m * P.d),
        DistanceCalculus.stateQForm S.psiHat
          (S.place .BA'' (S.expLineOp .bob W line f) *
            S.place .AA' ((S.pointMeasExpOption .alice W u).effect
              (evalOpt line u f))) :=
      Finset.sum_fiberwise Finset.univ (fun f => evalOpt line u f) _
    _ = _ := by
      simp_rw [pointMeasExpOption_effect_evalOpt]

/-- The identity of `sum_stateQForm_evalClass_AA'_BA''_eq` on the second
bipartition: summed over outcomes, the overlap of Alice's expanded evaluation
classes on `AB''` with Bob's completed expanded point measurement on `BB'`
equals the corresponding strategy overlap. -/
theorem sum_stateQForm_evalClass_AB''_BB'_eq (S : ProjectiveSetting P ε)
    (W : PauliKind) (line : LineDesc P.toLdParams)
    (u : Fin P.m → PauliScalar P) :
    ∑ o : Option (PauliScalar P),
        DistanceCalculus.stateQForm S.psiHat
          (S.place .AB'' ((S.lineEvalMeasExp .alice W line u).effect o) *
            S.place .BB' ((S.pointMeasExpOption .bob W u).effect o)) =
      ∑ o : Option (PauliScalar P),
        DistanceCalculus.stateQForm S.toStrategy.ψ
          (heteroKron ((S.lineEvalMeas .alice W line u).effect o)
            ((S.pointMeasOption .bob W u).effect o)) := by
  rw [← overlap_AB''_BB'_eq]
  calc
    _ = ∑ o : Option (PauliScalar P),
        ∑ f ∈ Finset.univ.filter
          (fun f : DegPoly P.toLdParams (P.m * P.d) => evalOpt line u f = o),
          DistanceCalculus.stateQForm S.psiHat
            (S.place .AB'' (S.expLineOp .alice W line f) *
              S.place .BB' ((S.pointMeasExpOption .bob W u).effect
                (evalOpt line u f))) := by
      refine Finset.sum_congr rfl fun o _ => ?_
      rw [lineEvalMeasExp_effect, place_AB''_finset_sum, Finset.sum_mul,
        DistanceCalculus.stateQForm_finset_sum]
      refine Finset.sum_congr rfl fun f hf => ?_
      rw [(Finset.mem_filter.mp hf).2]
    _ = ∑ f : DegPoly P.toLdParams (P.m * P.d),
        DistanceCalculus.stateQForm S.psiHat
          (S.place .AB'' (S.expLineOp .alice W line f) *
            S.place .BB' ((S.pointMeasExpOption .bob W u).effect
              (evalOpt line u f))) :=
      Finset.sum_fiberwise Finset.univ (fun f => evalOpt line u f) _
    _ = _ := by
      simp_rw [pointMeasExpOption_effect_evalOpt]

/-- The identity of `sum_stateQForm_evalClass_AB''_BB'_eq` with the two
placements exchanged, so that the completed point measurement is carried by
`AB''` and the evaluation classes by `BB'`. -/
theorem sum_stateQForm_evalClass_BB'_AB''_eq (S : ProjectiveSetting P ε)
    (W : PauliKind) (line : LineDesc P.toLdParams)
    (u : Fin P.m → PauliScalar P) :
    ∑ o : Option (PauliScalar P),
        DistanceCalculus.stateQForm S.psiHat
          (S.place .AB'' ((S.pointMeasExpOption .alice W u).effect o) *
            S.place .BB' ((S.lineEvalMeasExp .bob W line u).effect o)) =
      ∑ o : Option (PauliScalar P),
        DistanceCalculus.stateQForm S.toStrategy.ψ
          (heteroKron ((S.pointMeasOption .alice W u).effect o)
            ((S.lineEvalMeas .bob W line u).effect o)) := by
  rw [← overlap_BB'_AB''_eq]
  calc
    _ = ∑ o : Option (PauliScalar P),
        ∑ f ∈ Finset.univ.filter
          (fun f : DegPoly P.toLdParams (P.m * P.d) => evalOpt line u f = o),
          DistanceCalculus.stateQForm S.psiHat
            (S.place .BB' (S.expLineOp .bob W line f) *
              S.place .AB'' ((S.pointMeasExpOption .alice W u).effect
                (evalOpt line u f))) := by
      refine Finset.sum_congr rfl fun o _ => ?_
      rw [place_AB''_mul_place_BB'_comm, lineEvalMeasExp_effect,
        place_BB'_finset_sum, Finset.sum_mul,
        DistanceCalculus.stateQForm_finset_sum]
      refine Finset.sum_congr rfl fun f hf => ?_
      rw [(Finset.mem_filter.mp hf).2]
    _ = ∑ f : DegPoly P.toLdParams (P.m * P.d),
        DistanceCalculus.stateQForm S.psiHat
          (S.place .BB' (S.expLineOp .bob W line f) *
            S.place .AB'' ((S.pointMeasExpOption .alice W u).effect
              (evalOpt line u f))) :=
      Finset.sum_fiberwise Finset.univ (fun f => evalOpt line u f) _
    _ = _ := by
      simp_rw [pointMeasExpOption_effect_evalOpt]

/-! ## Item 3: evaluation classes versus completed expanded points -/

set_option synthInstance.maxSize 400 in
/-- The expanded evaluation-class distance on the directed `AA'`--`BA''`
pair equals the distance of the left- and right-placed families on the
corresponding bipartition. Formalization-only transport for item 3 of
`lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:540-545`. -/
theorem evalClassDist_aaBa_eq (S : ProjectiveSetting P ε) (W : PauliKind) :
    opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample a => S.place .AA'
          ((S.lineEvalMeasExp .alice W sample.1 sample.2).effect a))
        (fun sample a => S.place .BA''
          ((S.pointMeasExpOption .bob W sample.2).effect a))
        S.psiHat =
      opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample a => heteroKron ((S.lineEvalMeasExp .alice W sample.1 sample.2).effect a)
          (1 : Op ((S.toStrategy.ιB × PauliRegister P) × (PauliRegister P × PauliRegister P))))
        (fun sample a => heteroKron (1 : Op (S.toStrategy.ιA × PauliRegister P))
          ((DistanceCalculus.leftPlacedMeasurement
            (ιB := PauliRegister P × PauliRegister P)
            (S.pointMeasExpOption .bob W sample.2)).effect a))
        (reindexState (aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
          S.psiHat) := by
  unfold opFamilyDistSq
  apply avgOver_congr
  intro sample
  apply Finset.sum_congr rfl
  intro a _
  rw [norm_place_AA'_sub_place_BA'']
  rfl

set_option synthInstance.maxSize 400 in
/-- Expanded evaluation-class consistency on the directed `AA'`--`BA''`
pair is bounded by twice the strategy's line-point inconsistency. This is
`eq:qld-comm-line-pt-cons2`, paper
`14_analysis_of_the_pauli_basis_test.tex:540-545`. The source reaches it from
`eq:qld-comm-line-pt-cons` through an elementary sub-measurement inequality,
at the cost of a square root, paper
`14_analysis_of_the_pauli_basis_test.tex:598-677`; here it comes directly from
the exact overlap identity together with `fact:agreement`, so the bound is
linear in the error of the strategy. -/
theorem evalClassDist_aaBa_le (S : ProjectiveSetting P ε) (W : PauliKind) :
    opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample a => S.place .AA'
          ((S.lineEvalMeasExp .alice W sample.1 sample.2).effect a))
        (fun sample a => S.place .BA''
          ((S.pointMeasExpOption .bob W sample.2).effect a))
        S.psiHat ≤
      2 * consistencyDefect (linePointDist P.toLdParams)
        (fun sample a => heteroKron
          ((S.lineEvalMeas .alice W sample.1 sample.2).effect a) 1)
        (fun sample a => heteroKron 1
          ((S.pointMeasOption .bob W sample.2).effect a))
        S.toStrategy.ψ := by
  let X := LineDesc P.toLdParams × (Fin P.m → PauliScalar P)
  let R := PauliRegister P
  let μ := linePointDist P.toLdParams
  let e := aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB
  let A : X → Measurement (Option (PauliScalar P)) (S.toStrategy.ιA × R) :=
    fun sample => S.lineEvalMeasExp .alice W sample.1 sample.2
  let B : X → Measurement (Option (PauliScalar P))
      ((S.toStrategy.ιB × R) × (R × R)) := fun sample =>
    DistanceCalculus.leftPlacedMeasurement (ιB := R × R)
      (S.pointMeasExpOption .bob W sample.2)
  have hμ : μ.IsProbability := linePointDist_isProbability P.toLdParams
  rw [evalClassDist_aaBa_eq]
  refine (DistanceCalculus.opFamilyDistSq_placed_le_two_mul_one_sub_overlap μ hμ
    A B _ (norm_reindexState_psiHat S e)).trans (le_of_eq ?_)
  have hstrat := DistanceCalculus.consistencyDefect_eq_one_sub_overlap μ
    (fun sample => DistanceCalculus.leftPlacedMeasurement
      (S.lineEvalMeas .alice W sample.1 sample.2))
    (fun sample => DistanceCalculus.rightPlacedMeasurement
      (S.pointMeasOption .bob W sample.2)) S.toStrategy.ψ hμ S.toStrategy.ψ_norm
  change _ = 2 * consistencyDefect μ
    (fun sample a => (DistanceCalculus.leftPlacedMeasurement
      (S.lineEvalMeas .alice W sample.1 sample.2)).effect a)
    (fun sample a => (DistanceCalculus.rightPlacedMeasurement
      (S.pointMeasOption .bob W sample.2)).effect a) S.toStrategy.ψ
  rw [hstrat]
  congr 2
  apply avgOver_congr
  intro sample
  calc
    _ = ∑ a : Option (PauliScalar P),
        DistanceCalculus.stateQForm S.psiHat
          (S.place .AA' ((S.lineEvalMeasExp .alice W sample.1 sample.2).effect a) *
            S.place .BA'' ((S.pointMeasExpOption .bob W sample.2).effect a)) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      exact stateQForm_aaBa_mul_eq S _ _
    _ = ∑ a : Option (PauliScalar P),
        DistanceCalculus.stateQForm S.toStrategy.ψ
          (heteroKron ((S.lineEvalMeas .alice W sample.1 sample.2).effect a)
            ((S.pointMeasOption .bob W sample.2).effect a)) :=
      sum_stateQForm_evalClass_AA'_BA''_eq S W sample.1 sample.2
    _ = _ := by
      refine Finset.sum_congr rfl fun a _ => ?_
      exact (DistanceCalculus.placed_product_stateQForm_eq _ _ _).symm

set_option synthInstance.maxSize 400 in
/-- The expanded evaluation-class distance on the directed `AA'`--`BA''`
pair is at most four. This trivial bound supplies the large-`ε` case of the
common square-root error in item 3 of `lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:540-545`. -/
theorem evalClassDist_aaBa_le_four (S : ProjectiveSetting P ε) (W : PauliKind) :
    opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample a => S.place .AA'
          ((S.lineEvalMeasExp .alice W sample.1 sample.2).effect a))
        (fun sample a => S.place .BA''
          ((S.pointMeasExpOption .bob W sample.2).effect a))
        S.psiHat ≤ 4 := by
  rw [evalClassDist_aaBa_eq]
  exact DistanceCalculus.opFamilyDistSq_placed_le_four _
    (linePointDist_isProbability P.toLdParams) _ _ _
    (norm_reindexState_psiHat S _)

set_option synthInstance.maxSize 400 in
/-- The expanded evaluation-class distance on the directed `BA''`--`AA'`
pair equals the distance of the left- and right-placed families on the
corresponding bipartition. Formalization-only transport for item 3 of
`lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:540-545`. -/
theorem evalClassDist_baAa_eq (S : ProjectiveSetting P ε) (W : PauliKind) :
    opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample a => S.place .BA''
          ((S.lineEvalMeasExp .bob W sample.1 sample.2).effect a))
        (fun sample a => S.place .AA'
          ((S.pointMeasExpOption .alice W sample.2).effect a))
        S.psiHat =
      opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample a => heteroKron ((S.pointMeasExpOption .alice W sample.2).effect a)
          (1 : Op ((S.toStrategy.ιB × PauliRegister P) × (PauliRegister P × PauliRegister P))))
        (fun sample a => heteroKron (1 : Op (S.toStrategy.ιA × PauliRegister P))
          ((DistanceCalculus.leftPlacedMeasurement
            (ιB := PauliRegister P × PauliRegister P)
            (S.lineEvalMeasExp .bob W sample.1 sample.2)).effect a))
        (reindexState (aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
          S.psiHat) := by
  rw [DistanceCalculus.opFamilyDistSq_symm]
  unfold opFamilyDistSq
  apply avgOver_congr
  intro sample
  apply Finset.sum_congr rfl
  intro a _
  rw [norm_place_AA'_sub_place_BA'']
  rfl

set_option synthInstance.maxSize 400 in
/-- Expanded evaluation-class consistency on the directed `BA''`--`AA'`
pair, bounded by twice the interchanged strategy line-point inconsistency.
Paper `14_analysis_of_the_pauli_basis_test.tex:540-545`. -/
theorem evalClassDist_baAa_le (S : ProjectiveSetting P ε) (W : PauliKind) :
    opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample a => S.place .BA''
          ((S.lineEvalMeasExp .bob W sample.1 sample.2).effect a))
        (fun sample a => S.place .AA'
          ((S.pointMeasExpOption .alice W sample.2).effect a))
        S.psiHat ≤
      2 * consistencyDefect (linePointDist P.toLdParams)
        (fun sample a => heteroKron
          ((S.pointMeasOption .alice W sample.2).effect a) 1)
        (fun sample a => heteroKron 1
          ((S.lineEvalMeas .bob W sample.1 sample.2).effect a))
        S.toStrategy.ψ := by
  let X := LineDesc P.toLdParams × (Fin P.m → PauliScalar P)
  let R := PauliRegister P
  let μ := linePointDist P.toLdParams
  let e := aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB
  let A : X → Measurement (Option (PauliScalar P)) (S.toStrategy.ιA × R) :=
    fun sample => S.pointMeasExpOption .alice W sample.2
  let B : X → Measurement (Option (PauliScalar P))
      ((S.toStrategy.ιB × R) × (R × R)) := fun sample =>
    DistanceCalculus.leftPlacedMeasurement (ιB := R × R)
      (S.lineEvalMeasExp .bob W sample.1 sample.2)
  have hμ : μ.IsProbability := linePointDist_isProbability P.toLdParams
  rw [evalClassDist_baAa_eq]
  refine (DistanceCalculus.opFamilyDistSq_placed_le_two_mul_one_sub_overlap μ hμ
    A B _ (norm_reindexState_psiHat S e)).trans (le_of_eq ?_)
  have hstrat := DistanceCalculus.consistencyDefect_eq_one_sub_overlap μ
    (fun sample => DistanceCalculus.leftPlacedMeasurement
      (S.pointMeasOption .alice W sample.2))
    (fun sample => DistanceCalculus.rightPlacedMeasurement
      (S.lineEvalMeas .bob W sample.1 sample.2)) S.toStrategy.ψ hμ S.toStrategy.ψ_norm
  change _ = 2 * consistencyDefect μ
    (fun sample a => (DistanceCalculus.leftPlacedMeasurement
      (S.pointMeasOption .alice W sample.2)).effect a)
    (fun sample a => (DistanceCalculus.rightPlacedMeasurement
      (S.lineEvalMeas .bob W sample.1 sample.2)).effect a) S.toStrategy.ψ
  rw [hstrat]
  congr 2
  apply avgOver_congr
  intro sample
  calc
    _ = ∑ a : Option (PauliScalar P),
        DistanceCalculus.stateQForm S.psiHat
          (S.place .AA' ((S.pointMeasExpOption .alice W sample.2).effect a) *
            S.place .BA'' ((S.lineEvalMeasExp .bob W sample.1 sample.2).effect a)) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      exact stateQForm_aaBa_mul_eq S _ _
    _ = ∑ a : Option (PauliScalar P),
        DistanceCalculus.stateQForm S.toStrategy.ψ
          (heteroKron ((S.pointMeasOption .alice W sample.2).effect a)
            ((S.lineEvalMeas .bob W sample.1 sample.2).effect a)) :=
      sum_stateQForm_evalClass_BA''_AA'_eq S W sample.1 sample.2
    _ = _ := by
      refine Finset.sum_congr rfl fun a _ => ?_
      exact (DistanceCalculus.placed_product_stateQForm_eq _ _ _).symm

set_option synthInstance.maxSize 400 in
/-- The expanded evaluation-class distance on the directed `BA''`--`AA'`
pair is at most four. This trivial bound supplies the large-`ε` case of the
common square-root error in item 3 of `lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:540-545`. -/
theorem evalClassDist_baAa_le_four (S : ProjectiveSetting P ε) (W : PauliKind) :
    opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample a => S.place .BA''
          ((S.lineEvalMeasExp .bob W sample.1 sample.2).effect a))
        (fun sample a => S.place .AA'
          ((S.pointMeasExpOption .alice W sample.2).effect a))
        S.psiHat ≤ 4 := by
  rw [evalClassDist_baAa_eq]
  exact DistanceCalculus.opFamilyDistSq_placed_le_four _
    (linePointDist_isProbability P.toLdParams) _ _ _
    (norm_reindexState_psiHat S _)

set_option synthInstance.maxSize 400 in
/-- The expanded evaluation-class distance on the directed `AB''`--`BB'`
pair equals the distance of the left- and right-placed families on the
corresponding bipartition. Formalization-only transport for item 3 of
`lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:540-545`. -/
theorem evalClassDist_abBb_eq (S : ProjectiveSetting P ε) (W : PauliKind) :
    opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample a => S.place .AB''
          ((S.lineEvalMeasExp .alice W sample.1 sample.2).effect a))
        (fun sample a => S.place .BB'
          ((S.pointMeasExpOption .bob W sample.2).effect a))
        S.psiHat =
      opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample a => heteroKron ((S.lineEvalMeasExp .alice W sample.1 sample.2).effect a)
          (1 : Op ((S.toStrategy.ιB × PauliRegister P) × (PauliRegister P × PauliRegister P))))
        (fun sample a => heteroKron (1 : Op (S.toStrategy.ιA × PauliRegister P))
          ((DistanceCalculus.leftPlacedMeasurement
            (ιB := PauliRegister P × PauliRegister P)
            (S.pointMeasExpOption .bob W sample.2)).effect a))
        (reindexState (abBbBipartition P S.toStrategy.ιA S.toStrategy.ιB)
          S.psiHat) := by
  unfold opFamilyDistSq
  apply avgOver_congr
  intro sample
  apply Finset.sum_congr rfl
  intro a _
  rw [norm_place_AB''_sub_place_BB']
  rfl

set_option synthInstance.maxSize 400 in
/-- Expanded evaluation-class consistency on the directed `AB''`--`BB'`
pair. Paper `14_analysis_of_the_pauli_basis_test.tex:540-545`. -/
theorem evalClassDist_abBb_le (S : ProjectiveSetting P ε) (W : PauliKind) :
    opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample a => S.place .AB''
          ((S.lineEvalMeasExp .alice W sample.1 sample.2).effect a))
        (fun sample a => S.place .BB'
          ((S.pointMeasExpOption .bob W sample.2).effect a))
        S.psiHat ≤
      2 * consistencyDefect (linePointDist P.toLdParams)
        (fun sample a => heteroKron
          ((S.lineEvalMeas .alice W sample.1 sample.2).effect a) 1)
        (fun sample a => heteroKron 1
          ((S.pointMeasOption .bob W sample.2).effect a))
        S.toStrategy.ψ := by
  let X := LineDesc P.toLdParams × (Fin P.m → PauliScalar P)
  let R := PauliRegister P
  let μ := linePointDist P.toLdParams
  let e := abBbBipartition P S.toStrategy.ιA S.toStrategy.ιB
  let A : X → Measurement (Option (PauliScalar P)) (S.toStrategy.ιA × R) :=
    fun sample => S.lineEvalMeasExp .alice W sample.1 sample.2
  let B : X → Measurement (Option (PauliScalar P))
      ((S.toStrategy.ιB × R) × (R × R)) := fun sample =>
    DistanceCalculus.leftPlacedMeasurement (ιB := R × R)
      (S.pointMeasExpOption .bob W sample.2)
  have hμ : μ.IsProbability := linePointDist_isProbability P.toLdParams
  rw [evalClassDist_abBb_eq]
  refine (DistanceCalculus.opFamilyDistSq_placed_le_two_mul_one_sub_overlap μ hμ
    A B _ (norm_reindexState_psiHat S e)).trans (le_of_eq ?_)
  have hstrat := DistanceCalculus.consistencyDefect_eq_one_sub_overlap μ
    (fun sample => DistanceCalculus.leftPlacedMeasurement
      (S.lineEvalMeas .alice W sample.1 sample.2))
    (fun sample => DistanceCalculus.rightPlacedMeasurement
      (S.pointMeasOption .bob W sample.2)) S.toStrategy.ψ hμ S.toStrategy.ψ_norm
  change _ = 2 * consistencyDefect μ
    (fun sample a => (DistanceCalculus.leftPlacedMeasurement
      (S.lineEvalMeas .alice W sample.1 sample.2)).effect a)
    (fun sample a => (DistanceCalculus.rightPlacedMeasurement
      (S.pointMeasOption .bob W sample.2)).effect a) S.toStrategy.ψ
  rw [hstrat]
  congr 2
  apply avgOver_congr
  intro sample
  calc
    _ = ∑ a : Option (PauliScalar P),
        DistanceCalculus.stateQForm S.psiHat
          (S.place .AB'' ((S.lineEvalMeasExp .alice W sample.1 sample.2).effect a) *
            S.place .BB' ((S.pointMeasExpOption .bob W sample.2).effect a)) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      exact stateQForm_abBb_mul_eq S _ _
    _ = ∑ a : Option (PauliScalar P),
        DistanceCalculus.stateQForm S.toStrategy.ψ
          (heteroKron ((S.lineEvalMeas .alice W sample.1 sample.2).effect a)
            ((S.pointMeasOption .bob W sample.2).effect a)) :=
      sum_stateQForm_evalClass_AB''_BB'_eq S W sample.1 sample.2
    _ = _ := by
      refine Finset.sum_congr rfl fun a _ => ?_
      exact (DistanceCalculus.placed_product_stateQForm_eq _ _ _).symm

set_option synthInstance.maxSize 400 in
/-- The expanded evaluation-class distance on the directed `AB''`--`BB'`
pair is at most four. This trivial bound supplies the large-`ε` case of the
common square-root error in item 3 of `lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:540-545`. -/
theorem evalClassDist_abBb_le_four (S : ProjectiveSetting P ε) (W : PauliKind) :
    opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample a => S.place .AB''
          ((S.lineEvalMeasExp .alice W sample.1 sample.2).effect a))
        (fun sample a => S.place .BB'
          ((S.pointMeasExpOption .bob W sample.2).effect a))
        S.psiHat ≤ 4 := by
  rw [evalClassDist_abBb_eq]
  exact DistanceCalculus.opFamilyDistSq_placed_le_four _
    (linePointDist_isProbability P.toLdParams) _ _ _
    (norm_reindexState_psiHat S _)

set_option synthInstance.maxSize 400 in
/-- The expanded evaluation-class distance on the directed `BB'`--`AB''`
pair equals the distance of the left- and right-placed families on the
corresponding bipartition. Formalization-only transport for item 3 of
`lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:540-545`. -/
theorem evalClassDist_bbAb_eq (S : ProjectiveSetting P ε) (W : PauliKind) :
    opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample a => S.place .BB'
          ((S.lineEvalMeasExp .bob W sample.1 sample.2).effect a))
        (fun sample a => S.place .AB''
          ((S.pointMeasExpOption .alice W sample.2).effect a))
        S.psiHat =
      opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample a => heteroKron ((S.pointMeasExpOption .alice W sample.2).effect a)
          (1 : Op ((S.toStrategy.ιB × PauliRegister P) × (PauliRegister P × PauliRegister P))))
        (fun sample a => heteroKron (1 : Op (S.toStrategy.ιA × PauliRegister P))
          ((DistanceCalculus.leftPlacedMeasurement
            (ιB := PauliRegister P × PauliRegister P)
            (S.lineEvalMeasExp .bob W sample.1 sample.2)).effect a))
        (reindexState (abBbBipartition P S.toStrategy.ιA S.toStrategy.ιB)
          S.psiHat) := by
  rw [DistanceCalculus.opFamilyDistSq_symm]
  unfold opFamilyDistSq
  apply avgOver_congr
  intro sample
  apply Finset.sum_congr rfl
  intro a _
  rw [norm_place_AB''_sub_place_BB']
  rfl

set_option synthInstance.maxSize 400 in
/-- Expanded evaluation-class consistency on the directed `BB'`--`AB''`
pair. Paper `14_analysis_of_the_pauli_basis_test.tex:540-545`. -/
theorem evalClassDist_bbAb_le (S : ProjectiveSetting P ε) (W : PauliKind) :
    opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample a => S.place .BB'
          ((S.lineEvalMeasExp .bob W sample.1 sample.2).effect a))
        (fun sample a => S.place .AB''
          ((S.pointMeasExpOption .alice W sample.2).effect a))
        S.psiHat ≤
      2 * consistencyDefect (linePointDist P.toLdParams)
        (fun sample a => heteroKron
          ((S.pointMeasOption .alice W sample.2).effect a) 1)
        (fun sample a => heteroKron 1
          ((S.lineEvalMeas .bob W sample.1 sample.2).effect a))
        S.toStrategy.ψ := by
  let X := LineDesc P.toLdParams × (Fin P.m → PauliScalar P)
  let R := PauliRegister P
  let μ := linePointDist P.toLdParams
  let e := abBbBipartition P S.toStrategy.ιA S.toStrategy.ιB
  let A : X → Measurement (Option (PauliScalar P)) (S.toStrategy.ιA × R) :=
    fun sample => S.pointMeasExpOption .alice W sample.2
  let B : X → Measurement (Option (PauliScalar P))
      ((S.toStrategy.ιB × R) × (R × R)) := fun sample =>
    DistanceCalculus.leftPlacedMeasurement (ιB := R × R)
      (S.lineEvalMeasExp .bob W sample.1 sample.2)
  have hμ : μ.IsProbability := linePointDist_isProbability P.toLdParams
  rw [evalClassDist_bbAb_eq]
  refine (DistanceCalculus.opFamilyDistSq_placed_le_two_mul_one_sub_overlap μ hμ
    A B _ (norm_reindexState_psiHat S e)).trans (le_of_eq ?_)
  have hstrat := DistanceCalculus.consistencyDefect_eq_one_sub_overlap μ
    (fun sample => DistanceCalculus.leftPlacedMeasurement
      (S.pointMeasOption .alice W sample.2))
    (fun sample => DistanceCalculus.rightPlacedMeasurement
      (S.lineEvalMeas .bob W sample.1 sample.2)) S.toStrategy.ψ hμ S.toStrategy.ψ_norm
  change _ = 2 * consistencyDefect μ
    (fun sample a => (DistanceCalculus.leftPlacedMeasurement
      (S.pointMeasOption .alice W sample.2)).effect a)
    (fun sample a => (DistanceCalculus.rightPlacedMeasurement
      (S.lineEvalMeas .bob W sample.1 sample.2)).effect a) S.toStrategy.ψ
  rw [hstrat]
  congr 2
  apply avgOver_congr
  intro sample
  calc
    _ = ∑ a : Option (PauliScalar P),
        DistanceCalculus.stateQForm S.psiHat
          (S.place .AB'' ((S.pointMeasExpOption .alice W sample.2).effect a) *
            S.place .BB' ((S.lineEvalMeasExp .bob W sample.1 sample.2).effect a)) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      exact stateQForm_abBb_mul_eq S _ _
    _ = ∑ a : Option (PauliScalar P),
        DistanceCalculus.stateQForm S.toStrategy.ψ
          (heteroKron ((S.pointMeasOption .alice W sample.2).effect a)
            ((S.lineEvalMeas .bob W sample.1 sample.2).effect a)) :=
      sum_stateQForm_evalClass_BB'_AB''_eq S W sample.1 sample.2
    _ = _ := by
      refine Finset.sum_congr rfl fun a _ => ?_
      exact (DistanceCalculus.placed_product_stateQForm_eq _ _ _).symm

set_option synthInstance.maxSize 400 in
/-- The expanded evaluation-class distance on the directed `BB'`--`AB''`
pair is at most four. This trivial bound supplies the large-`ε` case of the
common square-root error in item 3 of `lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:540-545`. -/
theorem evalClassDist_bbAb_le_four (S : ProjectiveSetting P ε) (W : PauliKind) :
    opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample a => S.place .BB'
          ((S.lineEvalMeasExp .bob W sample.1 sample.2).effect a))
        (fun sample a => S.place .AB''
          ((S.pointMeasExpOption .alice W sample.2).effect a))
        S.psiHat ≤ 4 := by
  rw [evalClassDist_bbAb_eq]
  exact DistanceCalculus.opFamilyDistSq_placed_le_four _
    (linePointDist_isProbability P.toLdParams) _ _ _
    (norm_reindexState_psiHat S _)

end ProjectiveSetting

end

end MIPStarRE.QPBT
