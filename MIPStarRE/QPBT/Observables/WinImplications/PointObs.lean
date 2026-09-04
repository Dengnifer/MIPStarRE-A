import MIPStarRE.QPBT.Observables.WinImplications.Approx

/-!
# Self-consistency of the strategy point observables

This module converts the trace-coarse-grained point consistency of item 1 of
`lem:qld-win-implications` into the observable relation
`eq:pts-obs-consistency` of `lem:qld-win-implications-obs`.

## References

The declarations support `lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:663-682`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:294-308`.
-/

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace WinImplications

local instance pauliEdgeNonemptyPointObs : Nonempty PauliEdge :=
  pauliEdge_nonempty

/-! ## Linearity of the tensor placement -/

/-- The left tensor placement commutes with weighted finite sums. This is
formalization-only support for `lem:povm-to-obs`, blueprint
`ch14_qpbt_observables.tex:361-378`. -/
theorem heteroKron_left_sum_smul {α ιA ιB : Type*} [Fintype α]
    (c : α → ℂ) (A : α → Op ιA) (B : Op ιB) :
    heteroKron (∑ a, c a • A a) B = ∑ a, c a • heteroKron (A a) B := by
  ext i j
  simp only [heteroKron, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_mul,
    mul_assoc]

/-- The right tensor placement commutes with weighted finite sums. This is
formalization-only support for `lem:povm-to-obs`, blueprint
`ch14_qpbt_observables.tex:361-378`. -/
theorem heteroKron_right_sum_smul {α ιA ιB : Type*} [Fintype α]
    (c : α → ℂ) (A : Op ιA) (B : α → Op ιB) :
    heteroKron A (∑ a, c a • B a) = ∑ a, c a • heteroKron A (B a) := by
  ext i j
  simp only [heteroKron, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- The binary phase character has unit modulus. Paper
`references/qpbt-paper/04_preliminaries.tex:1052-1081`. -/
theorem norm_phaseSign (t : ZMod 2) : ‖phaseSign t‖ = 1 := by
  by_cases ht : t = 0 <;> simp [phaseSign, ht]

/-! ## The point observable as a binary observable -/

/-- The strategy point observable of `def:strategy-observables` is the
binary observable of the trace-coarse-grained point measurement. Paper
`14_analysis_of_the_pauli_basis_test.tex:174-190,294-308`, blueprint
`ch14_qpbt_observables.tex:480-503`. -/
theorem pointObs_eq_traceMeas_obs {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (side : PlayerSide) (W : PauliKind)
    (r : PauliScalar P) (u : Fin P.m → PauliScalar P) :
    S.pointObs side W r u =
      ∑ b : ZMod 2, phaseSign b • (S.pointTraceMeas side W u r).effect b := by
  classical
  rw [ProjectiveSetting.pointObs]
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := fun a : PauliScalar P => fixedBinTrace P.model (a * r))
    (t := (Finset.univ : Finset (ZMod 2)))
    (fun a _ => Finset.mem_univ _)
    (f := fun a => phaseSign (fixedBinTrace P.model (a * r)) •
      (S.pointMeas side W u).effect a)]
  refine Finset.sum_congr rfl ?_
  intro b _
  rw [ProjectiveSetting.pointTraceMeas,
    MIPStarRE.Quantum.Measurement.postprocess_effect, Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  intro a ha
  rw [(Finset.mem_filter.mp ha).2]

/-! ## Trace-coarse-grained point self-consistency -/

/-- The point self-loop mismatch of trace labels is contained in rejection.
This is item 1 of `lem:qld-win-implications` read on the point questions,
paper `14_analysis_of_the_pauli_basis_test.tex:197-199`, blueprint
`ch14_qpbt_observables.tex:515-522`. -/
theorem pointTraceMismatch_le_rejection {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind) (r : PauliScalar P)
    (z : PauliSpace P) :
    outcomeEventWeight S.toStrategy
        ((.point W), pauliCL P (.point W) z)
        ((.point W), pauliCL P (.point W) z)
        (fun A B =>
          fixedBinTrace P.model (ProjectiveSetting.pointAnswerOrZero A * r) ≠
            fixedBinTrace P.model
              (ProjectiveSetting.pointAnswerOrZero B * r)) ≤
      pauliRejectionAt S.toStrategy (pauliLoopEdge (.point W)) z := by
  refine le_trans ?_ (loopMismatch_le_rejection S (.point W) z)
  apply outcome_event_weight_mono
  intro A B hne hAB
  exact hne (by rw [hAB])

/-- Trace-coarse-grained point self-consistency is the point self-loop label
mismatch probability. Paper
`14_analysis_of_the_pauli_basis_test.tex:294-308`, blueprint
`ch14_qpbt_observables.tex:663-682`. -/
theorem pointTraceConsistency_eq_mismatch {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind) (r : PauliScalar P) :
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u b => heteroKron ((S.pointTraceMeas .alice W u r).effect b) 1)
        (fun u b => heteroKron 1 ((S.pointTraceMeas .bob W u r).effect b))
        S.toStrategy.ψ =
      avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun u =>
        outcomeEventWeight S.toStrategy
          (ProjectiveSetting.pointQuestion P W u)
          (ProjectiveSetting.pointQuestion P W u)
          (fun A B =>
            fixedBinTrace P.model
                (ProjectiveSetting.pointAnswerOrZero A * r) ≠
              fixedBinTrace P.model
                (ProjectiveSetting.pointAnswerOrZero B * r))) := by
  classical
  let X := Fin P.m → PauliScalar P
  let qA : X → PauliQuestion P := fun u => ProjectiveSetting.pointQuestion P W u
  let fA : X → PauliAnswer P → ZMod 2 := fun _ A =>
    fixedBinTrace P.model (ProjectiveSetting.pointAnswerOrZero A * r)
  have h := consistencyDefect_postprocess_eq_mismatch
    (X := X) (uniformDistribution X) S.toStrategy qA qA fA fA
  have hA : ∀ (u : X) c,
      heteroKron ((S.pointTraceMeas .alice W u r).effect c)
          (1 : Op S.toStrategy.ιB) =
        heteroKron (((S.toStrategy.A (qA u)).postprocess (fA u)).effect c)
          (1 : Op S.toStrategy.ιB) := by
    intro u c
    congr 1
    unfold ProjectiveSetting.pointTraceMeas ProjectiveSetting.pointMeas fA
    rw [measurement_postprocess_comp_effect]
    rfl
  have hB : ∀ (u : X) c,
      heteroKron (1 : Op S.toStrategy.ιA)
          ((S.pointTraceMeas .bob W u r).effect c) =
        heteroKron (1 : Op S.toStrategy.ιA)
          (((S.toStrategy.B (qA u)).postprocess (fA u)).effect c) := by
    intro u c
    congr 1
    unfold ProjectiveSetting.pointTraceMeas ProjectiveSetting.pointMeas fA
    rw [measurement_postprocess_comp_effect]
    rfl
  calc
    _ = consistencyDefect (uniformDistribution X)
        (fun u c => heteroKron
          (((S.toStrategy.A (qA u)).postprocess (fA u)).effect c) 1)
        (fun u c => heteroKron 1
          (((S.toStrategy.B (qA u)).postprocess (fA u)).effect c))
        S.toStrategy.ψ := consistencyDefect_congr _ _ _ _ _ _ hA hB
    _ = avgOver (uniformDistribution X) (fun u =>
        outcomeEventWeight S.toStrategy (qA u) (qA u)
          (fun A B => fA u A ≠ fA u B)) := h
    _ = _ := by rfl

/-- The trace-coarse-grained point measurements are self-consistent on average
over the point. This is item 1 of `lem:qld-win-implications` specialized to the
point questions, paper `14_analysis_of_the_pauli_basis_test.tex:294-300`,
blueprint `ch14_qpbt_observables.tex:663-682`. -/
theorem pointTrace_self_consistency_le {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind) (r : PauliScalar P) :
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u b => heteroKron ((S.pointTraceMeas .alice W u r).effect b) 1)
        (fun u b => heteroKron 1 ((S.pointTraceMeas .bob W u r).effect b))
        S.toStrategy.ψ ≤ (Fintype.card PauliEdge : ℝ) * ε := by
  classical
  rw [pointTraceConsistency_eq_mismatch]
  have hsource :
      avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun u =>
          outcomeEventWeight S.toStrategy
            (ProjectiveSetting.pointQuestion P W u)
            (ProjectiveSetting.pointQuestion P W u)
            (fun A B =>
              fixedBinTrace P.model
                  (ProjectiveSetting.pointAnswerOrZero A * r) ≠
                fixedBinTrace P.model
                  (ProjectiveSetting.pointAnswerOrZero B * r))) =
        avgOver (uniformDistribution (PauliSpace P)) (fun z =>
          outcomeEventWeight S.toStrategy
            (ProjectiveSetting.pointQuestion P W (pauliToLd P W z).point)
            (ProjectiveSetting.pointQuestion P W (pauliToLd P W z).point)
            (fun A B =>
              fixedBinTrace P.model
                  (ProjectiveSetting.pointAnswerOrZero A * r) ≠
                fixedBinTrace P.model
                  (ProjectiveSetting.pointAnswerOrZero B * r))) := by
    let f : (Fin P.m → PauliScalar P) → ℝ := fun u =>
      outcomeEventWeight S.toStrategy
        (ProjectiveSetting.pointQuestion P W u)
        (ProjectiveSetting.pointQuestion P W u)
        (fun A B =>
          fixedBinTrace P.model
              (ProjectiveSetting.pointAnswerOrZero A * r) ≠
            fixedBinTrace P.model
              (ProjectiveSetting.pointAnswerOrZero B * r))
    have hld := avgOver_pauliToLd_uniform P W (fun z => f z.point)
    have hpoint := avgOver_ldPoint_uniform P.toLdParams f
    exact (hld.trans hpoint).symm
  rw [hsource]
  calc
    _ ≤ avgOver (uniformDistribution (PauliSpace P))
        (pauliRejectionAt S.toStrategy (pauliLoopEdge (.point W))) := by
      apply avgOver_mono
      intro z
      have hs := pointTraceMismatch_le_rejection S W r z
      rw [pauliCL_point_eq] at hs
      simpa only [pauliCL, ProjectiveSetting.pointQuestion] using hs
    _ ≤ (Fintype.card PauliEdge : ℝ) * ε :=
      fixedEdgeRejection_le_error S _

/-! ## The observable consistency relation -/

/-- Observable self-consistency on both tensor-factor orientations. This is
Equation `eq:pts-obs-consistency` in `lem:qld-win-implications-obs`, paper
`14_analysis_of_the_pauli_basis_test.tex:294-308`, blueprint
`ch14_qpbt_observables.tex:663-682`. -/
theorem pointObs_self_consistent_proof :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ (W : PauliKind) (r : PauliScalar P),
      opDistSq (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u => heteroKron (S.pointObs .alice W r u) 1)
        (fun u => heteroKron 1 (S.pointObs .bob W r u))
        S.toStrategy.ψ ≤ C * ε ∧
      opDistSq (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u => heteroKron 1 (S.pointObs .bob W r u))
        (fun u => heteroKron (S.pointObs .alice W r u) 1)
        S.toStrategy.ψ ≤ C * ε := by
  classical
  refine ⟨4 * (Fintype.card PauliEdge : ℝ), ?_, ?_⟩
  · have hcard : (1 : ℝ) ≤ Fintype.card PauliEdge := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card PauliEdge)
    linarith
  intro P ε S _ W r
  set μ := uniformDistribution (Fin P.m → PauliScalar P) with hμ
  set A : (Fin P.m → PauliScalar P) →
      MIPStarRE.Quantum.Measurement (ZMod 2)
        (S.toStrategy.ιA × S.toStrategy.ιB) := fun u =>
    DistanceCalculus.leftPlacedMeasurement (ιB := S.toStrategy.ιB)
      (S.pointTraceMeas .alice W u r) with hA
  set B : (Fin P.m → PauliScalar P) →
      MIPStarRE.Quantum.Measurement (ZMod 2)
        (S.toStrategy.ιA × S.toStrategy.ιB) := fun u =>
    DistanceCalculus.rightPlacedMeasurement (ιA := S.toStrategy.ιA)
      (S.pointTraceMeas .bob W u r) with hB
  have hfam : opFamilyDistSq μ
      (fun u b => (A u).effect b) (fun u b => (B u).effect b)
      S.toStrategy.ψ ≤ 2 * ((Fintype.card PauliEdge : ℝ) * ε) := by
    exact opFamilyDistSq_placed_le_of_consistencyDefect_le μ
      (fun u => S.pointTraceMeas .alice W u r)
      (fun u => S.pointTraceMeas .bob W u r) S.toStrategy.ψ
      (pointTrace_self_consistency_le S W r)
  have hobs := povm_to_obs_of_measurements μ A B phaseSign norm_phaseSign
    S.toStrategy.ψ
  have hleft : ∀ u,
      (∑ b : ZMod 2, phaseSign b • (A u).effect b) =
        heteroKron (S.pointObs .alice W r u) (1 : Op S.toStrategy.ιB) := by
    intro u
    rw [pointObs_eq_traceMeas_obs, heteroKron_left_sum_smul]
    rfl
  have hright : ∀ u,
      (∑ b : ZMod 2, phaseSign b • (B u).effect b) =
        heteroKron (1 : Op S.toStrategy.ιA) (S.pointObs .bob W r u) := by
    intro u
    rw [pointObs_eq_traceMeas_obs, heteroKron_right_sum_smul]
    rfl
  have hcast : (Fintype.card (ZMod 2) : ℝ) = 2 := by simp
  have hmain : opDistSq μ
      (fun u => heteroKron (S.pointObs .alice W r u) 1)
      (fun u => heteroKron 1 (S.pointObs .bob W r u))
      S.toStrategy.ψ ≤ 4 * (Fintype.card PauliEdge : ℝ) * ε := by
    have hrw : opDistSq μ
        (fun u => heteroKron (S.pointObs .alice W r u) 1)
        (fun u => heteroKron 1 (S.pointObs .bob W r u))
        S.toStrategy.ψ =
      opDistSq μ (fun u => ∑ b : ZMod 2, phaseSign b • (A u).effect b)
        (fun u => ∑ b : ZMod 2, phaseSign b • (B u).effect b)
        S.toStrategy.ψ := by
      congr 1 <;> funext u
      · exact (hleft u).symm
      · exact (hright u).symm
    rw [hrw]
    calc
      _ ≤ (Fintype.card (ZMod 2) : ℝ) * opFamilyDistSq μ
          (fun u b => (A u).effect b) (fun u b => (B u).effect b)
          S.toStrategy.ψ := hobs
      _ ≤ 2 * (2 * ((Fintype.card PauliEdge : ℝ) * ε)) := by
        rw [hcast]
        exact mul_le_mul_of_nonneg_left hfam (by norm_num)
      _ = 4 * (Fintype.card PauliEdge : ℝ) * ε := by ring
  refine ⟨hmain, ?_⟩
  refine le_of_eq_of_le ?_ hmain
  exact DistanceCalculus.opFamilyDistSq_symm μ _ _ _

end WinImplications

end

end MIPStarRE.QPBT
