import MIPStarRE.QPBT.Games.MeasurementCompression
import MIPStarRE.QPBT.Observables.Defs
import MIPStarRE.QPBT.Test.SoundnessDefs
import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.Dilation

/-!
# Naimark reduction for Pauli-test strategies

An arbitrary Pauli-test strategy is dilated questionwise to a projective
strategy on two separately enlarged local spaces. The ground-slice embeddings
are fixed across questions. Compression recovers both original POVM families,
including the complete Pauli-answer postprocessing. Composing any isometry
witness on the dilation with the embeddings returns its state comparison to
the original spaces. Operator-family distance transfer is not asserted here.

## References

Paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`
(`thm:pauli`) and
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:160-190,1862-1876`.
Blueprint `thm:pauli-naimark-reduction-support`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum MagicSquareRigidity

noncomputable section

/-- The question-independent embedding of Alice's original space in the
ground slice of the completed Naimark dilation. -/
def pauliNaimarkEmbeddingA (P : AdmissibleParams)
    (S : Strategy (pauliBasisTest P)) :
    EuclideanSpace ℂ S.ιA →ₗᵢ[ℂ]
      EuclideanSpace ℂ (S.ιA × Option (PauliAnswer P)) :=
  naimarkEmbedding S.ιA (PauliAnswer P)

/-- The corresponding question-independent embedding of Bob's space. -/
def pauliNaimarkEmbeddingB (P : AdmissibleParams)
    (S : Strategy (pauliBasisTest P)) :
    EuclideanSpace ℂ S.ιB →ₗᵢ[ℂ]
      EuclideanSpace ℂ (S.ιB × Option (PauliAnswer P)) :=
  naimarkEmbedding S.ιB (PauliAnswer P)

/-- Complete the Naimark dilation separately for every question and both
players, padding the original bipartite state at the ground coordinates. -/
def pauliNaimarkStrategy (P : AdmissibleParams)
    (S : Strategy (pauliBasisTest P)) : Strategy (pauliBasisTest P) :=
  paddedStrategy S (none : Option (PauliAnswer P)) (none : Option (PauliAnswer P))
    (fun question => dilatedMeasurement (default : PauliAnswer P) (S.A question))
    (fun question => dilatedMeasurement (default : PauliAnswer P) (S.B question))

/-- Both local families of the dilated strategy are projective measurements. -/
theorem pauliNaimarkStrategy_isProjective (P : AdmissibleParams)
    (S : Strategy (pauliBasisTest P)) : (pauliNaimarkStrategy P S).IsProjective :=
  paddedStrategy_isProjective S none none _ _
    (fun question => dilatedMeasurement_isProjective
      (default : PauliAnswer P) (S.A question))
    (fun question => dilatedMeasurement_isProjective
      (default : PauliAnswer P) (S.B question))

/-- The two ground-slice compressions preserve the value of the game exactly. -/
theorem pauliNaimarkStrategy_value (P : AdmissibleParams)
    (S : Strategy (pauliBasisTest P)) : (pauliNaimarkStrategy P S).value = S.value :=
  paddedStrategy_value S none none _ _
    (fun question answer => dilatedMeasurement_compression
      (default : PauliAnswer P) answer (S.A question))
    (fun question answer => dilatedMeasurement_compression
      (default : PauliAnswer P) answer (S.B question))

/-- The padded state is precisely the tensor image under the two fixed ground
embeddings; there is no identification of Alice's and Bob's local spaces. -/
theorem pauliNaimarkStrategy_state (P : AdmissibleParams)
    (S : Strategy (pauliBasisTest P)) :
    (pauliNaimarkStrategy P S).ψ =
      isometryTensor (pauliNaimarkEmbeddingA P S) (pauliNaimarkEmbeddingB P S) S.ψ := by
  change padState none none S.ψ = naimarkDilatedState (PauliAnswer P) S.ψ
  ext p
  rw [naimarkDilatedState_apply]
  simp only [padState, EuclideanSpace.equiv]
  by_cases hA : p.1.2 = none <;> by_cases hB : p.2.2 = none <;> simp [hA, hB]

/-- A winning strategy supplies a projective setting after dilation, with no
extra premise beyond the original winning inequality. -/
def pauliNaimarkSetting (P : AdmissibleParams) (epsilon : ℝ)
    (S : Strategy (pauliBasisTest P)) (hwin : 1 - epsilon ≤ S.value) :
    ProjectiveSetting P epsilon where
  toStrategy := pauliNaimarkStrategy P S
  isProjective := pauliNaimarkStrategy_isProjective P S
  win := by rw [pauliNaimarkStrategy_value]; exact hwin

/-- Alice's full question-indexed POVM is recovered by compression. -/
theorem pauliNaimarkStrategy_compressA (P : AdmissibleParams)
    (S : Strategy (pauliBasisTest P)) (question : PauliQuestion P) :
    ((pauliNaimarkStrategy P S).A question).compressAt none = S.A question :=
  Measurement.compressAt_dilatedMeasurement _ _

/-- Bob's full question-indexed POVM is recovered by compression. -/
theorem pauliNaimarkStrategy_compressB (P : AdmissibleParams)
    (S : Strategy (pauliBasisTest P)) (question : PauliQuestion P) :
    ((pauliNaimarkStrategy P S).B question).compressAt none = S.B question :=
  Measurement.compressAt_dilatedMeasurement _ _

/-- Compression commutes with the complete `pauliAnswerOrZero` postprocessing
of Alice's Pauli-question measurement, including wrong-form outcomes. -/
theorem pauliNaimarkStrategy_pauli_compressA (P : AdmissibleParams)
    (S : Strategy (pauliBasisTest P)) (W : PauliKind) :
    (((pauliNaimarkStrategy P S).A (pauliQuestion P W)).postprocess
      pauliAnswerOrZero).compressAt none =
        (S.A (pauliQuestion P W)).postprocess pauliAnswerOrZero := by
  change ((dilatedMeasurement (default : PauliAnswer P)
      (S.A (pauliQuestion P W))).postprocess pauliAnswerOrZero).compressAt none = _
  rw [MIPStarRE.Quantum.Measurement.compressAt_postprocess,
    Measurement.compressAt_dilatedMeasurement]
  rfl

/-- Compression commutes with the complete `pauliAnswerOrZero` postprocessing
of Bob's Pauli-question measurement, including wrong-form outcomes. -/
theorem pauliNaimarkStrategy_pauli_compressB (P : AdmissibleParams)
    (S : Strategy (pauliBasisTest P)) (W : PauliKind) :
    (((pauliNaimarkStrategy P S).B (pauliQuestion P W)).postprocess
      pauliAnswerOrZero).compressAt none =
        (S.B (pauliQuestion P W)).postprocess pauliAnswerOrZero := by
  change ((dilatedMeasurement (default : PauliAnswer P)
      (S.B (pauliQuestion P W))).postprocess pauliAnswerOrZero).compressAt none = _
  rw [MIPStarRE.Quantum.Measurement.compressAt_postprocess,
    Measurement.compressAt_dilatedMeasurement]
  rfl

/-- Compose a witness on the dilated strategy with the ground embeddings,
keeping both auxiliary carrier spaces and the same normalized auxiliary state. -/
def pauliNaimarkWitness (P : AdmissibleParams)
    (S : Strategy (pauliBasisTest P))
    (w : PauliSoundnessWitness P (pauliNaimarkStrategy P S)) :
    PauliSoundnessWitness P S where
  ιA' := w.ιA'
  ιB' := w.ιB'
  φA := w.φA.comp (pauliNaimarkEmbeddingA P S)
  φB := w.φB.comp (pauliNaimarkEmbeddingB P S)
  aux := w.aux
  aux_norm := w.aux_norm

/-- The extracted original state is exactly the extracted dilated state. -/
theorem pauli_naimark_witness_state_eq (P : AdmissibleParams)
    (S : Strategy (pauliBasisTest P))
    (w : PauliSoundnessWitness P (pauliNaimarkStrategy P S)) :
    isometryTensor (pauliNaimarkWitness P S w).φA
        (pauliNaimarkWitness P S w).φB S.ψ =
      isometryTensor w.φA w.φB (pauliNaimarkStrategy P S).ψ := by
  rw [pauliNaimarkStrategy_state]
  exact isometryTensor_comp w.φA w.φB
    (pauliNaimarkEmbeddingA P S) (pauliNaimarkEmbeddingB P S) S.ψ

/-- Consequently the original and dilated witnesses have equal state-distance
quantities from the same ideal auxiliary state. -/
theorem pauli_naimark_witness_state_distance_eq (P : AdmissibleParams)
    (S : Strategy (pauliBasisTest P))
    (w : PauliSoundnessWitness P (pauliNaimarkStrategy P S)) :
    ‖isometryTensor (pauliNaimarkWitness P S w).φA
        (pauliNaimarkWitness P S w).φB S.ψ -
      idealState P (pauliNaimarkWitness P S w).aux‖ =
    ‖isometryTensor w.φA w.φB (pauliNaimarkStrategy P S).ψ -
      idealState P w.aux‖ := by
  rw [pauli_naimark_witness_state_eq]
  rfl

end

end MIPStarRE.QPBT
