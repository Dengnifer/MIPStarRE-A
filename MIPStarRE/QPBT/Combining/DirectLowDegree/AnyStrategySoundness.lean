import MIPStarRE.QPBT.Combining.DirectLowDegree.Soundness
import MIPStarRE.QPBT.Games.MeasurementCompression

/-!
# Direct low-degree soundness for arbitrary strategies

This module transports directly indexed low-degree soundness at simultaneity
parameter `1` from projective strategies to arbitrary strategies. Both local
measurement families are dilated by the existing one-measurement Naimark
construction. The polynomial-tuple POVMs returned by projective soundness are
then compressed to the original player carriers at the distinguished ancillary
coordinate.

Ground-slice compression preserves all three consistency defects exactly, so
the error function and its universal constants are unchanged. The compressed
polynomial POVMs are not asserted to be projective.

## Main result

* `exists_direct_ld_soundness_of_k_eq_one_any_strategy` removes the projectivity
  premise from the formalization-only direct `k = 1` soundness route.

## References

The projective soundness input formalizes the shape of paper
`lem:ld-soundness`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`.
The Naimark transport supports the first paragraph of the proof of paper
`lem:qld-4-7`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1277-1289`.
This module is Lean-only support and does not claim completion of that lemma.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.Quantum

noncomputable section

/-- Dilate every direct-game question measurement and pad the bipartite state
at the two distinguished `none` coordinates. -/
private def directLdNaimarkStrategy (D : DirectLdParams)
    (S : Strategy (directLdGame D)) : Strategy (directLdGame D) :=
  paddedStrategy S (none : Option (DirectLdAnswer D))
    (none : Option (DirectLdAnswer D))
    (fun question => dilatedMeasurement (default : DirectLdAnswer D) (S.A question))
    (fun question => dilatedMeasurement (default : DirectLdAnswer D) (S.B question))

/-- Every local measurement of the dilated direct-game strategy is projective. -/
private theorem directLdNaimarkStrategy_isProjective (D : DirectLdParams)
    (S : Strategy (directLdGame D)) : (directLdNaimarkStrategy D S).IsProjective :=
  paddedStrategy_isProjective S none none _ _
    (fun question => dilatedMeasurement_isProjective
      (default : DirectLdAnswer D) (S.A question))
    (fun question => dilatedMeasurement_isProjective
      (default : DirectLdAnswer D) (S.B question))

/-- The direct-game value is unchanged by the two local Naimark dilations. -/
private theorem directLdNaimarkStrategy_value (D : DirectLdParams)
    (S : Strategy (directLdGame D)) : (directLdNaimarkStrategy D S).value = S.value :=
  paddedStrategy_value S none none _ _
    (fun question answer => dilatedMeasurement_compression
      (default : DirectLdAnswer D) answer (S.A question))
    (fun question answer => dilatedMeasurement_compression
      (default : DirectLdAnswer D) answer (S.B question))

/-- Compressing Alice's dilated point measurement after point-answer
postprocessing recovers the original postprocessed point measurement. -/
private theorem directLdNaimarkStrategy_pointA_compress (D : DirectLdParams)
    (S : Strategy (directLdGame D)) (question : DirectLdQuestion D) :
    (((directLdNaimarkStrategy D S).A question).postprocess
        (directLdPointValuesOrZero D)).compressAt none =
      (S.A question).postprocess (directLdPointValuesOrZero D) := by
  change ((dilatedMeasurement (default : DirectLdAnswer D) (S.A question)).postprocess
      (directLdPointValuesOrZero D)).compressAt none = _
  rw [MIPStarRE.Quantum.Measurement.compressAt_postprocess,
    Measurement.compressAt_dilatedMeasurement]
  rfl

/-- Compressing Bob's dilated point measurement after point-answer
postprocessing recovers the original postprocessed point measurement. -/
private theorem directLdNaimarkStrategy_pointB_compress (D : DirectLdParams)
    (S : Strategy (directLdGame D)) (question : DirectLdQuestion D) :
    (((directLdNaimarkStrategy D S).B question).postprocess
        (directLdPointValuesOrZero D)).compressAt none =
      (S.B question).postprocess (directLdPointValuesOrZero D) := by
  change ((dilatedMeasurement (default : DirectLdAnswer D) (S.B question)).postprocess
      (directLdPointValuesOrZero D)).compressAt none = _
  rw [MIPStarRE.Quantum.Measurement.compressAt_postprocess,
    Measurement.compressAt_dilatedMeasurement]
  rfl

/-- Formalization-only soundness transport for the directly indexed low-degree
game at simultaneity parameter `1`, with no projectivity premise on the input
strategy.

Apply Naimark dilation to both question-indexed POVM families, use
`exists_direct_ld_soundness_of_k_eq_one` on the resulting projective strategy,
and compress its two polynomial-tuple POVMs at the distinguished ancillary
coordinates. The padded-state defect identity preserves the two point versus
polynomial bounds and the polynomial self-consistency bound exactly, with the
same witnesses `a`, `b`, and `deltaLd` as the projective theorem.

This theorem is Lean-only support for the Naimark step in the proof of paper
`lem:qld-4-7`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1277-1289`.
It does not assert projectivity of the compressed POVMs and introduces no
premise for a paper-labelled QPBT producer. -/
theorem exists_direct_ld_soundness_of_k_eq_one_any_strategy :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b ≤ 1 ∧
      ∀ (D : DirectLdParams) (ε : ℝ), D.k = 1 → 0 < ε →
        ∀ S : Strategy (directLdGame D), 1 - ε ≤ S.value →
          ∃ GA : DirectPolyMeasTuple D S.ιA,
            ∃ GB : DirectPolyMeasTuple D S.ιB,
              consistencyDefect
                  (uniformDistribution (Fin D.m → DirectScalarQ D))
                  (fun u outcome =>
                    heteroKron
                      (((S.A (directLdPointQuestionOf D u)).postprocess
                        (directLdPointValuesOrZero D)).effect outcome) 1)
                  (fun u outcome =>
                    heteroKron 1
                      ((GB.postprocess (evalDirectPolyTupleAt u)).effect outcome))
                  S.ψ ≤ deltaLd a b ε D.q D.m D.d D.k ∧
              consistencyDefect
                  (uniformDistribution (Fin D.m → DirectScalarQ D))
                  (fun u outcome =>
                    heteroKron
                      ((GA.postprocess (evalDirectPolyTupleAt u)).effect outcome) 1)
                  (fun u outcome =>
                    heteroKron 1
                      (((S.B (directLdPointQuestionOf D u)).postprocess
                        (directLdPointValuesOrZero D)).effect outcome))
                  S.ψ ≤ deltaLd a b ε D.q D.m D.d D.k ∧
              consistencyDefect (uniformDistribution Unit)
                  (fun _ g => heteroKron (GA.effect g) 1)
                  (fun _ g => heteroKron 1 (GB.effect g))
                  S.ψ ≤ deltaLd a b ε D.q D.m D.d D.k := by
  obtain ⟨a, b, ha, hb, hb1, hsound⟩ := exists_direct_ld_soundness_of_k_eq_one
  refine ⟨a, b, ha, hb, hb1, ?_⟩
  intro D ε hk hε S hwin
  have hwin' : 1 - ε ≤ (directLdNaimarkStrategy D S).value := by
    rw [directLdNaimarkStrategy_value]
    exact hwin
  obtain ⟨GA, GB, h1, h2, h3⟩ :=
    hsound D ε hk hε (directLdNaimarkStrategy D S)
      (directLdNaimarkStrategy_isProjective D S) hwin'
  let GA0 : DirectPolyMeasTuple D S.ιA :=
    GA.compressAt (none : Option (directLdGame D).AnswerA)
  let GB0 : DirectPolyMeasTuple D S.ιB :=
    GB.compressAt (none : Option (directLdGame D).AnswerB)
  refine ⟨GA0, GB0, ?_, ?_, ?_⟩
  · have htransport :
        consistencyDefect (uniformDistribution (Fin D.m → DirectScalarQ D))
            (fun u outcome => heteroKron
              ((((directLdNaimarkStrategy D S).A
                (directLdPointQuestionOf D u)).postprocess
                  (directLdPointValuesOrZero D)).effect outcome) 1)
            (fun u outcome => heteroKron 1
              ((GB.postprocess (evalDirectPolyTupleAt u)).effect outcome))
            (directLdNaimarkStrategy D S).ψ =
          consistencyDefect (uniformDistribution (Fin D.m → DirectScalarQ D))
            (fun u outcome => heteroKron
              (((((directLdNaimarkStrategy D S).A
                (directLdPointQuestionOf D u)).postprocess
                  (directLdPointValuesOrZero D)).compressAt none).effect outcome) 1)
            (fun u outcome => heteroKron 1
              (((GB.postprocess (evalDirectPolyTupleAt u)).compressAt none).effect outcome))
            S.ψ := by
      change consistencyDefect (uniformDistribution (Fin D.m → DirectScalarQ D))
          (fun u outcome => heteroKron
            ((((directLdNaimarkStrategy D S).A
              (directLdPointQuestionOf D u)).postprocess
                (directLdPointValuesOrZero D)).effect outcome) 1)
          (fun u outcome => heteroKron 1
            ((GB.postprocess (evalDirectPolyTupleAt u)).effect outcome))
          (padState none none S.ψ) = _
      exact consistencyDefect_padState_compressAt _ _ _ none none S.ψ
    calc
      consistencyDefect (uniformDistribution (Fin D.m → DirectScalarQ D))
          (fun u outcome => heteroKron
            (((S.A (directLdPointQuestionOf D u)).postprocess
              (directLdPointValuesOrZero D)).effect outcome) 1)
          (fun u outcome => heteroKron 1
            ((GB0.postprocess (evalDirectPolyTupleAt u)).effect outcome)) S.ψ =
        consistencyDefect (uniformDistribution (Fin D.m → DirectScalarQ D))
          (fun u outcome => heteroKron
            (((((directLdNaimarkStrategy D S).A
              (directLdPointQuestionOf D u)).postprocess
                (directLdPointValuesOrZero D)).compressAt none).effect outcome) 1)
          (fun u outcome => heteroKron 1
            (((GB.postprocess (evalDirectPolyTupleAt u)).compressAt none).effect outcome))
          S.ψ := by
            apply consistencyDefect_congr
            · intro u outcome
              rw [directLdNaimarkStrategy_pointA_compress]
            · intro u outcome
              dsimp only [GB0]
              congr 1
              ext i j
              simp only [MIPStarRE.Quantum.Measurement.compressAt_effect,
                MIPStarRE.Quantum.Measurement.postprocess_effect,
                Matrix.submatrix_apply, Matrix.sum_apply]
              rfl
      _ = consistencyDefect (uniformDistribution (Fin D.m → DirectScalarQ D))
          (fun u outcome => heteroKron
            ((((directLdNaimarkStrategy D S).A
              (directLdPointQuestionOf D u)).postprocess
                (directLdPointValuesOrZero D)).effect outcome) 1)
          (fun u outcome => heteroKron 1
            ((GB.postprocess (evalDirectPolyTupleAt u)).effect outcome))
          (directLdNaimarkStrategy D S).ψ := htransport.symm
      _ ≤ deltaLd a b ε D.q D.m D.d D.k := h1
  · have htransport :
        consistencyDefect (uniformDistribution (Fin D.m → DirectScalarQ D))
            (fun u outcome => heteroKron
              ((GA.postprocess (evalDirectPolyTupleAt u)).effect outcome) 1)
            (fun u outcome => heteroKron 1
              ((((directLdNaimarkStrategy D S).B
                (directLdPointQuestionOf D u)).postprocess
                  (directLdPointValuesOrZero D)).effect outcome))
            (directLdNaimarkStrategy D S).ψ =
          consistencyDefect (uniformDistribution (Fin D.m → DirectScalarQ D))
            (fun u outcome => heteroKron
              (((GA.postprocess (evalDirectPolyTupleAt u)).compressAt none).effect outcome) 1)
            (fun u outcome => heteroKron 1
              (((((directLdNaimarkStrategy D S).B
                (directLdPointQuestionOf D u)).postprocess
                  (directLdPointValuesOrZero D)).compressAt none).effect outcome))
            S.ψ := by
      change consistencyDefect (uniformDistribution (Fin D.m → DirectScalarQ D))
          (fun u outcome => heteroKron
            ((GA.postprocess (evalDirectPolyTupleAt u)).effect outcome) 1)
          (fun u outcome => heteroKron 1
            ((((directLdNaimarkStrategy D S).B
              (directLdPointQuestionOf D u)).postprocess
                (directLdPointValuesOrZero D)).effect outcome))
          (padState none none S.ψ) = _
      exact consistencyDefect_padState_compressAt _ _ _ none none S.ψ
    calc
      consistencyDefect (uniformDistribution (Fin D.m → DirectScalarQ D))
          (fun u outcome => heteroKron
            ((GA0.postprocess (evalDirectPolyTupleAt u)).effect outcome) 1)
          (fun u outcome => heteroKron 1
            (((S.B (directLdPointQuestionOf D u)).postprocess
              (directLdPointValuesOrZero D)).effect outcome)) S.ψ =
        consistencyDefect (uniformDistribution (Fin D.m → DirectScalarQ D))
          (fun u outcome => heteroKron
            (((GA.postprocess (evalDirectPolyTupleAt u)).compressAt none).effect outcome) 1)
          (fun u outcome => heteroKron 1
            (((((directLdNaimarkStrategy D S).B
              (directLdPointQuestionOf D u)).postprocess
                (directLdPointValuesOrZero D)).compressAt none).effect outcome))
          S.ψ := by
            apply consistencyDefect_congr
            · intro u outcome
              dsimp only [GA0]
              congr 1
              ext i j
              simp only [MIPStarRE.Quantum.Measurement.compressAt_effect,
                MIPStarRE.Quantum.Measurement.postprocess_effect,
                Matrix.submatrix_apply, Matrix.sum_apply]
              rfl
            · intro u outcome
              rw [directLdNaimarkStrategy_pointB_compress]
      _ = consistencyDefect (uniformDistribution (Fin D.m → DirectScalarQ D))
          (fun u outcome => heteroKron
            ((GA.postprocess (evalDirectPolyTupleAt u)).effect outcome) 1)
          (fun u outcome => heteroKron 1
            ((((directLdNaimarkStrategy D S).B
              (directLdPointQuestionOf D u)).postprocess
                (directLdPointValuesOrZero D)).effect outcome))
          (directLdNaimarkStrategy D S).ψ := htransport.symm
      _ ≤ deltaLd a b ε D.q D.m D.d D.k := h2
  · have htransport :
        consistencyDefect (uniformDistribution Unit)
            (fun _ g => heteroKron (GA.effect g) 1)
            (fun _ g => heteroKron 1 (GB.effect g))
            (directLdNaimarkStrategy D S).ψ =
          consistencyDefect (uniformDistribution Unit)
            (fun _ g => heteroKron ((GA.compressAt none).effect g) 1)
            (fun _ g => heteroKron 1 ((GB.compressAt none).effect g)) S.ψ := by
      change consistencyDefect (uniformDistribution Unit)
          (fun _ g => heteroKron (GA.effect g) 1)
          (fun _ g => heteroKron 1 (GB.effect g)) (padState none none S.ψ) = _
      exact consistencyDefect_padState_compressAt
        (uniformDistribution Unit) (fun _ => GA) (fun _ => GB) none none S.ψ
    calc
      consistencyDefect (uniformDistribution Unit)
          (fun _ g => heteroKron (GA0.effect g) 1)
          (fun _ g => heteroKron 1 (GB0.effect g)) S.ψ =
        consistencyDefect (uniformDistribution Unit)
          (fun _ g => heteroKron ((GA.compressAt none).effect g) 1)
          (fun _ g => heteroKron 1 ((GB.compressAt none).effect g)) S.ψ := by
            rfl
      _ = consistencyDefect (uniformDistribution Unit)
          (fun _ g => heteroKron (GA.effect g) 1)
          (fun _ g => heteroKron 1 (GB.effect g))
          (directLdNaimarkStrategy D S).ψ := htransport.symm
      _ ≤ deltaLd a b ε D.q D.m D.d D.k := h3

end

end MIPStarRE.QPBT
