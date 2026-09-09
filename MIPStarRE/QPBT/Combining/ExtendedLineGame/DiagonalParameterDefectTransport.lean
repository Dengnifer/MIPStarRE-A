import MIPStarRE.QPBT.Combining.ExtendedLineGame.ParameterEvaluatedLineBound
import MIPStarRE.QPBT.Combining.ExtendedLineGame.SameLineCoefficientBound
import MIPStarRE.QPBT.Observables.WinImplications.Averages

/-!
# Transport for the diagonal parameter defect

This module identifies the diagonal coefficient defect used in the same-line
rejection bound with the diagonal parameter-evaluation defect used in the
supplied-line comparison. The proof composes the measurement postprocessings
and uses `diagonalRead_eval` to compare the two coefficient readers.

The equality is a formalization-only bridge supporting the classical-game
construction in the proof of `lem:qld-4-7`. It retains the original diagonal
line marginal, including zero directions, and introduces no new hypotheses.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- Blueprint `lem:qld-4-7`.
- Issue #353.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace ExtendedLineGame

variable {P : AdmissibleParams} {epsilon deltaQ deltaL : Real}
variable {setting : ProjectiveSetting P epsilon}
variable {points : CombinedPointsWitness setting deltaQ}

/-- The independently evaluated diagonal coefficient defect equals the
diagonal parameter-evaluation defect of the direct-game strategy. -/
theorem diagonal_parameter_evaluated_coefficient_defect_eq
    (lines : ExtendedLinesWitness setting points deltaL) :
    diagonalParameterEvaluatedCoefficientDefect lines =
      diagonalParameterEvaluationDefect lines := by
  classical
  let readDiagonal : DirectLdAnswer P.extendedDirectLd →
      DirectDegPoly P.extendedDirectLd
        (P.extendedDirectLd.m * P.extendedDirectLd.d) := fun answer =>
    match answer with
    | .dlinePolys coefficients => coefficients ⟨0, by change 0 < 1; decide⟩
    | _ => 0
  let μ := Distribution.prod (uniformDistribution (DirectLdSpace P.extendedDirectLd))
    (uniformDistribution (DirectScalarQ P.extendedDirectLd))
  have hmeasurement :
      diagonalParameterEvaluatedCoefficientDefect lines =
        consistencyDefect μ
          (fun sample value => heteroKron
            (((answerMeasurement lines .alice
              (.dline, directLdMap P.extendedDirectLd .dline sample.1)).postprocess
                (fun answer => evalCoefficient (readDiagonal answer) sample.2)).effect value) 1)
          (fun sample value => heteroKron 1
            (((answerMeasurement lines .bob
              (.dline, directLdMap P.extendedDirectLd .dline sample.1)).postprocess
                (fun answer => evalCoefficient (readDiagonal answer) sample.2)).effect value))
          (pairState setting) := by
    unfold diagonalParameterEvaluatedCoefficientDefect consistencyDefect
    dsimp only [μ]
    simp only [SandwichProduct.avgOver_distribution_prod, directDLinePointDist,
      Distribution.map_map, Distribution.avgOver_map]
    apply avgOver_congr
    intro sample
    apply avgOver_congr
    intro parameter
    have hA (value : DirectScalarQ P.extendedDirectLd) :
        heteroKron
            (((lines.Qline .alice
              (directDLineDescOf P.extendedDirectLd sample)).postprocess
                (fun coefficients =>
                  evalCoefficient (diagonalRead P coefficients) parameter)).effect value)
            (1 : Op (setting.ExpandedLocalSpace .bob)) =
          heteroKron
            (((answerMeasurement lines .alice
              (.dline, directLdMap P.extendedDirectLd .dline sample)).postprocess
                (fun answer => evalCoefficient (readDiagonal answer) parameter)).effect value)
            1 := by
      apply congrArg (fun effect => heteroKron effect 1)
      unfold answerMeasurement
      rw [diagonal_description_canonical]
      rw [SandwichProduct.postprocess_postprocess_effect]
      apply congrArg (fun read =>
        ((lines.Qline .alice
          (directDLineDescOf P.extendedDirectLd sample)).postprocess read).effect value)
      funext coefficients
      calc
        evalCoefficient (diagonalRead P coefficients) parameter =
            evalCoefficient coefficients parameter :=
          diagonalRead_eval P coefficients parameter
        _ = evalCoefficient (readDiagonal (diagonalAnswer P coefficients)) parameter := by
          rw [show readDiagonal (diagonalAnswer P coefficients) =
            diagonalRead P coefficients by rfl]
          exact (diagonalRead_eval P coefficients parameter).symm
    have hB (value : DirectScalarQ P.extendedDirectLd) :
        heteroKron (1 : Op (setting.ExpandedLocalSpace .alice))
            (((lines.Qline .bob
              (directDLineDescOf P.extendedDirectLd sample)).postprocess
                (fun coefficients =>
                  evalCoefficient (diagonalRead P coefficients) parameter)).effect value) =
          heteroKron (1 : Op (setting.ExpandedLocalSpace .alice))
            (((answerMeasurement lines .bob
              (.dline, directLdMap P.extendedDirectLd .dline sample)).postprocess
                (fun answer => evalCoefficient (readDiagonal answer) parameter)).effect value) := by
      apply congrArg (fun effect => heteroKron 1 effect)
      unfold answerMeasurement
      rw [diagonal_description_canonical]
      rw [SandwichProduct.postprocess_postprocess_effect]
      apply congrArg (fun read =>
        ((lines.Qline .bob
          (directDLineDescOf P.extendedDirectLd sample)).postprocess read).effect value)
      funext coefficients
      calc
        evalCoefficient (diagonalRead P coefficients) parameter =
            evalCoefficient coefficients parameter :=
          diagonalRead_eval P coefficients parameter
        _ = evalCoefficient (readDiagonal (diagonalAnswer P coefficients)) parameter := by
          rw [show readDiagonal (diagonalAnswer P coefficients) =
            diagonalRead P coefficients by rfl]
          exact (diagonalRead_eval P coefficients parameter).symm
    apply Finset.sum_congr rfl
    intro valueA _
    apply Finset.sum_congr rfl
    intro valueB _
    simp only [SandwichProduct.postprocess_postprocess_effect]
    rw [hA valueA, hB valueB]
  rw [hmeasurement]
  change consistencyDefect μ
      (fun sample value => heteroKron
        ((((strategy lines).A
          (.dline, directLdMap P.extendedDirectLd .dline sample.1)).postprocess
            (fun answer => evalCoefficient (readDiagonal answer) sample.2)).effect value) 1)
      (fun sample value => heteroKron 1
        ((((strategy lines).B
          (.dline, directLdMap P.extendedDirectLd .dline sample.1)).postprocess
            (fun answer => evalCoefficient (readDiagonal answer) sample.2)).effect value))
      (strategy lines).ψ = diagonalParameterEvaluationDefect lines
  rw [WinImplications.consistencyDefect_postprocess_eq_mismatch]
  unfold diagonalParameterEvaluationDefect parameterEvalDefect
  simp only [directDLinePointDist, Distribution.avgOver_map]
  dsimp only [μ]
  rw [SandwichProduct.avgOver_distribution_prod]
  apply avgOver_congr
  intro sample
  apply avgOver_congr
  intro parameter
  rfl

end ExtendedLineGame

end

end MIPStarRE.QPBT
