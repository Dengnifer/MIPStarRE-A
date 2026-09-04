import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Consistency.State

/-!
# Low-degree consistency defect transport

This module expresses the consistency conclusions of the low individual
degree theorem in the coordinates of the directly indexed game, without
changing their numerical bounds.  The point/polynomial and polynomial/point
conclusions are taken at a fixed tuple coordinate; the polynomial/polynomial
conclusion is global.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:393-458`
- `references/ldt-paper/test_definition.tex:180-202`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.Quantum

noncomputable section

/-! ## The three LDT conclusions in direct coordinates -/

/-- The direct single-coordinate point/global defect is exactly the LDT
defect after the polynomial, point, and scalar equivalences. -/
theorem directPointPolynomial_consistencyDefect_eq
    (D : DirectLdParams) (S : Strategy (directLdGame D))
    (hS : S.IsProjective) (r : Fin D.k) :
    letI := D.toLDTFieldModel
    ∀ (G : ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) S.ιB),
      consistencyDefect
          (uniformDistribution (Fin D.m → DirectScalarQ D))
          (fun u a => heteroKron
            ((directPointCoordinateMeasurementA D S r u).effect a) 1)
          (fun u a => heteroKron 1
            ((directPolynomialEvaluationMeasurement D G u).effect a)) S.ψ =
        consistencyDefect (uniformDistribution (Point D.toLDTParameters))
          (ldtPointAPlaced D S hS r)
          (ldtPolynomialEvaluationRight D G) S.ψ := by
  letI := D.toLDTFieldModel
  intro G
  calc
    consistencyDefect
        (uniformDistribution (Fin D.m → DirectScalarQ D))
        (fun u a => heteroKron
          ((directPointCoordinateMeasurementA D S r u).effect a) 1)
        (fun u a => heteroKron 1
          ((directPolynomialEvaluationMeasurement D G u).effect a)) S.ψ =
      consistencyDefect
        (uniformDistribution (Fin D.m → DirectScalarQ D))
        (fun u a => ldtPointAPlaced D S hS r
          (directPointEquiv D u) (directScalarEquiv D a))
        (fun u a => ldtPolynomialEvaluationRight D G
          (directPointEquiv D u) (directScalarEquiv D a)) S.ψ := by
          apply consistencyDefect_congr
          · intro u a
            unfold ldtPointAPlaced
            congr 1
            exact (directCoordinatePointMeasurement_effect_transport
              D S hS r u a).symm
          · intro u a
            unfold ldtPolynomialEvaluationRight
            congr 1
            exact directPolynomialMeasurement_evaluation_effect D G u a
    _ = consistencyDefect (uniformDistribution (Point D.toLDTParameters))
        (ldtPointAPlaced D S hS r)
        (ldtPolynomialEvaluationRight D G) S.ψ :=
      consistencyDefect_uniform_question_outcome_equiv
        (directPointEquiv D) (directScalarEquiv D)
        (ldtPointAPlaced D S hS r)
        (ldtPolynomialEvaluationRight D G) S.ψ

/-- Convert the point-on-Alice/global-on-Bob conclusion of `LDT.Test.mainFormal`
for one simultaneous coordinate to the direct QPBT defect, with the identical
numerical bound. -/
theorem directPointPolynomial_consistencyDefect_le
    (D : DirectLdParams) (S : Strategy (directLdGame D))
    (hS : S.IsProjective) (r : Fin D.k) :
    letI := D.toLDTFieldModel
    ∀ (G : ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) S.ιB)
      (delta : ℝ),
      ConsRel (directCoordinateProjStrat D S hS r).state
          (uniformDistribution (Point D.toLDTParameters))
          (IdxProjMeas.toIdxSubMeas
            (directCoordinateProjStrat D S hS r).pointMeasurementA)
          (polynomialEvaluationFamily D.toLDTParameters G.toSubMeas) delta →
        consistencyDefect
          (uniformDistribution (Fin D.m → DirectScalarQ D))
          (fun u a => heteroKron
            ((directPointCoordinateMeasurementA D S r u).effect a) 1)
          (fun u a => heteroKron 1
            ((directPolynomialEvaluationMeasurement D G u).effect a))
          S.ψ ≤ delta := by
  letI := D.toLDTFieldModel
  intro G delta h
  rw [directPointPolynomial_consistencyDefect_eq D S hS r G]
  apply strategyConsRel_consistencyDefect_le S
    (uniformDistribution (Point D.toLDTParameters))
    (uniformDistribution_isProbability (Point D.toLDTParameters))
    (ldtCoordinatePointMeasurementA D S hS r)
    (ldtPolynomialEvaluationMeasurement D G) delta
  change ConsRel (directCoordinateProjStrat D S hS r).state
    (uniformDistribution (Point D.toLDTParameters))
    (IdxProjMeas.toIdxSubMeas
      (directCoordinateProjStrat D S hS r).pointMeasurementA)
    (polynomialEvaluationFamily D.toLDTParameters G.toSubMeas) delta
  exact h

/-- The direct single-coordinate global/point defect is exactly the LDT
defect after the polynomial, point, and scalar equivalences. -/
theorem directPolynomialPoint_consistencyDefect_eq
    (D : DirectLdParams) (S : Strategy (directLdGame D))
    (hS : S.IsProjective) (r : Fin D.k) :
    letI := D.toLDTFieldModel
    ∀ (G : ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) S.ιA),
      consistencyDefect
          (uniformDistribution (Fin D.m → DirectScalarQ D))
          (fun u a => heteroKron
            ((directPolynomialEvaluationMeasurement D G u).effect a) 1)
          (fun u a => heteroKron 1
            ((directPointCoordinateMeasurementB D S r u).effect a)) S.ψ =
        consistencyDefect (uniformDistribution (Point D.toLDTParameters))
          (ldtPolynomialEvaluationLeft D G)
          (ldtPointBPlaced D S hS r) S.ψ := by
  letI := D.toLDTFieldModel
  intro G
  calc
    consistencyDefect
        (uniformDistribution (Fin D.m → DirectScalarQ D))
        (fun u a => heteroKron
          ((directPolynomialEvaluationMeasurement D G u).effect a) 1)
        (fun u a => heteroKron 1
          ((directPointCoordinateMeasurementB D S r u).effect a)) S.ψ =
      consistencyDefect
        (uniformDistribution (Fin D.m → DirectScalarQ D))
        (fun u a => ldtPolynomialEvaluationLeft D G
          (directPointEquiv D u) (directScalarEquiv D a))
        (fun u a => ldtPointBPlaced D S hS r
          (directPointEquiv D u) (directScalarEquiv D a)) S.ψ := by
          apply consistencyDefect_congr
          · intro u a
            unfold ldtPolynomialEvaluationLeft
            congr 1
            exact directPolynomialMeasurement_evaluation_effect D G u a
          · intro u a
            unfold ldtPointBPlaced
            congr 1
            exact (directCoordinatePointMeasurementB_effect_transport
              D S hS r u a).symm
    _ = consistencyDefect (uniformDistribution (Point D.toLDTParameters))
        (ldtPolynomialEvaluationLeft D G)
        (ldtPointBPlaced D S hS r) S.ψ :=
      consistencyDefect_uniform_question_outcome_equiv
        (directPointEquiv D) (directScalarEquiv D)
        (ldtPolynomialEvaluationLeft D G)
        (ldtPointBPlaced D S hS r) S.ψ

/-- Convert the global-on-Alice/point-on-Bob conclusion of
`LDT.Test.mainFormal` for one simultaneous coordinate to the direct QPBT
defect, with the identical numerical bound. -/
theorem directPolynomialPoint_consistencyDefect_le
    (D : DirectLdParams) (S : Strategy (directLdGame D))
    (hS : S.IsProjective) (r : Fin D.k) :
    letI := D.toLDTFieldModel
    ∀ (G : ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) S.ιA)
      (delta : ℝ),
      ConsRel (directCoordinateProjStrat D S hS r).state
          (uniformDistribution (Point D.toLDTParameters))
          (polynomialEvaluationFamily D.toLDTParameters G.toSubMeas)
          (IdxProjMeas.toIdxSubMeas
            (directCoordinateProjStrat D S hS r).pointMeasurementB) delta →
        consistencyDefect
          (uniformDistribution (Fin D.m → DirectScalarQ D))
          (fun u a => heteroKron
            ((directPolynomialEvaluationMeasurement D G u).effect a) 1)
          (fun u a => heteroKron 1
            ((directPointCoordinateMeasurementB D S r u).effect a))
          S.ψ ≤ delta := by
  letI := D.toLDTFieldModel
  intro G delta h
  have hbase :
      ConsRel (strategyQuantumState S)
        (uniformDistribution (Point D.toLDTParameters))
        (fun u => (ldtPolynomialEvaluationMeasurement D G u).toSubMeas)
        (fun u => (ldtCoordinatePointMeasurementB D S hS r u).toSubMeas)
        delta := by
    change ConsRel (directCoordinateProjStrat D S hS r).state
      (uniformDistribution (Point D.toLDTParameters))
      (polynomialEvaluationFamily D.toLDTParameters G.toSubMeas)
      (IdxProjMeas.toIdxSubMeas
        (directCoordinateProjStrat D S hS r).pointMeasurementB) delta
    exact h
  have hldt := strategyConsRel_consistencyDefect_le S
    (uniformDistribution (Point D.toLDTParameters))
    (uniformDistribution_isProbability (Point D.toLDTParameters))
    (ldtPolynomialEvaluationMeasurement D G)
    (ldtCoordinatePointMeasurementB D S hS r) delta hbase
  have heq := consistencyDefect_congr
    (uniformDistribution (Point D.toLDTParameters))
    (ldtPolynomialEvaluationLeft D G)
    (fun u a => heteroKron
      ((ldtPolynomialEvaluationMeasurement D G u).outcome a) 1)
    (ldtPointBPlaced D S hS r)
    (fun u a => heteroKron 1
      ((ldtCoordinatePointMeasurementB D S hS r u).outcome a)) S.ψ
    (by intro u a; rfl) (by intro u a; rfl)
  rw [directPolynomialPoint_consistencyDefect_eq D S hS r G, heq]
  exact hldt

/-- Relabeling both global polynomial measurements identifies their direct
QPBT defect with the LDT global/global defect. -/
theorem directPolynomialPolynomial_consistencyDefect_eq
    (D : DirectLdParams) (S : Strategy (directLdGame D)) :
    letI := D.toLDTFieldModel
    ∀ (GA : ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) S.ιA)
      (GB : ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) S.ιB),
      consistencyDefect (uniformDistribution Unit)
          (fun _ g => heteroKron ((directPolynomialMeasurement D GA).effect g) 1)
          (fun _ g => heteroKron 1 ((directPolynomialMeasurement D GB).effect g))
          S.ψ =
        consistencyDefect (uniformDistribution Unit)
          (fun _ g => ldtPolynomialLeftPlaced D GA g)
          (fun _ g => ldtPolynomialRightPlaced D GB g) S.ψ := by
  letI := D.toLDTFieldModel
  intro GA GB
  calc
    consistencyDefect (uniformDistribution Unit)
        (fun _ g => heteroKron ((directPolynomialMeasurement D GA).effect g) 1)
        (fun _ g => heteroKron 1 ((directPolynomialMeasurement D GB).effect g))
        S.ψ =
      consistencyDefect (uniformDistribution Unit)
        (fun _ g => ldtPolynomialLeftPlaced D GA (directPolyEquivPolynomial D g))
        (fun _ g => ldtPolynomialRightPlaced D GB (directPolyEquivPolynomial D g))
        S.ψ := by
          apply consistencyDefect_congr
          · intro _ g
            unfold ldtPolynomialLeftPlaced
            rw [directPolynomialMeasurement_effect]
          · intro _ g
            unfold ldtPolynomialRightPlaced
            rw [directPolynomialMeasurement_effect]
    _ = consistencyDefect (uniformDistribution Unit)
        (fun _ g => ldtPolynomialLeftPlaced D GA g)
        (fun _ g => ldtPolynomialRightPlaced D GB g) S.ψ :=
      consistencyDefect_outcome_equiv (uniformDistribution Unit)
        (directPolyEquivPolynomial D)
        (fun _ g => ldtPolynomialLeftPlaced D GA g)
        (fun _ g => ldtPolynomialRightPlaced D GB g) S.ψ

/-- Convert the global/global conclusion of `LDT.Test.mainFormal` to the direct
QPBT defect, with the identical numerical bound. -/
theorem directPolynomialPolynomial_consistencyDefect_le
    (D : DirectLdParams) (S : Strategy (directLdGame D)) :
    letI := D.toLDTFieldModel
    ∀ (GA : ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) S.ιA)
      (GB : ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) S.ιB)
      (delta : ℝ),
      ConsRel (strategyQuantumState S) (uniformDistribution Unit)
          (constSubMeasFamily GA.toSubMeas)
          (constSubMeasFamily GB.toSubMeas) delta →
        consistencyDefect (uniformDistribution Unit)
          (fun _ g => heteroKron ((directPolynomialMeasurement D GA).effect g) 1)
          (fun _ g => heteroKron 1 ((directPolynomialMeasurement D GB).effect g))
          S.ψ ≤ delta := by
  letI := D.toLDTFieldModel
  intro GA GB delta h
  have hldt := strategyConsRel_consistencyDefect_le S
    (uniformDistribution Unit) (uniformDistribution_isProbability Unit)
    (fun _ => GA) (fun _ => GB) delta h
  have heq := consistencyDefect_congr (uniformDistribution Unit)
    (fun _ g => ldtPolynomialLeftPlaced D GA g)
    (fun _ g => heteroKron (GA.outcome g) 1)
    (fun _ g => ldtPolynomialRightPlaced D GB g)
    (fun _ g => heteroKron 1 (GB.outcome g)) S.ψ
    (by intro _ g; rfl) (by intro _ g; rfl)
  rw [directPolynomialPolynomial_consistencyDefect_eq D S GA GB, heq]
  exact hldt

/-- Deprecated specialization of `strategyConsRel_consistencyDefect_le` for
Alice's LDT point family and Bob's polynomial-evaluation family. -/
@[deprecated strategyConsRel_consistencyDefect_le (since := "2026-09-05")]
theorem maturePointPolynomial_consistencyDefect_le
    (D : DirectLdParams) (S : Strategy (directLdGame D))
    (hS : S.IsProjective) (r : Fin D.k) :
    letI := D.toLDTFieldModel
    ∀ (G : ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) S.ιB)
      (delta : ℝ),
      ConsRel (strategyQuantumState S)
          (uniformDistribution (Point D.toLDTParameters))
          (fun u => (ldtCoordinatePointMeasurementA D S hS r u).toSubMeas)
          (fun u => (ldtPolynomialEvaluationMeasurement D G u).toSubMeas) delta →
        consistencyDefect (uniformDistribution (Point D.toLDTParameters))
          (ldtPointAPlaced D S hS r)
          (ldtPolynomialEvaluationRight D G) S.ψ ≤ delta := by
  letI := D.toLDTFieldModel
  intro G delta h
  exact strategyConsRel_consistencyDefect_le S
    (uniformDistribution (Point D.toLDTParameters))
    (uniformDistribution_isProbability (Point D.toLDTParameters))
    (ldtCoordinatePointMeasurementA D S hS r)
    (ldtPolynomialEvaluationMeasurement D G) delta h

end

end MIPStarRE.QPBT
