import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Consistency.State

/-!
# Low-degree consistency defect transport

This module reindexes the QPBT consistency defect and transports the three
consistency conclusions of the mature low individual degree theorem without
changing their numerical bounds.

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

/-! ## Reindexing the QPBT defect -/

/-- A uniform consistency defect is invariant under a bijective relabeling of
its question type. -/
theorem consistencyDefect_uniform_question_equiv
    {X Y Outcome iota : Type*}
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype Outcome] [DecidableEq Outcome]
    [Fintype iota] [DecidableEq iota]
    (e : X ≃ Y) (A B : Y → Outcome → Op iota)
    (psi : EuclideanSpace ℂ iota) :
    consistencyDefect (uniformDistribution X)
        (fun x a => A (e x) a) (fun x a => B (e x) a) psi =
      consistencyDefect (uniformDistribution Y) A B psi := by
  unfold consistencyDefect
  simpa using avgOver_uniform_equiv e (fun x =>
    ∑ a : Outcome, ∑ b : Outcome,
      if a = b then 0 else
        (inner ℂ psi ((EuclideanSpace.equiv iota ℂ).symm
          (((A (e x) a) * (B (e x) b)).mulVec psi))).re)

/-- A consistency defect is invariant under a bijective relabeling of both
outcome families. -/
theorem consistencyDefect_outcome_equiv
    {X Alpha Beta iota : Type*}
    [Fintype X] [DecidableEq X]
    [Fintype Alpha] [DecidableEq Alpha]
    [Fintype Beta] [DecidableEq Beta]
    [Fintype iota] [DecidableEq iota]
    (mu : Distribution X) (e : Beta ≃ Alpha)
    (A B : X → Alpha → Op iota) (psi : EuclideanSpace ℂ iota) :
    consistencyDefect mu
        (fun x b => A x (e b)) (fun x b => B x (e b)) psi =
      consistencyDefect mu A B psi := by
  unfold consistencyDefect
  apply avgOver_congr
  intro x
  let term : Alpha → Alpha → ℝ := fun a b =>
    if a = b then 0 else
      (inner ℂ psi ((EuclideanSpace.equiv iota ℂ).symm
        (((A x a) * (B x b)).mulVec psi))).re
  calc
    _ = ∑ a : Beta, ∑ b : Beta, term (e a) (e b) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      unfold term
      by_cases hab : a = b
      · subst b
        simp
      · have heab : e a ≠ e b := fun h => hab (e.injective h)
        simp [hab, heab]
    _ =
        ∑ a : Beta, ∑ b : Alpha, term (e a) b := by
      apply Finset.sum_congr rfl
      intro a _
      exact Equiv.sum_comp e (fun b => term (e a) b)
    _ = ∑ a : Alpha, ∑ b : Alpha, term a b :=
      Equiv.sum_comp e (fun a => ∑ b : Alpha, term a b)
    _ = _ := rfl

/-- Simultaneous bijective relabeling of uniform questions and outcomes leaves
the consistency defect unchanged. -/
theorem consistencyDefect_uniform_question_outcome_equiv
    {X Y Alpha Beta iota : Type*}
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype Alpha] [DecidableEq Alpha]
    [Fintype Beta] [DecidableEq Beta]
    [Fintype iota] [DecidableEq iota]
    (questionEquiv : X ≃ Y) (outcomeEquiv : Beta ≃ Alpha)
    (A B : Y → Alpha → Op iota) (psi : EuclideanSpace ℂ iota) :
    consistencyDefect (uniformDistribution X)
        (fun x b => A (questionEquiv x) (outcomeEquiv b))
        (fun x b => B (questionEquiv x) (outcomeEquiv b)) psi =
      consistencyDefect (uniformDistribution Y) A B psi := by
  calc
    consistencyDefect (uniformDistribution X)
        (fun x b => A (questionEquiv x) (outcomeEquiv b))
        (fun x b => B (questionEquiv x) (outcomeEquiv b)) psi =
      consistencyDefect (uniformDistribution X)
        (fun x a => A (questionEquiv x) a)
        (fun x a => B (questionEquiv x) a) psi :=
      consistencyDefect_outcome_equiv (uniformDistribution X)
        outcomeEquiv _ _ psi
    _ = consistencyDefect (uniformDistribution Y) A B psi :=
      consistencyDefect_uniform_question_equiv questionEquiv A B psi

/-! ## The three mature LDT conclusions in direct coordinates -/

/-- Pointwise equality of both operator families gives equality of their
consistency defects. -/
theorem consistencyDefect_congr
    {X Outcome iota : Type*}
    [Fintype X] [DecidableEq X]
    [Fintype Outcome] [DecidableEq Outcome]
    [Fintype iota] [DecidableEq iota]
    (mu : Distribution X) (A A' B B' : X → Outcome → Op iota)
    (psi : EuclideanSpace ℂ iota)
    (hA : ∀ x a, A x a = A' x a) (hB : ∀ x a, B x a = B' x a) :
    consistencyDefect mu A B psi = consistencyDefect mu A' B' psi := by
  unfold consistencyDefect
  apply avgOver_congr
  intro x
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases hab : a = b
  · simp [hab]
  · simp only [hab, if_false]
    rw [hA x a, hB x b]

/-- The direct single-coordinate point/global defect is exactly the mature
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
          (maturePointAPlaced D S hS r)
          (maturePolynomialEvaluationRight D G) S.ψ := by
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
        (fun u a => maturePointAPlaced D S hS r
          (directPointEquiv D u) (directScalarEquiv D a))
        (fun u a => maturePolynomialEvaluationRight D G
          (directPointEquiv D u) (directScalarEquiv D a)) S.ψ := by
          apply consistencyDefect_congr
          · intro u a
            unfold maturePointAPlaced
            congr 1
            exact (directCoordinatePointMeasurement_effect_transport
              D S hS r u a).symm
          · intro u a
            unfold maturePolynomialEvaluationRight
            congr 1
            exact directPolynomialMeasurement_evaluation_effect D G u a
    _ = consistencyDefect (uniformDistribution (Point D.toLDTParameters))
        (maturePointAPlaced D S hS r)
        (maturePolynomialEvaluationRight D G) S.ψ :=
      consistencyDefect_uniform_question_outcome_equiv
        (directPointEquiv D) (directScalarEquiv D)
        (maturePointAPlaced D S hS r)
        (maturePolynomialEvaluationRight D G) S.ψ

/-- Convert the mature point/global `ConsRel` conclusion to its vector-state
QPBT defect formulation. -/
theorem maturePointPolynomial_consistencyDefect_le
    (D : DirectLdParams) (S : Strategy (directLdGame D))
    (hS : S.IsProjective) (r : Fin D.k) :
    letI := D.toLDTFieldModel
    ∀ (G : ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) S.ιB)
      (delta : ℝ),
      ConsRel (strategyQuantumState S)
          (uniformDistribution (Point D.toLDTParameters))
          (fun u => (matureCoordinatePointMeasurementA D S hS r u).toSubMeas)
          (fun u => (maturePolynomialEvaluationMeasurement D G u).toSubMeas) delta →
        consistencyDefect (uniformDistribution (Point D.toLDTParameters))
          (maturePointAPlaced D S hS r)
          (maturePolynomialEvaluationRight D G) S.ψ ≤ delta := by
  letI := D.toLDTFieldModel
  intro G delta h
  letI : Nonempty (S.ιA × S.ιB) :=
    (strategyQuantumState_isNormalized S).nonempty
  let pure : PureState (S.ιA × S.ιB) := gameStrategyPureState S
  have hpure :
      ConsRel (pure : QuantumState (S.ιA × S.ιB))
        (uniformDistribution (Point D.toLDTParameters))
        (fun u => (matureCoordinatePointMeasurementA D S hS r u).toSubMeas)
        (fun u => (maturePolynomialEvaluationMeasurement D G u).toSubMeas) delta := by
    rw [← strategyQuantumState_eq_gameStrategyPureState S]
    exact h
  have hconverted := (consRel_iff_consistencyDefect pure
    (uniformDistribution (Point D.toLDTParameters))
    (uniformDistribution_isProbability (Point D.toLDTParameters))
    (matureCoordinatePointMeasurementA D S hS r)
    (maturePolynomialEvaluationMeasurement D G) delta).mp hpure
  have hv : pureStateEuclideanVector pure = S.ψ := by
    exact gameStrategyPureState_euclideanVector S
  rw [hv] at hconverted
  have heq := consistencyDefect_congr
    (uniformDistribution (Point D.toLDTParameters))
    (maturePointAPlaced D S hS r)
    (fun u a => heteroKron
      ((matureCoordinatePointMeasurementA D S hS r u).outcome a) 1)
    (maturePolynomialEvaluationRight D G)
    (fun u a => heteroKron 1
      ((maturePolynomialEvaluationMeasurement D G u).outcome a)) S.ψ
    (by intro u a; rfl) (by intro u a; rfl)
  rw [heq]
  exact hconverted

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
  have hmature :
      consistencyDefect (uniformDistribution (Point D.toLDTParameters))
        (maturePointAPlaced D S hS r)
        (maturePolynomialEvaluationRight D G) S.ψ ≤ delta := by
    apply maturePointPolynomial_consistencyDefect_le D S hS r G delta
    change ConsRel (directCoordinateProjStrat D S hS r).state
      (uniformDistribution (Point D.toLDTParameters))
      (IdxProjMeas.toIdxSubMeas
        (directCoordinateProjStrat D S hS r).pointMeasurementA)
      (polynomialEvaluationFamily D.toLDTParameters G.toSubMeas) delta
    exact h
  rw [directPointPolynomial_consistencyDefect_eq D S hS r G]
  exact hmature

/-- The direct single-coordinate global/point defect is exactly the mature
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
          (maturePolynomialEvaluationLeft D G)
          (maturePointBPlaced D S hS r) S.ψ := by
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
        (fun u a => maturePolynomialEvaluationLeft D G
          (directPointEquiv D u) (directScalarEquiv D a))
        (fun u a => maturePointBPlaced D S hS r
          (directPointEquiv D u) (directScalarEquiv D a)) S.ψ := by
          apply consistencyDefect_congr
          · intro u a
            unfold maturePolynomialEvaluationLeft
            congr 1
            exact directPolynomialMeasurement_evaluation_effect D G u a
          · intro u a
            unfold maturePointBPlaced
            congr 1
            exact (directCoordinatePointMeasurementB_effect_transport
              D S hS r u a).symm
    _ = consistencyDefect (uniformDistribution (Point D.toLDTParameters))
        (maturePolynomialEvaluationLeft D G)
        (maturePointBPlaced D S hS r) S.ψ :=
      consistencyDefect_uniform_question_outcome_equiv
        (directPointEquiv D) (directScalarEquiv D)
        (maturePolynomialEvaluationLeft D G)
        (maturePointBPlaced D S hS r) S.ψ

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
        (fun u => (maturePolynomialEvaluationMeasurement D G u).toSubMeas)
        (fun u => (matureCoordinatePointMeasurementB D S hS r u).toSubMeas)
        delta := by
    change ConsRel (directCoordinateProjStrat D S hS r).state
      (uniformDistribution (Point D.toLDTParameters))
      (polynomialEvaluationFamily D.toLDTParameters G.toSubMeas)
      (IdxProjMeas.toIdxSubMeas
        (directCoordinateProjStrat D S hS r).pointMeasurementB) delta
    exact h
  have hmature := strategyConsRel_consistencyDefect_le S
    (uniformDistribution (Point D.toLDTParameters))
    (uniformDistribution_isProbability (Point D.toLDTParameters))
    (maturePolynomialEvaluationMeasurement D G)
    (matureCoordinatePointMeasurementB D S hS r) delta hbase
  have heq := consistencyDefect_congr
    (uniformDistribution (Point D.toLDTParameters))
    (maturePolynomialEvaluationLeft D G)
    (fun u a => heteroKron
      ((maturePolynomialEvaluationMeasurement D G u).outcome a) 1)
    (maturePointBPlaced D S hS r)
    (fun u a => heteroKron 1
      ((matureCoordinatePointMeasurementB D S hS r u).outcome a)) S.ψ
    (by intro u a; rfl) (by intro u a; rfl)
  rw [directPolynomialPoint_consistencyDefect_eq D S hS r G, heq]
  exact hmature

/-- Relabeling both global polynomial measurements identifies their direct
QPBT defect with the mature global/global defect. -/
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
          (fun _ g => maturePolynomialLeftPlaced D GA g)
          (fun _ g => maturePolynomialRightPlaced D GB g) S.ψ := by
  letI := D.toLDTFieldModel
  intro GA GB
  calc
    consistencyDefect (uniformDistribution Unit)
        (fun _ g => heteroKron ((directPolynomialMeasurement D GA).effect g) 1)
        (fun _ g => heteroKron 1 ((directPolynomialMeasurement D GB).effect g))
        S.ψ =
      consistencyDefect (uniformDistribution Unit)
        (fun _ g => maturePolynomialLeftPlaced D GA (directPolyEquivPolynomial D g))
        (fun _ g => maturePolynomialRightPlaced D GB (directPolyEquivPolynomial D g))
        S.ψ := by
          apply consistencyDefect_congr
          · intro _ g
            unfold maturePolynomialLeftPlaced
            rw [directPolynomialMeasurement_effect]
          · intro _ g
            unfold maturePolynomialRightPlaced
            rw [directPolynomialMeasurement_effect]
    _ = consistencyDefect (uniformDistribution Unit)
        (fun _ g => maturePolynomialLeftPlaced D GA g)
        (fun _ g => maturePolynomialRightPlaced D GB g) S.ψ :=
      consistencyDefect_outcome_equiv (uniformDistribution Unit)
        (directPolyEquivPolynomial D)
        (fun _ g => maturePolynomialLeftPlaced D GA g)
        (fun _ g => maturePolynomialRightPlaced D GB g) S.ψ

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
  have hmature := strategyConsRel_consistencyDefect_le S
    (uniformDistribution Unit) (uniformDistribution_isProbability Unit)
    (fun _ => GA) (fun _ => GB) delta h
  have heq := consistencyDefect_congr (uniformDistribution Unit)
    (fun _ g => maturePolynomialLeftPlaced D GA g)
    (fun _ g => heteroKron (GA.outcome g) 1)
    (fun _ g => maturePolynomialRightPlaced D GB g)
    (fun _ g => heteroKron 1 (GB.outcome g)) S.ψ
    (by intro _ g; rfl) (by intro _ g; rfl)
  rw [directPolynomialPolynomial_consistencyDefect_eq D S GA GB, heq]
  exact hmature

end

end MIPStarRE.QPBT
