import MIPStarRE.LDT.Preliminaries.PolynomialAgreement
import MIPStarRE.LDT.Test.MainTheorem.MainFormal
import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Consistency.Defect
import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Error
import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.PassConversion
import MIPStarRE.QPBT.Games.Sandwich

/-!
# Simultaneous polynomial measurements for the direct low-degree game

This module contains the coordinatewise application of the mature low
individual degree theorem and the palindromic measurement used to combine its
coordinate polynomial measurements. It also transports the Schwartz--Zippel
collision estimate to the direct polynomial representation.

The theorem `consistencyDefect_sandwich_le` proves the quantitative estimate
when the reference PVM already has tuple-polynomial outcomes. The simultaneous
direct-game reduction instead starts from a point-indexed PVM with tuple-value
outcomes. Relating its effects to the evaluated palindromic product requires
the unstructured point-reference estimate of Fact 4.35 in the secondary source;
the corresponding QPBT interface `exists_pasting_error` remains open (issue
#201), so this module does not use it as an assumption.

## References

* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:465-501`
* `references/neexp-paper/05_quantum_preliminaries.tex`, Fact 4.35
* `references/ldt-paper/test_definition.tex:180-202`
* `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.Quantum

noncomputable section

/-! ## Direct polynomial collision estimate -/

/-- Two distinct direct polynomial representatives agree at a uniformly
sampled direct point with probability at most `m d / q`.

This is `polynomialAgreement_avg_le_mdq` transported through the polynomial
and point equivalences of the direct low-degree interface. -/
theorem directPolynomialAgreement_avg_le_mdq (D : DirectLdParams)
    (g g' : PolyIndex D.m (DirectScalarQ D) D.d) (hneq : g ≠ g') :
    avgOver (uniformDistribution (Fin D.m → DirectScalarQ D))
        (fun u => if MvPolynomial.eval u g.1 = MvPolynomial.eval u g'.1 then
          (1 : Error) else 0) ≤
      (D.m * D.d : Error) / D.q := by
  letI := D.toLDTFieldModel
  let gLdt := directPolyEquivPolynomial D g
  let g'Ldt := directPolyEquivPolynomial D g'
  have hneqLdt : gLdt ≠ g'Ldt := by
    intro heq
    exact hneq ((directPolyEquivPolynomial D).injective heq)
  calc
    avgOver (uniformDistribution (Fin D.m → DirectScalarQ D))
        (fun u => if MvPolynomial.eval u g.1 = MvPolynomial.eval u g'.1 then
          (1 : Error) else 0) =
      avgOver (uniformDistribution (Fin D.m → DirectScalarQ D))
        (fun u => if gLdt (directPointEquiv D u) =
          g'Ldt (directPointEquiv D u) then (1 : Error) else 0) := by
            apply avgOver_congr
            intro u
            simp only [gLdt, g'Ldt, directPolyEquivPolynomial_apply]
            exact if_congr
              ((directScalarEquiv D).injective.eq_iff.symm) rfl rfl
    _ = avgOver (uniformDistribution (Point D.toLDTParameters))
        (fun u : Point D.toLDTParameters =>
          if gLdt u = g'Ldt u then (1 : Error) else 0) := by
      simpa using
        (avgOver_uniform_equiv (directPointEquiv D)
          (fun u : Fin D.m → DirectScalarQ D =>
            if gLdt (directPointEquiv D u) =
              g'Ldt (directPointEquiv D u) then (1 : Error) else 0))
    _ ≤ (D.m * D.d : Error) / D.q :=
      polynomialAgreement_avg_le_mdq D.toLDTParameters gLdt g'Ldt hneqLdt

/-! ## Palindromic tuple measurements -/

/-- Combine coordinate polynomial projective measurements into a tuple-valued
POVM by the ordered palindromic product of `lem:ld-sandwich`.

No commutativity between different coordinate measurements is assumed. -/
noncomputable def directSandwichPolynomialMeasurement
    (D : DirectLdParams) {iota : Type*} [Fintype iota] [DecidableEq iota]
    (G : Fin D.k → PolyMeas D.m (DirectScalarQ D) D.d iota)
    (hG : ∀ r, Measurement.IsProjective (G r)) :
    DirectPolyMeasTuple D iota := by
  let hmeasurement := sandwichProduct_isMeasurement
    (G := fun r (_ : Unit) => G r) (hG := fun r (_ : Unit) => hG r) ()
  exact Quantum.Measurement.ofSumEqOne
    (fun g => sandwichProduct (fun r (_ : Unit) h => (G r).effect h) () g)
    hmeasurement.1 hmeasurement.2

/-- The effects of the tuple POVM are its defining palindromic products. -/
@[simp] theorem directSandwichPolynomialMeasurement_effect
    (D : DirectLdParams) {iota : Type*} [Fintype iota] [DecidableEq iota]
    (G : Fin D.k → PolyMeas D.m (DirectScalarQ D) D.d iota)
    (hG : ∀ r, Measurement.IsProjective (G r))
    (g : DirectPolyTuple D) :
    (directSandwichPolynomialMeasurement D G hG).effect g =
      sandwichProduct (fun r (_ : Unit) h => (G r).effect h) () g :=
  rfl

/-- Relabeling a mature polynomial projective measurement by direct
polynomial representatives preserves projectivity. -/
theorem directPolynomialMeasurement_isProjective
    (D : DirectLdParams) :
    letI := D.toLDTFieldModel
    ∀ {iota : Type*} [Fintype iota] [DecidableEq iota]
      (G : ProjMeas (Polynomial D.toLDTParameters) iota),
      Measurement.IsProjective (directPolynomialMeasurement D G) := by
  letI := D.toLDTFieldModel
  intro iota _ _ G g
  rw [directPolynomialMeasurement_effect]
  refine { isIdempotentElem := ?_, isSelfAdjoint := ?_ }
  · exact G.proj (directPolyEquivPolynomial D g)
  · exact (Matrix.nonneg_iff_posSemidef.mp
      (G.outcome_pos (directPolyEquivPolynomial D g))).1.isSelfAdjoint

/-! ## Coordinatewise low individual degree soundness -/

/-- Apply `MIPStarRE.LDT.Test.mainFormal` to one coordinate of a projective
direct low-degree strategy.

The mature theorem receives the transported pass bound `3 ε` and the
auxiliary sampling parameter `directLdAuxParameter D`; both of its numerical
side conditions follow from the positivity fields of `D`. -/
theorem directCoordinateMainFormal
    (D : DirectLdParams) (S : Strategy (directLdGame D))
    (hS : S.IsProjective) (r : Fin D.k) (ε : Error)
    (hwin : 1 - ε ≤ S.value) :
    letI := D.toLDTFieldModel
    ∃ GA : ProjMeas (Polynomial D.toLDTParameters) S.ιA,
      ∃ GB : ProjMeas (Polynomial D.toLDTParameters) S.ιB,
        ConsRel (directCoordinateProjStrat D S hS r).state
            (uniformDistribution (Point D.toLDTParameters))
            (IdxProjMeas.toIdxSubMeas
              (directCoordinateProjStrat D S hS r).pointMeasurementA)
            (polynomialEvaluationFamily D.toLDTParameters GB.toSubMeas)
            (Test.mainFormalError D.toLDTParameters
              (directLdAuxParameter D) (3 * ε)) ∧
          ConsRel (directCoordinateProjStrat D S hS r).state
            (uniformDistribution (Point D.toLDTParameters))
            (polynomialEvaluationFamily D.toLDTParameters GA.toSubMeas)
            (IdxProjMeas.toIdxSubMeas
              (directCoordinateProjStrat D S hS r).pointMeasurementB)
            (Test.mainFormalError D.toLDTParameters
              (directLdAuxParameter D) (3 * ε)) ∧
          ConsRel (directCoordinateProjStrat D S hS r).state
            (uniformDistribution Unit)
            (constSubMeasFamily GA.toSubMeas)
            (constSubMeasFamily GB.toSubMeas)
            (Test.mainFormalError D.toLDTParameters
              (directLdAuxParameter D) (3 * ε)) := by
  letI := D.toLDTFieldModel
  exact Test.mainFormal D.toLDTParameters
    (directCoordinateProjStrat D S hS r) (3 * ε)
    (directCoordinate_passes D S hS r ε hwin).soundnessHypothesis
    (directLdAuxParameter D) (four_hundred_mul_le_directLdAuxParameter D)
    (directLdAuxParameter_pos D)

end

end MIPStarRE.QPBT
