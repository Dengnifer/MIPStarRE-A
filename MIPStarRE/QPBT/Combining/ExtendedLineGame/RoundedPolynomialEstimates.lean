import MIPStarRE.QPBT.Combining.OrderedPolynomialEstimates
import MIPStarRE.QPBT.Combining.ExtendedLineGame.PassingValue
import MIPStarRE.QPBT.Combining.DirectLowDegree.AnyStrategySoundness
import MIPStarRE.QPBT.Games.DistanceTheorems.RoundingTransport

/-!
# Rounded extended-polynomial ordered estimates

Direct soundness retains all three consistency conclusions through compression.
Its same-space projective rounding supplies the point comparison used in both
ordered estimates, with the actual point and line errors retained.

## References

`eq:qld-g-42` and `eq:qld-g-43`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1278-1300`.
The directly indexed completed-answer restriction is documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` and
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

namespace ExtendedLineGame

/-- Evaluation of the single extended polynomial returned by direct soundness,
at the point with blocks `(x,z,alpha,beta)`, in the canonical Pauli scalar field.
The singleton tuple carrier is exactly the `k = 1` soundness outcome carrier. -/
def extendedPolynomialRead (P : AdmissibleParams) (x : ExtendedPointQuestion P)
    (g : DirectPolyTuple P.extendedDirectLd) : PauliScalar P :=
  extendedDirectScalarEquiv P
    (evalDirectPolyTupleAt ((directPointExtendedQuestionEquiv P).symm x) g (0 : Fin 1))

/-- Undoing the joint coordinate equivalence recovers direct polynomial evaluation. -/
private theorem extendedPolynomialRead_equiv (P : AdmissibleParams)
    (u : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) :
    extendedPolynomialRead P (directPointExtendedQuestionEquiv P u) =
      fun g => extendedDirectScalarEquiv P (evalDirectPolyTupleAt u g (0 : Fin 1)) := by
  funext g
  unfold extendedPolynomialRead
  rw [Equiv.symm_apply_apply]

/-- The full polynomial-outcome squared-norm sum in `eq:qld-g-42/43`.
`reverse = false` uses `M_X M_Z`; `reverse = true` uses `M_Z M_X`.
The polynomial effect acts on `p1` and both point effects on `p2`. -/
def extendedPolynomialOrderedError {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (p1 p2 : Placement)
    (R : DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace p1.side))
    (reverse : Bool) : ℝ :=
  avgOver (uniformDistribution (ExtendedPointQuestion P)) (fun x =>
    ∑ g, ‖applyOperatorToState (S.place p1 (R.effect g) *
      (1 - S.place p2
        (∑ ab ∈ Finset.univ.filter (fun ab : PauliScalar P × PauliScalar P =>
            x.2.1 * ab.1 + x.2.2 * ab.2 = extendedPolynomialRead P x g),
          if reverse then
            (S.pointMeasExp p2.side .Z x.1.2).effect ab.2 *
              (S.pointMeasExp p2.side .X x.1.1).effect ab.1
          else
            (S.pointMeasExp p2.side .X x.1.1).effect ab.1 *
              (S.pointMeasExp p2.side .Z x.1.2).effect ab.2))) S.psiHat‖ ^ 2)

/-- Specialize projective refinement to the full polynomial-outcome norm sum. -/
private theorem ordered_error_le {P : AdmissibleParams} {ε δQ : ℝ}
    {S : ProjectiveSetting P ε} (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopposite : p1.IsOpposite p2)
    (R : DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace p1.side))
    (hR : Measurement.IsProjective R) (eta : ℝ)
    (hpoint : consistencyDefect (uniformDistribution (ExtendedPointQuestion P))
      (fun x a => S.place p1 ((R.postprocess (extendedPolynomialRead P x)).effect a))
      (fun x a => S.place p2
        ((points.extendedQ p2.side x.1.1 x.1.2 x.2.1 x.2.2).effect a)) S.psiHat ≤ eta)
    (reverse : Bool) :
    extendedPolynomialOrderedError S p1 p2 R reverse ≤ 4 * eta + 8 * δQ := by
  have h := points.ordered_dist_le p1 p2 hopposite R hR (extendedPolynomialRead P)
    eta hpoint
  cases reverse
  · simpa only [extendedPolynomialOrderedError, Bool.false_eq_true, if_false,
      mul_sub, mul_one, opFamilyDistSq] using h.1
  · simpa only [extendedPolynomialOrderedError, if_true,
      mul_sub, mul_one, opFamilyDistSq] using h.2

/-- Reading the single scalar of an actual direct-game point answer recovers `Q`. -/
private theorem point_scalar_measurement {P : AdmissibleParams} {ε δQ δL : ℝ}
    {S : ProjectiveSetting P ε} {points : CombinedPointsWitness S δQ}
    (lines : ExtendedLinesWitness S points δL) (side : PlayerSide)
    (u : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) :
    (((answerMeasurement lines side (directLdPointQuestionOf P.extendedDirectLd u)).postprocess
      (directLdPointValuesOrZero P.extendedDirectLd)).postprocess
        (fun values => extendedDirectScalarEquiv P (values (0 : Fin 1)))) =
      points.extendedQ side
        (directPointExtendedQuestionEquiv P u).1.1
        (directPointExtendedQuestionEquiv P u).1.2
        (directPointExtendedQuestionEquiv P u).2.1
        (directPointExtendedQuestionEquiv P u).2.2 := by
  rw [directPointExtendedQuestionEquiv_apply]
  simp only [answerMeasurement, directLdPointQuestionOf,
    MIPStarRE.Quantum.Measurement.postprocess_comp,
    pointAnswer, directLdPointValuesOrZero, RingEquiv.apply_symm_apply]
  apply MIPStarRE.Quantum.Measurement.ext
  intro a
  change (∑ b ∈ Finset.univ.filter (fun b : PauliScalar P => b = a), _) = _
  classical
  erw [Finset.sum_filter, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]

/-- Transport arbitrary POVM consistency to both heterogeneous expanded placements. -/
private theorem placed_consistency_pairState {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) {X α : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    (μ : Distribution X) (A : X → Measurement α (S.ExpandedLocalSpace .alice))
    (B : X → Measurement α (S.ExpandedLocalSpace .bob)) :
    (consistencyDefect μ (fun x a => S.place .AA' ((A x).effect a))
      (fun x a => S.place .BA'' ((B x).effect a)) S.psiHat =
      consistencyDefect μ (fun x a => heteroKron ((A x).effect a) 1)
        (fun x a => heteroKron 1 ((B x).effect a)) (pairState S)) ∧
    (consistencyDefect μ (fun x a => S.place .BB' ((B x).effect a))
      (fun x a => S.place .AB'' ((A x).effect a)) S.psiHat =
      consistencyDefect μ (fun x a => heteroKron ((A x).effect a) 1)
        (fun x a => heteroKron 1 ((B x).effect a)) (pairState S)) := by
  have hA (x : X) (a : α) := (Matrix.nonneg_iff_posSemidef.mp ((A x).pos a)).isHermitian
  have hB (x : X) (a : α) := (Matrix.nonneg_iff_posSemidef.mp ((B x).pos a)).isHermitian
  constructor
  · unfold consistencyDefect
    apply avgOver_congr
    intro x
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    split_ifs
    · rfl
    · simp only [consistency_term_eq_stateQForm, placed_product_stateQForm_eq]
      exact (stateQForm_pairState_eq_AA'_BA'' S _ _ (hA x a) (hB x b)).symm
  · unfold consistencyDefect
    apply avgOver_congr
    intro x
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    by_cases hab : a = b
    · simp [hab]
    · simp only [hab, Ne.symm hab, if_false, consistency_term_eq_stateQForm,
        placed_product_stateQForm_eq]
      rw [S.place_comm .BB' .AB'' (by trivial)]
      exact (stateQForm_pairState_eq_AB''_BB' S _ _ (hA x a) (hB x b)).symm

set_option maxHeartbeats 800000 in
/-- Direct soundness and same-space rounding construct extended-polynomial
projective measurements satisfying both ordered estimates on `AA'|BA''` and
`BB'|AB''`. The actual passing error is
`3 * (sqrt (deltaQ + deltaL) + m*d/q)`. All three compressed soundness
conclusions are used; in particular the polynomial consistency error is `delta`,
not the weaker point-derived estimate. The rounded point error is
`eta = delta + sqrt (220 * delta^(1/4)) + 2 * sqrt (2 * delta)`.

This proves the calculation `eq:qld-g-42/43` from the directly indexed extended
line witness with its completed-answer domain. It does not construct that line
witness, prove polynomial separation, or certify source lemma `lem:qld-4-7`.
The remaining source obligations are tracked by issue #513 and the module's
paper-gap references. -/
theorem exists_rounded_polynomial_ordered_estimates :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b ≤ 1 ∧
      ∀ (P : AdmissibleParams) (ε δQ δL : ℝ) (S : ProjectiveSetting P ε)
        (points : CombinedPointsWitness S δQ) (_lines : ExtendedLinesWitness S points δL),
      let delta := deltaLd a b
        (directPassingErrorEnvelope (δQ + δL) ((P.m * P.d : ℝ) / P.q))
        P.q (2 * P.m + 2) P.d 1
      let eta := delta + Real.sqrt (220 * Real.rpow delta (1 / 4 : ℝ)) +
        2 * Real.sqrt (2 * delta)
      ∃ RA : DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace .alice),
      ∃ RB : DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace .bob),
        Measurement.IsProjective RA ∧ Measurement.IsProjective RB ∧
        ∀ reverse : Bool,
          extendedPolynomialOrderedError S .AA' .BA'' RA reverse ≤ 4 * eta + 8 * δQ ∧
          extendedPolynomialOrderedError S .BB' .AB'' RB reverse ≤ 4 * eta + 8 * δQ := by
  classical
  obtain ⟨a, b, ha, hb, hb1, hsound⟩ :=
    exists_direct_ld_soundness_of_k_eq_one_any_strategy
  refine ⟨a, b, ha, hb, hb1, ?_⟩
  intro P ε δQ δL S points lines delta eta
  have hm := P.one_le_m
  have hd := P.hd
  have hq : 0 < P.q := by
    obtain ⟨k, _, hk⟩ := P.hq
    rw [hk]
    positivity
  have hpos : 0 < directPassingErrorEnvelope (δQ + δL) ((P.m * P.d : ℝ) / P.q) :=
    directPassingErrorEnvelope_pos _ _ (by positivity)
  obtain ⟨A, B, hB, hA, hAB⟩ := hsound P.extendedDirectLd _ rfl hpos
    (strategy lines) (strategy_value_ge_directPassingErrorEnvelope lines)
  change consistencyDefect _ _ _ _ ≤ delta at hA hB hAB
  have hdelta : 0 ≤ delta := by
    dsimp [delta, deltaLd]
    have ha0 : 0 ≤ a := le_trans (by norm_num) ha
    positivity
  obtain ⟨RA, RB, hRA, hRB, _, _, htransport⟩ :=
    projective_rounding_preserves_postprocessed_consistency
      (pairState S) (pairState_norm S) A B delta hdelta hAB
  have hround := htransport
    (uniformDistribution (Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd))
    (uniformDistribution_isProbability _) (fun u => evalDirectPolyTupleAt u)
  have hRApoint := hround.1
    (fun u => ((strategy lines).B (directLdPointQuestionOf P.extendedDirectLd u)).postprocess
      (directLdPointValuesOrZero P.extendedDirectLd)) delta hA
  have hRBpoint := hround.2
    (fun u => ((strategy lines).A (directLdPointQuestionOf P.extendedDirectLd u)).postprocess
      (directLdPointValuesOrZero P.extendedDirectLd)) delta hB
  rw [← two_mul delta] at hRApoint hRBpoint
  change consistencyDefect _ _ _ _ ≤ eta at hRApoint hRBpoint
  have hAscalar := (consistencyDefect_postprocess_question_le
    (uniformDistribution (Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd))
    (fun u => RA.postprocess (evalDirectPolyTupleAt u))
    (fun u => ((strategy lines).B (directLdPointQuestionOf P.extendedDirectLd u)).postprocess
      (directLdPointValuesOrZero P.extendedDirectLd)) (pairState S)
    (fun _ values => extendedDirectScalarEquiv P (values (0 : Fin 1)))).trans hRApoint
  have hBscalar := (consistencyDefect_postprocess_question_le
    (uniformDistribution (Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd))
    (fun u => ((strategy lines).A (directLdPointQuestionOf P.extendedDirectLd u)).postprocess
      (directLdPointValuesOrZero P.extendedDirectLd))
    (fun u => RB.postprocess (evalDirectPolyTupleAt u)) (pairState S)
    (fun _ values => extendedDirectScalarEquiv P (values (0 : Fin 1)))).trans hRBpoint
  change consistencyDefect _ _ _ (pairState S) ≤ eta at hAscalar hBscalar
  dsimp only [strategy] at hAscalar hBscalar
  conv at hAscalar =>
    lhs; arg 3; ext u c; arg 2; arg 1
    erw [point_scalar_measurement lines .bob u]
  conv at hBscalar =>
    lhs; arg 2; ext u c; arg 1; arg 1
    erw [point_scalar_measurement lines .alice u]
  simp only [MIPStarRE.Quantum.Measurement.postprocess_comp] at hAscalar hBscalar
  have hAquestion : consistencyDefect (uniformDistribution (ExtendedPointQuestion P))
      (fun x c => heteroKron ((RA.postprocess (extendedPolynomialRead P x)).effect c) 1)
      (fun x c => heteroKron 1
        ((points.extendedQ .bob x.1.1 x.1.2 x.2.1 x.2.2).effect c)) (pairState S) ≤ eta := by
    rw [← consistencyDefect_uniform_question_equiv (directPointExtendedQuestionEquiv P)]
    simp only [extendedPolynomialRead_equiv]
    exact hAscalar
  have hBquestion : consistencyDefect (uniformDistribution (ExtendedPointQuestion P))
      (fun x c => heteroKron
        ((points.extendedQ .alice x.1.1 x.1.2 x.2.1 x.2.2).effect c) 1)
      (fun x c => heteroKron 1 ((RB.postprocess (extendedPolynomialRead P x)).effect c))
      (pairState S) ≤ eta := by
    rw [← consistencyDefect_uniform_question_equiv (directPointExtendedQuestionEquiv P)]
    simp only [extendedPolynomialRead_equiv]
    exact hBscalar
  have hAplaced := (placed_consistency_pairState S
    (uniformDistribution (ExtendedPointQuestion P))
    (fun x => RA.postprocess (extendedPolynomialRead P x))
    (fun x => points.extendedQ .bob x.1.1 x.1.2 x.2.1 x.2.2)).1.trans_le hAquestion
  have hBplaced := (placed_consistency_pairState S
    (uniformDistribution (ExtendedPointQuestion P))
    (fun x => points.extendedQ .alice x.1.1 x.1.2 x.2.1 x.2.2)
    (fun x => RB.postprocess (extendedPolynomialRead P x))).2.trans_le hBquestion
  exact ⟨RA, RB, hRA, hRB, fun reverse =>
    ⟨ordered_error_le points .AA' .BA'' (by trivial) RA hRA eta hAplaced reverse,
      ordered_error_le points .BB' .AB'' (by trivial) RB hRB eta hBplaced reverse⟩⟩

end ExtendedLineGame

end

end MIPStarRE.QPBT
