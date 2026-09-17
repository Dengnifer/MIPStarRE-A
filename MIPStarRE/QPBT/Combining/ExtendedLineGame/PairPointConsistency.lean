import MIPStarRE.QPBT.Combining.ExtendedLineGame.RetainedPointMass
import MIPStarRE.QPBT.Combining.OverlapGap

/-!
# Point consistency of the completed polynomial-pair measurements

The polynomial-pair completion is applied to the actual rounded outcomes. Its missing
mass and retained point mismatch are kept separate until the final bound.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1375-1404`,
`eq:qld-sgg-completeness` and `eq:qld-sgg-mhat-sandwich`;
blueprint `lem:qld-4-7`.
-/

open scoped BigOperators MatrixOrder

namespace MIPStarRE.QPBT.ExtendedLineGame

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus PolynomialImageBounds

noncomputable section

private theorem place_add {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (p : Placement)
    (A B : Op (S.ExpandedLocalSpace p.side)) :
    S.place p (A + B) = S.place p A + S.place p B := by
  ext i j
  cases p <;> simp only [ProjectiveSetting.place, Matrix.add_apply, add_mul, mul_add]

/-- The retained diagonal overlap with the actual opposite point measurement. -/
def retainedPointOverlap {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (p1 p2 : Placement)
    (R : DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace p1.side))
    (W : PauliKind) : ℝ :=
  avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun x =>
    ∑ pair : PolyPair P, stateQForm S.psiHat
      (S.place p1 (R.effect (directCombinedEmbedding P pair)) *
        S.place p2 ((S.pointMeasExp p2.side W x).effect (evalAt W x pair))))

private theorem retained_mass_eq {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (p : Placement)
    (R : DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace p.side))
    (hR : Measurement.IsProjective R) :
    (∑ pair : PolyPair P,
      ‖applyOperatorToState (S.place p (R.effect (directCombinedEmbedding P pair)))
        S.psiHat‖ ^ 2) = 1 - separatedPolynomialMass S p R := by
  classical
  let w := fun g => ‖applyOperatorToState (S.place p (R.effect g)) S.psiHat‖ ^ 2
  have hmass : ∑ g, w g = 1 := by
    simpa only [w, ProjectiveSetting.placedMeasurement_effect, S.psiHat_norm, one_pow] using
      sum_projective_state_norm_sq (S.placedMeasurement p R)
        (S.placedMeasurement_isProjective p R hR) S.psiHat
  have hgood : Finset.univ.image (directCombinedEmbedding P) =
      Finset.univ.filter (fun g => ∃ pair : PolyPair P,
        MvPolynomial.map (extendedDirectScalarEquiv P).toRingHom (g (0 : Fin 1)).1 =
          combinePoly pair.1.1 pair.2.1) := by
    ext g
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    exact mem_range_directCombinedEmbedding P g
  change (∑ pair, w (directCombinedEmbedding P pair)) = _
  rw [← Finset.sum_image (f := w) (fun a _ b _ h =>
    (directCombinedEmbedding P).injective h), hgood]
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun g => ∃ pair : PolyPair P,
      MvPolynomial.map (extendedDirectScalarEquiv P).toRingHom (g (0 : Fin 1)).1 =
        combinePoly pair.1.1 pair.2.1) w
  rw [hmass] at hsplit
  exact eq_sub_of_add_eq hsplit

/-- Retained mass splits exactly into point overlap and point mismatch.
This is the normalized good/bad identity of `eq:qld-s-good-and-bad`; the
individual projected vectors in its proof remain unnormalized. -/
theorem retainedPointMismatch_eq {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (p1 p2 : Placement) (hopposite : p1.IsOpposite p2)
    (R : DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace p1.side))
    (hR : Measurement.IsProjective R) (W : PauliKind) :
    retainedPointMismatch S p1 p2 R W =
      1 - separatedPolynomialMass S p1 R - retainedPointOverlap S p1 p2 R W := by
  have hpoint (x : Fin P.m → PauliScalar P) (pair : PolyPair P) :
      ‖applyOperatorToState
        (1 - S.place p2 ((S.pointMeasExp p2.side W x).effect (evalAt W x pair)))
        (applyOperatorToState (S.place p1 (R.effect (directCombinedEmbedding P pair)))
          S.psiHat)‖ ^ 2 =
      ‖applyOperatorToState (S.place p1 (R.effect (directCombinedEmbedding P pair)))
        S.psiHat‖ ^ 2 - stateQForm S.psiHat
          (S.place p1 (R.effect (directCombinedEmbedding P pair)) *
            S.place p2 ((S.pointMeasExp p2.side W x).effect (evalAt W x pair))) := by
    have hM := S.placedMeasurement_isProjective p2 _ (S.pointMeasExp_isProjective _ W x)
      (evalAt W x pair)
    have hG := S.placedMeasurement_isProjective p1 R hR (directCombinedEmbedding P pair)
    simp only [ProjectiveSetting.placedMeasurement_effect] at hM hG
    have hcomm := S.place_comm p1 p2 hopposite
      (R.effect (directCombinedEmbedding P pair))
      ((S.pointMeasExp p2.side W x).effect (evalAt W x pair))
    rw [MagicSquareRigidity.norm_applyOperatorToState_sq]
    change stateQForm _ _ = _
    have hsub (ψ : EuclideanSpace ℂ (SixReg P S.toStrategy.ιA S.toStrategy.ιB))
        (A B : Op (SixReg P S.toStrategy.ιA S.toStrategy.ιB)) :
        stateQForm ψ (A - B) = stateQForm ψ A - stateQForm ψ B := by
      simp [stateQForm, applyOperatorToState]
    rw [hM.one_sub.isSelfAdjoint.isHermitian.eq, hM.one_sub.isIdempotentElem.eq,
      hsub, stateQForm_one,
      stateQForm_applyOperatorToState_eq_of_isProj S.psiHat hG hcomm.symm, hcomm]
  unfold retainedPointMismatch retainedPointOverlap
  simp_rw [hpoint, Finset.sum_sub_distrib, avgOver_sub, avgOver_uniform_const]
  rw [retained_mass_eq S p1 R hR]

/-- The retained overlap loses only the excluded mass and `2E + 4/q`.
Both bases and heterogeneous placements use their actual ordered residual. -/
theorem retainedPointOverlap_ge_ordered_error {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (p1 p2 : Placement) (hopposite : p1.IsOpposite p2)
    (R : DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace p1.side))
    (hR : Measurement.IsProjective R) (reverse : Bool) :
    1 - separatedPolynomialMass S p1 R -
        2 * extendedPolynomialOrderedError S p1 p2 R reverse - 4 / P.q ≤
      retainedPointOverlap S p1 p2 R (if reverse then .Z else .X) := by
  have h := retainedPointMismatch_le_ordered_error S p1 p2 hopposite R hR reverse
  rw [retainedPointMismatch_eq S p1 p2 hopposite R hR] at h
  linarith

/-- Completion increases the retained diagonal overlap on any opposite
placement. This transports the completion estimate to all four directed
expanded placements, without identifying the player spaces. -/
theorem directPairMeasurement_consistency_le {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (p1 p2 : Placement) (hopposite : p1.IsOpposite p2)
    (R : DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace p1.side))
    (hR : Measurement.IsProjective R) (pair₀ : PolyPair P) (W : PauliKind) :
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
      (fun x a => S.place p1 (((directPairMeasurement R pair₀).postprocess
        (evalAt W x)).effect a))
      (fun x a => S.place p2 ((S.pointMeasExp p2.side W x).effect a)) S.psiHat ≤
      separatedPolynomialMass S p1 R + retainedPointMismatch S p1 p2 R W := by
  classical
  let C := directPairMeasurement R pair₀
  let B := fun x => S.pointMeasExp p2.side W x
  have hdiag (x : Fin P.m → PauliScalar P) :
      (∑ a : PauliScalar P, stateQForm S.psiHat
        (S.place p1 ((C.postprocess (evalAt W x)).effect a) * S.place p2 ((B x).effect a))) =
      ∑ pair : PolyPair P, stateQForm S.psiHat
        (S.place p1 (C.effect pair) * S.place p2 ((B x).effect (evalAt W x pair))) := by
    simp_rw [Quantum.Measurement.postprocess_effect, S.place_finsetSum, Finset.sum_mul,
      stateQForm_finset_sum]
    calc
      _ = ∑ a : PauliScalar P, ∑ pair ∈ Finset.univ.filter
          (fun pair => evalAt W x pair = a), stateQForm S.psiHat
          (S.place p1 (C.effect pair) * S.place p2 ((B x).effect (evalAt W x pair))) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro pair hp
        rw [(Finset.mem_filter.mp hp).2]
      _ = _ := Finset.sum_fiberwise Finset.univ (evalAt W x) _
  have hretained (x : Fin P.m → PauliScalar P) :
      (∑ pair : PolyPair P, stateQForm S.psiHat
        (S.place p1 (R.effect (directCombinedEmbedding P pair)) *
          S.place p2 ((B x).effect (evalAt W x pair)))) ≤
      ∑ pair : PolyPair P, stateQForm S.psiHat
        (S.place p1 (C.effect pair) * S.place p2 ((B x).effect (evalAt W x pair))) := by
    apply Finset.sum_le_sum
    intro pair _
    dsimp only [C, directPairMeasurement]
    rw [completedPairMeasurement_effect, place_add, add_mul, stateQForm_add]
    have heffect : (combinedPairSubmeasurement P
        (canonicalPolynomialMeasurement R)).effect pair =
        R.effect (directCombinedEmbedding P pair) :=
      canonicalPolynomialMeasurement_effect R (combinedPolyEmbedding P pair)
    rw [heffect]
    apply le_add_of_nonneg_right
    apply stateQForm_nonneg
    apply Commute.mul_nonneg
    · apply S.place_nonneg
      split_ifs
      · exact sub_nonneg.mpr (combinedPairSubmeasurement P
          (canonicalPolynomialMeasurement R)).total_le_one
      · exact le_rfl
    · exact S.place_nonneg p2 ((B x).pos _)
    · exact S.place_comm p1 p2 hopposite _ _
  have hbound : consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
      (fun x a => S.place p1 ((C.postprocess (evalAt W x)).effect a))
      (fun x a => S.place p2 ((B x).effect a)) S.psiHat ≤
      1 - retainedPointOverlap S p1 p2 R W := by
    unfold consistencyDefect
    simp_rw [consistency_term_eq_stateQForm]
    have heq (x : Fin P.m → PauliScalar P) := point_defect_eq
      (S.placedMeasurement p1 (C.postprocess (evalAt W x)))
      (S.placedMeasurement p2 (B x)) S.psiHat
    simp only [ProjectiveSetting.placedMeasurement_effect, S.psiHat_norm, one_pow] at heq
    simp_rw [heq, hdiag]
    have h := avgOver_mono (uniformDistribution (Fin P.m → PauliScalar P)) _ _
      (fun x => sub_le_sub_left (hretained x) 1)
    simpa only [avgOver_sub, avgOver_uniform_const, retainedPointOverlap, B] using h
  rw [retainedPointMismatch_eq S p1 p2 hopposite R hR W]
  linarith

/-- The completed pair measurement has point defect at most bad mass plus
`2E + 4/q`, for each basis and every opposite placement. -/
theorem directPairMeasurement_consistency_le_ordered_error
    {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (p1 p2 : Placement) (hopposite : p1.IsOpposite p2)
    (R : DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace p1.side))
    (hR : Measurement.IsProjective R) (pair₀ : PolyPair P) (reverse : Bool) :
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
      (fun x a => S.place p1 (((directPairMeasurement R pair₀).postprocess
        (evalAt (if reverse then .Z else .X) x)).effect a))
      (fun x a => S.place p2
        ((S.pointMeasExp p2.side (if reverse then .Z else .X) x).effect a)) S.psiHat ≤
      separatedPolynomialMass S p1 R +
        2 * extendedPolynomialOrderedError S p1 p2 R reverse + 4 / P.q := by
  have h := directPairMeasurement_consistency_le S p1 p2 hopposite R hR pair₀
    (if reverse then .Z else .X)
  have hm := retainedPointMismatch_le_ordered_error S p1 p2 hopposite R hR reverse
  linarith

/-- Construct complete projective polynomial-pair measurements with all four
point-consistency conclusions at the actual explicit error. The point and
directly indexed completed-answer line witnesses are exactly the inputs of
the established rounded constructor. They are not assumptions of the source
theorem; its proof supplies them internally and absorbs the eighth-root rounding term.
The direct-domain and line-error discrepancies remain documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` and
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`.
-/
theorem exists_pairWitness_of_points_lines :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b ≤ 1 ∧
      ∀ (P : AdmissibleParams) (ε δQ δL : ℝ) (S : ProjectiveSetting P ε)
        (points : CombinedPointsWitness S δQ) (_lines : ExtendedLinesWitness S points δL),
      let delta := deltaLd a b
        (directPassingErrorEnvelope (δQ + δL) ((P.m * P.d : ℝ) / P.q))
        P.q (2 * P.m + 2) P.d 1
      let eta := delta + Real.sqrt (220 * Real.rpow delta (1 / 4 : ℝ)) +
        2 * Real.sqrt (2 * delta)
      Nonempty (GlobalPairWitness S (8 * (4 * eta + 8 * δQ) +
        (((12 * P.m * P.d + 4 * P.d + 14 : ℕ) : ℝ) / P.q))) := by
  obtain ⟨a, b, ha, hb, hb1, h⟩ := exists_rounded_polynomial_separated_mass
  refine ⟨a, b, ha, hb, hb1, ?_⟩
  intro P ε δQ δL S points lines delta eta
  obtain ⟨RA, RB, hRA, hRB, horder, hmassA, hmassB⟩ := h P ε δQ δL S points lines
  let pair₀ : PolyPair P := (0, 0)
  have hA (reverse : Bool) := directPairMeasurement_consistency_le_ordered_error
    S .AA' .BA'' (by trivial) RA hRA pair₀ reverse
  have hB (reverse : Bool) := directPairMeasurement_consistency_le_ordered_error
    S .BB' .AB'' (by trivial) RB hRB pair₀ reverse
  have hbound :
      6 * (4 * eta + 8 * δQ) + (((12 * P.m * P.d + 4 * P.d + 10 : ℕ) : ℝ) / P.q) +
        2 * (4 * eta + 8 * δQ) + 4 / P.q =
      8 * (4 * eta + 8 * δQ) + (((12 * P.m * P.d + 4 * P.d + 14 : ℕ) : ℝ) / P.q) := by
    push_cast
    ring
  refine ⟨{
    Smeas := fun side => match side with
      | .alice => directPairMeasurement RA pair₀
      | .bob => directPairMeasurement RB pair₀
    projective := ?_
    point_consistent_alice := ?_
    point_consistent_bob := ?_ }⟩
  · intro side
    cases side
    · exact directPairMeasurement_projective RA hRA pair₀
    · exact directPairMeasurement_projective RB hRB pair₀
  · intro W
    cases W
    · exact (hA false).trans ((add_le_add
        (add_le_add hmassA (mul_le_mul_of_nonneg_left (horder false).1 (by norm_num)))
        le_rfl).trans_eq hbound)
    · exact (hA true).trans ((add_le_add
        (add_le_add hmassA (mul_le_mul_of_nonneg_left (horder true).1 (by norm_num)))
        le_rfl).trans_eq hbound)
  · intro W
    cases W
    · exact (hB false).trans ((add_le_add
        (add_le_add hmassB (mul_le_mul_of_nonneg_left (horder false).2 (by norm_num)))
        le_rfl).trans_eq hbound)
    · exact (hB true).trans ((add_le_add
        (add_le_add hmassB (mul_le_mul_of_nonneg_left (horder true).2 (by norm_num)))
        le_rfl).trans_eq hbound)

end

end MIPStarRE.QPBT.ExtendedLineGame
