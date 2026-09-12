import MIPStarRE.QPBT.Combining.SubLineZDeficit

/-!
# X-point deficit from joint line consistency

This directly indexed auxiliary construction follows the first consistency
route for combined lines. The question carrier, completed answer alphabet,
and corrected error convention retain their existing meanings.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1118-1246`,
blueprint `lem:qld-4-13-established`. Recovered from commit
`6e8d67ef8ba22de69a0c166adcdf23ba6e7a33aa` for issue #512.
See `docs/paper-gaps/qpbt_combined-lines-error-term.tex` and
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` for the remaining
comparison with the printed source theorem.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open scoped BigOperators Matrix MatrixOrder ComplexOrder

noncomputable section

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

/-- The completed `X`-then-`Z` point product vanishes on both `none` classes
and restricts to the ordered product on evaluated pairs. -/
theorem completedPair_norm_sq_sum_XZ (S : ProjectiveSetting P ε) {δ : ℝ}
    (points : CombinedPointsWitness S δ) (p : Placement)
    (x z : Fin P.m → PauliScalar P) :
    (∑ o : Option (PauliScalar P) × Option (PauliScalar P),
        ‖applyOperatorToState
          (S.place p (((points.Q p.side x z).postprocess (fun ab =>
              (some ab.1, some ab.2))).effect o) -
            S.place p
              ((S.pointMeasExpOption p.side .X x).effect o.1 *
                (S.pointMeasExpOption p.side .Z z).effect o.2))
          S.psiHat‖ ^ 2) =
      ∑ ab : PauliScalar P × PauliScalar P,
        ‖applyOperatorToState
          (S.place p ((points.Q p.side x z).effect ab) -
            S.place p
              ((S.pointMeasExp p.side .X x).effect ab.1 *
                (S.pointMeasExp p.side .Z z).effect ab.2))
          S.psiHat‖ ^ 2 := by
  refine S.sum_norm_place_completedPair_sub_sq p (points.Q p.side x z) _ _ ?_ ?_ ?_
  · intro ab
    rw [S.pointMeasExpOption_effect_some, S.pointMeasExpOption_effect_some]
  · intro o2
    rw [S.pointMeasExpOption_effect_none, zero_mul]
  · intro o1
    rw [S.pointMeasExpOption_effect_none, mul_zero]

end ProjectiveSetting

variable {P : AdmissibleParams} {ε δQ δP : ℝ} {S : ProjectiveSetting P ε}
  {points : CombinedPointsWitness S δQ}

/-- The `X`-point deficit of the evaluated pair-line measurement over a
probability law on pairs of line-point pairs, from the consistency of the
evaluated pair-line measurement with the completed joint point measurement
and the closeness of the latter to the `X`-then-`Z` product.  This is the
deficit bounded in the proof of `lem:claim-17-2`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1168-1201`. -/
theorem CombinedLinesWitness.one_sub_X_overlap_le_at
    (lines : CombinedLinesWitness S points δP)
    (first second : Placement) (hopposite : first.IsOpposite second)
    (ν : Distribution (LinePointPairSample P)) (hν : ν.IsProbability) (η ζ : ℝ)
    (hcons : consistencyDefect ν
      (fun s o => S.place first
        (((lines.T first.side s.1.1 s.2.1).postprocess fun fs =>
          (evalOpt s.1.1 s.1.2 fs.1, evalOpt s.2.1 s.2.2 fs.2)).effect o))
      (fun s o => S.place second
        (((points.Q second.side s.1.2 s.2.2).postprocess fun ab =>
          (some ab.1, some ab.2)).effect o))
      S.psiHat ≤ η)
    (hXZ : opFamilyDistSq ν
      (fun s o => S.place second
        (((points.Q second.side s.1.2 s.2.2).postprocess fun ab =>
          (some ab.1, some ab.2)).effect o))
      (fun s o => S.place second
        ((S.pointMeasExpOption second.side .X s.1.2).effect o.1 *
          (S.pointMeasExpOption second.side .Z s.2.2).effect o.2))
      S.psiHat ≤ ζ) :
    1 - avgOver ν (fun s =>
      ∑ o : Option (PauliScalar P) × Option (PauliScalar P),
        stateQForm S.psiHat
          (S.place first
            (((lines.T first.side s.1.1 s.2.1).postprocess fun fs =>
              (evalOpt s.1.1 s.1.2 fs.1, evalOpt s.2.1 s.2.2 fs.2)).effect o) *
            S.place second ((S.pointMeasExpOption second.side .X s.1.2).effect o.1))) ≤
      2 * Real.sqrt η + 2 * Real.sqrt ζ := by
  have hQproj : ∀ s : LinePointPairSample P,
      Measurement.IsProjective (S.placedMeasurement second
        ((points.Q second.side s.1.2 s.2.2).postprocess fun ab => (some ab.1, some ab.2))) :=
    fun s => S.placedMeasurement_isProjective _ _
      (completedPair_isProjective _ (points.projective _ _ _))
  have hRproj : ∀ (s : LinePointPairSample P)
      (o : Option (PauliScalar P) × Option (PauliScalar P)),
      IsProj (S.place second ((S.pointMeasExpOption second.side .X s.1.2).effect o.1)) :=
    fun s o => S.place_isProj _ (S.pointMeasExpOption_isProj _ _ _ _)
  have hWR : ∀ (s : LinePointPairSample P)
      (o : Option (PauliScalar P) × Option (PauliScalar P)),
      S.place second ((S.pointMeasExpOption second.side .Z s.2.2).effect o.2 *
          (S.pointMeasExpOption second.side .X s.1.2).effect o.1) *
        S.place second ((S.pointMeasExpOption second.side .X s.1.2).effect o.1) =
      S.place second ((S.pointMeasExpOption second.side .Z s.2.2).effect o.2 *
        (S.pointMeasExpOption second.side .X s.1.2).effect o.1) := by
    intro s o
    have hlocal : (S.pointMeasExpOption second.side .Z s.2.2).effect o.2 *
          (S.pointMeasExpOption second.side .X s.1.2).effect o.1 *
        (S.pointMeasExpOption second.side .X s.1.2).effect o.1 =
        (S.pointMeasExpOption second.side .Z s.2.2).effect o.2 *
          (S.pointMeasExpOption second.side .X s.1.2).effect o.1 := by
      rw [mul_assoc, (S.pointMeasExpOption_isProj second.side .X s.1.2 o.1).isIdempotentElem.eq]
    exact (ProjectiveSetting.place_mul S second _ _).symm.trans
      (congrArg (S.place second) hlocal)
  have hnonneg : ∀ (s : LinePointPairSample P)
      (o : Option (PauliScalar P) × Option (PauliScalar P)),
      0 ≤ stateQForm S.psiHat
        (S.place first
          (((lines.T first.side s.1.1 s.2.1).postprocess fun fs =>
            (evalOpt s.1.1 s.1.2 fs.1, evalOpt s.2.1 s.2.2 fs.2)).effect o) *
          S.place second
            (((points.Q second.side s.1.2 s.2.2).postprocess fun ab =>
              (some ab.1, some ab.2)).effect o)) :=
    fun s o => stateQForm_nonneg _ (S.place_mul_place_nonneg first second hopposite
      (((lines.T first.side s.1.1 s.2.1).postprocess fun fs =>
        (evalOpt s.1.1 s.1.2 fs.1, evalOpt s.2.1 s.2.2 fs.2)).pos o)
      (((points.Q second.side s.1.2 s.2.2).postprocess fun ab =>
        (some ab.1, some ab.2)).pos o))
  have hdist : opFamilyDistSq ν
      (fun s o => S.place second
        (((points.Q second.side s.1.2 s.2.2).postprocess fun ab =>
          (some ab.1, some ab.2)).effect o))
      (fun s o => (S.place second
        ((S.pointMeasExpOption second.side .Z s.2.2).effect o.2 *
          (S.pointMeasExpOption second.side .X s.1.2).effect o.1))ᴴ)
      S.psiHat ≤ ζ := by
    refine le_of_eq_of_le ?_ hXZ
    unfold opFamilyDistSq
    refine avgOver_congr _ _ _ fun s => Finset.sum_congr rfl fun o _ => ?_
    have hlocal : ((S.pointMeasExpOption second.side .Z s.2.2).effect o.2 *
          (S.pointMeasExpOption second.side .X s.1.2).effect o.1)ᴴ =
        (S.pointMeasExpOption second.side .X s.1.2).effect o.1 *
          (S.pointMeasExpOption second.side .Z s.2.2).effect o.2 := by
      rw [Matrix.conjTranspose_mul,
        (S.pointMeasExpOption_isProj second.side .X s.1.2 o.1).isSelfAdjoint.isHermitian.eq,
        (S.pointMeasExpOption_isProj second.side .Z s.2.2 o.2).isSelfAdjoint.isHermitian.eq]
    have hplace : (S.place second
        ((S.pointMeasExpOption second.side .Z s.2.2).effect o.2 *
          (S.pointMeasExpOption second.side .X s.1.2).effect o.1))ᴴ =
        S.place second ((S.pointMeasExpOption second.side .X s.1.2).effect o.1 *
          (S.pointMeasExpOption second.side .Z s.2.2).effect o.2) :=
      (ProjectiveSetting.place_conjTranspose S second _).symm.trans
        (congrArg (S.place second) hlocal)
    dsimp only
    rw [hplace]
  exact one_sub_overlap_le_of_consistencyDefect ν
    (fun s => S.placedMeasurement first
      ((lines.T first.side s.1.1 s.2.1).postprocess fun fs =>
        (evalOpt s.1.1 s.1.2 fs.1, evalOpt s.2.1 s.2.2 fs.2)))
    (fun s => S.placedMeasurement second
      ((points.Q second.side s.1.2 s.2.2).postprocess fun ab => (some ab.1, some ab.2)))
    (fun s o => S.place second ((S.pointMeasExpOption second.side .X s.1.2).effect o.1))
    (fun s o => S.place second
      ((S.pointMeasExpOption second.side .Z s.2.2).effect o.2 *
        (S.pointMeasExpOption second.side .X s.1.2).effect o.1))
    S.psiHat hν S.psiHat_norm hQproj hRproj
    (fun s o => S.place_comm first second hopposite _ _)
    (fun s o => S.place_comm first second hopposite _ _)
    (fun s o => S.place_comm first second hopposite _ _)
    hWR hnonneg η ζ hcons hdist

/-- The `X`-point deficit over a product of two restricted line-point laws,
with the inflation `4 m ^ 2` of the line consistency error and the inflation
`4` of the point consistency error. -/
theorem CombinedLinesWitness.one_sub_X_overlap_restricted_le_at
    (lines : CombinedLinesWitness S points δP)
    (first second : Placement) (hopposite : first.IsOpposite second) (kindX kindZ : LineKind)
    (i j : Fin P.m) :
    1 - avgOver
      (Distribution.prod (restrictedLinePointDist P kindX i)
        (restrictedLinePointDist P kindZ j))
      (fun s => ∑ o : Option (PauliScalar P) × Option (PauliScalar P),
        stateQForm S.psiHat
          (S.place first
            (((lines.T first.side s.1.1 s.2.1).postprocess fun fs =>
              (evalOpt s.1.1 s.1.2 fs.1, evalOpt s.2.1 s.2.2 fs.2)).effect o) *
            S.place second ((S.pointMeasExpOption second.side .X s.1.2).effect o.1))) ≤
      2 * Real.sqrt (4 * (P.m : ℝ) ^ 2 * δP) + 2 * Real.sqrt (4 * δQ) := by
  refine lines.one_sub_X_overlap_le_at first second hopposite _
    (Distribution.prod_isProbability _ _
      (restrictedLinePointDist_isProbability P kindX i)
      (restrictedLinePointDist_isProbability P kindZ j)) _ _ ?_ ?_
  · unfold consistencyDefect at ⊢
    refine le_trans
      (avgOver_prod_restrictedLinePointDist_le _ ?_ kindX kindZ i j) ?_
    · intro sample
      exact consistencyDefect_integrand_nonneg S first second hopposite
        ((lines.T first.side sample.1.1 sample.2.1).postprocess fun fs =>
          (evalOpt sample.1.1 sample.1.2 fs.1, evalOpt sample.2.1 sample.2.2 fs.2))
        ((points.Q second.side sample.1.2 sample.2.2).postprocess fun ab =>
          (some ab.1, some ab.2))
    · exact mul_le_mul_of_nonneg_left (lines.consistent first second hopposite) (by positivity)
  · calc
      _ = opFamilyDistSq
            (uniformDistribution
              ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
            (fun xz o => S.place second
              (((points.Q second.side xz.1 xz.2).postprocess fun ab =>
                (some ab.1, some ab.2)).effect o))
            (fun xz o => S.place second
              ((S.pointMeasExpOption second.side .X xz.1).effect o.1 *
                (S.pointMeasExpOption second.side .Z xz.2).effect o.2))
            S.psiHat :=
        opFamilyDistSq_prod_restricted_points P kindX kindZ i j _ _ _
      _ = opFamilyDistSq
            (uniformDistribution
              ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
            (fun xz ab => S.place second ((points.Q second.side xz.1 xz.2).effect ab))
            (fun xz ab => S.place second
              ((S.pointMeasExp second.side .X xz.1).effect ab.1 *
                (S.pointMeasExp second.side .Z xz.2).effect ab.2))
            S.psiHat := by
        unfold opFamilyDistSq
        exact avgOver_congr _ _ _ fun xz =>
          S.completedPair_norm_sq_sum_XZ points second xz.1 xz.2
      _ ≤ 4 * δQ := points.orderedXZ_dist_le second


end

end MIPStarRE.QPBT
