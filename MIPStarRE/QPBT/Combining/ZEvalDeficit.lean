import MIPStarRE.QPBT.Combining.Lines
import MIPStarRE.QPBT.Combining.OrderedPoints
import MIPStarRE.QPBT.Combining.OverlapGap
import MIPStarRE.QPBT.Combining.Points.Placement

/-!
# One-point deficits of the evaluated pair-line measurement

The proofs of `lem:claim-17-2` and `lem:claim-17-3` bound, after their
Cauchy--Schwarz step, the deficit of the overlap between the evaluated
pair-line measurement and one of the two expanded point measurements: the
`X`-point measurement at the `X`-point of the sample, or the `Z`-point
measurement at its `Z`-point.  This module derives those two deficits from the
consistency of the evaluated pair-line measurement with the completed joint
point measurement and from the closeness of the joint point measurement to the
two ordered point products.  The derivation inserts the joint point measurement
on the point side, replaces it by the ordered product whose trailing factor is
the retained point effect, and sums the other factor, at the cost of three
square roots.  The deficits are first bounded over an arbitrary probability
law on pairs of line-point pairs and then over a product of two restricted
line-point laws, whose point marginal is the uniform pair.
The `_at` variants retain arbitrary opposite placements, including Bob at
`BBprime` and Alice at `ABdoubleprime`. The original statements are unchanged
specializations; register commutation does not assume symmetry of the state.

## References

The two deficits are the quantities bounded in the proofs of `lem:claim-17-2`
and `lem:claim-17-3` in `blueprint/src/chapter/ch15_qpbt_combining.tex`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1168-1239`; the
consistency input is `lem:qld-xz-lines` and the ordered products are those of
`lem:qld-4-10`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

noncomputable section

/-! ## Completed point pairs -/

/-- A sum over completed outcome pairs of a function vanishing on both `none`
classes is the sum over the uncompleted pairs. -/
theorem sum_option_prod_eq_of_none {β γ : Type*} [Fintype β] [Fintype γ]
    (F : Option β × Option γ → ℝ) (h1 : ∀ o2, F (none, o2) = 0)
    (h2 : ∀ o1, F (o1, none) = 0) :
    (∑ o, F o) = ∑ bc : β × γ, F (some bc.1, some bc.2) := by
  calc (∑ o : Option β × Option γ, F o)
      = ∑ o1 : Option β, ∑ o2 : Option γ, F (o1, o2) := Fintype.sum_prod_type (f := F)
    _ = (∑ o2 : Option γ, F (none, o2)) +
          ∑ b : β, ∑ o2 : Option γ, F (some b, o2) := Fintype.sum_option _
    _ = ∑ b : β, ∑ o2 : Option γ, F (some b, o2) := by
        rw [Finset.sum_eq_zero fun o2 _ => h1 o2, zero_add]
    _ = ∑ b : β, (F (some b, none) + ∑ c : γ, F (some b, some c)) :=
        Finset.sum_congr rfl fun b _ => Fintype.sum_option _
    _ = ∑ b : β, ∑ c : γ, F (some b, some c) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [h2 (some b), zero_add]
    _ = ∑ bc : β × γ, F (some bc.1, some bc.2) :=
        (Fintype.sum_prod_type (f := fun bc : β × γ => F (some bc.1, some bc.2))).symm

/-- The completed joint measurement has the joint effect on a pair of
evaluations. -/
theorem completedPair_effect_some {β γ d : Type*} [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] [Fintype d] [DecidableEq d]
    (Q : Measurement (β × γ) d) (bc : β × γ) :
    (Q.postprocess fun ab => (some ab.1, some ab.2)).effect (some bc.1, some bc.2) =
      Q.effect bc := by
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect,
    show (Finset.univ.filter fun cd : β × γ =>
        (some cd.1, some cd.2) = (some bc.1, some bc.2)) = {bc} by
      ext cd; simp [Prod.ext_iff, eq_comm]]
  simp

/-- The completed joint measurement vanishes on outcomes outside the image of
the completion. -/
theorem completedPair_effect_eq_zero {β γ d : Type*} [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] [Fintype d] [DecidableEq d]
    (Q : Measurement (β × γ) d) (o : Option β × Option γ)
    (ho : ∀ bc : β × γ, (some bc.1, some bc.2) ≠ o) :
    (Q.postprocess fun ab => (some ab.1, some ab.2)).effect o = 0 := by
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
  exact Finset.sum_eq_zero fun bc hbc =>
    absurd (Finset.mem_filter.mp hbc).2 (ho bc)

/-- The completion of a projective joint measurement is projective. -/
theorem completedPair_isProjective {β γ d : Type*} [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] [Fintype d] [DecidableEq d]
    (Q : Measurement (β × γ) d) (hQ : Measurement.IsProjective Q) :
    Measurement.IsProjective (Q.postprocess fun ab => (some ab.1, some ab.2)) := by
  intro o
  by_cases h : ∃ bc : β × γ, (some bc.1, some bc.2) = o
  · obtain ⟨bc, rfl⟩ := h
    rw [completedPair_effect_some]
    exact hQ bc
  · push Not at h
    rw [completedPair_effect_eq_zero Q o h]
    exact IsStarProjection.zero _

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

/-- A placed projection is a projection. -/
theorem place_isProj (S : ProjectiveSetting P ε) (p : Placement)
    {E : Op (S.ExpandedLocalSpace p.side)} (hE : IsProj E) :
    IsProj (S.place p E) := by
  refine isStarProjection_iff'.2 ⟨?_, ?_⟩
  · change S.place p E * S.place p E = S.place p E
    rw [← place_mul, hE.isIdempotentElem.eq]
  · rw [Matrix.star_eq_conjTranspose, ← place_conjTranspose,
      hE.isSelfAdjoint.isHermitian.eq]

/-- Every effect of the completed expanded point measurement is a projection,
the `none` effect being zero. -/
theorem pointMeasExpOption_isProj (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (u : Fin P.m → PauliScalar P)
    (o : Option (PauliScalar P)) :
    IsProj ((S.pointMeasExpOption side W u).effect o) := by
  cases o with
  | none =>
    rw [S.pointMeasExpOption_effect_none]
    exact IsStarProjection.zero _
  | some a =>
    rw [S.pointMeasExpOption_effect_some]
    exact S.pointMeasExp_isProjective side W u a

/-- The completed joint point measurement and a completed point product differ
only on outcome pairs with two evaluations, so their placed state-dependent
squared distance is the one of the joint point measurement and the point
product.  Blueprint `ch15_qpbt_combining.tex:2651-2698`. -/
theorem sum_norm_place_completedPair_sub_sq (S : ProjectiveSetting P ε)
    (p : Placement)
    (Q : Measurement (PauliScalar P × PauliScalar P) (S.ExpandedLocalSpace p.side))
    (Gc : Option (PauliScalar P) × Option (PauliScalar P) →
      Op (S.ExpandedLocalSpace p.side))
    (G : PauliScalar P × PauliScalar P → Op (S.ExpandedLocalSpace p.side))
    (hsome : ∀ ab : PauliScalar P × PauliScalar P, Gc (some ab.1, some ab.2) = G ab)
    (hnone1 : ∀ o2, Gc (none, o2) = 0) (hnone2 : ∀ o1, Gc (o1, none) = 0) :
    (∑ o : Option (PauliScalar P) × Option (PauliScalar P),
        ‖applyOperatorToState
          (S.place p ((Q.postprocess fun ab => (some ab.1, some ab.2)).effect o) -
            S.place p (Gc o)) S.psiHat‖ ^ 2) =
      ∑ ab : PauliScalar P × PauliScalar P,
        ‖applyOperatorToState (S.place p (Q.effect ab) - S.place p (G ab))
          S.psiHat‖ ^ 2 := by
  refine Eq.trans (sum_option_prod_eq_of_none _ ?_ ?_) ?_
  · intro o2
    rw [completedPair_effect_eq_zero Q (none, o2) (fun ab => by simp), hnone1,
      place_zero, sub_self]
    simp [applyOperatorToState]
  · intro o1
    rw [completedPair_effect_eq_zero Q (o1, none) (fun ab => by simp), hnone2,
      place_zero, sub_self]
    simp [applyOperatorToState]
  · refine Finset.sum_congr rfl fun ab _ => ?_
    rw [completedPair_effect_some, hsome]

/-- The completed `Z`-then-`X` point product vanishes on both `none` classes
and restricts to the ordered product on evaluated pairs. -/
theorem completedPair_norm_sq_sum_ZX (S : ProjectiveSetting P ε) {δ : ℝ}
    (points : CombinedPointsWitness S δ) (p : Placement)
    (x z : Fin P.m → PauliScalar P) :
    (∑ o : Option (PauliScalar P) × Option (PauliScalar P),
        ‖applyOperatorToState
          (S.place p (((points.Q p.side x z).postprocess (fun ab =>
              (some ab.1, some ab.2))).effect o) -
            S.place p
              ((S.pointMeasExpOption p.side .Z z).effect o.2 *
                (S.pointMeasExpOption p.side .X x).effect o.1))
          S.psiHat‖ ^ 2) =
      ∑ ab : PauliScalar P × PauliScalar P,
        ‖applyOperatorToState
          (S.place p ((points.Q p.side x z).effect ab) -
            S.place p
              ((S.pointMeasExp p.side .Z z).effect ab.2 *
                (S.pointMeasExp p.side .X x).effect ab.1))
          S.psiHat‖ ^ 2 := by
  refine S.sum_norm_place_completedPair_sub_sq p (points.Q p.side x z) _ _ ?_ ?_ ?_
  · intro ab
    rw [S.pointMeasExpOption_effect_some, S.pointMeasExpOption_effect_some]
  · intro o2
    rw [S.pointMeasExpOption_effect_none, mul_zero]
  · intro o1
    rw [S.pointMeasExpOption_effect_none, zero_mul]


end ProjectiveSetting

/-! ## The abstract one-point deficit -/

/-- Let `A` be a complete measurement, `Q` a projective measurement, `R` a
family of projections and `W` a family of operators, all indexed by the same
outcomes, with `Q`, `R` and `W` commuting with the effects of `A` and with
`W R = W`.  If `A` and `Q` are consistent with defect at most `η` and `Q` is
within squared distance `ζ` of `Wᴴ`, then the deficit of the overlap of `A`
with `R` is at most `2 √η + 2 √ζ`.  The proof inserts `Q` before `R`, replaces
`Q R` by `W R = W`, and compares `W` with `Q`; each of the three steps is a
Cauchy--Schwarz estimate weighted by `A`.  This is the common estimate behind
the deficits in the proofs of `lem:claim-17-2` and `lem:claim-17-3`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1168-1239`. -/
theorem one_sub_overlap_le_of_consistencyDefect {X α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A Q : X → Measurement α ι) (R W : X → α → Op ι)
    (ψ : EuclideanSpace ℂ ι) (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1)
    (hQ : ∀ x, Measurement.IsProjective (Q x)) (hR : ∀ x a, IsProj (R x a))
    (hAQ : ∀ x a, Commute ((A x).effect a) ((Q x).effect a))
    (hAR : ∀ x a, Commute ((A x).effect a) (R x a))
    (hAW : ∀ x a, Commute ((A x).effect a) (W x a))
    (hWR : ∀ x a, W x a * R x a = W x a)
    (hnonneg : ∀ x a, 0 ≤ stateQForm ψ ((A x).effect a * (Q x).effect a))
    (η ζ : ℝ)
    (hcons : consistencyDefect μ (fun x a => (A x).effect a)
      (fun x a => (Q x).effect a) ψ ≤ η)
    (hdist : opFamilyDistSq μ (fun x a => (Q x).effect a)
      (fun x a => (W x a)ᴴ) ψ ≤ ζ) :
    1 - avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * R x a)) ≤
      2 * Real.sqrt η + 2 * Real.sqrt ζ := by
  set ovQ := avgOver μ (fun x =>
    ∑ a, stateQForm ψ ((A x).effect a * (Q x).effect a)) with hovQ
  have h1 : 1 - ovQ ≤ η := by
    rw [← consistencyDefect_eq_one_sub_overlap μ A Q ψ hμ hψ]
    exact hcons
  have hovQ_nonneg : 0 ≤ ovQ :=
    avgOver_nonneg μ _ fun x => Finset.sum_nonneg fun a _ => hnonneg x a
  have hovQ_le : ovQ ≤ 1 :=
    avgOver_sum_stateQForm_mul_le_one μ A (fun x a => (Q x).effect a) ψ hμ hψ
      (fun x a => hQ x a) hAQ
  have h1' : 1 - ovQ ≤ Real.sqrt η := by
    have h0 : 0 ≤ 1 - ovQ := by linarith
    calc 1 - ovQ = Real.sqrt ((1 - ovQ) ^ 2) := (Real.sqrt_sq h0).symm
      _ ≤ Real.sqrt η := Real.sqrt_le_sqrt (by nlinarith)
  -- comparing `Q` with `W` under the weight `A`
  have hWconj : ∀ x a, stateQForm ψ ((A x).effect a * W x a) =
      stateQForm ψ ((A x).effect a * (W x a)ᴴ) := by
    intro x a
    rw [← stateQForm_conjTranspose ψ ((A x).effect a * W x a),
      Matrix.conjTranspose_mul, measurement_effect_hermitian]
    congr 1
    have h := congrArg Matrix.conjTranspose (hAW x a).eq
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      measurement_effect_hermitian] at h
    exact h
  have h2 : |ovQ - avgOver μ (fun x =>
      ∑ a, stateQForm ψ ((A x).effect a * W x a))| ≤ Real.sqrt ζ := by
    rw [avgOver_congr μ _ _ fun x => Finset.sum_congr rfl fun a _ => hWconj x a]
    exact abs_overlap_gap_le_sqrt_of_opFamilyDistSq μ A
      (fun x a => (Q x).effect a) (fun x a => (W x a)ᴴ) ψ hμ hψ ζ hdist
  -- replacing `Q R` by `W R = W`
  have h4 : |avgOver μ (fun x =>
      ∑ a, stateQForm ψ ((A x).effect a * ((Q x).effect a * R x a))) -
        avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * W x a))| ≤
      Real.sqrt ζ := by
    have hpt : ∀ x,
        (∑ a, stateQForm ψ ((A x).effect a * ((Q x).effect a * R x a))) -
          (∑ a, stateQForm ψ ((A x).effect a * W x a)) =
        ∑ a, stateQForm ψ ((A x).effect a * (((Q x).effect a - W x a) * R x a)) := by
      intro x
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [sub_mul, hWR]
      simp [stateQForm, applyOperatorToState, mul_sub]
    rw [← avgOver_sub, avgOver_congr μ _ _ hpt]
    have hcs := abs_avgOver_sum_stateQForm_mul_le_sqrt_of_isProj' μ A
      (fun x a => (Q x).effect a - W x a) R ψ hμ hψ hR hAR
      (fun x a => (hAQ x a).sub_right (hAW x a))
    refine hcs.trans (Real.sqrt_le_sqrt ?_)
    have hdist' : avgOver μ (fun x =>
        ∑ a, ‖applyOperatorToState ((Q x).effect a - (W x a)ᴴ) ψ‖ ^ 2) ≤ ζ :=
      hdist
    refine le_of_eq_of_le ?_ hdist'
    refine avgOver_congr μ _ _ fun x => Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.conjTranspose_sub, measurement_effect_hermitian]
  -- inserting `Q` before `R`
  have h5 : |avgOver μ (fun x =>
      ∑ a, stateQForm ψ ((A x).effect a * ((Q x).effect a * R x a))) -
        avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * R x a))| ≤
      Real.sqrt η := by
    have hpt : ∀ x,
        (∑ a, stateQForm ψ ((A x).effect a * R x a)) -
          (∑ a, stateQForm ψ ((A x).effect a * ((Q x).effect a * R x a))) =
        ∑ a, stateQForm ψ ((A x).effect a * ((1 - (Q x).effect a) * R x a)) := by
      intro x
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp [stateQForm, applyOperatorToState, sub_mul, mul_sub]
    rw [abs_sub_comm, ← avgOver_sub, avgOver_congr μ _ _ hpt]
    have hcs := abs_avgOver_sum_stateQForm_mul_mul_le_sqrt_mul_sqrt μ A
      (fun x a => 1 - (Q x).effect a) R ψ (fun x a => (hQ x a).one_sub)
      (fun x a => (Commute.one_right _).sub_right (hAQ x a))
    have hfirst : avgOver μ (fun x =>
        ∑ a, stateQForm ψ ((A x).effect a * (1 - (Q x).effect a))) = 1 - ovQ := by
      have hx : ∀ x,
          (∑ a, stateQForm ψ ((A x).effect a * (1 - (Q x).effect a))) =
            1 - ∑ a, stateQForm ψ ((A x).effect a * (Q x).effect a) := by
        intro x
        rw [← sum_stateQForm_effect_eq_one (A x) ψ hψ, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        simp [stateQForm, applyOperatorToState, mul_sub]
      rw [avgOver_congr μ _ _ hx, avgOver_sub, avgOver_const_of_isProbability μ hμ]
    have hsecond : avgOver μ (fun x =>
        ∑ a, stateQForm (applyOperatorToState (R x a) ψ) ((A x).effect a)) ≤ 1 := by
      rw [avgOver_congr μ _ _ fun x => Finset.sum_congr rfl fun a _ =>
        stateQForm_applyOperatorToState_eq_of_isProj ψ (hR x a) (hAR x a)]
      exact avgOver_sum_stateQForm_mul_le_one μ A R ψ hμ hψ hR hAR
    rw [hfirst] at hcs
    calc
      _ ≤ _ := hcs
      _ ≤ Real.sqrt (1 - ovQ) * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt hsecond
      _ = Real.sqrt (1 - ovQ) := mul_one _
      _ ≤ Real.sqrt η := Real.sqrt_le_sqrt h1
  have h2' := abs_le.mp h2
  have h4' := abs_le.mp h4
  have h5' := abs_le.mp h5
  linarith [h2'.1, h4'.1, h5'.1, h2'.2, h4'.2, h5'.2]

/-! ## The two placed deficits -/

/-- A pair of line-point pairs of the source space: the sample type of the
consistency display of `lem:qld-xz-lines`. -/
abbrev LinePointPairSample (P : AdmissibleParams) :=
  (LineDesc P.toLdParams × (Fin P.m → PauliScalar P)) ×
    (LineDesc P.toLdParams × (Fin P.m → PauliScalar P))

section Placed

variable {P : AdmissibleParams} {ε δQ δP : ℝ} {S : ProjectiveSetting P ε}
  {points : CombinedPointsWitness S δQ}

/-- The `Z`-point deficit of the evaluated pair-line measurement over a
probability law on pairs of line-point pairs, from the consistency of the
evaluated pair-line measurement with the completed joint point measurement
and the closeness of the latter to the `Z`-then-`X` product.  This is the
deficit bounded in the proof of `lem:claim-17-3`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1204-1239`. -/
theorem CombinedLinesWitness.one_sub_Z_overlap_le_at
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
    (hZX : opFamilyDistSq ν
      (fun s o => S.place second
        (((points.Q second.side s.1.2 s.2.2).postprocess fun ab =>
          (some ab.1, some ab.2)).effect o))
      (fun s o => S.place second
        ((S.pointMeasExpOption second.side .Z s.2.2).effect o.2 *
          (S.pointMeasExpOption second.side .X s.1.2).effect o.1))
      S.psiHat ≤ ζ) :
    1 - avgOver ν (fun s =>
      ∑ o : Option (PauliScalar P) × Option (PauliScalar P),
        stateQForm S.psiHat
          (S.place first
            (((lines.T first.side s.1.1 s.2.1).postprocess fun fs =>
              (evalOpt s.1.1 s.1.2 fs.1, evalOpt s.2.1 s.2.2 fs.2)).effect o) *
            S.place second ((S.pointMeasExpOption second.side .Z s.2.2).effect o.2))) ≤
      2 * Real.sqrt η + 2 * Real.sqrt ζ := by
  have hQproj : ∀ s : LinePointPairSample P,
      Measurement.IsProjective (S.placedMeasurement second
        ((points.Q second.side s.1.2 s.2.2).postprocess fun ab => (some ab.1, some ab.2))) :=
    fun s => S.placedMeasurement_isProjective _ _
      (completedPair_isProjective _ (points.projective _ _ _))
  have hRproj : ∀ (s : LinePointPairSample P)
      (o : Option (PauliScalar P) × Option (PauliScalar P)),
      IsProj (S.place second ((S.pointMeasExpOption second.side .Z s.2.2).effect o.2)) :=
    fun s o => S.place_isProj _ (S.pointMeasExpOption_isProj _ _ _ _)
  have hWR : ∀ (s : LinePointPairSample P)
      (o : Option (PauliScalar P) × Option (PauliScalar P)),
      S.place second ((S.pointMeasExpOption second.side .X s.1.2).effect o.1 *
          (S.pointMeasExpOption second.side .Z s.2.2).effect o.2) *
        S.place second ((S.pointMeasExpOption second.side .Z s.2.2).effect o.2) =
      S.place second ((S.pointMeasExpOption second.side .X s.1.2).effect o.1 *
        (S.pointMeasExpOption second.side .Z s.2.2).effect o.2) := by
    intro s o
    have hlocal : (S.pointMeasExpOption second.side .X s.1.2).effect o.1 *
          (S.pointMeasExpOption second.side .Z s.2.2).effect o.2 *
        (S.pointMeasExpOption second.side .Z s.2.2).effect o.2 =
        (S.pointMeasExpOption second.side .X s.1.2).effect o.1 *
          (S.pointMeasExpOption second.side .Z s.2.2).effect o.2 := by
      rw [mul_assoc, (S.pointMeasExpOption_isProj second.side .Z s.2.2 o.2).isIdempotentElem.eq]
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
        ((S.pointMeasExpOption second.side .X s.1.2).effect o.1 *
          (S.pointMeasExpOption second.side .Z s.2.2).effect o.2))ᴴ)
      S.psiHat ≤ ζ := by
    refine le_of_eq_of_le ?_ hZX
    unfold opFamilyDistSq
    refine avgOver_congr _ _ _ fun s => Finset.sum_congr rfl fun o _ => ?_
    have hlocal : ((S.pointMeasExpOption second.side .X s.1.2).effect o.1 *
          (S.pointMeasExpOption second.side .Z s.2.2).effect o.2)ᴴ =
        (S.pointMeasExpOption second.side .Z s.2.2).effect o.2 *
          (S.pointMeasExpOption second.side .X s.1.2).effect o.1 := by
      rw [Matrix.conjTranspose_mul,
        (S.pointMeasExpOption_isProj second.side .Z s.2.2 o.2).isSelfAdjoint.isHermitian.eq,
        (S.pointMeasExpOption_isProj second.side .X s.1.2 o.1).isSelfAdjoint.isHermitian.eq]
    have hplace : (S.place second
        ((S.pointMeasExpOption second.side .X s.1.2).effect o.1 *
          (S.pointMeasExpOption second.side .Z s.2.2).effect o.2))ᴴ =
        S.place second ((S.pointMeasExpOption second.side .Z s.2.2).effect o.2 *
          (S.pointMeasExpOption second.side .X s.1.2).effect o.1) :=
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
    (fun s o => S.place second ((S.pointMeasExpOption second.side .Z s.2.2).effect o.2))
    (fun s o => S.place second
      ((S.pointMeasExpOption second.side .X s.1.2).effect o.1 *
        (S.pointMeasExpOption second.side .Z s.2.2).effect o.2))
    S.psiHat hν S.psiHat_norm hQproj hRproj
    (fun s o => S.place_comm first second hopposite _ _)
    (fun s o => S.place_comm first second hopposite _ _)
    (fun s o => S.place_comm first second hopposite _ _)
    hWR hnonneg η ζ hcons hdist

/-- The original first-player specialization of the opposite-placement estimate. -/
theorem CombinedLinesWitness.one_sub_Z_overlap_le
    (lines : CombinedLinesWitness S points δP)
    (ν : Distribution (LinePointPairSample P)) (hν : ν.IsProbability) (η ζ : ℝ)
    (hcons : consistencyDefect ν
      (fun s o => S.place .AA'
        (((lines.T .alice s.1.1 s.2.1).postprocess fun fs =>
          (evalOpt s.1.1 s.1.2 fs.1, evalOpt s.2.1 s.2.2 fs.2)).effect o))
      (fun s o => S.place .BA''
        (((points.Q .bob s.1.2 s.2.2).postprocess fun ab =>
          (some ab.1, some ab.2)).effect o))
      S.psiHat ≤ η)
    (hZX : opFamilyDistSq ν
      (fun s o => S.place .BA''
        (((points.Q .bob s.1.2 s.2.2).postprocess fun ab =>
          (some ab.1, some ab.2)).effect o))
      (fun s o => S.place .BA''
        ((S.pointMeasExpOption .bob .Z s.2.2).effect o.2 *
          (S.pointMeasExpOption .bob .X s.1.2).effect o.1))
      S.psiHat ≤ ζ) :
    1 - avgOver ν (fun s =>
      ∑ o : Option (PauliScalar P) × Option (PauliScalar P),
        stateQForm S.psiHat
          (S.place .AA'
            (((lines.T .alice s.1.1 s.2.1).postprocess fun fs =>
              (evalOpt s.1.1 s.1.2 fs.1, evalOpt s.2.1 s.2.2 fs.2)).effect o) *
            S.place .BA'' ((S.pointMeasExpOption .bob .Z s.2.2).effect o.2))) ≤
      2 * Real.sqrt η + 2 * Real.sqrt ζ := by
  exact lines.one_sub_Z_overlap_le_at .AA' .BA'' trivial ν hν η ζ hcons hZX


end Placed

/-! ## The two deficits over a product of restricted line-point laws -/

/-- Every restricted line-point law has total mass one. -/
theorem restrictedLinePointDist_isProbability (P : AdmissibleParams)
    (kind : LineKind) (i : Fin P.m) :
    (restrictedLinePointDist P kind i).IsProbability := by
  cases kind
  · change (restrictedALineDist P.toLdParams i).IsProbability
    exact restrictedALineDist_isProbability P.toLdParams i
  · change (restrictedDLineDist P.toLdParams i).IsProbability
    exact restrictedDLineDist_isProbability P.toLdParams i

/-- The point marginal of a restricted line-point law is uniform. -/
theorem restrictedLinePointDist_map_snd (P : AdmissibleParams) (kind : LineKind)
    (i : Fin P.m) :
    (restrictedLinePointDist P kind i).map Prod.snd =
      uniformDistribution (Fin P.m → PauliScalar P) := by
  rw [restrictedLinePointDist_eq_map_prod, Distribution.map_map]
  exact Distribution.prod_map_fst _ _ (Distribution.prod_isProbability _ _
    (subLineSeedDist_isProbability P i) (uniformDistribution_isProbability _))

/-- The pair of points of a product of two restricted line-point laws is a
uniform pair. -/
theorem prod_restrictedLinePointDist_map_points (P : AdmissibleParams)
    (kindX kindZ : LineKind) (i j : Fin P.m) :
    (Distribution.prod (restrictedLinePointDist P kindX i)
        (restrictedLinePointDist P kindZ j)).map (fun s => (s.1.2, s.2.2)) =
      uniformDistribution
        ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)) := by
  have h : Distribution.prod ((restrictedLinePointDist P kindX i).map Prod.snd)
      ((restrictedLinePointDist P kindZ j).map Prod.snd) =
      uniformDistribution
        ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)) := by
    rw [restrictedLinePointDist_map_snd, restrictedLinePointDist_map_snd,
      uniformDistribution_prod]
  rw [← h, Distribution.prod_map_left, Distribution.prod_map_right,
    Distribution.map_map]

/-- A state-dependent distance between two families depending on the pair of
points only, averaged over a product of two restricted line-point laws, is the
distance averaged over a uniform pair of points. -/
theorem opFamilyDistSq_prod_restricted_points {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι] (P : AdmissibleParams) (kindX kindZ : LineKind)
    (i j : Fin P.m)
    (F G : (Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P) → α → Op ι)
    (ψ : EuclideanSpace ℂ ι) :
    opFamilyDistSq
        (Distribution.prod (restrictedLinePointDist P kindX i)
          (restrictedLinePointDist P kindZ j))
        (fun s a => F (s.1.2, s.2.2) a) (fun s a => G (s.1.2, s.2.2) a) ψ =
      opFamilyDistSq
        (uniformDistribution
          ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P))) F G ψ := by
  unfold opFamilyDistSq
  rw [← prod_restrictedLinePointDist_map_points P kindX kindZ i j,
    Distribution.avgOver_map]

section Restricted

variable {P : AdmissibleParams} {ε δQ δP : ℝ} {S : ProjectiveSetting P ε}
  {points : CombinedPointsWitness S δQ}

/-- The `Z`-point deficit over a product of two restricted line-point laws,
with the inflation `4 m ^ 2` of the line consistency error and the inflation
`4` of the point consistency error. -/
theorem CombinedLinesWitness.one_sub_Z_overlap_restricted_le_at
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
            S.place second ((S.pointMeasExpOption second.side .Z s.2.2).effect o.2))) ≤
      2 * Real.sqrt (4 * (P.m : ℝ) ^ 2 * δP) + 2 * Real.sqrt (4 * δQ) := by
  refine lines.one_sub_Z_overlap_le_at first second hopposite _
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
              ((S.pointMeasExpOption second.side .Z xz.2).effect o.2 *
                (S.pointMeasExpOption second.side .X xz.1).effect o.1))
            S.psiHat :=
        opFamilyDistSq_prod_restricted_points P kindX kindZ i j _ _ _
      _ = opFamilyDistSq
            (uniformDistribution
              ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
            (fun xz ab => S.place second ((points.Q second.side xz.1 xz.2).effect ab))
            (fun xz ab => S.place second
              ((S.pointMeasExp second.side .Z xz.2).effect ab.2 *
                (S.pointMeasExp second.side .X xz.1).effect ab.1))
            S.psiHat := by
        unfold opFamilyDistSq
        exact avgOver_congr _ _ _ fun xz =>
          S.completedPair_norm_sq_sum_ZX points second xz.1 xz.2
      _ ≤ 4 * δQ := points.orderedZX_dist_le second

/-- The original first-player specialization of the opposite-placement estimate. -/
theorem CombinedLinesWitness.one_sub_Z_overlap_restricted_le
    (lines : CombinedLinesWitness S points δP) (kindX kindZ : LineKind)
    (i j : Fin P.m) :
    1 - avgOver
      (Distribution.prod (restrictedLinePointDist P kindX i)
        (restrictedLinePointDist P kindZ j))
      (fun s => ∑ o : Option (PauliScalar P) × Option (PauliScalar P),
        stateQForm S.psiHat
          (S.place .AA'
            (((lines.T .alice s.1.1 s.2.1).postprocess fun fs =>
              (evalOpt s.1.1 s.1.2 fs.1, evalOpt s.2.1 s.2.2 fs.2)).effect o) *
            S.place .BA'' ((S.pointMeasExpOption .bob .Z s.2.2).effect o.2))) ≤
      2 * Real.sqrt (4 * (P.m : ℝ) ^ 2 * δP) + 2 * Real.sqrt (4 * δQ) := by
  exact lines.one_sub_Z_overlap_restricted_le_at .AA' .BA'' trivial kindX kindZ i j


end Restricted

end

end MIPStarRE.QPBT
