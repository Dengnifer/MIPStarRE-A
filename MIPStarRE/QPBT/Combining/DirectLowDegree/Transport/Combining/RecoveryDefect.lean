import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Combining.Recovery
import MIPStarRE.QPBT.Games.Sandwich

/-!
# Transporting a consistency relation along the recovery step

The recovery step of `lem:ld-combining-recovery` replaces a relation between a
point measurement of the original strategy read through a combination and a
measurement of the combined game read at a point of the combined space by a
relation between the point measurement itself and the same measurement read
through the recovered polynomial tuple.  This module isolates the consistency
calculus of that replacement, in a form which does not mention the low-degree
game.

Both relations are diagonal overlaps of the same pair of measurements placed on
opposite tensor factors, and the two relabellings differ only on the event that
the recovered outcome disagrees with the outcome of the point measurement while
the two relabellings agree.  The probability of that event, averaged over the
auxiliary sample, is bounded at each question by a quantity depending only on
the outcome of the second measurement; since the first measurement is complete,
the total Born weight of an outcome of the second measurement does not depend on
the question, and the bound may therefore be averaged over the question against
that weight.

The two conclusions of `lem:ld-soundness` transported here place the point
measurement on opposite tensor factors, so the calculus is recorded twice, once
for each placement; the two statements share the averaging estimate, which is
insensitive to the placement.

## Main statements

* `consistencyDefect_le_of_recoveryBound` — the transport of a consistency
  relation along a relabelling which is correct off a rare event, with the
  point measurement on the first tensor factor.
* `consistencyDefect_le_of_recoveryBound_right` — the same transport with the
  point measurement on the second tensor factor.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1440-1503`
* `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:219-288`
* `blueprint/src/chapter/ch13_qpbt_test.tex:617-680`
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum
open DistanceCalculus
open SandwichProduct

noncomputable section

namespace RecoveryInternal

/-! ## The quadratic form of the identity -/

/-- The one-outcome measurement, whose single effect is the identity. -/
private def unitMeasurement (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Measurement (Fin 1) ι :=
  Measurement.ofSumEqOne (fun _ => (1 : Op ι))
    (fun _ => (Matrix.PosSemidef.one.nonneg : (0 : Op ι) ≤ 1)) (by simp)

/-- The quadratic form of the identity in a state vector is its squared norm. -/
private theorem stateQForm_one_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) : stateQForm ψ (1 : Op ι) = ‖ψ‖ ^ 2 := by
  classical
  have h := point_defect_eq (unitMeasurement ι) (unitMeasurement ι) ψ
  have hzero : ∀ a b : Fin 1,
      (if a = b then (0 : ℝ) else stateQForm ψ
        ((unitMeasurement ι).effect a * (unitMeasurement ι).effect b)) = 0 :=
    fun a b => if_pos (Subsingleton.elim a b)
  simp only [hzero, Finset.sum_const_zero] at h
  simp only [Fin.sum_univ_one] at h
  have heff : (unitMeasurement ι).effect 0 = (1 : Op ι) := rfl
  rw [heff, one_mul] at h
  linarith

/-! ## Pair expansions of the diagonal overlap -/

/-- The diagonal overlap of a measurement against a relabelled measurement on the
opposite factor is the sum over pairs of outcomes with matching labels. -/
private theorem diagonalRight_pair_sum {β Γ ιA ιB : Type*}
    [Fintype β] [DecidableEq β] [Fintype Γ] [DecidableEq Γ]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Measurement β ιA) (B : Measurement Γ ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (f : Γ → β) :
    (∑ b : β, stateQForm ψ
      (heteroKron (A.effect b) ((B.postprocess f).effect b))) =
      ∑ b : β, ∑ g : Γ, if f g = b then
        stateQForm ψ (heteroKron (A.effect b) (B.effect g)) else 0 := by
  classical
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect,
    heteroKron_finset_sum_right, stateQForm_finset_sum, Finset.sum_filter]

/-- The diagonal overlap of a relabelled measurement against a measurement on
the opposite factor, with the relabelled measurement on the first factor. -/
private theorem diagonalLeft_pair_sum {β Γ ιA ιB : Type*}
    [Fintype β] [DecidableEq β] [Fintype Γ] [DecidableEq Γ]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Measurement β ιB) (B : Measurement Γ ιA)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (f : Γ → β) :
    (∑ b : β, stateQForm ψ
      (heteroKron ((B.postprocess f).effect b) (A.effect b))) =
      ∑ b : β, ∑ g : Γ, if f g = b then
        stateQForm ψ (heteroKron (B.effect g) (A.effect b)) else 0 := by
  classical
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect,
    heteroKron_finset_sum_left, stateQForm_finset_sum, Finset.sum_filter]

/-- The diagonal overlap of two relabelled measurements on opposite factors is
the sum over pairs of outcomes with matching labels. -/
private theorem diagonalPair_pair_sum {β Γ R ιA ιB : Type*}
    [Fintype β] [DecidableEq β] [Fintype Γ] [DecidableEq Γ]
    [Fintype R] [DecidableEq R]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Measurement β ιA) (B : Measurement Γ ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (e : β → R) (f : Γ → R) :
    (∑ r : R, stateQForm ψ
      (heteroKron ((A.postprocess e).effect r) ((B.postprocess f).effect r))) =
      ∑ b : β, ∑ g : Γ, if e b = f g then
        stateQForm ψ (heteroKron (A.effect b) (B.effect g)) else 0 := by
  classical
  have hterm (r : R) : stateQForm ψ
      (heteroKron ((A.postprocess e).effect r) ((B.postprocess f).effect r)) =
      ∑ b : β, ∑ g : Γ, if e b = r ∧ f g = r then
        stateQForm ψ (heteroKron (A.effect b) (B.effect g)) else 0 := by
    rw [MIPStarRE.Quantum.Measurement.postprocess_effect,
      MIPStarRE.Quantum.Measurement.postprocess_effect,
      heteroKron_finset_sum_left, stateQForm_finset_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : e b = r
    · rw [if_pos hb, heteroKron_finset_sum_right, stateQForm_finset_sum,
        Finset.sum_filter]
      refine Finset.sum_congr rfl fun g _ => ?_
      by_cases hg : f g = r <;> simp [hb, hg]
    · simp [hb]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  by_cases hbg : e b = f g
  · rw [hbg]
    simp
  · refine Eq.trans (Finset.sum_eq_zero fun r _ => ?_) (by simp [hbg])
    simp only [ite_eq_right_iff]
    intro hpair
    exact (hbg (hpair.1.trans hpair.2.symm)).elim

/-- The diagonal overlap of two relabelled measurements on opposite factors,
with the second measurement on the first tensor factor. -/
private theorem diagonalPairLeft_pair_sum {β Γ R ιA ιB : Type*}
    [Fintype β] [DecidableEq β] [Fintype Γ] [DecidableEq Γ]
    [Fintype R] [DecidableEq R]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Measurement β ιB) (B : Measurement Γ ιA)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (e : β → R) (f : Γ → R) :
    (∑ r : R, stateQForm ψ
      (heteroKron ((B.postprocess f).effect r) ((A.postprocess e).effect r))) =
      ∑ b : β, ∑ g : Γ, if e b = f g then
        stateQForm ψ (heteroKron (B.effect g) (A.effect b)) else 0 := by
  classical
  have hterm (r : R) : stateQForm ψ
      (heteroKron ((B.postprocess f).effect r) ((A.postprocess e).effect r)) =
      ∑ b : β, ∑ g : Γ, if e b = r ∧ f g = r then
        stateQForm ψ (heteroKron (B.effect g) (A.effect b)) else 0 := by
    rw [MIPStarRE.Quantum.Measurement.postprocess_effect,
      MIPStarRE.Quantum.Measurement.postprocess_effect,
      heteroKron_finset_sum_right, stateQForm_finset_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : e b = r
    · rw [if_pos hb, heteroKron_finset_sum_left, stateQForm_finset_sum,
        Finset.sum_filter]
      refine Finset.sum_congr rfl fun g _ => ?_
      by_cases hg : f g = r <;> simp [hb, hg]
    · simp [hb]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  by_cases hbg : e b = f g
  · rw [hbg]
    simp
  · refine Eq.trans (Finset.sum_eq_zero fun r _ => ?_) (by simp [hbg])
    simp only [ite_eq_right_iff]
    intro hpair
    exact (hbg (hpair.1.trans hpair.2.symm)).elim

/-! ## The averaging estimate -/

set_option maxHeartbeats 1600000 in
/-- The averaging estimate underlying the recovery transport, stated for the
Born weights alone.  The weights `w x b g` of a pair of outcomes have fiber
sums `W g` independent of the question `x`, and the two diagonal overlaps
differ only on the discrepancy event, whose conditional probability is bounded
by `F x g`; averaging that bound against the fiber weights gives `η`. -/
private theorem recovery_avg_le {X Y β Γ R : Type*}
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype β] [DecidableEq β] [Fintype Γ] [DecidableEq Γ]
    [Fintype R] [DecidableEq R]
    (w : X → β → Γ → ℝ) (W : Γ → ℝ)
    (f : X → Γ → β) (e₁ : X → Y → β → R) (f₁ : X → Y → Γ → R)
    (F : X → Γ → ℝ) (η : ℝ)
    (hwnonneg : ∀ x b g, 0 ≤ w x b g) (hWnonneg : ∀ g, 0 ≤ W g)
    (hfiber : ∀ x g, (∑ b : β, w x b g) = W g) (hWsum : (∑ g : Γ, W g) = 1)
    (hFbound : ∀ x b g, avgOver (uniformDistribution Y)
      (fun y => if f x g ≠ b ∧ e₁ x y b = f₁ x y g then (1 : ℝ) else 0) ≤ F x g)
    (hFavg : ∀ g, avgOver (uniformDistribution X) (fun x => F x g) ≤ η) :
    avgOver (uniformDistribution X) (fun x =>
        avgOver (uniformDistribution Y) (fun y =>
          ∑ b : β, ∑ g : Γ, if e₁ x y b = f₁ x y g then w x b g else 0)) ≤
      avgOver (uniformDistribution X)
        (fun x => ∑ b : β, ∑ g : Γ, if f x g = b then w x b g else 0) + η := by
  classical
  have hstep : ∀ x : X,
      avgOver (uniformDistribution Y) (fun y =>
          ∑ b : β, ∑ g : Γ, if e₁ x y b = f₁ x y g then w x b g else 0) ≤
        (∑ b : β, ∑ g : Γ, if f x g = b then w x b g else 0) +
          ∑ g : Γ, W g * F x g := by
    intro x
    have hexp : avgOver (uniformDistribution Y) (fun y =>
        ∑ b : β, ∑ g : Γ, if e₁ x y b = f₁ x y g then w x b g else 0) =
        ∑ b : β, ∑ g : Γ, avgOver (uniformDistribution Y)
          (fun y => if e₁ x y b = f₁ x y g then w x b g else 0) := by
      rw [avgOver_sum]
      exact Finset.sum_congr rfl fun b _ => avgOver_sum _ _
    rw [hexp]
    have hterm : ∀ b : β, ∀ g : Γ,
        avgOver (uniformDistribution Y)
          (fun y => if e₁ x y b = f₁ x y g then w x b g else 0) ≤
          (if f x g = b then w x b g else 0) + w x b g * F x g := by
      intro b g
      have hsplit : ∀ y : Y,
          (if e₁ x y b = f₁ x y g then w x b g else 0) ≤
            (if f x g = b then w x b g else 0) +
              (if f x g ≠ b ∧ e₁ x y b = f₁ x y g then (1 : ℝ) else 0) *
                w x b g := by
        intro y
        by_cases hy : e₁ x y b = f₁ x y g
        · by_cases hb : f x g = b
          · rw [if_pos hy, if_pos hb, if_neg, zero_mul, add_zero]
            rintro ⟨hne, -⟩
            exact hne hb
          · rw [if_pos hy, if_neg hb, if_pos ⟨hb, hy⟩, one_mul, zero_add]
        · rw [if_neg hy]
          have h1 : (0 : ℝ) ≤ if f x g = b then w x b g else 0 := by
            split_ifs
            · exact hwnonneg x b g
            · exact le_rfl
          have h2 : (0 : ℝ) ≤
              (if f x g ≠ b ∧ e₁ x y b = f₁ x y g then (1 : ℝ) else 0) *
                w x b g := by
            have : (0 : ℝ) ≤
                if f x g ≠ b ∧ e₁ x y b = f₁ x y g then (1 : ℝ) else 0 := by
              split_ifs
              · exact zero_le_one
              · exact le_rfl
            exact mul_nonneg this (hwnonneg x b g)
          linarith
      refine le_trans (avgOver_mono _ _ _ hsplit) ?_
      rw [avgOver_add, avgOver_uniform_const, avgOver_mul_const]
      have hcomm : w x b g * F x g = F x g * w x b g := mul_comm _ _
      linarith [mul_le_mul_of_nonneg_right (hFbound x b g) (hwnonneg x b g)]
    refine le_trans (Finset.sum_le_sum fun b _ =>
      Finset.sum_le_sum fun g _ => hterm b g) ?_
    have hsum : (∑ b : β, ∑ g : Γ,
        ((if f x g = b then w x b g else 0) + w x b g * F x g)) =
        (∑ b : β, ∑ g : Γ, if f x g = b then w x b g else 0) +
          ∑ g : Γ, (∑ b : β, w x b g) * F x g := by
      calc (∑ b : β, ∑ g : Γ,
            ((if f x g = b then w x b g else 0) + w x b g * F x g))
          = ∑ b : β, ((∑ g : Γ, if f x g = b then w x b g else 0) +
              ∑ g : Γ, w x b g * F x g) :=
            Finset.sum_congr rfl fun b _ => Finset.sum_add_distrib
        _ = (∑ b : β, ∑ g : Γ, if f x g = b then w x b g else 0) +
              ∑ b : β, ∑ g : Γ, w x b g * F x g := Finset.sum_add_distrib
        _ = (∑ b : β, ∑ g : Γ, if f x g = b then w x b g else 0) +
              ∑ g : Γ, (∑ b : β, w x b g) * F x g := by
            congr 1
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun g _ => (Finset.sum_mul _ _ _).symm
    have hW2 : (∑ g : Γ, (∑ b : β, w x b g) * F x g) =
        ∑ g : Γ, W g * F x g :=
      Finset.sum_congr rfl fun g _ => by rw [hfiber x g]
    rw [hsum, hW2]
  refine le_trans (avgOver_mono _ _ _ hstep) ?_
  rw [avgOver_add]
  have hswap : avgOver (uniformDistribution X)
      (fun x => ∑ g : Γ, W g * F x g) =
      ∑ g : Γ, W g * avgOver (uniformDistribution X) (fun x => F x g) := by
    rw [avgOver_sum]
    exact Finset.sum_congr rfl fun g _ => avgOver_const_mul _ _ _
  have hfinal : avgOver (uniformDistribution X)
      (fun x => ∑ g : Γ, W g * F x g) ≤ η := by
    rw [hswap]
    calc
      (∑ g : Γ, W g * avgOver (uniformDistribution X) (fun x => F x g)) ≤
          ∑ g : Γ, W g * η :=
        Finset.sum_le_sum fun g _ =>
          mul_le_mul_of_nonneg_left (hFavg g) (hWnonneg g)
      _ = η := by rw [← Finset.sum_mul, hWsum, one_mul]
  linarith

end RecoveryInternal

/-! ## The transport of a consistency relation -/

open RecoveryInternal

set_option maxHeartbeats 1600000 in
/-- Transport of a consistency relation along the recovery relabelling, with
the point measurement on the first tensor factor.  The point measurement is
complete at every question, so the total Born weight of an outcome of the
second measurement does not depend on the question; the bound on the
discrepancy event may therefore be averaged over the question against that
weight, and the defect of the recovered relation exceeds the defect of the
relation with the auxiliary sample by at most the resulting average. -/
theorem consistencyDefect_le_of_recoveryBound
    {X Y β Γ R ιA ιB : Type*}
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype β] [DecidableEq β] [Fintype Γ] [DecidableEq Γ]
    [Fintype R] [DecidableEq R]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : X → Measurement β ιA) (B : Measurement Γ ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (hψ : ‖ψ‖ = 1)
    (f : X → Γ → β) (e₁ : X → Y → β → R) (f₁ : X → Y → Γ → R)
    (F : X → Γ → ℝ) (η : ℝ)
    (hFbound : ∀ x b g, avgOver (uniformDistribution Y)
      (fun y => if f x g ≠ b ∧ e₁ x y b = f₁ x y g then (1 : ℝ) else 0) ≤ F x g)
    (hFavg : ∀ g, avgOver (uniformDistribution X) (fun x => F x g) ≤ η) :
    consistencyDefect (uniformDistribution X)
        (fun x b => heteroKron ((A x).effect b) 1)
        (fun x b => heteroKron 1 ((B.postprocess (f x)).effect b)) ψ ≤
      consistencyDefect (uniformDistribution (X × Y))
        (fun z r => heteroKron (((A z.1).postprocess (e₁ z.1 z.2)).effect r) 1)
        (fun z r => heteroKron 1 ((B.postprocess (f₁ z.1 z.2)).effect r)) ψ + η := by
  classical
  set w : X → β → Γ → ℝ := fun x b g =>
    stateQForm ψ (heteroKron ((A x).effect b) (B.effect g)) with hwdef
  have hwnonneg : ∀ x b g, 0 ≤ w x b g := fun x b g =>
    stateQForm_nonneg ψ (MIPStarRE.Quantum.kronecker_nonneg ((A x).pos b) (B.pos g))
  set W : Γ → ℝ := fun g => stateQForm ψ (heteroKron (1 : Op ιA) (B.effect g))
    with hWdef
  have hWnonneg : ∀ g, 0 ≤ W g := fun g =>
    stateQForm_nonneg ψ (MIPStarRE.Quantum.kronecker_nonneg
      (Matrix.PosSemidef.one.nonneg : (0 : Op ιA) ≤ 1) (B.pos g))
  have hfiber : ∀ x g, (∑ b : β, w x b g) = W g := by
    intro x g
    rw [hwdef, hWdef]
    simp only
    rw [← (A x).sum_eq_one, heteroKron_finset_sum_left, stateQForm_finset_sum]
  have hWsum : (∑ g : Γ, W g) = 1 := by
    rw [hWdef]
    simp only
    rw [← stateQForm_finset_sum, ← heteroKron_finset_sum_right, B.sum_eq_one,
      heteroKron_one_one, stateQForm_one_eq, hψ, one_pow]
  -- the two diagonal overlaps
  set AgrG : X → ℝ := fun x =>
    ∑ b : β, ∑ g : Γ, if f x g = b then w x b g else 0 with hAgrG
  set AgrH : X → Y → ℝ := fun x y =>
    ∑ b : β, ∑ g : Γ, if e₁ x y b = f₁ x y g then w x b g else 0 with hAgrH
  have hgoal : consistencyDefect (uniformDistribution X)
      (fun x b => heteroKron ((A x).effect b) 1)
      (fun x b => heteroKron 1 ((B.postprocess (f x)).effect b)) ψ =
      1 - avgOver (uniformDistribution X) AgrG := by
    rw [consistencyDefect_placed_eq_avg_point (uniformDistribution X) A
      (fun x => B.postprocess (f x))]
    have hpoint : ∀ x : X,
        (∑ b : β, ∑ b' : β, if b = b' then 0 else stateQForm ψ
          (heteroKron ((A x).effect b) ((B.postprocess (f x)).effect b'))) =
          1 - AgrG x := by
      intro x
      have h := point_defect_eq (leftPlacedMeasurement (ιB := ιB) (A x))
        (rightPlacedMeasurement (ιA := ιA) (B.postprocess (f x))) ψ
      simp only [leftPlacedMeasurement, rightPlacedMeasurement,
        MIPStarRE.Quantum.Measurement.ofSumEqOne] at h
      simp_rw [placed_product_stateQForm_eq] at h
      rw [h, hψ, one_pow, hAgrG]
      simp only
      rw [diagonalRight_pair_sum (A x) B ψ (f x)]
    rw [avgOver_congr _ _ _ hpoint, avgOver_sub, avgOver_uniform_const]
  have hhyp : consistencyDefect (uniformDistribution (X × Y))
      (fun z r => heteroKron (((A z.1).postprocess (e₁ z.1 z.2)).effect r) 1)
      (fun z r => heteroKron 1 ((B.postprocess (f₁ z.1 z.2)).effect r)) ψ =
      1 - avgOver (uniformDistribution X)
        (fun x => avgOver (uniformDistribution Y) (AgrH x)) := by
    rw [consistencyDefect_placed_eq_avg_point (uniformDistribution (X × Y))
      (fun z => (A z.1).postprocess (e₁ z.1 z.2))
      (fun z => B.postprocess (f₁ z.1 z.2))]
    have hpoint : ∀ z : X × Y,
        (∑ r : R, ∑ r' : R, if r = r' then 0 else stateQForm ψ
          (heteroKron (((A z.1).postprocess (e₁ z.1 z.2)).effect r)
            ((B.postprocess (f₁ z.1 z.2)).effect r'))) =
          1 - AgrH z.1 z.2 := by
      intro z
      have h := point_defect_eq
        (leftPlacedMeasurement (ιB := ιB) ((A z.1).postprocess (e₁ z.1 z.2)))
        (rightPlacedMeasurement (ιA := ιA) (B.postprocess (f₁ z.1 z.2))) ψ
      simp only [leftPlacedMeasurement, rightPlacedMeasurement,
        MIPStarRE.Quantum.Measurement.ofSumEqOne] at h
      simp_rw [placed_product_stateQForm_eq] at h
      rw [h, hψ, one_pow, hAgrH]
      simp only
      rw [diagonalPair_pair_sum (A z.1) B ψ (e₁ z.1 z.2) (f₁ z.1 z.2)]
    rw [avgOver_congr _ _ _ hpoint, avgOver_sub, avgOver_uniform_const,
      avgOver_uniform_prod (fun x y => AgrH x y)]
  rw [hgoal, hhyp]
  have hkey : avgOver (uniformDistribution X)
      (fun x => avgOver (uniformDistribution Y) (AgrH x)) ≤
      avgOver (uniformDistribution X) AgrG + η := by
    rw [hAgrG, hAgrH]
    exact recovery_avg_le w W f e₁ f₁ F η hwnonneg hWnonneg hfiber hWsum
      hFbound hFavg
  linarith

set_option maxHeartbeats 1600000 in
/-- Transport of a consistency relation along the recovery relabelling, with
the point measurement on the second tensor factor.  This is
`consistencyDefect_le_of_recoveryBound` with the two tensor factors exchanged;
it transports the second conclusion of `lem:ld-soundness`, in which the point
measurement of the strategy is the one placed on the second factor. -/
theorem consistencyDefect_le_of_recoveryBound_right
    {X Y β Γ R ιA ιB : Type*}
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype β] [DecidableEq β] [Fintype Γ] [DecidableEq Γ]
    [Fintype R] [DecidableEq R]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : X → Measurement β ιB) (B : Measurement Γ ιA)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (hψ : ‖ψ‖ = 1)
    (f : X → Γ → β) (e₁ : X → Y → β → R) (f₁ : X → Y → Γ → R)
    (F : X → Γ → ℝ) (η : ℝ)
    (hFbound : ∀ x b g, avgOver (uniformDistribution Y)
      (fun y => if f x g ≠ b ∧ e₁ x y b = f₁ x y g then (1 : ℝ) else 0) ≤ F x g)
    (hFavg : ∀ g, avgOver (uniformDistribution X) (fun x => F x g) ≤ η) :
    consistencyDefect (uniformDistribution X)
        (fun x b => heteroKron ((B.postprocess (f x)).effect b) 1)
        (fun x b => heteroKron 1 ((A x).effect b)) ψ ≤
      consistencyDefect (uniformDistribution (X × Y))
        (fun z r => heteroKron ((B.postprocess (f₁ z.1 z.2)).effect r) 1)
        (fun z r => heteroKron 1
          (((A z.1).postprocess (e₁ z.1 z.2)).effect r)) ψ + η := by
  classical
  set w : X → β → Γ → ℝ := fun x b g =>
    stateQForm ψ (heteroKron (B.effect g) ((A x).effect b)) with hwdef
  have hwnonneg : ∀ x b g, 0 ≤ w x b g := fun x b g =>
    stateQForm_nonneg ψ (MIPStarRE.Quantum.kronecker_nonneg (B.pos g) ((A x).pos b))
  set W : Γ → ℝ := fun g => stateQForm ψ (heteroKron (B.effect g) (1 : Op ιB))
    with hWdef
  have hWnonneg : ∀ g, 0 ≤ W g := fun g =>
    stateQForm_nonneg ψ (MIPStarRE.Quantum.kronecker_nonneg (B.pos g)
      (Matrix.PosSemidef.one.nonneg : (0 : Op ιB) ≤ 1))
  have hfiber : ∀ x g, (∑ b : β, w x b g) = W g := by
    intro x g
    rw [hwdef, hWdef]
    simp only
    rw [← (A x).sum_eq_one, heteroKron_finset_sum_right, stateQForm_finset_sum]
  have hWsum : (∑ g : Γ, W g) = 1 := by
    rw [hWdef]
    simp only
    rw [← stateQForm_finset_sum, ← heteroKron_finset_sum_left, B.sum_eq_one,
      heteroKron_one_one, stateQForm_one_eq, hψ, one_pow]
  set AgrG : X → ℝ := fun x =>
    ∑ b : β, ∑ g : Γ, if f x g = b then w x b g else 0 with hAgrG
  set AgrH : X → Y → ℝ := fun x y =>
    ∑ b : β, ∑ g : Γ, if e₁ x y b = f₁ x y g then w x b g else 0 with hAgrH
  have hgoal : consistencyDefect (uniformDistribution X)
      (fun x b => heteroKron ((B.postprocess (f x)).effect b) 1)
      (fun x b => heteroKron 1 ((A x).effect b)) ψ =
      1 - avgOver (uniformDistribution X) AgrG := by
    rw [consistencyDefect_placed_eq_avg_point (uniformDistribution X)
      (fun x => B.postprocess (f x)) A]
    have hpoint : ∀ x : X,
        (∑ b : β, ∑ b' : β, if b = b' then 0 else stateQForm ψ
          (heteroKron ((B.postprocess (f x)).effect b) ((A x).effect b'))) =
          1 - AgrG x := by
      intro x
      have h := point_defect_eq
        (leftPlacedMeasurement (ιB := ιB) (B.postprocess (f x)))
        (rightPlacedMeasurement (ιA := ιA) (A x)) ψ
      simp only [leftPlacedMeasurement, rightPlacedMeasurement,
        MIPStarRE.Quantum.Measurement.ofSumEqOne] at h
      simp_rw [placed_product_stateQForm_eq] at h
      rw [h, hψ, one_pow, hAgrG]
      simp only
      rw [diagonalLeft_pair_sum (A x) B ψ (f x)]
    rw [avgOver_congr _ _ _ hpoint, avgOver_sub, avgOver_uniform_const]
  have hhyp : consistencyDefect (uniformDistribution (X × Y))
      (fun z r => heteroKron ((B.postprocess (f₁ z.1 z.2)).effect r) 1)
      (fun z r => heteroKron 1
        (((A z.1).postprocess (e₁ z.1 z.2)).effect r)) ψ =
      1 - avgOver (uniformDistribution X)
        (fun x => avgOver (uniformDistribution Y) (AgrH x)) := by
    rw [consistencyDefect_placed_eq_avg_point (uniformDistribution (X × Y))
      (fun z => B.postprocess (f₁ z.1 z.2))
      (fun z => (A z.1).postprocess (e₁ z.1 z.2))]
    have hpoint : ∀ z : X × Y,
        (∑ r : R, ∑ r' : R, if r = r' then 0 else stateQForm ψ
          (heteroKron ((B.postprocess (f₁ z.1 z.2)).effect r)
            (((A z.1).postprocess (e₁ z.1 z.2)).effect r'))) =
          1 - AgrH z.1 z.2 := by
      intro z
      have h := point_defect_eq
        (leftPlacedMeasurement (ιB := ιB) (B.postprocess (f₁ z.1 z.2)))
        (rightPlacedMeasurement (ιA := ιA) ((A z.1).postprocess (e₁ z.1 z.2))) ψ
      simp only [leftPlacedMeasurement, rightPlacedMeasurement,
        MIPStarRE.Quantum.Measurement.ofSumEqOne] at h
      simp_rw [placed_product_stateQForm_eq] at h
      rw [h, hψ, one_pow, hAgrH]
      simp only
      rw [diagonalPairLeft_pair_sum (A z.1) B ψ (e₁ z.1 z.2) (f₁ z.1 z.2)]
    rw [avgOver_congr _ _ _ hpoint, avgOver_sub, avgOver_uniform_const,
      avgOver_uniform_prod (fun x y => AgrH x y)]
  rw [hgoal, hhyp]
  have hkey : avgOver (uniformDistribution X)
      (fun x => avgOver (uniformDistribution Y) (AgrH x)) ≤
      avgOver (uniformDistribution X) AgrG + η := by
    rw [hAgrG, hAgrH]
    exact recovery_avg_le w W f e₁ f₁ F η hwnonneg hWnonneg hfiber hWsum
      hFbound hFavg
  linarith

end

end MIPStarRE.QPBT
