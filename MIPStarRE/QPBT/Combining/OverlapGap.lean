import MIPStarRE.QPBT.Games.DistanceTheorems.Support
import MIPStarRE.LDT.Preliminaries.SwitchSandwichPrep.InnerProduct

/-!
# Replacing one factor of a measurement-weighted overlap

The scalar estimates used to combine the two Pauli bases compare averaged
overlaps whose left factor is one complete measurement and whose right factors
are operator families at small state-dependent distance.  This module records
the corresponding Cauchy--Schwarz estimate.  The right-hand families are
arbitrary, so the estimate covers an ordered product of point effects, which
is not itself a measurement.

## References

The estimate is `lem:overlap-gap-distance` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`; it is the Cauchy--Schwarz
step at paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1147-1166`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

/-- Replacing one operator family inside an overlap weighted on the left by a
complete measurement changes the average by at most the square root of the
state-dependent squared distance between the two families. -/
theorem abs_overlap_gap_le_sqrt_of_opFamilyDistSq {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A : X → Measurement α ι) (B C : X → α → Op ι)
    (ψ : EuclideanSpace ℂ ι) (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1)
    (ζ : ℝ) (hBC : opFamilyDistSq μ B C ψ ≤ ζ) :
    |avgOver μ (fun x => ∑ a : α, stateQForm ψ ((A x).effect a * B x a)) -
        avgOver μ (fun x => ∑ a : α, stateQForm ψ ((A x).effect a * C x a))| ≤
      Real.sqrt ζ := by
  classical
  have hnorm_sq : ∀ M : Op ι,
      ‖applyOperatorToState M ψ‖ ^ 2 = stateQForm ψ (Mᴴ * M) := by
    intro M
    rw [@norm_sq_eq_re_inner ℂ]
    unfold stateQForm applyOperatorToState
    rw [Matrix.toEuclideanLin_conjTranspose_mul_self]
    change (inner ℂ (Matrix.toEuclideanLin M ψ) (Matrix.toEuclideanLin M ψ)).re =
      (inner ℂ ψ ((Matrix.toEuclideanLin M).adjoint
        (Matrix.toEuclideanLin M ψ))).re
    rw [LinearMap.adjoint_inner_right]
  have hmul : ∀ M N : Op ι, Mᴴ = M →
      stateQForm ψ (M * N) =
        (inner ℂ (applyOperatorToState M ψ)
          (applyOperatorToState N ψ)).re := by
    intro M N hM
    have hadjoint : (Matrix.toEuclideanLin M).adjoint =
        Matrix.toEuclideanLin M := by
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hM]
    calc
      stateQForm ψ (M * N) =
          (inner ℂ ψ
            (applyOperatorToState M (applyOperatorToState N ψ))).re := by
        rw [stateQForm, applyOperatorToState_mul]
      _ = (inner ℂ ψ ((Matrix.toEuclideanLin M).adjoint
            (applyOperatorToState N ψ))).re := by
        rw [hadjoint]
        rfl
      _ = _ := by
        rw [LinearMap.adjoint_inner_right]
        rfl
  have hleft : ∀ x : X,
      (∑ a : α, ‖applyOperatorToState ((A x).effect a) ψ‖ ^ 2) ≤ 1 := by
    intro x
    have htotal : (∑ a : α, stateQForm ψ ((A x).effect a)) = 1 := by
      calc
        (∑ a : α, stateQForm ψ ((A x).effect a)) =
            stateQForm ψ (∑ a : α, (A x).effect a) := by
          simp [stateQForm, applyOperatorToState]
        _ = stateQForm ψ 1 := by rw [(A x).sum_eq_one]
        _ = 1 := by rw [stateQForm]; simp [applyOperatorToState, hψ]
    calc
      (∑ a : α, ‖applyOperatorToState ((A x).effect a) ψ‖ ^ 2) ≤
          ∑ a : α, stateQForm ψ ((A x).effect a) := by
        refine Finset.sum_le_sum ?_
        intro a _
        rw [hnorm_sq, measurement_effect_hermitian]
        exact quadratic_form_mono (MIPStarRE.Quantum.sq_le_self ((A x).pos a)
          (measurement_effect_le_one (A x) a)) ψ
      _ = 1 := htotal
  have hgnonneg : ∀ x : X,
      0 ≤ ∑ a : α, ‖applyOperatorToState (B x a - C x a) ψ‖ ^ 2 :=
    fun x => Finset.sum_nonneg fun a _ => sq_nonneg _
  have hpoint : ∀ x : X,
      |∑ a : α, stateQForm ψ ((A x).effect a * (B x a - C x a))| ≤
        Real.sqrt (∑ a : α, ‖applyOperatorToState (B x a - C x a) ψ‖ ^ 2) := by
    intro x
    let u : α → EuclideanSpace ℂ ι := fun a =>
      applyOperatorToState ((A x).effect a) ψ
    let v : α → EuclideanSpace ℂ ι := fun a =>
      applyOperatorToState (B x a - C x a) ψ
    have hrw : (∑ a : α, stateQForm ψ ((A x).effect a * (B x a - C x a))) =
        ∑ a : α, (inner ℂ (u a) (v a)).re := by
      refine Finset.sum_congr rfl ?_
      intro a _
      exact hmul _ _ (measurement_effect_hermitian (A x) a)
    have hone : Real.sqrt (∑ a : α, ‖u a‖ ^ 2) ≤ 1 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (hleft x)
    calc
      |∑ a : α, stateQForm ψ ((A x).effect a * (B x a - C x a))| =
          |∑ a : α, (inner ℂ (u a) (v a)).re| := by rw [hrw]
      _ ≤ ∑ a : α, |(inner ℂ (u a) (v a)).re| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a : α, ‖u a‖ * ‖v a‖ := by
        refine Finset.sum_le_sum ?_
        intro a _
        exact (Complex.abs_re_le_norm _).trans (norm_inner_le_norm (u a) (v a))
      _ ≤ Real.sqrt (∑ a : α, ‖u a‖ ^ 2) * Real.sqrt (∑ a : α, ‖v a‖ ^ 2) := by
        simpa using Real.sum_mul_le_sqrt_mul_sqrt
          (Finset.univ : Finset α) (fun a => ‖u a‖) (fun a => ‖v a‖)
      _ ≤ 1 * Real.sqrt (∑ a : α, ‖v a‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hone (Real.sqrt_nonneg _)
      _ = Real.sqrt (∑ a : α,
            ‖applyOperatorToState (B x a - C x a) ψ‖ ^ 2) := one_mul _
  have hdiff :
      avgOver μ (fun x => ∑ a : α, stateQForm ψ ((A x).effect a * B x a)) -
          avgOver μ (fun x => ∑ a : α,
            stateQForm ψ ((A x).effect a * C x a)) =
        avgOver μ (fun x => ∑ a : α,
          stateQForm ψ ((A x).effect a * (B x a - C x a))) := by
    rw [← avgOver_sub]
    refine avgOver_congr μ _ _ ?_
    intro x
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro a _
    simp [stateQForm, applyOperatorToState, mul_sub]
  rw [hdiff]
  refine le_trans
    (MIPStarRE.LDT.Preliminaries.avgOver_abs_le_sqrt_of_pointwise μ _ _
      hpoint hgnonneg (by rw [hμ.weight_sum_eq_one])) ?_
  exact Real.sqrt_le_sqrt hBC

/-! ## The Cauchy--Schwarz inequality weighted by a positive operator -/

/-- For a positive operator `A`, the sesquilinear form `⟨u, A v⟩` satisfies the
Cauchy--Schwarz inequality with the two diagonal values `⟨u, A u⟩` and
`⟨v, A v⟩`.  This is the inequality behind the Cauchy--Schwarz steps of the
proofs of `lem:claim-17-2` and `lem:claim-17-3`, in which both factors carry
the square root of the line effect, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1168-1209`. -/
theorem norm_inner_applyOperatorToState_le_sqrt_mul_sqrt {ι : Type*}
    [Fintype ι] [DecidableEq ι] {A : Op ι} (hA : 0 ≤ A)
    (u v : EuclideanSpace ℂ ι) :
    ‖inner ℂ u (applyOperatorToState A v)‖ ≤
      Real.sqrt (inner ℂ u (applyOperatorToState A u)).re *
        Real.sqrt (inner ℂ v (applyOperatorToState A v)).re := by
  set R : Op ι := CFC.sqrt A with hR
  have hRnonneg : 0 ≤ R := CFC.sqrt_nonneg A
  have hRR : R * R = A := CFC.sqrt_mul_sqrt_self A hA
  have hRherm : Rᴴ = R :=
    (Matrix.nonneg_iff_posSemidef.mp hRnonneg).isHermitian.eq
  have hadjoint : (Matrix.toEuclideanLin R).adjoint = Matrix.toEuclideanLin R := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hRherm]
  have hsplit : ∀ w z : EuclideanSpace ℂ ι,
      inner ℂ w (applyOperatorToState A z) =
        inner ℂ (applyOperatorToState R w) (applyOperatorToState R z) := by
    intro w z
    have h := LinearMap.adjoint_inner_right (Matrix.toEuclideanLin R) w
      (Matrix.toEuclideanLin R z)
    rw [hadjoint] at h
    rw [← hRR, applyOperatorToState_mul]
    exact h
  have hnorm : ∀ w : EuclideanSpace ℂ ι,
      ‖applyOperatorToState R w‖ =
        Real.sqrt (inner ℂ w (applyOperatorToState A w)).re := by
    intro w
    have h2 : ‖applyOperatorToState R w‖ ^ 2 =
        (inner ℂ (applyOperatorToState R w) (applyOperatorToState R w)).re := by
      rw [@norm_sq_eq_re_inner ℂ]
      rfl
    rw [hsplit, ← h2, Real.sqrt_sq (norm_nonneg _)]
  rw [hsplit, ← hnorm, ← hnorm]
  exact norm_inner_le_norm _ _

/-- The sum over outcomes of the real parts of `⟨u a, A a (v a)⟩`, for
positive weights `A a`, is bounded by the product of the square roots of the
two diagonal sums. -/
theorem abs_sum_re_inner_le_sqrt_mul_sqrt {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι] (A : α → Op ι) (hA : ∀ a, 0 ≤ A a)
    (u v : α → EuclideanSpace ℂ ι) :
    |∑ a, (inner ℂ (u a) (applyOperatorToState (A a) (v a))).re| ≤
      Real.sqrt (∑ a, (inner ℂ (u a) (applyOperatorToState (A a) (u a))).re) *
        Real.sqrt (∑ a, (inner ℂ (v a) (applyOperatorToState (A a) (v a))).re) := by
  have hu : ∀ a, 0 ≤ (inner ℂ (u a) (applyOperatorToState (A a) (u a))).re :=
    fun a => stateQForm_nonneg (u a) (hA a)
  have hv : ∀ a, 0 ≤ (inner ℂ (v a) (applyOperatorToState (A a) (v a))).re :=
    fun a => stateQForm_nonneg (v a) (hA a)
  calc
    |∑ a, (inner ℂ (u a) (applyOperatorToState (A a) (v a))).re|
        ≤ ∑ a, |(inner ℂ (u a) (applyOperatorToState (A a) (v a))).re| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, Real.sqrt (inner ℂ (u a) (applyOperatorToState (A a) (u a))).re *
          Real.sqrt (inner ℂ (v a) (applyOperatorToState (A a) (v a))).re := by
      refine Finset.sum_le_sum fun a _ => ?_
      exact (Complex.abs_re_le_norm _).trans
        (norm_inner_applyOperatorToState_le_sqrt_mul_sqrt (hA a) (u a) (v a))
    _ ≤ Real.sqrt (∑ a,
            Real.sqrt (inner ℂ (u a) (applyOperatorToState (A a) (u a))).re ^ 2) *
          Real.sqrt (∑ a,
            Real.sqrt (inner ℂ (v a) (applyOperatorToState (A a) (v a))).re ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = _ := by
      rw [Finset.sum_congr rfl fun a _ => Real.sq_sqrt (hu a),
        Finset.sum_congr rfl fun a _ => Real.sq_sqrt (hv a)]

/-- The averaged form of the preceding estimate: the average over a
distribution of the outcome sums of `Re ⟨u, A v⟩` is bounded by the product of
the square roots of the two averaged diagonal sums. -/
theorem abs_avgOver_sum_re_inner_le_sqrt_mul_sqrt {X α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι] (μ : Distribution X) (A : X → α → Op ι)
    (hA : ∀ x a, 0 ≤ A x a) (u v : X → α → EuclideanSpace ℂ ι) :
    |avgOver μ (fun x =>
        ∑ a, (inner ℂ (u x a) (applyOperatorToState (A x a) (v x a))).re)| ≤
      Real.sqrt (avgOver μ (fun x =>
          ∑ a, (inner ℂ (u x a) (applyOperatorToState (A x a) (u x a))).re)) *
        Real.sqrt (avgOver μ (fun x =>
          ∑ a, (inner ℂ (v x a) (applyOperatorToState (A x a) (v x a))).re)) := by
  set f : X → ℝ := fun x =>
    ∑ a, (inner ℂ (u x a) (applyOperatorToState (A x a) (v x a))).re with hf
  set g : X → ℝ := fun x =>
    ∑ a, (inner ℂ (u x a) (applyOperatorToState (A x a) (u x a))).re with hg
  set h : X → ℝ := fun x =>
    ∑ a, (inner ℂ (v x a) (applyOperatorToState (A x a) (v x a))).re with hh
  have hg0 : ∀ x, 0 ≤ g x := fun x =>
    Finset.sum_nonneg fun a _ => stateQForm_nonneg (u x a) (hA x a)
  have hh0 : ∀ x, 0 ≤ h x := fun x =>
    Finset.sum_nonneg fun a _ => stateQForm_nonneg (v x a) (hA x a)
  have hpoint : ∀ x, |f x| ≤ Real.sqrt (g x) * Real.sqrt (h x) := fun x =>
    abs_sum_re_inner_le_sqrt_mul_sqrt (A x) (hA x) (u x) (v x)
  unfold avgOver
  calc
    |∑ x ∈ μ.support, μ.weight x * f x|
        ≤ ∑ x ∈ μ.support, |μ.weight x * f x| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x ∈ μ.support, μ.weight x * |f x| := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [abs_mul, abs_of_nonneg (μ.nonnegative x)]
    _ ≤ ∑ x ∈ μ.support, μ.weight x * (Real.sqrt (g x) * Real.sqrt (h x)) :=
      Finset.sum_le_sum fun x _ =>
        mul_le_mul_of_nonneg_left (hpoint x) (μ.nonnegative x)
    _ = ∑ x ∈ μ.support,
          Real.sqrt (μ.weight x * g x) * Real.sqrt (μ.weight x * h x) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Real.sqrt_mul (μ.nonnegative x), Real.sqrt_mul (μ.nonnegative x),
        show Real.sqrt (μ.weight x) * Real.sqrt (g x) *
            (Real.sqrt (μ.weight x) * Real.sqrt (h x)) =
          Real.sqrt (μ.weight x) * Real.sqrt (μ.weight x) *
            (Real.sqrt (g x) * Real.sqrt (h x)) by ring,
        Real.mul_self_sqrt (μ.nonnegative x)]
    _ ≤ Real.sqrt (∑ x ∈ μ.support, Real.sqrt (μ.weight x * g x) ^ 2) *
          Real.sqrt (∑ x ∈ μ.support, Real.sqrt (μ.weight x * h x) ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = _ := by
      rw [Finset.sum_congr rfl fun x _ =>
          Real.sq_sqrt (mul_nonneg (μ.nonnegative x) (hg0 x)),
        Finset.sum_congr rfl fun x _ =>
          Real.sq_sqrt (mul_nonneg (μ.nonnegative x) (hh0 x))]

/-! ## Quadratic forms against projections -/

/-- The real quadratic form is invariant under the conjugate transpose. -/
theorem stateQForm_conjTranspose {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (M : Op ι) :
    stateQForm ψ Mᴴ = stateQForm ψ M := by
  unfold stateQForm
  change (inner ℂ ψ (Matrix.toEuclideanLin Mᴴ ψ)).re =
    (inner ℂ ψ (Matrix.toEuclideanLin M ψ)).re
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_right,
    ← inner_conj_symm, Complex.conj_re]

/-- Conjugating an operator transfers the outer operator to the state vector. -/
theorem stateQForm_conjTranspose_mul_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (W M : Op ι) :
    stateQForm ψ (Wᴴ * M * W) = stateQForm (applyOperatorToState W ψ) M := by
  unfold stateQForm
  rw [applyOperatorToState_mul, applyOperatorToState_mul]
  congr 1
  change inner ℂ ψ (Matrix.toEuclideanLin Wᴴ _) =
    inner ℂ (Matrix.toEuclideanLin W ψ) _
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_right]

/-- For a projection `B` commuting with `A`, the quadratic form of `A` in
`B ψ` is the quadratic form of `A B` in `ψ`. -/
theorem stateQForm_applyOperatorToState_eq_of_isProj {ι : Type*} [Fintype ι]
    [DecidableEq ι] (ψ : EuclideanSpace ℂ ι) {A B : Op ι} (hB : IsProj B)
    (hAB : Commute A B) :
    stateQForm (applyOperatorToState B ψ) A = stateQForm ψ (A * B) := by
  rw [← stateQForm_conjTranspose_mul_mul, hB.isSelfAdjoint.isHermitian.eq,
    ← hAB.eq, mul_assoc, hB.isIdempotentElem.eq]

/-- The quadratic form of an operator bounded by the identity is bounded by
the squared norm of the vector. -/
theorem stateQForm_le_norm_sq_of_le_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : EuclideanSpace ℂ ι) {A : Op ι} (hA : A ≤ 1) :
    stateQForm v A ≤ ‖v‖ ^ 2 := by
  rw [← stateQForm_one]
  exact quadratic_form_mono hA v

/-- The effects of a complete measurement have total quadratic form one on a
unit vector. -/
theorem sum_stateQForm_effect_eq_one {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq ι] (A : Measurement α ι) (ψ : EuclideanSpace ℂ ι)
    (hψ : ‖ψ‖ = 1) :
    (∑ a : α, stateQForm ψ (A.effect a)) = 1 := by
  calc
    (∑ a : α, stateQForm ψ (A.effect a)) =
        stateQForm ψ (∑ a : α, A.effect a) := by
      simp [stateQForm, applyOperatorToState]
    _ = stateQForm ψ 1 := by rw [A.sum_eq_one]
    _ = 1 := by rw [stateQForm_one, hψ, one_pow]

/-- Weighting a complete measurement by commuting projections cannot exceed
the total mass one. -/
theorem avgOver_sum_stateQForm_mul_le_one {X α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι] (μ : Distribution X) (A : X → Measurement α ι)
    (C : X → α → Op ι) (ψ : EuclideanSpace ℂ ι) (hμ : μ.IsProbability)
    (hψ : ‖ψ‖ = 1) (hC : ∀ x a, IsProj (C x a))
    (hAC : ∀ x a, Commute ((A x).effect a) (C x a)) :
    avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * C x a)) ≤ 1 := by
  have hpt : ∀ x, (∑ a, stateQForm ψ ((A x).effect a * C x a)) ≤ 1 := by
    intro x
    calc
      (∑ a, stateQForm ψ ((A x).effect a * C x a)) ≤
          ∑ a, stateQForm ψ ((A x).effect a) := by
        refine Finset.sum_le_sum fun a _ => ?_
        have h1 : stateQForm ψ ((A x).effect a * (1 - C x a)) =
            stateQForm ψ ((A x).effect a) -
              stateQForm ψ ((A x).effect a * C x a) := by
          simp [stateQForm, applyOperatorToState, mul_sub]
        have h2 : 0 ≤ stateQForm ψ ((A x).effect a * (1 - C x a)) := by
          rw [← stateQForm_applyOperatorToState_eq_of_isProj ψ (hC x a).one_sub
            ((Commute.one_right _).sub_right (hAC x a))]
          exact stateQForm_nonneg _ ((A x).pos a)
        linarith
      _ = 1 := sum_stateQForm_effect_eq_one (A x) ψ hψ
  calc
    avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * C x a)) ≤
        avgOver μ (fun _ => 1) := avgOver_mono μ _ _ hpt
    _ = 1 := avgOver_const_of_isProbability μ hμ 1

/-! ## Replacing a factor under the weight of a measurement -/

/-- Cauchy--Schwarz with the measurement as weight: for projections `B`
commuting with the effects of `A`, the averaged overlap of `A` against the
product `B C` is bounded by the square roots of the averaged overlap of `A`
against `B` and of the averaged quadratic form of `A` in `C ψ`.  This is the
Cauchy--Schwarz step of the proofs of `lem:claim-17-2` and `lem:claim-17-3`,
paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1168-1209`. -/
theorem abs_avgOver_sum_stateQForm_mul_mul_le_sqrt_mul_sqrt {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι] (μ : Distribution X)
    (A : X → Measurement α ι) (B C : X → α → Op ι) (ψ : EuclideanSpace ℂ ι)
    (hB : ∀ x a, IsProj (B x a))
    (hAB : ∀ x a, Commute ((A x).effect a) (B x a)) :
    |avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * (B x a * C x a)))| ≤
      Real.sqrt (avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * B x a))) *
        Real.sqrt (avgOver μ (fun x => ∑ a,
          stateQForm (applyOperatorToState (C x a) ψ) ((A x).effect a))) := by
  have hrw : ∀ x a, stateQForm ψ ((A x).effect a * (B x a * C x a)) =
      (inner ℂ (applyOperatorToState (B x a) ψ)
        (applyOperatorToState ((A x).effect a)
          (applyOperatorToState (C x a) ψ))).re := by
    intro x a
    unfold stateQForm
    rw [← mul_assoc, (hAB x a).eq, mul_assoc, applyOperatorToState_mul,
      applyOperatorToState_mul]
    congr 1
    have hadj : (Matrix.toEuclideanLin (B x a)).adjoint =
        Matrix.toEuclideanLin (B x a) := by
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
        (hB x a).isSelfAdjoint.isHermitian.eq]
    have h := LinearMap.adjoint_inner_right (Matrix.toEuclideanLin (B x a)) ψ
      (applyOperatorToState ((A x).effect a) (applyOperatorToState (C x a) ψ))
    rw [hadj] at h
    exact h
  have hleft : (fun x => ∑ a, stateQForm ψ ((A x).effect a * B x a)) =
      fun x => ∑ a, (inner ℂ (applyOperatorToState (B x a) ψ)
        (applyOperatorToState ((A x).effect a)
          (applyOperatorToState (B x a) ψ))).re :=
    funext fun x => Finset.sum_congr rfl fun a _ =>
      (stateQForm_applyOperatorToState_eq_of_isProj ψ (hB x a) (hAB x a)).symm
  have hmain : (fun x => ∑ a, stateQForm ψ ((A x).effect a * (B x a * C x a))) =
      fun x => ∑ a, (inner ℂ (applyOperatorToState (B x a) ψ)
        (applyOperatorToState ((A x).effect a)
          (applyOperatorToState (C x a) ψ))).re :=
    funext fun x => Finset.sum_congr rfl fun a _ => hrw x a
  rw [hmain, hleft]
  exact abs_avgOver_sum_re_inner_le_sqrt_mul_sqrt μ (fun x a => (A x).effect a)
    (fun x a => (A x).pos a) (fun x a => applyOperatorToState (B x a) ψ)
    (fun x a => applyOperatorToState (C x a) ψ)

/-- Deficit form of the Cauchy--Schwarz estimate: for projections `B` and `C`
commuting with the effects of `A`, replacing the factor `C B` by `C` inside an
overlap weighted by the complete measurement `A` changes the average by at
most the square root of the deficit `1 - E Σ_a ⟨A_a B_a⟩`.  This is the
estimate used in the proof of `lem:claim-17-2` and, with `C = Id`, in the proof
of `lem:claim-17-3`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1168-1209`. -/
theorem abs_overlap_gap_le_sqrt_one_sub_of_isProj {X α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι] (μ : Distribution X) (A : X → Measurement α ι)
    (B C : X → α → Op ι) (ψ : EuclideanSpace ℂ ι) (hμ : μ.IsProbability)
    (hψ : ‖ψ‖ = 1) (hB : ∀ x a, IsProj (B x a)) (hC : ∀ x a, IsProj (C x a))
    (hAB : ∀ x a, Commute ((A x).effect a) (B x a))
    (hAC : ∀ x a, Commute ((A x).effect a) (C x a)) :
    |avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * (C x a * B x a))) -
        avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * C x a))| ≤
      Real.sqrt (1 - avgOver μ (fun x =>
        ∑ a, stateQForm ψ ((A x).effect a * B x a))) := by
  have hpt : ∀ x, (∑ a, stateQForm ψ ((A x).effect a * C x a)) -
      (∑ a, stateQForm ψ ((A x).effect a * (C x a * B x a))) =
        ∑ a, stateQForm ψ ((A x).effect a * (C x a * (1 - B x a))) := by
    intro x
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [stateQForm, applyOperatorToState, mul_sub]
  rw [abs_sub_comm, ← avgOver_sub, avgOver_congr μ _ _ hpt]
  have h1B : ∀ x a, IsProj (1 - B x a) := fun x a => (hB x a).one_sub
  have hA1B : ∀ x a, Commute ((A x).effect a) (1 - B x a) := fun x a =>
    (Commute.one_right _).sub_right (hAB x a)
  have hcs := abs_avgOver_sum_stateQForm_mul_mul_le_sqrt_mul_sqrt μ A C
    (fun x a => 1 - B x a) ψ hC hAC
  have hsecond : avgOver μ (fun x => ∑ a,
      stateQForm (applyOperatorToState (1 - B x a) ψ) ((A x).effect a)) =
      1 - avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * B x a)) := by
    have hx : ∀ x, (∑ a,
        stateQForm (applyOperatorToState (1 - B x a) ψ) ((A x).effect a)) =
        1 - ∑ a, stateQForm ψ ((A x).effect a * B x a) := by
      intro x
      rw [← sum_stateQForm_effect_eq_one (A x) ψ hψ, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [stateQForm_applyOperatorToState_eq_of_isProj ψ (h1B x a) (hA1B x a)]
      simp [stateQForm, applyOperatorToState, mul_sub]
    rw [avgOver_congr μ _ _ hx, avgOver_sub, avgOver_const_of_isProbability μ hμ]
  have hfirst : Real.sqrt (avgOver μ (fun x =>
      ∑ a, stateQForm ψ ((A x).effect a * C x a))) ≤ 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt
      (avgOver_sum_stateQForm_mul_le_one μ A C ψ hμ hψ hC hAC)
  rw [hsecond] at hcs
  calc
    _ ≤ _ := hcs
    _ ≤ 1 * Real.sqrt (1 - avgOver μ (fun x =>
          ∑ a, stateQForm ψ ((A x).effect a * B x a))) :=
      mul_le_mul_of_nonneg_right hfirst (Real.sqrt_nonneg _)
    _ = _ := one_mul _

/-- The deficit form of the Cauchy--Schwarz estimate with the product family
`C B` supplied as one family `CB`, which is convenient when the product is
formed on a local space before being placed. -/
theorem abs_overlap_gap_le_sqrt_one_sub_of_isProj' {X α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι] (μ : Distribution X) (A : X → Measurement α ι)
    (B C CB : X → α → Op ι) (ψ : EuclideanSpace ℂ ι) (hμ : μ.IsProbability)
    (hψ : ‖ψ‖ = 1) (hB : ∀ x a, IsProj (B x a)) (hC : ∀ x a, IsProj (C x a))
    (hAB : ∀ x a, Commute ((A x).effect a) (B x a))
    (hAC : ∀ x a, Commute ((A x).effect a) (C x a))
    (hCB : ∀ x a, CB x a = C x a * B x a) :
    |avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * CB x a)) -
        avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * C x a))| ≤
      Real.sqrt (1 - avgOver μ (fun x =>
        ∑ a, stateQForm ψ ((A x).effect a * B x a))) := by
  rw [avgOver_congr μ _ _ fun x => Finset.sum_congr rfl fun a _ => by rw [hCB]]
  exact abs_overlap_gap_le_sqrt_one_sub_of_isProj μ A B C ψ hμ hψ hB hC hAB hAC

/-- Inserting an arbitrary operator family `W` after a projection family `R`
commuting with the effects of `A` costs at most the square root of the
averaged squared norms of `W ψ`. -/
theorem abs_avgOver_sum_stateQForm_mul_le_sqrt_of_isProj {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι] (μ : Distribution X)
    (A : X → Measurement α ι) (R W : X → α → Op ι) (ψ : EuclideanSpace ℂ ι)
    (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1) (hR : ∀ x a, IsProj (R x a))
    (hAR : ∀ x a, Commute ((A x).effect a) (R x a)) :
    |avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * (R x a * W x a)))| ≤
      Real.sqrt (avgOver μ (fun x =>
        ∑ a, ‖applyOperatorToState (W x a) ψ‖ ^ 2)) := by
  have hcs := abs_avgOver_sum_stateQForm_mul_mul_le_sqrt_mul_sqrt μ A R W ψ hR hAR
  have hfirst : Real.sqrt (avgOver μ (fun x =>
      ∑ a, stateQForm ψ ((A x).effect a * R x a))) ≤ 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt
      (avgOver_sum_stateQForm_mul_le_one μ A R ψ hμ hψ hR hAR)
  have hsecond : avgOver μ (fun x => ∑ a,
      stateQForm (applyOperatorToState (W x a) ψ) ((A x).effect a)) ≤
      avgOver μ (fun x => ∑ a, ‖applyOperatorToState (W x a) ψ‖ ^ 2) :=
    avgOver_mono μ _ _ fun x => Finset.sum_le_sum fun a _ =>
      stateQForm_le_norm_sq_of_le_one _ (measurement_effect_le_one (A x) a)
  calc
    _ ≤ _ := hcs
    _ ≤ 1 * Real.sqrt (avgOver μ (fun x =>
          ∑ a, ‖applyOperatorToState (W x a) ψ‖ ^ 2)) :=
      mul_le_mul hfirst (Real.sqrt_le_sqrt hsecond) (Real.sqrt_nonneg _)
        zero_le_one
    _ = _ := one_mul _

/-- The mirror image of the preceding estimate: an operator family `W`
commuting with the effects of `A`, inserted before a commuting projection
family `R`, costs at most the square root of the averaged squared norms of
`Wᴴ ψ`. -/
theorem abs_avgOver_sum_stateQForm_mul_le_sqrt_of_isProj' {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι] (μ : Distribution X)
    (A : X → Measurement α ι) (W R : X → α → Op ι) (ψ : EuclideanSpace ℂ ι)
    (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1) (hR : ∀ x a, IsProj (R x a))
    (hAR : ∀ x a, Commute ((A x).effect a) (R x a))
    (hAW : ∀ x a, Commute ((A x).effect a) (W x a)) :
    |avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * (W x a * R x a)))| ≤
      Real.sqrt (avgOver μ (fun x =>
        ∑ a, ‖applyOperatorToState (W x a)ᴴ ψ‖ ^ 2)) := by
  have hrw : ∀ x a, stateQForm ψ ((A x).effect a * (W x a * R x a)) =
      stateQForm ψ ((A x).effect a * (R x a * (W x a)ᴴ)) := by
    intro x a
    have hAWH : Commute ((A x).effect a) (W x a)ᴴ := by
      have h := congrArg Matrix.conjTranspose (hAW x a).eq
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        measurement_effect_hermitian] at h
      exact h.symm
    rw [← stateQForm_conjTranspose ψ ((A x).effect a * (W x a * R x a)),
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      measurement_effect_hermitian, (hR x a).isSelfAdjoint.isHermitian.eq]
    congr 1
    exact ((hAR x a).mul_right hAWH).eq.symm
  rw [avgOver_congr μ _ _ fun x => Finset.sum_congr rfl fun a _ => hrw x a]
  exact abs_avgOver_sum_stateQForm_mul_le_sqrt_of_isProj μ A R
    (fun x a => (W x a)ᴴ) ψ hμ hψ hR hAR

end MIPStarRE.QPBT
