import MIPStarRE.QPBT.Combining.Points.Sandwich

/-!
# Self-consistency of the sandwich POVM

The sandwich POVM `R^{x,z}_{a,b} = M^Z_b M^X_a M^Z_b` of
`MIPStarRE/QPBT/Combining/Points/Sandwich.lean` is approximately self-consistent
between opposite register placements.  The source establishes this by a
Cauchy--Schwarz chain (displays `eq:qld-rw-self-cons-1` to
`eq:qld-rw-self-cons-4`); here an exact identity is used instead.  Writing
`P_1, P_2` for the two placements of an operator `P`,
`W_b = (M^Z_b)_1 (M^Z_b)_2`, and `D^W_c = (M^W_c)_1 - (M^W_c)_2`, the
consistency defect of the two placed sandwiches equals
`(1/2) ∑_b ‖D^Z_b ψ‖^2 + (1/2) ∑_{a,b} ‖D^X_a W_b ψ‖^2`,
by two applications of the identity
`∑_c ⟨w, P_c Q_c w⟩ = ‖w‖^2 - (1/2) ∑_c ‖(P_c - Q_c) w‖^2` for projective
measurements.  The second sum is then bounded by the self-consistency of `M^X`
and the commutators on the two placements, since
`D^X_a W_b = W_b D^X_a + (M^Z_b)_2 K^1_{a,b} - (M^Z_b)_1 K^2_{a,b}`, where
`K^i_{a,b}` is the placed commutator of `M^X_a` and `M^Z_b`.

## Main results

* `sandwich_overlap_identity`: the exact expression of the overlap of two
  placed sandwiches.
* `sandwich_defect_pointwise_le`: the pointwise bound on the consistency
  defect of the sandwich for a fixed point pair.
* `ProjectiveSetting.sandwichDefectBound`,
  `ProjectiveSetting.sandwich_offDiagonal_le_sandwichDefectBound`, and
  `ProjectiveSetting.avg_sandwichDefectBound_le`: the bound as a function of
  the point pair, the pointwise estimate, and the average.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:743-790`,
blueprint `blueprint/src/chapter/ch15_qpbt_combining.tex:851-880`
(`lem:qld-4-10`, first step); the identity route is explained in
`docs/paper-gaps/qpbt_linearity-theorem-quotation.tex`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

/-! ## Quadratic-form identities -/

/-- The quadratic form of `Wᴴ M W` in `ψ` is the quadratic form of `M` in
`W ψ`. -/
theorem stateQForm_conjTranspose_mul_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (W M : Op ι) :
    stateQForm ψ (Wᴴ * M * W) = stateQForm (applyOperatorToState W ψ) M := by
  unfold stateQForm
  rw [applyOperatorToState_mul', applyOperatorToState_mul']
  congr 1
  change inner ℂ ψ (Matrix.toEuclideanLin Wᴴ _) =
    inner ℂ (Matrix.toEuclideanLin W ψ) _
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_right]

/-- The squared norm of `W ψ` is the quadratic form of `Wᴴ W`. -/
theorem norm_applyOperatorToState_sq_eq_stateQForm {ι : Type*} [Fintype ι]
    [DecidableEq ι] (ψ : EuclideanSpace ℂ ι) (W : Op ι) :
    ‖applyOperatorToState W ψ‖ ^ 2 = stateQForm ψ (Wᴴ * W) :=
  MagicSquareRigidity.norm_applyOperatorToState_sq W ψ

/-- For two projective measurements, the diagonal overlap in a vector `w` is
the squared norm of `w` minus half the summed squared distances.  This is the
identity behind `fact:agreement` for projective families, blueprint
`blueprint/src/chapter/ch12_qpbt_games.tex:260-272`. -/
theorem sum_stateQForm_mul_eq_of_projective {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι]
    (A B : Measurement α ι) (w : EuclideanSpace ℂ ι)
    (hA : MIPStarRE.QPBT.Measurement.IsProjective A)
    (hB : MIPStarRE.QPBT.Measurement.IsProjective B) :
    ∑ a, stateQForm w (A.effect a * B.effect a) =
      ‖w‖ ^ 2 -
        (1 / 2) * ∑ a, ‖applyOperatorToState (A.effect a - B.effect a) w‖ ^ 2 := by
  classical
  rw [point_distance_eq_two_defect_of_projective A B w hA hB, point_defect_eq]
  ring

/-- An effect of a projective measurement is a contraction. -/
theorem norm_applyOperatorToState_proj_effect_le {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι] (M : Measurement α ι)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) (a : α)
    (v : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState (M.effect a) v‖ ≤ ‖v‖ := by
  refine MagicSquareRigidity.norm_applyOperatorToState_le ?_ v
  rw [(hM a).isSelfAdjoint.isHermitian.eq, (hM a).isIdempotentElem.eq]
  exact measurement_effect_le_one M a

/-- The effects of a projective measurement are square-summable to the
identity. -/
theorem sum_effect_conjTranspose_mul_self_le_one_of_projective {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι] (M : Measurement α ι)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) :
    ∑ a, (M.effect a)ᴴ * M.effect a ≤ 1 := by
  refine le_of_eq ?_
  calc ∑ a, (M.effect a)ᴴ * M.effect a = ∑ a, M.effect a := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [(hM a).isSelfAdjoint.isHermitian.eq, (hM a).isIdempotentElem.eq]
    _ = 1 := M.sum_eq_one

/-! ## The overlap of two placed sandwiches -/

section Abstract

variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]

/-- Formalization-only auxiliary for `lem:qld-4-10`: the product of the two
placed sandwiches is `W_bᴴ (X_1 X_2) W_b` with `W_b = Z_1 Z_2`, whenever the
operators of the two placements commute. -/
theorem sandwich_mul_sandwich_eq (X₁ X₂ : Measurement α ι) (Z₁ Z₂ : Measurement β ι)
    (hXZ : ∀ a b, X₁.effect a * Z₂.effect b = Z₂.effect b * X₁.effect a)
    (hZX : ∀ a b, Z₁.effect b * X₂.effect a = X₂.effect a * Z₁.effect b)
    (hZZ : ∀ b, Z₁.effect b * Z₂.effect b = Z₂.effect b * Z₁.effect b)
    (a : α) (b : β) :
    (Z₁.effect b * X₁.effect a * Z₁.effect b) *
        (Z₂.effect b * X₂.effect a * Z₂.effect b) =
      (Z₁.effect b * Z₂.effect b)ᴴ * (X₁.effect a * X₂.effect a) *
        (Z₁.effect b * Z₂.effect b) := by
  rw [Matrix.conjTranspose_mul, measurement_effect_hermitian,
    measurement_effect_hermitian]
  simp only [Matrix.mul_assoc]
  rw [(show Commute (Z₁.effect b) (Z₂.effect b) from hZZ b).left_comm
      (X₂.effect a * Z₂.effect b),
    (show Commute (X₁.effect a) (Z₂.effect b) from hXZ a b).left_comm,
    (show Commute (Z₁.effect b) (Z₂.effect b) from hZZ b).left_comm,
    (show Commute (Z₁.effect b) (X₂.effect a) from hZX a b).left_comm]

omit [DecidableEq ι] in
/-- Formalization-only auxiliary for `lem:qld-4-10`: the decomposition of
`(X_1 - X_2) Z_1 Z_2` into `Z_1 Z_2 (X_1 - X_2)` and the two commutator
terms. -/
theorem sub_mul_mul_eq_add_commutators (X₁ X₂ Z₁ Z₂ : Op ι)
    (hXZ : X₁ * Z₂ = Z₂ * X₁) (hZX : Z₁ * X₂ = X₂ * Z₁)
    (hZZ : Z₁ * Z₂ = Z₂ * Z₁) :
    (X₁ - X₂) * (Z₁ * Z₂) =
      Z₁ * Z₂ * (X₁ - X₂) + Z₂ * (X₁ * Z₁ - Z₁ * X₁) -
        Z₁ * (X₂ * Z₂ - Z₂ * X₂) := by
  simp only [sub_mul, mul_sub, Matrix.mul_assoc]
  rw [(show Commute Z₂ X₁ from hXZ.symm).left_comm Z₁, ← hZZ,
    (show Commute Z₂ Z₁ from hZZ.symm).left_comm X₁,
    (show Commute Z₁ X₂ from hZX).left_comm Z₂]
  abel

/-- The overlap of the two placed sandwiches, exactly: with
`W_b = Z_1(b) Z_2(b)`,
`∑_{a,b} ⟨ψ, R_1(a,b) R_2(a,b) ψ⟩ = ‖ψ‖^2 - (1/2) ∑_b ‖(Z_1(b) - Z_2(b)) ψ‖^2
  - (1/2) ∑_{a,b} ‖(X_1(a) - X_2(a)) W_b ψ‖^2`.
This replaces the Cauchy--Schwarz chain of displays
`eq:qld-rw-self-cons-1` to `eq:qld-rw-self-cons-4`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:743-790`. -/
theorem sandwich_overlap_identity (ψ : EuclideanSpace ℂ ι)
    (X₁ X₂ : Measurement α ι) (Z₁ Z₂ : Measurement β ι)
    (hX₁ : MIPStarRE.QPBT.Measurement.IsProjective X₁)
    (hX₂ : MIPStarRE.QPBT.Measurement.IsProjective X₂)
    (hZ₁ : MIPStarRE.QPBT.Measurement.IsProjective Z₁)
    (hZ₂ : MIPStarRE.QPBT.Measurement.IsProjective Z₂)
    (hXZ : ∀ a b, X₁.effect a * Z₂.effect b = Z₂.effect b * X₁.effect a)
    (hZX : ∀ a b, Z₁.effect b * X₂.effect a = X₂.effect a * Z₁.effect b)
    (hZZ : ∀ b, Z₁.effect b * Z₂.effect b = Z₂.effect b * Z₁.effect b) :
    ∑ ab : α × β, stateQForm ψ
        ((Z₁.effect ab.2 * X₁.effect ab.1 * Z₁.effect ab.2) *
          (Z₂.effect ab.2 * X₂.effect ab.1 * Z₂.effect ab.2)) =
      ‖ψ‖ ^ 2 -
        (1 / 2) * ∑ b, ‖applyOperatorToState (Z₁.effect b - Z₂.effect b) ψ‖ ^ 2 -
        (1 / 2) * ∑ ab : α × β, ‖applyOperatorToState (X₁.effect ab.1 - X₂.effect ab.1)
          (applyOperatorToState (Z₁.effect ab.2 * Z₂.effect ab.2) ψ)‖ ^ 2 := by
  have hW : ∀ b, ‖applyOperatorToState (Z₁.effect b * Z₂.effect b) ψ‖ ^ 2 =
      stateQForm ψ (Z₁.effect b * Z₂.effect b) := by
    intro b
    rw [norm_applyOperatorToState_sq_eq_stateQForm, Matrix.conjTranspose_mul,
      measurement_effect_hermitian, measurement_effect_hermitian]
    congr 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Z₁.effect b) (Z₁.effect b),
      (hZ₁ b).isIdempotentElem.eq, hZZ b, ← Matrix.mul_assoc,
      (hZ₂ b).isIdempotentElem.eq]
  have hstep : ∀ ab : α × β, stateQForm ψ
      ((Z₁.effect ab.2 * X₁.effect ab.1 * Z₁.effect ab.2) *
        (Z₂.effect ab.2 * X₂.effect ab.1 * Z₂.effect ab.2)) =
      stateQForm (applyOperatorToState (Z₁.effect ab.2 * Z₂.effect ab.2) ψ)
        (X₁.effect ab.1 * X₂.effect ab.1) := by
    intro ab
    rw [sandwich_mul_sandwich_eq X₁ X₂ Z₁ Z₂ hXZ hZX hZZ,
      stateQForm_conjTranspose_mul_mul]
  have hWsum : ∑ b, ‖applyOperatorToState (Z₁.effect b * Z₂.effect b) ψ‖ ^ 2 =
      ‖ψ‖ ^ 2 -
        (1 / 2) * ∑ b, ‖applyOperatorToState (Z₁.effect b - Z₂.effect b) ψ‖ ^ 2 := by
    simp_rw [hW]
    exact sum_stateQForm_mul_eq_of_projective Z₁ Z₂ ψ hZ₁ hZ₂
  calc ∑ ab : α × β, stateQForm ψ
        ((Z₁.effect ab.2 * X₁.effect ab.1 * Z₁.effect ab.2) *
          (Z₂.effect ab.2 * X₂.effect ab.1 * Z₂.effect ab.2))
      = ∑ b, ∑ a, stateQForm (applyOperatorToState (Z₁.effect b * Z₂.effect b) ψ)
          (X₁.effect a * X₂.effect a) := by
        simp_rw [hstep]
        exact Fintype.sum_prod_type_right _
    _ = ∑ b, (‖applyOperatorToState (Z₁.effect b * Z₂.effect b) ψ‖ ^ 2 -
          (1 / 2) * ∑ a, ‖applyOperatorToState (X₁.effect a - X₂.effect a)
            (applyOperatorToState (Z₁.effect b * Z₂.effect b) ψ)‖ ^ 2) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        exact sum_stateQForm_mul_eq_of_projective X₁ X₂ _ hX₁ hX₂
    _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hWsum,
          Fintype.sum_prod_type_right]

/-- The pointwise bound on the consistency defect of the placed sandwiches:
in terms of the distances `D^Z`, `D^X` of the two placements and the placed
commutators `K^1`, `K^2`,
`‖ψ‖^2 - ∑_{a,b} ⟨ψ, R_1 R_2 ψ⟩ ≤ (1/2) D^Z + (3/2) (D^X + K^1 + K^2)`. -/
theorem sandwich_defect_pointwise_le (ψ : EuclideanSpace ℂ ι)
    (X₁ X₂ : Measurement α ι) (Z₁ Z₂ : Measurement β ι)
    (hX₁ : MIPStarRE.QPBT.Measurement.IsProjective X₁)
    (hX₂ : MIPStarRE.QPBT.Measurement.IsProjective X₂)
    (hZ₁ : MIPStarRE.QPBT.Measurement.IsProjective Z₁)
    (hZ₂ : MIPStarRE.QPBT.Measurement.IsProjective Z₂)
    (hXZ : ∀ a b, X₁.effect a * Z₂.effect b = Z₂.effect b * X₁.effect a)
    (hZX : ∀ a b, Z₁.effect b * X₂.effect a = X₂.effect a * Z₁.effect b)
    (hZZ : ∀ b, Z₁.effect b * Z₂.effect b = Z₂.effect b * Z₁.effect b) :
    ‖ψ‖ ^ 2 - ∑ ab : α × β, stateQForm ψ
        ((Z₁.effect ab.2 * X₁.effect ab.1 * Z₁.effect ab.2) *
          (Z₂.effect ab.2 * X₂.effect ab.1 * Z₂.effect ab.2)) ≤
      (1 / 2) * ∑ b, ‖applyOperatorToState (Z₁.effect b - Z₂.effect b) ψ‖ ^ 2 +
        (3 / 2) * ((∑ a, ‖applyOperatorToState (X₁.effect a - X₂.effect a) ψ‖ ^ 2) +
          (∑ ab : α × β, ‖applyOperatorToState
            (X₁.effect ab.1 * Z₁.effect ab.2 -
              Z₁.effect ab.2 * X₁.effect ab.1) ψ‖ ^ 2) +
          ∑ ab : α × β, ‖applyOperatorToState
            (X₂.effect ab.1 * Z₂.effect ab.2 -
              Z₂.effect ab.2 * X₂.effect ab.1) ψ‖ ^ 2) := by
  rw [sandwich_overlap_identity ψ X₁ X₂ Z₁ Z₂ hX₁ hX₂ hZ₁ hZ₂ hXZ hZX hZZ]
  -- the pointwise decomposition of `(X_1 - X_2) W_b ψ`
  have hpt : ∀ ab : α × β,
      ‖applyOperatorToState (X₁.effect ab.1 - X₂.effect ab.1)
          (applyOperatorToState (Z₁.effect ab.2 * Z₂.effect ab.2) ψ)‖ ^ 2 ≤
        3 * (‖applyOperatorToState (Z₂.effect ab.2 *
              (X₁.effect ab.1 - X₂.effect ab.1)) ψ‖ ^ 2 +
          ‖applyOperatorToState
            (X₁.effect ab.1 * Z₁.effect ab.2 -
              Z₁.effect ab.2 * X₁.effect ab.1) ψ‖ ^ 2 +
          ‖applyOperatorToState
            (X₂.effect ab.1 * Z₂.effect ab.2 -
              Z₂.effect ab.2 * X₂.effect ab.1) ψ‖ ^ 2) := by
    intro ab
    obtain ⟨a, b⟩ := ab
    rw [← applyOperatorToState_mul', sub_mul_mul_eq_add_commutators _ _ _ _
      (hXZ a b) (hZX a b) (hZZ b)]
    have hlin : applyOperatorToState
        (Z₁.effect b * Z₂.effect b * (X₁.effect a - X₂.effect a) +
          Z₂.effect b * (X₁.effect a * Z₁.effect b - Z₁.effect b * X₁.effect a) -
          Z₁.effect b * (X₂.effect a * Z₂.effect b - Z₂.effect b * X₂.effect a)) ψ =
        applyOperatorToState (Z₁.effect b)
            (applyOperatorToState (Z₂.effect b * (X₁.effect a - X₂.effect a)) ψ) +
          applyOperatorToState (Z₂.effect b) (applyOperatorToState
            (X₁.effect a * Z₁.effect b - Z₁.effect b * X₁.effect a) ψ) -
          applyOperatorToState (Z₁.effect b) (applyOperatorToState
            (X₂.effect a * Z₂.effect b - Z₂.effect b * X₂.effect a) ψ) := by
      rw [← applyOperatorToState_mul', ← applyOperatorToState_mul',
        ← applyOperatorToState_mul', Matrix.mul_assoc]
      unfold applyOperatorToState
      simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
    rw [hlin]
    set u := applyOperatorToState (Z₁.effect b)
      (applyOperatorToState (Z₂.effect b * (X₁.effect a - X₂.effect a)) ψ)
    set v := applyOperatorToState (Z₂.effect b) (applyOperatorToState
      (X₁.effect a * Z₁.effect b - Z₁.effect b * X₁.effect a) ψ)
    set w := applyOperatorToState (Z₁.effect b) (applyOperatorToState
      (X₂.effect a * Z₂.effect b - Z₂.effect b * X₂.effect a) ψ)
    have hu : ‖u‖ ≤ ‖applyOperatorToState
        (Z₂.effect b * (X₁.effect a - X₂.effect a)) ψ‖ :=
      norm_applyOperatorToState_proj_effect_le Z₁ hZ₁ b _
    have hv : ‖v‖ ≤ ‖applyOperatorToState
        (X₁.effect a * Z₁.effect b - Z₁.effect b * X₁.effect a) ψ‖ :=
      norm_applyOperatorToState_proj_effect_le Z₂ hZ₂ b _
    have hw : ‖w‖ ≤ ‖applyOperatorToState
        (X₂.effect a * Z₂.effect b - Z₂.effect b * X₂.effect a) ψ‖ :=
      norm_applyOperatorToState_proj_effect_le Z₁ hZ₁ b _
    have htri : ‖u + v - w‖ ≤ ‖u‖ + ‖v‖ + ‖w‖ :=
      le_trans (norm_sub_le (u + v) w) (add_le_add (norm_add_le u v) (le_refl ‖w‖))
    have hsq : ‖u + v - w‖ ^ 2 ≤ 3 * (‖u‖ ^ 2 + ‖v‖ ^ 2 + ‖w‖ ^ 2) := by
      nlinarith [sq_nonneg (‖u‖ - ‖v‖), sq_nonneg (‖v‖ - ‖w‖),
        sq_nonneg (‖u‖ - ‖w‖), norm_nonneg (u + v - w), norm_nonneg u,
        norm_nonneg v, norm_nonneg w]
    have hu2 := pow_le_pow_left₀ (norm_nonneg _) hu 2
    have hv2 := pow_le_pow_left₀ (norm_nonneg _) hv 2
    have hw2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
    linarith
  -- the contraction sum over `b`
  have hcontr : ∑ ab : α × β, ‖applyOperatorToState (Z₂.effect ab.2 *
      (X₁.effect ab.1 - X₂.effect ab.1)) ψ‖ ^ 2 ≤
      ∑ a, ‖applyOperatorToState (X₁.effect a - X₂.effect a) ψ‖ ^ 2 := by
    simp only [Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun a _ => ?_
    exact sum_norm_mul_apply_le Z₂.effect (X₁.effect a - X₂.effect a) ψ
      (sum_effect_conjTranspose_mul_self_le_one_of_projective Z₂ hZ₂)
  have hsum := Finset.sum_le_sum fun ab (_ : ab ∈ Finset.univ) => hpt ab
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  linarith

end Abstract

/-! ## The bound for the placed sandwiches -/

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

/-- The pointwise bound on the consistency defect of the sandwich POVM between
two placements, as a function of the point pair: one half of the
`Z`-distance plus three halves of the `X`-distance and of the two placed
commutator sums. -/
def sandwichDefectBound (S : ProjectiveSetting P ε) (p₁ p₂ : Placement)
    (xz : PointPair P) : ℝ :=
  (1 / 2) * ∑ b : PauliScalar P, ‖applyOperatorToState
      (S.place p₁ ((S.pointMeasExp p₁.side .Z xz.2).effect b) -
        S.place p₂ ((S.pointMeasExp p₂.side .Z xz.2).effect b)) S.psiHat‖ ^ 2 +
    (3 / 2) * ((∑ a : PauliScalar P, ‖applyOperatorToState
        (S.place p₁ ((S.pointMeasExp p₁.side .X xz.1).effect a) -
          S.place p₂ ((S.pointMeasExp p₂.side .X xz.1).effect a)) S.psiHat‖ ^ 2) +
      (∑ ab : PauliScalar P × PauliScalar P, ‖applyOperatorToState
        (S.place p₁ ((S.pointMeasExp p₁.side .X xz.1).effect ab.1 *
            (S.pointMeasExp p₁.side .Z xz.2).effect ab.2) -
          S.place p₁ ((S.pointMeasExp p₁.side .Z xz.2).effect ab.2 *
            (S.pointMeasExp p₁.side .X xz.1).effect ab.1)) S.psiHat‖ ^ 2) +
      ∑ ab : PauliScalar P × PauliScalar P, ‖applyOperatorToState
        (S.place p₂ ((S.pointMeasExp p₂.side .X xz.1).effect ab.1 *
            (S.pointMeasExp p₂.side .Z xz.2).effect ab.2) -
          S.place p₂ ((S.pointMeasExp p₂.side .Z xz.2).effect ab.2 *
            (S.pointMeasExp p₂.side .X xz.1).effect ab.1)) S.psiHat‖ ^ 2)

/-- The pointwise bound is nonnegative. -/
theorem sandwichDefectBound_nonneg (S : ProjectiveSetting P ε) (p₁ p₂ : Placement)
    (xz : PointPair P) : 0 ≤ S.sandwichDefectBound p₁ p₂ xz := by
  unfold sandwichDefectBound
  positivity

/-- For a fixed point pair, the off-diagonal mass of the two placed sandwiches
is at most the pointwise bound.  This is the consistency of the sandwich POVM
between opposite placements, display `eq:rw-sc` of the proof of
`lem:qld-4-10`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:743-790`, in
exact form. -/
theorem sandwich_offDiagonal_le_sandwichDefectBound (S : ProjectiveSetting P ε)
    (p₁ p₂ : Placement) (hopp : p₁.IsOpposite p₂) (xz : PointPair P) :
    (∑ ab : PauliScalar P × PauliScalar P, ∑ ab' : PauliScalar P × PauliScalar P,
      if ab = ab' then 0 else stateQForm S.psiHat
        (S.place p₁ ((S.sandwichPoint p₁.side xz.1 xz.2).effect ab) *
          S.place p₂ ((S.sandwichPoint p₂.side xz.1 xz.2).effect ab'))) ≤
      S.sandwichDefectBound p₁ p₂ xz := by
  have hdefect := point_defect_eq
    (S.placedMeasurement p₁ (S.sandwichPoint p₁.side xz.1 xz.2))
    (S.placedMeasurement p₂ (S.sandwichPoint p₂.side xz.1 xz.2)) S.psiHat
  simp only [placedMeasurement_effect] at hdefect
  rw [hdefect, psiHat_norm]
  have hkey := sandwich_defect_pointwise_le S.psiHat
    (S.placedMeasurement p₁ (S.pointMeasExp p₁.side .X xz.1))
    (S.placedMeasurement p₂ (S.pointMeasExp p₂.side .X xz.1))
    (S.placedMeasurement p₁ (S.pointMeasExp p₁.side .Z xz.2))
    (S.placedMeasurement p₂ (S.pointMeasExp p₂.side .Z xz.2))
    (S.placedMeasurement_isProjective p₁ _ (S.pointMeasExp_isProjective _ _ _))
    (S.placedMeasurement_isProjective p₂ _ (S.pointMeasExp_isProjective _ _ _))
    (S.placedMeasurement_isProjective p₁ _ (S.pointMeasExp_isProjective _ _ _))
    (S.placedMeasurement_isProjective p₂ _ (S.pointMeasExp_isProjective _ _ _))
    (fun a b => S.place_comm p₁ p₂ hopp _ _)
    (fun a b => S.place_comm p₁ p₂ hopp _ _)
    (fun b => S.place_comm p₁ p₂ hopp _ _)
  simp only [placedMeasurement_effect, psiHat_norm] at hkey
  unfold sandwichDefectBound
  simp only [sandwichPoint_effect, place_mul]
  simpa only [place_mul] using hkey

/-- The average over the point pair of the pointwise bound is polynomially
small: at most a universal constant times `ε + √ε`.  The `X`- and
`Z`-distances are the self-consistency of item 1 of `lem:qld-comm-cons`, and
the two commutator sums are the field-valued commutation estimate. -/
theorem avg_sandwichDefectBound_le :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
        (p₁ p₂ : Placement), p₁.IsOpposite p₂ →
        avgOver (uniformDistribution (PointPair P)) (S.sandwichDefectBound p₁ p₂) ≤
          C * (ε + Real.sqrt ε) := by
  obtain ⟨C₁, hC₁, h₁⟩ := expPoint_self_cons
  obtain ⟨C₂, hC₂, h₂⟩ := expPoint_comm
  refine ⟨2 * C₁ + 3 * C₂, by linarith, ?_⟩
  intro P ε S p₁ p₂ hopp
  have hε : (0 : ℝ) ≤ ε := by
    have hv := WinImplications.strategy_value_le_one S.toStrategy
    have hw := S.win
    linarith
  have hZ : avgOver (uniformDistribution (PointPair P)) (fun xz =>
      ∑ b : PauliScalar P, ‖applyOperatorToState
        (S.place p₁ ((S.pointMeasExp p₁.side .Z xz.2).effect b) -
          S.place p₂ ((S.pointMeasExp p₂.side .Z xz.2).effect b)) S.psiHat‖ ^ 2) ≤
      C₁ * ε := by
    rw [avgOver_uniform_snd (α := Fin P.m → PauliScalar P)
      (fun z => ∑ b : PauliScalar P, ‖applyOperatorToState
        (S.place p₁ ((S.pointMeasExp p₁.side .Z z).effect b) -
          S.place p₂ ((S.pointMeasExp p₂.side .Z z).effect b)) S.psiHat‖ ^ 2)]
    exact h₁ P ε S p₁ p₂ hopp .Z
  have hX : avgOver (uniformDistribution (PointPair P)) (fun xz =>
      ∑ a : PauliScalar P, ‖applyOperatorToState
        (S.place p₁ ((S.pointMeasExp p₁.side .X xz.1).effect a) -
          S.place p₂ ((S.pointMeasExp p₂.side .X xz.1).effect a)) S.psiHat‖ ^ 2) ≤
      C₁ * ε := by
    rw [avgOver_uniform_fst (β := Fin P.m → PauliScalar P)
      (fun x => ∑ a : PauliScalar P, ‖applyOperatorToState
        (S.place p₁ ((S.pointMeasExp p₁.side .X x).effect a) -
          S.place p₂ ((S.pointMeasExp p₂.side .X x).effect a)) S.psiHat‖ ^ 2)]
    exact h₁ P ε S p₁ p₂ hopp .X
  have hK₁ := h₂ P ε S p₁
  have hK₂ := h₂ P ε S p₂
  unfold opFamilyDistSq at hK₁ hK₂
  unfold sandwichDefectBound
  rw [avgOver_add, avgOver_const_mul, avgOver_const_mul, avgOver_add,
    avgOver_add]
  have hs : (0 : ℝ) ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  nlinarith [hZ, hX, hK₁, hK₂, hs, hε, hC₁, hC₂]

end ProjectiveSetting

end

end MIPStarRE.QPBT
