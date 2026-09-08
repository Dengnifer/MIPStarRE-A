import MIPStarRE.QPBT.Combining.Points.Commutation

/-!
# The sandwich POVM of the expanded point measurements

The first step of the proof of `lem:qld-4-10` combines the two expanded point
measurements into the sandwich POVM
`R^{x,z}_{a,b} = M^{(Point,Z),z}_b M^{(Point,X),x}_a M^{(Point,Z),z}_b`.  The
source forms it from the binary refinements; here it is formed directly with
outcomes in `F_q × F_q`, which the Parseval transfer of
`MIPStarRE/QPBT/Combining/Points/Commutation.lean` makes possible.  This file
defines the POVM, proves that it is close to the ordered product
`M^Z_b M^X_a` by the approximate commutation, and records the consistency of
the ordered products across opposite register placements, which follows from
the self-consistency of each factor.

## Main results

* `ProjectiveSetting.sandwichPoint`: the sandwich POVM.
* `sandwichPoint_ordered_dist_le`: closeness of the sandwich to the ordered
  product on every placement, with the error of `lem:qld-comm-cons`.
* `ordered_cross_dist_le`: the ordered product on one placement is close to
  the reversed ordered product on the opposite placement.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:731-748`
(the sandwich and display `eq:qld-r-2`), blueprint
`blueprint/src/chapter/ch15_qpbt_combining.tex:803-960` (`lem:qld-4-10`); the
route is explained in `docs/paper-gaps/qpbt_linearity-theorem-quotation.tex`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-- Formalization-only auxiliary: applying a product of operators to a state
applies the factors in sequence. -/
theorem applyOperatorToState_mul' {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Op ι) (ψ : EuclideanSpace ℂ ι) :
    applyOperatorToState (A * B) ψ =
      applyOperatorToState A (applyOperatorToState B ψ) := by
  ext k
  change ((A * B) *ᵥ ψ.ofLp) k = (A *ᵥ (B *ᵥ ψ.ofLp)) k
  rw [Matrix.mulVec_mulVec]

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

/-- An expanded point effect is self-adjoint. -/
theorem pointMeasExp_effect_conjTranspose (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (u : Fin P.m → PauliScalar P)
    (a : PauliScalar P) :
    ((S.pointMeasExp side W u).effect a)ᴴ = (S.pointMeasExp side W u).effect a :=
  (S.pointMeasExp_isProjective side W u a).isSelfAdjoint.isHermitian.eq

/-- An expanded point effect is idempotent. -/
theorem pointMeasExp_effect_mul_self (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (u : Fin P.m → PauliScalar P)
    (a : PauliScalar P) :
    (S.pointMeasExp side W u).effect a * (S.pointMeasExp side W u).effect a =
      (S.pointMeasExp side W u).effect a :=
  (S.pointMeasExp_isProjective side W u a).isIdempotentElem.eq

/-- The sandwich `M^Z_b M^X_a M^Z_b` is `(M^X_a M^Z_b)ᴴ (M^X_a M^Z_b)`. -/
theorem sandwich_eq_conjTranspose_mul_self (S : ProjectiveSetting P ε)
    (side : PlayerSide) (x z : Fin P.m → PauliScalar P) (a b : PauliScalar P) :
    (S.pointMeasExp side .Z z).effect b * (S.pointMeasExp side .X x).effect a *
        (S.pointMeasExp side .Z z).effect b =
      ((S.pointMeasExp side .X x).effect a * (S.pointMeasExp side .Z z).effect b)ᴴ *
        ((S.pointMeasExp side .X x).effect a * (S.pointMeasExp side .Z z).effect b) := by
  rw [Matrix.conjTranspose_mul, pointMeasExp_effect_conjTranspose,
    pointMeasExp_effect_conjTranspose, Matrix.mul_assoc _ _
      ((S.pointMeasExp side .X x).effect a * (S.pointMeasExp side .Z z).effect b),
    ← Matrix.mul_assoc ((S.pointMeasExp side .X x).effect a)
      ((S.pointMeasExp side .X x).effect a), pointMeasExp_effect_mul_self,
    ← Matrix.mul_assoc]

/-- The sandwich effects resolve the identity. -/
theorem sum_sandwich_eq_one (S : ProjectiveSetting P ε) (side : PlayerSide)
    (x z : Fin P.m → PauliScalar P) :
    ∑ ab : PauliScalar P × PauliScalar P,
        (S.pointMeasExp side .Z z).effect ab.2 *
          (S.pointMeasExp side .X x).effect ab.1 *
          (S.pointMeasExp side .Z z).effect ab.2 = 1 := by
  rw [Fintype.sum_prod_type_right]
  calc ∑ b : PauliScalar P, ∑ a : PauliScalar P,
        (S.pointMeasExp side .Z z).effect b * (S.pointMeasExp side .X x).effect a *
          (S.pointMeasExp side .Z z).effect b
      = ∑ b : PauliScalar P, (S.pointMeasExp side .Z z).effect b *
          (∑ a : PauliScalar P, (S.pointMeasExp side .X x).effect a) *
          (S.pointMeasExp side .Z z).effect b := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
    _ = 1 := by
        simp_rw [(S.pointMeasExp side .X x).sum_eq_one, mul_one,
          pointMeasExp_effect_mul_self]
        exact (S.pointMeasExp side .Z z).sum_eq_one

/-- The sandwich POVM `R^{x,z}_{a,b} = M^Z_b M^X_a M^Z_b` of the two expanded
point measurements, with outcomes in `F_q × F_q`.  This is the POVM of the
first step of the proof of `lem:qld-4-10`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:731-736`,
formed directly with field-valued outcomes rather than from the binary
refinements; see `docs/paper-gaps/qpbt_linearity-theorem-quotation.tex`. -/
def sandwichPoint (S : ProjectiveSetting P ε) (side : PlayerSide)
    (x z : Fin P.m → PauliScalar P) :
    Measurement (PauliScalar P × PauliScalar P) (S.ExpandedLocalSpace side) :=
  Measurement.ofSumEqOne
    (fun ab => (S.pointMeasExp side .Z z).effect ab.2 *
      (S.pointMeasExp side .X x).effect ab.1 *
      (S.pointMeasExp side .Z z).effect ab.2)
    (fun ab => by
      rw [sandwich_eq_conjTranspose_mul_self]
      exact Matrix.nonneg_iff_posSemidef.mpr
        (Matrix.posSemidef_conjTranspose_mul_self _))
    (sum_sandwich_eq_one S side x z)

/-- The effects of the sandwich POVM. -/
@[simp] theorem sandwichPoint_effect (S : ProjectiveSetting P ε)
    (side : PlayerSide) (x z : Fin P.m → PauliScalar P)
    (ab : PauliScalar P × PauliScalar P) :
    (S.sandwichPoint side x z).effect ab =
      (S.pointMeasExp side .Z z).effect ab.2 *
        (S.pointMeasExp side .X x).effect ab.1 *
        (S.pointMeasExp side .Z z).effect ab.2 := rfl

/-- The sandwich differs from the ordered product `M^Z_b M^X_a` by
`M^Z_b` times the commutator.  This is the algebra behind display
`eq:qld-r-2`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:737-742`. -/
theorem sandwichPoint_effect_sub_ordered (S : ProjectiveSetting P ε)
    (side : PlayerSide) (x z : Fin P.m → PauliScalar P)
    (ab : PauliScalar P × PauliScalar P) :
    (S.sandwichPoint side x z).effect ab -
        (S.pointMeasExp side .Z z).effect ab.2 *
          (S.pointMeasExp side .X x).effect ab.1 =
      (S.pointMeasExp side .Z z).effect ab.2 *
        ((S.pointMeasExp side .X x).effect ab.1 *
            (S.pointMeasExp side .Z z).effect ab.2 -
          (S.pointMeasExp side .Z z).effect ab.2 *
            (S.pointMeasExp side .X x).effect ab.1) := by
  rw [sandwichPoint_effect, mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    pointMeasExp_effect_mul_self]

/-- The sandwich POVM is close to the ordered product `M^Z_b M^X_a` on every
register placement, on average over the point pair, with the error of
`lem:qld-comm-cons`.  This is display `eq:qld-r-2` of the proof of
`lem:qld-4-10`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:737-742`, with
field-valued outcomes. -/
theorem sandwichPoint_ordered_dist_le :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
        (p : Placement),
        opFamilyDistSq (uniformDistribution (PointPair P))
          (fun xz (ab : PauliScalar P × PauliScalar P) => S.place p
            ((S.sandwichPoint p.side xz.1 xz.2).effect ab))
          (fun xz ab => S.place p
            ((S.pointMeasExp p.side .Z xz.2).effect ab.2 *
              (S.pointMeasExp p.side .X xz.1).effect ab.1))
          S.psiHat ≤ C * Real.sqrt ε := by
  obtain ⟨C, hC, h⟩ := expPoint_comm
  refine ⟨C, hC, fun P ε S p => le_trans ?_ (h P ε S p)⟩
  unfold opFamilyDistSq
  refine avgOver_mono _ _ _ fun xz => Finset.sum_le_sum fun ab _ => ?_
  rw [← place_sub, sandwichPoint_effect_sub_ordered, place_mul,
    applyOperatorToState_mul', ← place_sub]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (MagicSquareRigidity.norm_applyOperatorToState_le
      (S.place_conjTranspose_mul_self_le_one p
        (S.pointMeasExp_isProjective p.side .Z xz.2 ab.2)) _) 2

/-- Formalization-only auxiliary: the placed effects of an expanded point
measurement are square-summable to the identity. -/
theorem sum_place_pointMeasExp_conjTranspose_mul_self (S : ProjectiveSetting P ε)
    (p : Placement) (W : PauliKind) (u : Fin P.m → PauliScalar P) :
    ∑ a : PauliScalar P, (S.place p ((S.pointMeasExp p.side W u).effect a))ᴴ *
        S.place p ((S.pointMeasExp p.side W u).effect a) ≤ 1 := by
  refine le_of_eq ?_
  calc ∑ a : PauliScalar P, (S.place p ((S.pointMeasExp p.side W u).effect a))ᴴ *
        S.place p ((S.pointMeasExp p.side W u).effect a)
      = ∑ a : PauliScalar P, S.place p ((S.pointMeasExp p.side W u).effect a) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← place_conjTranspose, ← place_mul, pointMeasExp_effect_conjTranspose,
          pointMeasExp_effect_mul_self]
    _ = 1 := by
        rw [← place_finsetSum, (S.pointMeasExp p.side W u).sum_eq_one, place_one]

/-- The ordered product `M^Z_b M^X_a` on one placement is close to the
reversed ordered product `M^X_a M^Z_b` on the opposite placement, on average
over the point pair, with the self-consistency error of `lem:qld-comm-cons`.
The two factors are transported one at a time, each transport costing the
self-consistency of that factor by `fact:add-a-proj`.  Paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:743-770`
(displays `eq:qld-rw-self-cons-2` and `eq:qld-rw-self-cons-3`), blueprint
`blueprint/src/chapter/ch15_qpbt_combining.tex:851-870`. -/
theorem ordered_cross_dist_le :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
        (p₁ p₂ : Placement), p₁.IsOpposite p₂ →
        opFamilyDistSq (uniformDistribution (PointPair P))
          (fun xz (ab : PauliScalar P × PauliScalar P) => S.place p₁
            ((S.pointMeasExp p₁.side .Z xz.2).effect ab.2 *
              (S.pointMeasExp p₁.side .X xz.1).effect ab.1))
          (fun xz ab => S.place p₂
            ((S.pointMeasExp p₂.side .X xz.1).effect ab.1 *
              (S.pointMeasExp p₂.side .Z xz.2).effect ab.2))
          S.psiHat ≤ C * ε := by
  obtain ⟨C, hC, h⟩ := expPoint_self_cons
  refine ⟨4 * C, by linarith, ?_⟩
  intro P ε S p₁ p₂ hopp
  have hX := h P ε S p₁ p₂ hopp .X
  have hZ := h P ε S p₁ p₂ hopp .Z
  -- the middle family is `M^Z_b` on the first placement times `M^X_a` on the
  -- second; each factor is transported by the self-consistency of that factor
  have h₁ : opFamilyDistSq (uniformDistribution (PointPair P))
      (fun xz (ab : PauliScalar P × PauliScalar P) => S.place p₁
        ((S.pointMeasExp p₁.side .Z xz.2).effect ab.2 *
          (S.pointMeasExp p₁.side .X xz.1).effect ab.1))
      (fun xz ab => S.place p₁ ((S.pointMeasExp p₁.side .Z xz.2).effect ab.2) *
        S.place p₂ ((S.pointMeasExp p₂.side .X xz.1).effect ab.1))
      S.psiHat ≤ C * ε := by
    refine le_trans ?_ (le_of_eq_of_le (avgOver_uniform_fst
      (β := Fin P.m → PauliScalar P)
      (fun x => ∑ a : PauliScalar P, ‖applyOperatorToState
        (S.place p₁ ((S.pointMeasExp p₁.side .X x).effect a) -
          S.place p₂ ((S.pointMeasExp p₂.side .X x).effect a)) S.psiHat‖ ^ 2)) hX)
    unfold opFamilyDistSq
    refine avgOver_mono _ _ _ fun xz => ?_
    have hpt : ∀ ab : PauliScalar P × PauliScalar P,
        S.place p₁ ((S.pointMeasExp p₁.side .Z xz.2).effect ab.2 *
            (S.pointMeasExp p₁.side .X xz.1).effect ab.1) -
          S.place p₁ ((S.pointMeasExp p₁.side .Z xz.2).effect ab.2) *
            S.place p₂ ((S.pointMeasExp p₂.side .X xz.1).effect ab.1) =
          S.place p₁ ((S.pointMeasExp p₁.side .Z xz.2).effect ab.2) *
            (S.place p₁ ((S.pointMeasExp p₁.side .X xz.1).effect ab.1) -
              S.place p₂ ((S.pointMeasExp p₂.side .X xz.1).effect ab.1)) := by
      intro ab
      rw [S.place_mul p₁ ((S.pointMeasExp p₁.side .Z xz.2).effect ab.2)
        ((S.pointMeasExp p₁.side .X xz.1).effect ab.1), mul_sub]
    simp only [hpt, Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun a _ => ?_
    exact DistanceCalculus.sum_norm_mul_apply_le
      (fun b => S.place p₁ ((S.pointMeasExp p₁.side .Z xz.2).effect b))
      (S.place p₁ ((S.pointMeasExp p₁.side .X xz.1).effect a) -
        S.place p₂ ((S.pointMeasExp p₂.side .X xz.1).effect a)) S.psiHat
      (S.sum_place_pointMeasExp_conjTranspose_mul_self p₁ .Z xz.2)
  have h₂ : opFamilyDistSq (uniformDistribution (PointPair P))
      (fun xz (ab : PauliScalar P × PauliScalar P) =>
        S.place p₁ ((S.pointMeasExp p₁.side .Z xz.2).effect ab.2) *
          S.place p₂ ((S.pointMeasExp p₂.side .X xz.1).effect ab.1))
      (fun xz ab => S.place p₂
        ((S.pointMeasExp p₂.side .X xz.1).effect ab.1 *
          (S.pointMeasExp p₂.side .Z xz.2).effect ab.2))
      S.psiHat ≤ C * ε := by
    refine le_trans ?_ (le_of_eq_of_le (avgOver_uniform_snd
      (α := Fin P.m → PauliScalar P)
      (fun z => ∑ b : PauliScalar P, ‖applyOperatorToState
        (S.place p₁ ((S.pointMeasExp p₁.side .Z z).effect b) -
          S.place p₂ ((S.pointMeasExp p₂.side .Z z).effect b)) S.psiHat‖ ^ 2)) hZ)
    unfold opFamilyDistSq
    refine avgOver_mono _ _ _ fun xz => ?_
    have hpt : ∀ ab : PauliScalar P × PauliScalar P,
        S.place p₁ ((S.pointMeasExp p₁.side .Z xz.2).effect ab.2) *
            S.place p₂ ((S.pointMeasExp p₂.side .X xz.1).effect ab.1) -
          S.place p₂ ((S.pointMeasExp p₂.side .X xz.1).effect ab.1 *
            (S.pointMeasExp p₂.side .Z xz.2).effect ab.2) =
          S.place p₂ ((S.pointMeasExp p₂.side .X xz.1).effect ab.1) *
            (S.place p₁ ((S.pointMeasExp p₁.side .Z xz.2).effect ab.2) -
              S.place p₂ ((S.pointMeasExp p₂.side .Z xz.2).effect ab.2)) := by
      intro ab
      rw [S.place_mul p₂ ((S.pointMeasExp p₂.side .X xz.1).effect ab.1)
        ((S.pointMeasExp p₂.side .Z xz.2).effect ab.2),
        S.place_comm p₁ p₂ hopp ((S.pointMeasExp p₁.side .Z xz.2).effect ab.2)
          ((S.pointMeasExp p₂.side .X xz.1).effect ab.1), ← mul_sub]
    simp only [hpt, Fintype.sum_prod_type_right]
    refine Finset.sum_le_sum fun b _ => ?_
    exact DistanceCalculus.sum_norm_mul_apply_le
      (fun a => S.place p₂ ((S.pointMeasExp p₂.side .X xz.1).effect a))
      (S.place p₁ ((S.pointMeasExp p₁.side .Z xz.2).effect b) -
        S.place p₂ ((S.pointMeasExp p₂.side .Z xz.2).effect b)) S.psiHat
      (S.sum_place_pointMeasExp_conjTranspose_mul_self p₂ .X xz.1)
  have htri := opFamilyDistSq_le_of_le_of_le (uniformDistribution (PointPair P))
    _ _ _ S.psiHat (C * ε) (C * ε) h₁ h₂
  linarith

end ProjectiveSetting

end

end MIPStarRE.QPBT
