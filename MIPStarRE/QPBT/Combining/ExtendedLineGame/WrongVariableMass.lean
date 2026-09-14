import MIPStarRE.QPBT.Combining.ExtendedLineGame.ScalarNonlinearMass
import MIPStarRE.QPBT.Combining.PolynomialFiberBounds

/-!
# Wrong-variable mass of rounded polynomial outcomes

The two block orders use the actual projected state vectors and the full
ordered-error sum. A common exceptional coefficient controls all outcomes
of the fixed-block measurement before their weights are summed.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1328-1368`,
`eq:qld-g-separable`, `eq:qld-g-48`, `eq:qld-g-2`, and the two wrong-variable
mass bounds. This supports blueprint `lem:qld-4-7`; it does not establish
the subsequent retained overlaps or global polynomial-pair witness.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus PolynomialImageBounds

noncomputable section

namespace ExtendedLineGame

/-- Actual mass of scalar-linear outcomes whose second coefficient in the
chosen order depends on the varying block. For `false` this is the coefficient
of beta depending on x; for `true` it is the coefficient of alpha depending
on z. These are the two classes in `eq:qld-g-prime-xpt-bound` and
`eq:qld-g-prime-zpt-bound`, supporting blueprint `lem:qld-4-7`. -/
def scalarWrongVariableMass {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (p : Placement)
    (R : DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace p.side))
    (reverse : Bool) : ℝ := by
  classical
  exact ∑ g ∈ Finset.univ.filter (fun g =>
    (∃ r t : MvPolynomial (Fin (2 * P.m)) (PauliScalar P),
      scalarPolynomial P g = MvPolynomial.C r * MvPolynomial.X 0 +
        MvPolynomial.C t * MvPolynomial.X 1) ∧
    ¬ ∃ r, blockCoefficientPolynomial P g
      (Finsupp.single (if reverse then 0 else 1) 1) reverse = MvPolynomial.C r),
    ‖applyOperatorToState (S.place p (R.effect g)) S.psiHat‖ ^ 2

/-- Exact placement and order transport for the common joint scalar sample.
This also transports the retained-overlap calculation in `lem:qld-4-7`. -/
theorem placed_fiber_orderedIndicator {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (p : Placement) (reverse : Bool)
    (x z : Fin P.m → PauliScalar P) (v : Fin 2 → PauliScalar P) (a : PauliScalar P) :
    orderedIndicator
      (S.placedMeasurement p (S.pointMeasExp p.side (if reverse then .Z else .X) x))
      (S.placedMeasurement p (S.pointMeasExp p.side (if reverse then .X else .Z) z))
      (v 0) (v 1) a =
    let y := fiberQuestionEquiv P reverse ((z, x), v)
    S.place p (∑ ab ∈ Finset.univ.filter (fun ab : PauliScalar P × PauliScalar P =>
        y.2.1 * ab.1 + y.2.2 * ab.2 = a),
      if reverse then
        (S.pointMeasExp p.side .Z y.1.2).effect ab.2 *
          (S.pointMeasExp p.side .X y.1.1).effect ab.1
      else
        (S.pointMeasExp p.side .X y.1.1).effect ab.1 *
          (S.pointMeasExp p.side .Z y.1.2).effect ab.2) := by
  dsimp only
  rw [S.place_finsetSum, Finset.sum_filter]
  simp only [orderedIndicator, ProjectiveSetting.placedMeasurement_effect]
  cases reverse
  · simp [fiberQuestionEquiv, ProjectiveSetting.place_mul]
  · apply Fintype.sum_equiv (Equiv.prodComm (PauliScalar P) (PauliScalar P))
    intro ab
    simp [fiberQuestionEquiv, add_comm, ProjectiveSetting.place_mul]

/-- Both wrong-variable classes are bounded in their appropriate actual
ordered errors, for every pair of opposite placements. The common exceptional
coefficient and both `md` degree bounds are derived internally. Completeness
and normalization retain the full outcome sum, so there is no outcome-count
loss. This is the quantitative concentration step of
`eq:qld-g-prime-xpt-bound` and `eq:qld-g-prime-zpt-bound`, supporting
blueprint `lem:qld-4-7`. -/
theorem scalarWrongVariableMass_le_ordered_error {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (p1 p2 : Placement) (hopposite : p1.IsOpposite p2)
    (R : DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace p1.side))
    (hR : Measurement.IsProjective R) (reverse : Bool) :
    scalarWrongVariableMass S p1 R reverse ≤
      2 * extendedPolynomialOrderedError S p1 p2 R reverse +
        2 * (((P.m * P.d + P.m * P.d + 2 : ℕ) : ℝ) / P.q) := by
  classical
  let s := Finset.univ.filter (fun g =>
    (∃ r t : MvPolynomial (Fin (2 * P.m)) (PauliScalar P),
      scalarPolynomial P g = MvPolynomial.C r * MvPolynomial.X 0 +
        MvPolynomial.C t * MvPolynomial.X 1) ∧
    ¬ ∃ r, blockCoefficientPolynomial P g
      (Finsupp.single (if reverse then 0 else 1) 1) reverse = MvPolynomial.C r)
  let ψ := fun g => applyOperatorToState (S.place p1 (R.effect g)) S.psiHat
  let X := fun x : Fin P.m → PauliScalar P => S.placedMeasurement p2
    (S.pointMeasExp p2.side (if reverse then .Z else .X) x)
  let Z := fun z : Fin P.m → PauliScalar P => S.placedMeasurement p2
    (S.pointMeasExp p2.side (if reverse then .X else .Z) z)
  let A := fun (z x : Fin P.m → PauliScalar P) (v : Fin 2 → PauliScalar P) g =>
    applyOperatorToState (orderedIndicator (X x) (Z z) (v 0) (v 1)
      (extendedPolynomialRead P (fiberQuestionEquiv P reverse ((z, x), v)) g)) (ψ g)
  let B : ℝ := ((P.m * P.d + P.m * P.d + 2 : ℕ) : ℝ) / P.q
  have hmass : ∑ g, ‖ψ g‖ ^ 2 = 1 := by
    simpa only [ψ, ProjectiveSetting.placedMeasurement_effect, S.psiHat_norm, one_pow] using
      sum_projective_state_norm_sq (S.placedMeasurement p1 R)
        (S.placedMeasurement_isProjective p1 R hR) S.psiHat
  have hnorm (g) (hg : g ∈ s) :
      avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun z =>
        avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun x =>
          avgOver (uniformDistribution (Fin 2 → PauliScalar P)) (fun v =>
            ‖A z x v g‖ ^ 2))) ≤ B * ‖ψ g‖ ^ 2 := by
    obtain ⟨hlin, hnon⟩ := (Finset.mem_filter.mp hg).2
    have hd := blockCoefficientPolynomial_degrees P g
      (Finsupp.single (if reverse then 0 else 1) 1) reverse
    have h := avg_orderedIndicator_norm_sq_le_of_nonconstant
      (blockCoefficientPolynomial P g (Finsupp.single (if reverse then 0 else 1) 1) reverse)
      hnon hd.1 hd.2
      (fun x z => MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval z)
        (blockCoefficientPolynomial P g
          (Finsupp.single (if reverse then 1 else 0) 1) reverse))) X Z
      (fun x => S.placedMeasurement_isProjective p2 _ (S.pointMeasExp_isProjective _ _ _))
      (fun z => S.placedMeasurement_isProjective p2 _ (S.pointMeasExp_isProjective _ _ _)) (ψ g)
    have hcard : Fintype.card (PauliScalar P) = P.q :=
      @FieldModel.card P.q P.model.toFieldModel
    simpa only [A, scalarPolynomial_linear_read_fiber P g hlin, hcard, B] using h
  have hnormsum :
      avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun z =>
        avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun x =>
          avgOver (uniformDistribution (Fin 2 → PauliScalar P)) (fun v =>
            ∑ g ∈ s, ‖A z x v g‖ ^ 2))) ≤ B := by
    simp_rw [avgOver_finset_sum]
    calc
      _ ≤ ∑ g ∈ s, B * ‖ψ g‖ ^ 2 := Finset.sum_le_sum hnorm
      _ ≤ ∑ g, B * ‖ψ g‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
          intros; dsimp [B]; positivity)
      _ = B := by rw [← Finset.mul_sum, hmass, mul_one]
  have hfull :
      avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun z =>
        avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun x =>
          avgOver (uniformDistribution (Fin 2 → PauliScalar P)) (fun v =>
            ∑ g, ‖ψ g - A z x v g‖ ^ 2))) =
        extendedPolynomialOrderedError S p1 p2 R reverse := by
    rw [← avgOver_uniform_prod (fun z x =>
      avgOver (uniformDistribution (Fin 2 → PauliScalar P)) (fun v =>
        ∑ g, ‖ψ g - A z x v g‖ ^ 2))]
    rw [← avgOver_uniform_prod
      (fun zx : (Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P) =>
        fun v => ∑ g, ‖ψ g - A zx.1 zx.2 v g‖ ^ 2)]
    unfold extendedPolynomialOrderedError
    rw [avgOver_uniform_equiv (fiberQuestionEquiv P reverse).symm]
    apply avgOver_congr
    rintro ⟨⟨z, x⟩, v⟩
    apply Finset.sum_congr rfl
    intro g _
    dsimp only [A, X, Z]
    rw [placed_fiber_orderedIndicator]
    dsimp only [ψ]
    rw [placed_residual S p1 p2 hopposite]
    rfl
  have herror :
      avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun z =>
        avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun x =>
          avgOver (uniformDistribution (Fin 2 → PauliScalar P)) (fun v =>
            ∑ g ∈ s, ‖ψ g - A z x v g‖ ^ 2))) ≤
        extendedPolynomialOrderedError S p1 p2 R reverse := by
    rw [← hfull]
    apply avgOver_mono
    intro z
    apply avgOver_mono
    intro x
    apply avgOver_mono
    intro v
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
      intros; exact sq_nonneg _)
  have h := avgOver_mono (uniformDistribution (Fin P.m → PauliScalar P)) _ _ fun z =>
    avgOver_mono (uniformDistribution (Fin P.m → PauliScalar P)) _ _ fun x =>
      avgOver_mono (uniformDistribution (Fin 2 → PauliScalar P)) _ _ fun v =>
        sum_mass_le_residual_add_image s ψ (A z x v)
  simp only [avgOver_uniform_const, avgOver_add, avgOver_const_mul] at h
  change scalarWrongVariableMass S p1 R reverse ≤ _ at h
  change scalarWrongVariableMass S p1 R reverse ≤ _ + 2 * B
  linarith

/-- The actual rounded measurements satisfy both wrong-variable mass bounds,
with both player placements and both ordered estimates preserved. The scalar
nonlinear estimate is retained for the union of the three unwanted classes.
All errors are the errors of direct soundness and rounding, including the
line-witness contribution. The directly indexed completed-answer restriction
remains explicit, as in `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
and `docs/paper-gaps/qpbt_combined-lines-error-term.tex`. This supports the
two wrong-variable displays in blueprint `lem:qld-4-7`; it does not supply
the retained point overlaps or the global-pair witness. -/
theorem exists_rounded_polynomial_wrong_variable_mass :
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
        (∀ reverse : Bool,
          extendedPolynomialOrderedError S .AA' .BA'' RA reverse ≤ 4 * eta + 8 * δQ ∧
          extendedPolynomialOrderedError S .BB' .AB'' RB reverse ≤ 4 * eta + 8 * δQ) ∧
        scalarNonlinearMass S .AA' RA ≤ 2 * (4 * eta + 8 * δQ) +
          2 * (((2 * P.m + 2) * P.d + 1 : ℕ) : ℝ) / P.q ∧
        scalarNonlinearMass S .BB' RB ≤ 2 * (4 * eta + 8 * δQ) +
          2 * (((2 * P.m + 2) * P.d + 1 : ℕ) : ℝ) / P.q ∧
        (∀ reverse : Bool,
          scalarWrongVariableMass S .AA' RA reverse ≤ 2 * (4 * eta + 8 * δQ) +
            2 * (((P.m * P.d + P.m * P.d + 2 : ℕ) : ℝ) / P.q) ∧
          scalarWrongVariableMass S .BB' RB reverse ≤ 2 * (4 * eta + 8 * δQ) +
            2 * (((P.m * P.d + P.m * P.d + 2 : ℕ) : ℝ) / P.q)) := by
  obtain ⟨a, b, ha, hb, hb1, h⟩ := exists_rounded_polynomial_scalar_mass
  refine ⟨a, b, ha, hb, hb1, ?_⟩
  intro P ε δQ δL S points lines delta eta
  obtain ⟨RA, RB, hRA, hRB, horder, hNA, hNB⟩ := h P ε δQ δL S points lines
  refine ⟨RA, RB, hRA, hRB, horder, hNA, hNB, ?_⟩
  intro reverse
  constructor
  · exact (scalarWrongVariableMass_le_ordered_error S .AA' .BA''
      (by trivial) RA hRA reverse).trans (add_le_add
        (mul_le_mul_of_nonneg_left (horder reverse).1 (by norm_num : (0 : ℝ) ≤ 2)) le_rfl)
  · exact (scalarWrongVariableMass_le_ordered_error S .BB' .AB''
      (by trivial) RB hRB reverse).trans (add_le_add
        (mul_le_mul_of_nonneg_left (horder reverse).2 (by norm_num : (0 : ℝ) ≤ 2)) le_rfl)

/-- Mass outside the existing bounded polynomial-pair combining image after
the canonical field transport. This is the actual separated image of
`eq:qld-g-non-separable` and `def:combine-map`, supporting blueprint
`lem:qld-4-7`; no completion or overlap assertion is included. -/
def separatedPolynomialMass {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (p : Placement)
    (R : DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace p.side)) : ℝ := by
  classical
  exact ∑ g ∈ Finset.univ.filter (fun g => ¬ ∃ pair : PolyPair P,
      MvPolynomial.map (extendedDirectScalarEquiv P).toRingHom (g (0 : Fin 1)).1 =
        combinePoly pair.1.1 pair.2.1),
    ‖applyOperatorToState (S.place p (R.effect g)) S.psiHat‖ ^ 2

private theorem separatedPolynomialMass_le_three_masses {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (p : Placement)
    (R : DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace p.side)) :
    separatedPolynomialMass S p R ≤ scalarNonlinearMass S p R +
      scalarWrongVariableMass S p R false + scalarWrongVariableMass S p R true := by
  classical
  simp only [separatedPolynomialMass, scalarNonlinearMass, scalarWrongVariableMass,
    Finset.sum_filter, Bool.false_eq_true, ↓reduceIte]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro g _
  by_cases hlin : ∃ r t : MvPolynomial (Fin (2 * P.m)) (PauliScalar P),
      scalarPolynomial P g = MvPolynomial.C r * MvPolynomial.X 0 +
        MvPolynomial.C t * MvPolynomial.X 1
  · by_cases hX : ∃ r, blockCoefficientPolynomial P g (Finsupp.single 0 1) true =
        MvPolynomial.C r
    · by_cases hZ : ∃ r, blockCoefficientPolynomial P g (Finsupp.single 1 1) false =
          MvPolynomial.C r
      · have himage := exists_polyPair_of_scalar_separated P g hlin hX hZ
        simp only [hlin, hX, hZ, not_true_eq_false, and_false, ↓reduceIte, zero_add]
        split_ifs with hout
        · exact le_rfl
        · exact False.elim (hout himage)
      · simp only [hlin, hX, hZ, not_false_eq_true, not_true_eq_false, and_true,
          and_false, ↓reduceIte, zero_add, add_zero]
        split_ifs <;> nlinarith [sq_nonneg ‖applyOperatorToState (S.place p (R.effect g)) S.psiHat‖]
    · simp only [hlin, hX, not_false_eq_true, not_true_eq_false, true_and, ↓reduceIte,
        zero_add]
      split_ifs <;> nlinarith [sq_nonneg ‖applyOperatorToState (S.place p (R.effect g)) S.psiHat‖]
  · simp only [hlin, not_false_eq_true, false_and, ↓reduceIte, add_zero]
    split_ifs <;> nlinarith [sq_nonneg ‖applyOperatorToState (S.place p (R.effect g)) S.psiHat‖]

/-- The union of the three excluded classes is bounded in the actual two
ordered errors. The image is the existing faithful `combinePoly` encoding
with both components in `Poly P`. This proves concentration only, as in
`eq:qld-g-non-separable`, supporting blueprint `lem:qld-4-7`. -/
theorem separatedPolynomialMass_le_ordered_errors {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (p1 p2 : Placement) (hopposite : p1.IsOpposite p2)
    (R : DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace p1.side))
    (hR : Measurement.IsProjective R) :
    separatedPolynomialMass S p1 R ≤
      4 * extendedPolynomialOrderedError S p1 p2 R false +
      2 * extendedPolynomialOrderedError S p1 p2 R true +
      (((12 * P.m * P.d + 4 * P.d + 10 : ℕ) : ℝ) / P.q) := by
  have h := separatedPolynomialMass_le_three_masses S p1 R
  have hN := scalarNonlinearMass_le_ordered_error S p1 p2 hopposite R hR
  have hX := scalarWrongVariableMass_le_ordered_error S p1 p2 hopposite R hR true
  have hZ := scalarWrongVariableMass_le_ordered_error S p1 p2 hopposite R hR false
  refine h.trans ((add_le_add (add_le_add hN hZ) hX).trans_eq ?_)
  push_cast
  ring

/-- Both actual rounded measurements concentrate on faithful separated
polynomial pairs, with error `6E + (12md + 4d + 10)/q` and
`E = 4eta + 8deltaQ`. The same measurements retain both ordered estimates.
The point and directly indexed completed-answer line witnesses are precisely
the inputs of the preceding rounded constructor, with the same documented
domain restriction. This proves `eq:qld-g-non-separable`, supporting
blueprint `lem:qld-4-7`, without claiming the subsequent retained overlaps
or the source global-pair witness. -/
theorem exists_rounded_polynomial_separated_mass :
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
        (∀ reverse : Bool,
          extendedPolynomialOrderedError S .AA' .BA'' RA reverse ≤ 4 * eta + 8 * δQ ∧
          extendedPolynomialOrderedError S .BB' .AB'' RB reverse ≤ 4 * eta + 8 * δQ) ∧
        separatedPolynomialMass S .AA' RA ≤ 6 * (4 * eta + 8 * δQ) +
          (((12 * P.m * P.d + 4 * P.d + 10 : ℕ) : ℝ) / P.q) ∧
        separatedPolynomialMass S .BB' RB ≤ 6 * (4 * eta + 8 * δQ) +
          (((12 * P.m * P.d + 4 * P.d + 10 : ℕ) : ℝ) / P.q) := by
  obtain ⟨a, b, ha, hb, hb1, h⟩ := exists_rounded_polynomial_ordered_estimates
  refine ⟨a, b, ha, hb, hb1, ?_⟩
  intro P ε δQ δL S points lines delta eta
  obtain ⟨RA, RB, hRA, hRB, horder⟩ := h P ε δQ δL S points lines
  refine ⟨RA, RB, hRA, hRB, horder, ?_, ?_⟩
  · have hA := separatedPolynomialMass_le_ordered_errors S .AA' .BA'' (by trivial) RA hRA
    have h0 := (horder false).1
    have h1 := (horder true).1
    linarith
  · have hB := separatedPolynomialMass_le_ordered_errors S .BB' .AB'' (by trivial) RB hRB
    have h0 := (horder false).2
    have h1 := (horder true).2
    linarith

end ExtendedLineGame

end

end MIPStarRE.QPBT
