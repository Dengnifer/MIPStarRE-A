import MIPStarRE.QPBT.Combining.ExtendedLineGame.ScalarPolynomial
import MIPStarRE.QPBT.Combining.PolynomialImageBounds

/-!
# Scalar-nonlinear mass of the actual rounded measurements

The full polynomial-outcome ordered estimate is composed with the concentration
proof recovered from PR296. Opposite placements commute; no symmetry of the
player spaces is required. Projectivity retains the actual outcome masses.

## References

`eq:qld-g-42`, `eq:qld-g-prime`, and `eq:qld-g-prime-bound`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1283-1326`.
PR296 proof provenance: `2c8f147643d151d8616864cf49817dc6422a9a86`.
This is only scalar-linearity concentration; issue #513 still requires both
variable-separation estimates and retained overlaps.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus PolynomialImageBounds

noncomputable section

namespace ExtendedLineGame

/-- Actual mass of outcomes outside `alpha*g1(x,z) + beta*g2(x,z)`. The
coefficients may still depend on both base blocks. -/
def scalarNonlinearMass {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (p : Placement)
    (R : DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace p.side)) : ℝ := by
  classical
  exact ∑ g ∈ Finset.univ.filter (fun g => ¬ ∃ r t : MvPolynomial (Fin (2 * P.m))
      (PauliScalar P), scalarPolynomial P g =
        MvPolynomial.C r * MvPolynomial.X 0 + MvPolynomial.C t * MvPolynomial.X 1),
    ‖applyOperatorToState (S.place p (R.effect g)) S.psiHat‖ ^ 2

private theorem placed_orderedIndicator {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (p : Placement) (x : ExtendedPointQuestion P)
    (a : PauliScalar P) :
    orderedIndicator (S.placedMeasurement p (S.pointMeasExp p.side .X x.1.1))
      (S.placedMeasurement p (S.pointMeasExp p.side .Z x.1.2)) x.2.1 x.2.2 a =
    S.place p (∑ ab ∈ Finset.univ.filter (fun ab : PauliScalar P × PauliScalar P =>
        x.2.1 * ab.1 + x.2.2 * ab.2 = a),
      (S.pointMeasExp p.side .X x.1.1).effect ab.1 *
        (S.pointMeasExp p.side .Z x.1.2).effect ab.2) := by
  rw [S.place_finsetSum, Finset.sum_filter]
  simp only [orderedIndicator, ProjectiveSetting.placedMeasurement_effect,
    ProjectiveSetting.place_mul]

/-- Opposite placements commute, identifying the residual on the actual
projected state with the ordered-error residual. This supports both orders
of `eq:qld-g-42/43` and blueprint `lem:qld-4-7`. -/
theorem placed_residual {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (p1 p2 : Placement) (hopposite : p1.IsOpposite p2)
    (R : Op (S.ExpandedLocalSpace p1.side)) (T : Op (S.ExpandedLocalSpace p2.side)) :
    applyOperatorToState (S.place p1 R) S.psiHat -
      applyOperatorToState (S.place p2 T)
        (applyOperatorToState (S.place p1 R) S.psiHat) =
      applyOperatorToState (S.place p1 R * (1 - S.place p2 T)) S.psiHat := by
  rw [← applyOperatorToState_mul, ← S.place_comm p1 p2 hopposite R T, mul_sub, mul_one]
  simp only [applyOperatorToState, map_sub, LinearMap.sub_apply]

/-- The scalar-nonlinear outcome mass is bounded by twice the actual full
ordered error plus `2*((2m+2)d+1)/q`. All transports and degree bounds are
derived internally from the actual singleton outcomes. This auxiliary applies
to every opposite placement of a complete projective measurement. -/
theorem scalarNonlinearMass_le_ordered_error {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (p1 p2 : Placement) (hopposite : p1.IsOpposite p2)
    (R : DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace p1.side))
    (hR : Measurement.IsProjective R) :
    scalarNonlinearMass S p1 R ≤ 2 * extendedPolynomialOrderedError S p1 p2 R false +
      2 * (((2 * P.m + 2) * P.d + 1 : ℕ) : ℝ) / P.q := by
  classical
  let s := Finset.univ.filter (fun g => ¬ ∃ r t : MvPolynomial (Fin (2 * P.m))
      (PauliScalar P), scalarPolynomial P g =
        MvPolynomial.C r * MvPolynomial.X 0 + MvPolynomial.C t * MvPolynomial.X 1)
  let ψ := fun g => applyOperatorToState (S.place p1 (R.effect g)) S.psiHat
  let X := fun u : Fin (2 * P.m) → PauliScalar P => S.placedMeasurement p2
    (S.pointMeasExp p2.side .X (fun i => u ((baseCoordinateEquiv P.m).symm (.inl i))))
  let Z := fun u : Fin (2 * P.m) → PauliScalar P => S.placedMeasurement p2
    (S.pointMeasExp p2.side .Z (fun i => u ((baseCoordinateEquiv P.m).symm (.inr i))))
  have hX : ∀ u, Measurement.IsProjective (X u) := fun u =>
    S.placedMeasurement_isProjective p2 _ (S.pointMeasExp_isProjective _ _ _)
  have hZ : ∀ u, Measurement.IsProjective (Z u) := fun u =>
    S.placedMeasurement_isProjective p2 _ (S.pointMeasExp_isProjective _ _ _)
  have h := nonlinear_mass_le_ordered_error s (scalarPolynomial P)
    (fun g hg => (Finset.mem_filter.mp hg).2) X Z hX hZ ψ
  have hmass : ∑ g, ‖ψ g‖ ^ 2 = 1 := by
    simpa only [ψ, ProjectiveSetting.placedMeasurement_effect, S.psiHat_norm, one_pow] using
      sum_projective_state_norm_sq (S.placedMeasurement p1 R)
        (S.placedMeasurement_isProjective p1 R hR) S.psiHat
  have hdegree : (∑ g ∈ s,
      (((scalarPolynomial P g).support.sup fun e =>
          ((scalarPolynomial P g).coeff e).totalDegree) +
        max 1 (scalarPolynomial P g).totalDegree + 1 : ℕ) /
          (Fintype.card (PauliScalar P) : ℝ) * ‖ψ g‖ ^ 2) ≤
      (((2 * P.m + 2) * P.d + 1 : ℕ) : ℝ) / P.q := by
    have hcard : Fintype.card (PauliScalar P) = P.q :=
      @FieldModel.card P.q P.model.toFieldModel
    rw [hcard]
    calc
      _ ≤ ∑ g ∈ s, ((((2 * P.m + 2) * P.d + 1 : ℕ) : ℝ) / P.q) * ‖ψ g‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro g _
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        exact_mod_cast scalarPolynomial_degree_term_le P g
      _ ≤ ∑ g, ((((2 * P.m + 2) * P.d + 1 : ℕ) : ℝ) / P.q) * ‖ψ g‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
          intros; positivity)
      _ = _ := by rw [← Finset.mul_sum, hmass, mul_one]
  let f := fun (u : Fin (2 * P.m) → PauliScalar P) (v : Fin 2 → PauliScalar P) g =>
    ‖ψ g - applyOperatorToState (orderedIndicator (X u) (Z u) (v 0) (v 1)
      (MvPolynomial.eval v (MvPolynomial.map (MvPolynomial.eval u)
        (scalarPolynomial P g)))) (ψ g)‖ ^ 2
  have hfull : avgOver (uniformDistribution (Fin (2 * P.m) → PauliScalar P)) (fun u =>
      avgOver (uniformDistribution (Fin 2 → PauliScalar P)) (fun v => ∑ g, f u v g)) =
        extendedPolynomialOrderedError S p1 p2 R false := by
    rw [← avgOver_uniform_prod (fun u v => ∑ g, f u v g)]
    unfold extendedPolynomialOrderedError
    rw [avgOver_uniform_equiv (scalarBaseQuestionEquiv P).symm]
    apply avgOver_congr
    rintro ⟨u, v⟩
    apply Finset.sum_congr rfl
    intro g _
    dsimp only [f]
    rw [scalarPolynomial_eval]
    have hXZ : orderedIndicator (X u) (Z u) (v 0) (v 1)
        (extendedPolynomialRead P (scalarBaseQuestionEquiv P (u, v)) g) =
        orderedIndicator
          (S.placedMeasurement p2 (S.pointMeasExp p2.side .X
            (scalarBaseQuestionEquiv P (u, v)).1.1))
          (S.placedMeasurement p2 (S.pointMeasExp p2.side .Z
            (scalarBaseQuestionEquiv P (u, v)).1.2))
          (scalarBaseQuestionEquiv P (u, v)).2.1
          (scalarBaseQuestionEquiv P (u, v)).2.2
          (extendedPolynomialRead P (scalarBaseQuestionEquiv P (u, v)) g) := by
      simp [X, Z, scalarBaseQuestionEquiv, Equiv.piCongrLeft_apply]
    rw [hXZ, placed_orderedIndicator]
    dsimp only [ψ]
    rw [placed_residual S p1 p2 hopposite]
    rfl
  have herror : avgOver (uniformDistribution (Fin (2 * P.m) → PauliScalar P)) (fun u =>
      avgOver (uniformDistribution (Fin 2 → PauliScalar P)) (fun v => ∑ g ∈ s, f u v g)) ≤
        extendedPolynomialOrderedError S p1 p2 R false := by
    rw [← hfull]
    apply avgOver_mono
    intro u
    apply avgOver_mono
    intro v
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
      intros; exact sq_nonneg _)
  change scalarNonlinearMass S p1 R ≤ 2 * _ + 2 * _ at h
  have hout := h.trans (add_le_add
    (mul_le_mul_of_nonneg_left herror (by norm_num : (0 : ℝ) ≤ 2))
    (mul_le_mul_of_nonneg_left hdegree (by norm_num : (0 : ℝ) ≤ 2)))
  simpa only [mul_div_assoc] using hout

/-- Actual rounded measurements satisfy scalar-linearity concentration for both
player placements, with all point, line, soundness, and rounding errors retained.
The measurements are produced by `exists_rounded_polynomial_ordered_estimates`;
neither an ordered estimate nor a mass bound is an assumption. Both ordered
estimates remain available for the subsequent variable-separation argument.

The directly indexed, completed-answer line witness is an explicit restriction
of this auxiliary, as documented in `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
and `docs/paper-gaps/qpbt_combined-lines-error-term.tex`. This proves only the
scalar-linearity calculation `eq:qld-g-prime-bound`, not `lem:qld-4-7`. -/
theorem exists_rounded_polynomial_scalar_mass :
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
          2 * (((2 * P.m + 2) * P.d + 1 : ℕ) : ℝ) / P.q := by
  obtain ⟨a, b, ha, hb, hb1, h⟩ := exists_rounded_polynomial_ordered_estimates
  refine ⟨a, b, ha, hb, hb1, ?_⟩
  intro P ε δQ δL S points lines delta eta
  obtain ⟨RA, RB, hRA, hRB, horder⟩ := h P ε δQ δL S points lines
  refine ⟨RA, RB, hRA, hRB, horder, ?_, ?_⟩
  · exact (scalarNonlinearMass_le_ordered_error S .AA' .BA'' (by trivial) RA hRA).trans
      (add_le_add
        (mul_le_mul_of_nonneg_left (horder false).1 (by norm_num : (0 : ℝ) ≤ 2)) le_rfl)
  · exact (scalarNonlinearMass_le_ordered_error S .BB' .AB'' (by trivial) RB hRB).trans
      (add_le_add
        (mul_le_mul_of_nonneg_left (horder false).2 (by norm_num : (0 : ℝ) ≤ 2)) le_rfl)

end ExtendedLineGame

end

end MIPStarRE.QPBT
