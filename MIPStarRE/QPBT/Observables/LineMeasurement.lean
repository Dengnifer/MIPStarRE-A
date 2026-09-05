import MIPStarRE.QPBT.Observables.PointConsistency
import MIPStarRE.QPBT.Observables.LineMeasurement.Expanded

/-!
# Expanded line measurements

This module restricts low-degree encodings to canonical lines, constructs the
expanded line measurements by convolution, and records their consistency with
the expanded point measurements on all four register placements.

The construction is split over the submodules `LineMeasurement.Restriction`
(restriction of low-degree encodings to lines and its degree bound),
`LineMeasurement.Projector` (the Pauli-register line projectors), and
`LineMeasurement.Expanded` (the convolution measurement, its projectivity, and
its vanishing outside the degree-`d` outcomes on axis lines). This file states
the three consistency conclusions and the source's existential form.

## References

The declarations formalize `def:expanded-line-measurement` and
`lem:qld-comm-line-cons` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:1034-1210`. Their paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:506-679`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-- The square-root error exhibited by the expanded-line consistency proof.
This is the final quantitative conclusion of `lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:657-679`, blueprint
`ch14_qpbt_observables.tex:1082-1210`. -/
noncomputable def deltaLine (ε : ℝ) : ℝ :=
  Real.sqrt ε

/-- The concrete expanded-line error is polynomially small. This discharges
the error-function component of `lem:qld-comm-line-cons`, using the value
proved at paper `14_analysis_of_the_pauli_basis_test.tex:657-679`, blueprint
`ch14_qpbt_observables.tex:1082-1210`. -/
theorem deltaLine_isPolyErr : IsPolyErr deltaLine := by
  refine ⟨1, (2 : ℝ)⁻¹, le_rfl, by positivity, ?_⟩
  intro x hx
  constructor
  · exact Real.sqrt_nonneg x
  · rw [deltaLine, Real.sqrt_eq_rpow]
    simp

/-- The three conclusions of expanded-line consistency at an abstract error
function. This proposition collects the full existential content of
`lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:559-679`, blueprint
`ch14_qpbt_observables.tex:1082-1210`. -/
def ExpandedLineConclusions (δ : ℝ → ℝ) : Prop :=
  (∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
      (side : PlayerSide) (W : PauliKind) (line : LineDesc P.toLdParams),
      MIPStarRE.QPBT.Measurement.IsProjective
        (S.lineMeasExp side W line)) ∧
  (∃ C : ℝ, 1 ≤ C ∧
    ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
      (p₁ p₂ : Placement), p₁.IsOpposite p₂ → ∀ W : PauliKind,
      opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample f => S.place p₁
          ((S.lineMeasExp p₁.side W sample.1).effect f))
        (fun sample f => S.place p₂
          ((S.lineMeasExp p₂.side W sample.1).effect f))
        S.psiHat ≤ C * δ ε) ∧
  (∃ C : ℝ, 1 ≤ C ∧
    ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
      (p₁ p₂ : Placement), p₁.IsOpposite p₂ → ∀ W : PauliKind,
      opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample f => S.place p₁
          ((S.lineMeasExp p₁.side W sample.1).effect f))
        (fun sample f =>
          S.place p₁ ((S.lineMeasExp p₁.side W sample.1).effect f) *
            S.place p₂ (S.expPointEffectAtLineAnswer p₂.side W
              sample.1 sample.2 f))
        S.psiHat ≤ C * δ ε) ∧
  (∃ C : ℝ, 1 ≤ C ∧
    ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
      (p₁ p₂ : Placement), p₁.IsOpposite p₂ → ∀ W : PauliKind,
      opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample a => S.place p₁
          ((S.lineEvalMeasExp p₁.side W sample.1 sample.2).effect a))
        (fun sample a => S.place p₂
          ((S.pointMeasExpOption p₂.side W sample.2).effect a))
        S.psiHat ≤ C * δ ε)

/-- Expanded line measurements are self-consistent for each of the four
directed opposite-placement pairs. The universal constant precedes all test
parameters and strategies. This is item 1 of `lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:559-568`, blueprint
`ch14_qpbt_observables.tex:1082-1102`. -/
theorem expLine_self_cons :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
        (p₁ p₂ : Placement), p₁.IsOpposite p₂ → ∀ W : PauliKind,
        opFamilyDistSq (linePointDist P.toLdParams)
          (fun sample f => S.place p₁
            ((S.lineMeasExp p₁.side W sample.1).effect f))
          (fun sample f => S.place p₂
            ((S.lineMeasExp p₂.side W sample.1).effect f))
          S.psiHat ≤ C * deltaLine ε := by
  sorry

/-- An expanded line effect is consistent with itself followed by the
expanded point effect selected by its value at the sampled point, with the
common square-root error. This is item 2 of `lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:569-620`, blueprint
`ch14_qpbt_observables.tex:1103-1119`. -/
theorem expLine_point_cons :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
        (p₁ p₂ : Placement), p₁.IsOpposite p₂ → ∀ W : PauliKind,
        opFamilyDistSq (linePointDist P.toLdParams)
          (fun sample f => S.place p₁
            ((S.lineMeasExp p₁.side W sample.1).effect f))
          (fun sample f =>
            S.place p₁ ((S.lineMeasExp p₁.side W sample.1).effect f) *
              S.place p₂ (S.expPointEffectAtLineAnswer p₂.side W
                sample.1 sample.2 f))
          S.psiHat ≤ C * deltaLine ε := by
  sorry

/-- Evaluation classes of expanded line measurements are consistent with the
completed expanded point family, including the `none` class. This is item 3 of
`lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:621-679`, blueprint
`ch14_qpbt_observables.tex:1120-1210`. -/
theorem expLine_point_cons' :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
        (p₁ p₂ : Placement), p₁.IsOpposite p₂ → ∀ W : PauliKind,
        opFamilyDistSq (linePointDist P.toLdParams)
          (fun sample a => S.place p₁
            ((S.lineEvalMeasExp p₁.side W sample.1 sample.2).effect a))
          (fun sample a => S.place p₂
            ((S.pointMeasExpOption p₂.side W sample.2).effect a))
          S.psiHat ≤ C * deltaLine ε := by
  sorry

/-- The source's existential polynomial-error form, derived from the concrete
expanded-line witnesses and square-root error. This is
`lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:506-679`, blueprint
`ch14_qpbt_observables.tex:1082-1210`. -/
theorem exists_deltaLine :
    ∃ δ : ℝ → ℝ, IsPolyErr δ ∧ ExpandedLineConclusions δ := by
  refine ⟨deltaLine, deltaLine_isPolyErr, ?_⟩
  exact ⟨fun P ε S side W line => S.lineMeasExp_isProjective side W line,
    expLine_self_cons, expLine_point_cons, expLine_point_cons'⟩

end


end MIPStarRE.QPBT
