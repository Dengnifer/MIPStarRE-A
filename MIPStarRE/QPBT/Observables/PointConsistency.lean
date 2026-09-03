import MIPStarRE.QPBT.Games.ErrorFunctions
import MIPStarRE.QPBT.Observables.Anticommuting
import MIPStarRE.QPBT.Observables.ExpandedDefs

/-!
# Expanded point consistency and commutation

This module records the quantitative conclusions for the expanded point
measurements on each of the four register placements. No symmetry-transfer
principle is assumed: the four placements occur explicitly in the statements.

## References

The declarations formalize `lem:qld-comm-cons` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:932-1032`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:452-505`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-- The four directed cross-party placement pairs asserted by the source's
“symmetric equivalents” clause. The relation lists the two orientations of
each of the `AA'`--`BA''` and `BB'`--`AB''` pairs; paper
`14_analysis_of_the_pauli_basis_test.tex:420-450`, blueprint
`ch14_qpbt_observables.tex:876-922`. -/
def Placement.IsOpposite : Placement → Placement → Prop
  | .AA', .BA'' => True
  | .BA'', .AA' => True
  | .BB', .AB'' => True
  | .AB'', .BB' => True
  | _, _ => False

/-- The square-root error obtained by the expanded-observable commutation
argument in `lem:qld-comm-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:475-505`, blueprint
`ch14_qpbt_observables.tex:932-1032`. -/
noncomputable def deltaAnticom (ε : ℝ) : ℝ :=
  Real.sqrt ε

/-- The concrete square-root error is polynomially small in the sense used by
chapters 14 and 15. This discharges the error-function part of
`lem:qld-comm-cons`, blueprint `ch14_qpbt_observables.tex:932-1032`, from the
explicit value proved at paper `14_analysis_of_the_pauli_basis_test.tex:503-505`. -/
theorem deltaAnticom_isPolyErr : IsPolyErr deltaAnticom := by
  refine ⟨1, (2 : ℝ)⁻¹, le_rfl, by positivity, ?_⟩
  intro x hx
  constructor
  · exact Real.sqrt_nonneg x
  · rw [deltaAnticom, Real.sqrt_eq_rpow]
    simp

/-- All expanded-point conclusions at an abstract error function. The first
conjunct lists the four directed cross-party placements; the second lists all
four same-placement commutation conclusions. This proposition collects the
expanded-point conclusions of `lem:qld-comm-cons`, blueprint
`ch14_qpbt_observables.tex:932-1032`, paper
`14_analysis_of_the_pauli_basis_test.tex:452-505`. -/
def ExpandedPointConclusions (δ : ℝ → ℝ) : Prop :=
  (∃ C : ℝ, 1 ≤ C ∧
    ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
      (p₁ p₂ : Placement), p₁.IsOpposite p₂ →
      ∀ W : PauliKind,
        opFamilyDistSq (uniformDistribution (Fin P.m → PauliScalar P))
          (fun u a => S.place p₁
            ((S.pointMeasExp p₁.side W u).effect a))
          (fun u a => S.place p₂
            ((S.pointMeasExp p₂.side W u).effect a))
          S.psiHat ≤ C * ε) ∧
  (∃ C : ℝ, 1 ≤ C ∧
    ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
      (p : Placement),
      opFamilyDistSq (uniformDistribution (PauliTuple P))
        (fun ω (bits : ZMod 2 × ZMod 2) => S.place p
          ((S.expPointTrace p.side .X ω.1 ω.2.2.1).effect bits.1 *
            (S.expPointTrace p.side .Z ω.2.1 ω.2.2.2).effect bits.2))
        (fun ω (bits : ZMod 2 × ZMod 2) => S.place p
          ((S.expPointTrace p.side .Z ω.2.1 ω.2.2.2).effect bits.2 *
            (S.expPointTrace p.side .X ω.1 ω.2.2.1).effect bits.1))
        S.psiHat ≤ C * δ ε)

/-- Expanded point measurements are self-consistent for each of the four
directed opposite-placement pairs. The universal constant precedes all test
parameters and strategies. This is item 1 of `lem:qld-comm-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:455-465`, blueprint
`ch14_qpbt_observables.tex:942-959`. -/
theorem expPoint_self_cons :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
        (p₁ p₂ : Placement), p₁.IsOpposite p₂ →
        ∀ W : PauliKind,
          opFamilyDistSq (uniformDistribution (Fin P.m → PauliScalar P))
            (fun u a => S.place p₁
              ((S.pointMeasExp p₁.side W u).effect a))
            (fun u a => S.place p₂
              ((S.pointMeasExp p₂.side W u).effect a))
            S.psiHat ≤ C * ε := by
  sorry

/-- Trace-coarse-grained expanded point projections approximately commute on
each of `AA'`, `BA''`, `BB'`, and `AB''`. The universal constant precedes all
test parameters and strategies. This is item 2 of `lem:qld-comm-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:466-505`, blueprint
`ch14_qpbt_observables.tex:960-1032`. -/
theorem expPointTrace_comm :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
        (p : Placement),
        opFamilyDistSq (uniformDistribution (PauliTuple P))
          (fun ω (bits : ZMod 2 × ZMod 2) => S.place p
            ((S.expPointTrace p.side .X ω.1 ω.2.2.1).effect bits.1 *
              (S.expPointTrace p.side .Z ω.2.1 ω.2.2.2).effect bits.2))
          (fun ω (bits : ZMod 2 × ZMod 2) => S.place p
            ((S.expPointTrace p.side .Z ω.2.1 ω.2.2.2).effect bits.2 *
              (S.expPointTrace p.side .X ω.1 ω.2.2.1).effect bits.1))
          S.psiHat ≤ C * deltaAnticom ε := by
  sorry

/-- The source's existential polynomial-error formulation, derived from the
concrete square-root bounds rather than postulated independently. This is
`lem:qld-comm-cons`, paper `14_analysis_of_the_pauli_basis_test.tex:452-505`,
blueprint `ch14_qpbt_observables.tex:932-1032`. -/
theorem exists_deltaAnticom :
    ∃ δ : ℝ → ℝ, IsPolyErr δ ∧ ExpandedPointConclusions δ := by
  refine ⟨deltaAnticom, deltaAnticom_isPolyErr, ?_⟩
  exact ⟨expPoint_self_cons, expPointTrace_comm⟩

end


end MIPStarRE.QPBT
