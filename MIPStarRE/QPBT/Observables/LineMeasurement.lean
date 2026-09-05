import MIPStarRE.QPBT.Observables.PointConsistency

/-!
# Expanded line measurements

This module restricts low-degree encodings to canonical lines, constructs the
expanded line measurements by convolution, and records their consistency with
the expanded point measurements on all four register placements.

## References

The declarations formalize blueprint `def:expanded-line-measurement` and
`lem:qld-comm-line-cons`. Their paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:506-679`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-- Substitute the affine parameterization of a canonical line into a
multivariate polynomial. This is the polynomial `g_h(u₀ + tv)` used in
`def:expanded-line-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:535-557`, blueprint
`def:expanded-line-measurement`. -/
noncomputable def polynomialOnLine (L : LdParams) (line : LineDesc L)
    (g : MvPolynomial (Fin L.m) (ScalarQ L)) : Polynomial (ScalarQ L) :=
  MvPolynomial.eval₂Hom _root_.Polynomial.C
    (fun i : Fin L.m =>
      (_root_.Polynomial.C (line.base i) +
        _root_.Polynomial.X * _root_.Polynomial.C (line.direction i) :
        Polynomial (ScalarQ L))) g

/-- The degree-`m*d` coefficient list obtained by restricting `g` to `line`.
This is the concrete restriction operation in `def:expanded-line-measurement`,
paper `14_analysis_of_the_pauli_basis_test.tex:535-557`, blueprint
`def:expanded-line-measurement`. -/
noncomputable def restrictToLine (L : LdParams) (line : LineDesc L)
    (g : MvPolynomial (Fin L.m) (ScalarQ L)) : DegPoly L (L.m * L.d) :=
  fun i => (polynomialOnLine L line g).coeff i.val

/-- Restricting a multilinear low-degree encoding to a line has degree at most
`m*d`. This is the degree justification in `def:expanded-line-measurement`,
paper `14_analysis_of_the_pauli_basis_test.tex:535-557`, blueprint
`def:expanded-line-measurement`. -/
theorem polynomialOnLine_lowDegreeEncoding_natDegree_le (L : LdParams)
    (line : LineDesc L) (h : Cube L.m → ScalarQ L) :
    (polynomialOnLine L line (lowDegreeEncoding h)).natDegree ≤ L.m * L.d := by
  sorry

/-- A degree-`m*d` coefficient list actually lies in the embedded degree-`d`
subspace when all coefficients above `d` vanish. This is the coefficient
interpretation of `deg_d(line) ⊆ deg_md(line)` in
`def:expanded-line-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:548-557`. -/
def DegPoly.FitsDegree {L : LdParams} {c : ℕ} (d : ℕ)
    (f : DegPoly L c) : Prop :=
  ∀ i : Fin (c + 1), d < i.val → f i = 0

/-- The Pauli-register projector onto labels whose low-degree encoding
restricts to `f` on `line`. This is `tau^{W,line}_f` in the proof of
`lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:535-557`, blueprint
`lem:qld-comm-line-cons`. -/
noncomputable def tauLineProj (P : AdmissibleParams) (W : PauliKind)
    (line : LineDesc P.toLdParams) (f : DegPoly P.toLdParams (P.m * P.d)) :
    Op (PauliRegister P) :=
  ∑ h ∈ Finset.univ.filter (fun h : PauliRegister P =>
      restrictToLine P.toLdParams line (lowDegreeEncoding h) = f),
    pauliProj W h

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

/-- The convolution of a strategy line effect with the corresponding
Pauli-register line projector. This is the displayed definition of
`hat M^(Line,W),line_f`, paper
`14_analysis_of_the_pauli_basis_test.tex:530-557`, blueprint
`def:expanded-line-measurement`. -/
noncomputable def expLineOp (S : ProjectiveSetting P ε) (side : PlayerSide)
    (W : PauliKind) (line : LineDesc P.toLdParams)
    (f : DegPoly P.toLdParams (P.m * P.d)) : Op (S.ExpandedLocalSpace side) :=
  ∑ pair ∈ Finset.univ.filter
      (fun pair : DegPoly P.toLdParams (P.m * P.d) ×
          DegPoly P.toLdParams (P.m * P.d) => pair.1 + pair.2 = f),
    heteroKron ((S.lineMeas side W line).effect pair.1)
      (tauLineProj P W line pair.2)

/-- Expanded line effects are positive semidefinite. This is the positivity
obligation of `def:expanded-line-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:530-557`. -/
theorem expLineOp_nonneg (S : ProjectiveSetting P ε) (side : PlayerSide)
    (W : PauliKind) (line : LineDesc P.toLdParams)
    (f : DegPoly P.toLdParams (P.m * P.d)) :
    0 ≤ S.expLineOp side W line f := by
  sorry

/-- Expanded line effects sum to the identity. This is the completeness
obligation of `def:expanded-line-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:530-557`. -/
theorem expLineOp_sum_eq_one (S : ProjectiveSetting P ε) (side : PlayerSide)
    (W : PauliKind) (line : LineDesc P.toLdParams) :
    ∑ f, S.expLineOp side W line f = 1 := by
  sorry

/-- The concrete expanded line measurement exhibited in the proof of
`lem:qld-comm-line-cons`. Paper
`14_analysis_of_the_pauli_basis_test.tex:530-557`, blueprint
`lem:qld-comm-line-cons`. -/
noncomputable def lineMeasExp (S : ProjectiveSetting P ε) (side : PlayerSide)
    (W : PauliKind) (line : LineDesc P.toLdParams) :
    Measurement (DegPoly P.toLdParams (P.m * P.d))
      (S.ExpandedLocalSpace side) :=
  Measurement.ofSumEqOne (S.expLineOp side W line)
    (S.expLineOp_nonneg side W line) (S.expLineOp_sum_eq_one side W line)

/-- The expanded line measurement is projective. This is the projectivity
assertion in `def:expanded-line-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:530-557`. -/
theorem lineMeasExp_isProjective (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (line : LineDesc P.toLdParams) :
    MIPStarRE.QPBT.Measurement.IsProjective (S.lineMeasExp side W line) := by
  sorry

/-- On an axis line, expanded effects outside the embedded degree-`d` outcome
space vanish. This is the last assertion of
`def:expanded-line-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:548-557`, blueprint
`def:expanded-line-measurement`. -/
theorem expLineOp_zero_of_not_deg_d (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (line : LineDesc P.toLdParams)
    (haxis : line.kind = .axis) (f : DegPoly P.toLdParams (P.m * P.d))
    (hf : ¬ f.FitsDegree P.d) :
    S.expLineOp side W line f = 0 := by
  sorry

/-- Evaluation classes of the expanded line measurement, including the
explicit `none` class for a non-evaluating canonical line. This is the
completed bracket family used in item 3 of blueprint
`lem:qld-comm-line-cons`. -/
noncomputable def lineEvalMeasExp (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (line : LineDesc P.toLdParams)
    (u : Fin P.m → PauliScalar P) :
    Measurement (Option (PauliScalar P)) (S.ExpandedLocalSpace side) :=
  (S.lineMeasExp side W line).postprocess (evalOpt line u)

/-- Complete an expanded point measurement with a zero `none` outcome. This
is the right-hand family in the corrected item 3 of
blueprint
`lem:qld-comm-line-cons`. -/
noncomputable def pointMeasExpOption (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (u : Fin P.m → PauliScalar P) :
    Measurement (Option (PauliScalar P)) (S.ExpandedLocalSpace side) :=
  (S.pointMeasExp side W u).postprocess some

/-- The point effect indexed by a line answer, with zero assigned when the
answer has no evaluation at the sampled point. This is the zero-direction
completion used in item 2 of blueprint
`lem:qld-comm-line-cons`. -/
noncomputable def expPointEffectAtLineAnswer (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (line : LineDesc P.toLdParams)
    (u : Fin P.m → PauliScalar P) (f : DegPoly P.toLdParams (P.m * P.d)) :
    Op (S.ExpandedLocalSpace side) :=
  match evalOpt line u f with
  | some a => (S.pointMeasExp side W u).effect a
  | none => 0

end ProjectiveSetting

/-- The square-root error exhibited by the expanded-line consistency proof.
This is the final quantitative conclusion of `lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:657-679`, blueprint
`lem:qld-comm-line-cons`. -/
noncomputable def deltaLine (ε : ℝ) : ℝ :=
  Real.sqrt ε

/-- The concrete expanded-line error is polynomially small. This discharges
the error-function component of `lem:qld-comm-line-cons`, using the value
proved at paper `14_analysis_of_the_pauli_basis_test.tex:657-679`, blueprint
`lem:qld-comm-line-cons`. -/
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
`lem:qld-comm-line-cons`. -/
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
`lem:qld-comm-line-cons`. -/
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
`lem:qld-comm-line-cons`. -/
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
`lem:qld-comm-line-cons`. -/
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
`lem:qld-comm-line-cons`. -/
theorem exists_deltaLine :
    ∃ δ : ℝ → ℝ, IsPolyErr δ ∧ ExpandedLineConclusions δ := by
  refine ⟨deltaLine, deltaLine_isPolyErr, ?_⟩
  exact ⟨fun P ε S side W line => S.lineMeasExp_isProjective side W line,
    expLine_self_cons, expLine_point_cons, expLine_point_cons'⟩

end


end MIPStarRE.QPBT
