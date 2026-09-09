import MIPStarRE.QPBT.Observables.LineMeasurement.LinePointConsistency

/-!
# Expanded line measurements

For a generalized-Pauli basis `W` and a canonical line, the expanded line
measurement is the convolution of the strategy line measurement with the
projective measurement of one Pauli register whose outcome is the restriction
to that line of the low-degree encoding of the measured basis label. This file
states the three consistency conclusions the source draws for that family,
together with the existential form in which the source states them.

The argument runs as follows. Restricting a multilinear low-degree encoding to
a line gives a polynomial of degree at most `m*d` in the line parameter, and at
most `d` on an axis-parallel line (`LineMeasurement.Restriction`), whose
partial evaluation at a sampled point obeys the elementary calculus of
`LineMeasurement.Evaluation`.
Coarse-graining the generalized Pauli basis measurement along that restriction
gives the ancillary projectors `tau^{W,line}`, which are symmetric and hence
perfectly self-consistent on an EPR pair (`LineMeasurement.Projector`). Their
convolution with the strategy line measurement is again projective and vanishes
outside the degree-`d` outcomes on an axis line (`LineMeasurement.Expanded`).
Self-consistency of the convolution follows from self-consistency of the
strategy line measurements and the data-processing inequality
(`LineMeasurement.SelfConsistency`). The overlap of an expanded line
measurement with the expanded point effects selected by evaluation at the
sampled point factorizes exactly through the ancillary consistency of
`tau^{W,line}` with `tau^{W,u}` (`LineMeasurement.LinePointOverlap`); the
generic bipartite estimates of `LineMeasurement.BipartiteTransport` carry that
overlap to the two bipartitions of the six registers, giving the
evaluation-class conclusion (`LineMeasurement.EvalClassConsistency`) and, by
projective refinement, the line-versus-point conclusion
(`LineMeasurement.LinePointConsistency`).

Two features of this route differ from the source. The source derives its third
item from its second; here the evaluation-class estimate comes first, from the
exact overlap identity, and the second item follows from it by projective
refinement, so that the source's elementary sub-measurement inequality is not
needed. The source also transports a relation proved for one pair of register
placements to the remaining three by the symmetry of the test
(`lem:symmetric-equivalents-transfer`, which is not formalized); here each of
the four directed opposite-placement pairs is proved directly. The estimates
established are linear in `ε` for all three items, hence stronger than the
square-root error whenever `ε ≤ 1`; they are weakened to the common error
`deltaLine ε = √ε` only because the source states the three items with a single
error function (`LineMeasurement.SquareRootError`).

## References

The declarations formalize `def:expanded-line-measurement` and
`lem:qld-comm-line-cons` of `blueprint/src/chapter/ch14_qpbt_observables.tex`.
Their paper source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:523-678`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

local instance pauliEdgeNonemptyLineMeasurement : Nonempty PauliEdge :=
  pauliEdge_nonempty

/-- The square-root error exhibited by the expanded-line consistency proof.
This is the final quantitative conclusion of `lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:675-677`. -/
noncomputable def deltaLine (ε : ℝ) : ℝ :=
  Real.sqrt ε

/-- The concrete expanded-line error is polynomially small. This discharges
the error-function component of `lem:qld-comm-line-cons`, using the value
proved at paper `14_analysis_of_the_pauli_basis_test.tex:675-677`. -/
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
`14_analysis_of_the_pauli_basis_test.tex:527-545`. -/
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
`14_analysis_of_the_pauli_basis_test.tex:527-532`, blueprint
`enu:qld-comm-line-self-cons`.

The estimate established below is the linear bound
`2 * (|PauliEdge| * ε)` coming from the two line self-loops of the Pauli basis
test; it is weakened to the common square-root error exactly as for the other
two items. -/
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
  have hcard : (1 : ℝ) ≤ Fintype.card PauliEdge := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card PauliEdge)
  refine ⟨2 * (Fintype.card PauliEdge : ℝ) + 4, by linarith, ?_⟩
  intro P ε S p₁ p₂ hopp W
  have key : ∀ x : ℝ, 0 ≤ x → x ≤ 2 * ((Fintype.card PauliEdge : ℝ) * ε) →
      x ≤ 4 → x ≤ (2 * (Fintype.card PauliEdge : ℝ) + 4) * deltaLine ε := by
    intro x hx0 hxε hx4
    exact le_mul_sqrt_of_le_mul_of_le_four (by linarith) hx0
      (by rw [mul_assoc]; exact hxε) hx4
  cases p₁ <;> cases p₂ <;> simp only [Placement.IsOpposite] at hopp
  · exact key _ (DistanceCalculus.opFamilyDistSq_nonneg _ _ _ _)
      (by simpa only [Placement.side] using
        ProjectiveSetting.expLineDist_aaBa_le S W)
      (by simpa only [Placement.side] using
        ProjectiveSetting.expLineDist_aaBa_le_four S W)
  · rw [DistanceCalculus.opFamilyDistSq_symm]
    exact key _ (DistanceCalculus.opFamilyDistSq_nonneg _ _ _ _)
      (by simpa only [Placement.side] using
        ProjectiveSetting.expLineDist_aaBa_le S W)
      (by simpa only [Placement.side] using
        ProjectiveSetting.expLineDist_aaBa_le_four S W)
  · rw [DistanceCalculus.opFamilyDistSq_symm]
    exact key _ (DistanceCalculus.opFamilyDistSq_nonneg _ _ _ _)
      (by simpa only [Placement.side] using
        ProjectiveSetting.expLineDist_abBb_le S W)
      (by simpa only [Placement.side] using
        ProjectiveSetting.expLineDist_abBb_le_four S W)
  · exact key _ (DistanceCalculus.opFamilyDistSq_nonneg _ _ _ _)
      (by simpa only [Placement.side] using
        ProjectiveSetting.expLineDist_abBb_le S W)
      (by simpa only [Placement.side] using
        ProjectiveSetting.expLineDist_abBb_le_four S W)

/-- An expanded line effect is consistent with itself followed by the expanded
point effect selected by its value at the sampled point. This is item 2 of
`lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:534-539`, blueprint
`eq:qld-comm-line-pt-cons`.

The estimate established below is linear in `ε`, matching the error `ε` with
which the source states this item. Combined with the universal bound `4` on the
distance between two placed complete measurements, it is weakened by
`le_mul_sqrt_of_le_mul_of_le_four` to the square-root form `C * √ε`, so that the
three items of the lemma share the single error function `deltaLine ε = √ε`
that the source requires; for `ε ≤ 1` the linear bound is the stronger
statement. -/
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
  obtain ⟨C₁, hC₁, h₁⟩ := win_low_degree
  obtain ⟨C₂, hC₂, h₂⟩ := WinImplications.win_low_degree_interchanged_proof
  refine ⟨2 * (C₁ + C₂) + 4, by linarith, ?_⟩
  intro P ε S p₁ p₂ hopp W
  have hε : 0 ≤ ε := S.eps_nonneg
  have key : ∀ (x a : ℝ), 1 ≤ a → a ≤ C₁ + C₂ → 0 ≤ x → x ≤ 2 * (a * ε) →
      x ≤ 4 → x ≤ (2 * (C₁ + C₂) + 4) * deltaLine ε := by
    intro x a ha haC hx0 hxa hx4
    calc
      x ≤ (2 * a + 4) * Real.sqrt ε :=
        le_mul_sqrt_of_le_mul_of_le_four (by linarith) hx0
          (by rw [mul_assoc]; exact hxa) hx4
      _ ≤ (2 * (C₁ + C₂) + 4) * Real.sqrt ε := by
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg ε)
        linarith
  have htwo : (0 : ℝ) ≤ 2 := by norm_num
  cases p₁ <;> cases p₂ <;> simp only [Placement.IsOpposite] at hopp
  · have hb := ((ProjectiveSetting.linePointDist_aaBa_le S W).trans
      (ProjectiveSetting.evalClassDist_aaBa_le S W)).trans
      (mul_le_mul_of_nonneg_left (h₁ P ε S hε W) htwo)
    have h4 := (ProjectiveSetting.linePointDist_aaBa_le S W).trans
      (ProjectiveSetting.evalClassDist_aaBa_le_four S W)
    simpa only [Placement.side] using key _ C₁ hC₁ (by linarith)
      (DistanceCalculus.opFamilyDistSq_nonneg _ _ _ _) hb h4
  · have hb := ((ProjectiveSetting.linePointDist_baAa_le S W).trans
      (ProjectiveSetting.evalClassDist_baAa_le S W)).trans
      (mul_le_mul_of_nonneg_left (h₂ P ε S hε W) htwo)
    have h4 := (ProjectiveSetting.linePointDist_baAa_le S W).trans
      (ProjectiveSetting.evalClassDist_baAa_le_four S W)
    simpa only [Placement.side] using key _ C₂ hC₂ (by linarith)
      (DistanceCalculus.opFamilyDistSq_nonneg _ _ _ _) hb h4
  · have hb := ((ProjectiveSetting.linePointDist_bbAb_le S W).trans
      (ProjectiveSetting.evalClassDist_bbAb_le S W)).trans
      (mul_le_mul_of_nonneg_left (h₂ P ε S hε W) htwo)
    have h4 := (ProjectiveSetting.linePointDist_bbAb_le S W).trans
      (ProjectiveSetting.evalClassDist_bbAb_le_four S W)
    simpa only [Placement.side] using key _ C₂ hC₂ (by linarith)
      (DistanceCalculus.opFamilyDistSq_nonneg _ _ _ _) hb h4
  · have hb := ((ProjectiveSetting.linePointDist_abBb_le S W).trans
      (ProjectiveSetting.evalClassDist_abBb_le S W)).trans
      (mul_le_mul_of_nonneg_left (h₁ P ε S hε W) htwo)
    have h4 := (ProjectiveSetting.linePointDist_abBb_le S W).trans
      (ProjectiveSetting.evalClassDist_abBb_le_four S W)
    simpa only [Placement.side] using key _ C₁ hC₁ (by linarith)
      (DistanceCalculus.opFamilyDistSq_nonneg _ _ _ _) hb h4

/-- Evaluation classes of expanded line measurements are consistent with the
completed expanded point family, including the `none` class. This is item 3 of
`lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:540-545`, blueprint
`eq:qld-comm-line-pt-cons2`.

The source obtains this item from its second one through an elementary
inequality for projective sub-measurements, which costs a square root. Here the
exact overlap identity of `LineMeasurement.LinePointOverlap` gives a bound
linear in `ε` directly; as for item 2 it is combined with the universal bound
`4` and weakened to the common square-root error of the lemma. -/
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
  obtain ⟨C₁, hC₁, h₁⟩ := win_low_degree
  obtain ⟨C₂, hC₂, h₂⟩ := WinImplications.win_low_degree_interchanged_proof
  refine ⟨2 * (C₁ + C₂) + 4, by linarith, ?_⟩
  intro P ε S p₁ p₂ hopp W
  have hε : 0 ≤ ε := S.eps_nonneg
  have key : ∀ (x a : ℝ), 1 ≤ a → a ≤ C₁ + C₂ → 0 ≤ x → x ≤ 2 * (a * ε) →
      x ≤ 4 → x ≤ (2 * (C₁ + C₂) + 4) * deltaLine ε := by
    intro x a ha haC hx0 hxa hx4
    calc
      x ≤ (2 * a + 4) * Real.sqrt ε :=
        le_mul_sqrt_of_le_mul_of_le_four (by linarith) hx0
          (by rw [mul_assoc]; exact hxa) hx4
      _ ≤ (2 * (C₁ + C₂) + 4) * Real.sqrt ε := by
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg ε)
        linarith
  have htwo : (0 : ℝ) ≤ 2 := by norm_num
  cases p₁ <;> cases p₂ <;> simp only [Placement.IsOpposite] at hopp
  · have hb := (ProjectiveSetting.evalClassDist_aaBa_le S W).trans
      (mul_le_mul_of_nonneg_left (h₁ P ε S hε W) htwo)
    simpa only [Placement.side] using key _ C₁ hC₁ (by linarith)
      (DistanceCalculus.opFamilyDistSq_nonneg _ _ _ _) hb
      (ProjectiveSetting.evalClassDist_aaBa_le_four S W)
  · have hb := (ProjectiveSetting.evalClassDist_baAa_le S W).trans
      (mul_le_mul_of_nonneg_left (h₂ P ε S hε W) htwo)
    simpa only [Placement.side] using key _ C₂ hC₂ (by linarith)
      (DistanceCalculus.opFamilyDistSq_nonneg _ _ _ _) hb
      (ProjectiveSetting.evalClassDist_baAa_le_four S W)
  · have hb := (ProjectiveSetting.evalClassDist_bbAb_le S W).trans
      (mul_le_mul_of_nonneg_left (h₂ P ε S hε W) htwo)
    simpa only [Placement.side] using key _ C₂ hC₂ (by linarith)
      (DistanceCalculus.opFamilyDistSq_nonneg _ _ _ _) hb
      (ProjectiveSetting.evalClassDist_bbAb_le_four S W)
  · have hb := (ProjectiveSetting.evalClassDist_abBb_le S W).trans
      (mul_le_mul_of_nonneg_left (h₁ P ε S hε W) htwo)
    simpa only [Placement.side] using key _ C₁ hC₁ (by linarith)
      (DistanceCalculus.opFamilyDistSq_nonneg _ _ _ _) hb
      (ProjectiveSetting.evalClassDist_abBb_le_four S W)

/-- The source's existential polynomial-error form, derived from the concrete
expanded-line witnesses and square-root error. This is
`lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:523-678`. -/
theorem exists_deltaLine :
    ∃ δ : ℝ → ℝ, IsPolyErr δ ∧ ExpandedLineConclusions δ := by
  refine ⟨deltaLine, deltaLine_isPolyErr, ?_⟩
  exact ⟨fun P ε S side W line => S.lineMeasExp_isProjective side W line,
    expLine_self_cons, expLine_point_cons, expLine_point_cons'⟩

end


end MIPStarRE.QPBT
