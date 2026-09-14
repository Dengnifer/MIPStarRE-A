import MIPStarRE.QPBT.Combining.Lines.CombinedMeasurement
import MIPStarRE.QPBT.Combining.Lines.Marginal
import MIPStarRE.QPBT.Combining.Lines.RestoredConsistency
import MIPStarRE.QPBT.Combining.Lines.ConsistencyPositivity
import MIPStarRE.QPBT.Combining.Lines.DiagonalResampling
import MIPStarRE.QPBT.Combining.Lines.RestrictedAverage
import MIPStarRE.QPBT.Combining.Lines.SubLineMixture
import MIPStarRE.QPBT.Combining.Points
import MIPStarRE.QPBT.Combining.Witnesses
import MIPStarRE.QPBT.Games.RestrictedAverage

/-!
# Combined lines and restricted line distributions

This module states the construction of the joint X/Z line measurements, the
mixture and error-inflation estimates for restricted line distributions, and
the sub-line distribution used to combine the two bases.  The extended line
in the sub-line construction uses the directly indexed carrier, so the
sub-line statement is a formalization auxiliary assertion and carries no
divisibility hypothesis at dimension `2 * m + 2`.

## References

The declarations formalize `lem:qld-xz-lines` and
`lem:restricted-line-mixture-bounds` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`; `exists_subLineWitness`
instead supports `lem:qld-sublines` through the directly indexed extended-line
carrier and probability law.  Their paper sources
are `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:882-894`
and `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1038-1069`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-! ## Combined line measurements -/

/-- Consistency of the particular X-Z-X measurement
constructed in the proof of `lem:qld-xz-lines`, paper
`14_analysis_of_the_pauli_basis_test.tex:942-961`.

The point family is supplied with its polynomial error bound. The line error
may depend on this function, as in `exists_combinedLinesWitness_ofPointsWitness`.
The conclusion concerns `combinedLineMeasurement` itself, so subsequent uses of
Claim 17-2 retain the source construction.

The point-to-line comparisons feed heterogeneous pasting after conditioning on
nonzero X-line direction. Restoring the discarded mass costs at most `1/(2q)`;
the scalar polynomial bound absorbs this cost and the supplied point error.
This discharges the obligation tracked by issues #18, #414, and #515, without
an equality or marginal assumption. See blueprint
`lem:combined-line-measurement-consistency` and
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`. -/
theorem combined_line_measurement_consistency (deltaQ : ℝ → ℝ)
    (hdeltaQ : IsPolyErr deltaQ) :
    ∃ deltaP : ℝ → ℝ → ℝ, IsPolyErr₂ deltaP ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
        (points : CombinedPointsWitness S (deltaQ ε))
        (p1 p2 : Placement), p1.IsOpposite p2 →
        consistencyDefect
          (Distribution.prod (linePointDist P.toLdParams)
            (linePointDist P.toLdParams))
          (fun sample answer => S.place p1
            (((S.combinedLineMeasurement p1.side sample.1.1 sample.2.1).postprocess
              fun fs => (evalOpt sample.1.1 sample.1.2 fs.1,
                evalOpt sample.2.1 sample.2.2 fs.2)).effect answer))
          (fun sample answer => S.place p2
            (((points.Q p2.side sample.1.2 sample.2.2).postprocess fun ab =>
              (some ab.1, some ab.2)).effect answer))
          S.psiHat ≤ deltaP ε (((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)) := by
  classical
  obtain ⟨constant, hconstant, pastingError, hpasting, hrestored⟩ :=
    exists_combinedLine_restored_defect_le
  obtain ⟨lineError, hlineError, hscalar⟩ :=
    exists_conditioned_polynomial_bound deltaQ hdeltaQ constant hconstant pastingError hpasting
  refine ⟨lineError, hlineError, ?_⟩
  intro params error setting points first second hopposite
  have hreverse : second.IsOpposite first := by
    cases first <;> cases second <;> trivial
  rw [consistencyDefect_opposite_symm setting first second hopposite]
  have hbound := hrestored params error (deltaQ error) setting points second first hreverse
  have hcard : Fintype.card (ScalarQ params.toLdParams) = params.q :=
    @FieldModel.card params.q params.model.toFieldModel
  rw [hcard] at hbound
  have hq : (0 : ℝ) < params.q := by
    rw [← hcard]
    exact_mod_cast Fintype.card_pos (α := ScalarQ params.toLdParams)
  have hmd : (1 : ℝ) ≤ (params.m * params.d : ℕ) := by
    exact_mod_cast (show 1 ≤ params.m * params.d by
      simpa using Nat.mul_le_mul params.one_le_m params.hd)
  have hdiscard : 1 / (2 * (params.q : ℝ)) ≤
      (params.m * params.d : ℕ) / (params.q : ℝ) := by
    calc
      _ ≤ 1 / (params.q : ℝ) := one_div_le_one_div_of_le hq (by linarith)
      _ ≤ _ := div_le_div_of_nonneg_right hmd hq.le
  have hunit : consistencyDefect
      (Distribution.prod (linePointDist params.toLdParams) (linePointDist params.toLdParams))
      (fun sample answer => setting.place second
        (((points.Q second.side sample.1.2 sample.2.2).postprocess
          (fun pair => (some pair.1, some pair.2))).effect answer))
      (fun sample answer => setting.place first
        (((setting.combinedLineMeasurement first.side sample.1.1 sample.2.1).postprocess
          (fun polys => (evalOpt sample.1.1 sample.1.2 polys.1,
            evalOpt sample.2.1 sample.2.2 polys.2))).effect answer)) setting.psiHat ≤ 1 := by
    unfold consistencyDefect
    calc
      _ ≤ avgOver (Distribution.prod (linePointDist params.toLdParams)
          (linePointDist params.toLdParams)) (fun _ => 1) :=
        avgOver_mono _ _ _ fun sample =>
          consistencyDefect_integrand_le_one setting second first hreverse _ _
      _ = 1 := avgOver_const_of_isProbability _
        (Distribution.prod_isProbability _ _ (linePointDist_isProbability params.toLdParams)
          (linePointDist_isProbability params.toLdParams)) 1
  exact (le_min hunit (hbound.trans (add_le_add le_rfl hdiscard))).trans
    (hscalar error _ _ setting.eps_nonneg (by positivity)
      (nondegenerateLinePastingMass_bounds params.toLdParams).1
      (nondegenerateLinePastingMass_bounds params.toLdParams).2)

/-- Conditional joint X/Z line measurements for a polynomially controlled
point-witness family supporting `lem:qld-xz-lines`.

**Source statement:** blueprint
`lem:qld-xz-lines`, from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:882-894`.
The error depends polynomially on `ε` and `md/q`, and the witness retains all
directed opposite-placement comparisons.  This Lean-only conditional form takes
the point-error function and its polynomial bound before choosing the line-error
function.  The witness at strategy error `ε` must have error `deltaQ ε`.

**Domain repair (issue #389):** The former statement quantified an arbitrary
scalar point error after choosing `deltaP`, although the pasting estimate depends
on that point error.  The repaired domain matches the point family supplied by
`exists_combinedPointsWitness`.  The source-facing theorem below still supplies
that family existentially and has an unchanged statement.  The obstruction and
the named construction obligations are recorded in
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`.

The witness below uses `S.combinedLineMeasurement` explicitly. Its consistency
is `combined_line_measurement_consistency`, as recorded in
`docs/paper-gaps/qpbt_subline-claims-line-marginal.tex` and issue #414.

**Error contract:** the polynomial bound printed in the source is carried
by `IsPolyErr₂`, which states the corrected sum form
`f x y ≤ C * (x ^ r + y ^ s)` with `1 ≤ C` and positive exponents on the
closed nonnegative quadrant, in place of the product form `C * (x * y) ^ C`
of the source shorthand at `04_preliminaries.tex:22-29`.  The correction and
the two-dimensional strategy that refutes the product form are recorded in
`docs/paper-gaps/qpbt_pasting-product-error.tex` and tracked by issue #196.
Here `poly(ε, md/q)` is read in that sense. -/
theorem exists_combinedLinesWitness_ofPointsWitness (deltaQ : ℝ -> ℝ)
    (hdeltaQ : IsPolyErr deltaQ) :
    ∃ deltaP : ℝ -> ℝ -> ℝ, IsPolyErr₂ deltaP ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
        (points : CombinedPointsWitness S (deltaQ ε)),
        Nonempty (CombinedLinesWitness S points
          (deltaP ε (((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)))) := by
  obtain ⟨deltaP, hdeltaP, hconsistent⟩ :=
    combined_line_measurement_consistency deltaQ hdeltaQ
  refine ⟨deltaP, hdeltaP, ?_⟩
  intro P ε S points
  exact ⟨{ T := S.combinedLineMeasurement
           axis_degree_X := S.combinedLineMeasurement_axis_degree_X
           axis_degree_Z := S.combinedLineMeasurement_axis_degree_Z
           consistent := hconsistent P ε S points }⟩

/-! The source-facing declaration below supplies the point witness produced by
`lem:qld-4-10` existentially.  The `_ofPointsWitness` companion above is the
conditional form for a supplied polynomially controlled point family. -/

/-- The source-facing joint X/Z line measurement construction of
`lem:qld-xz-lines`, paper lines 882--894.

Unlike the formalization-only `_ofPointsWitness` companion, this declaration
does not assume a `CombinedPointsWitness` as an external bridge input.  It
quantifies the point error function and witness construction together with the
line construction, as the preceding source lemma supplies those points.

The proof constructs the line witness with `T := S.combinedLineMeasurement`.
The only remaining line-construction obligation is
`combined_line_measurement_consistency`, from paper lines 942--961 and tracked
by issue #414 in `docs/paper-gaps/qpbt_subline-claims-line-marginal.tex`.
Downstream arguments requiring the construction use that consistency theorem
and the same explicit record, rather than an unspecified existential witness.

**Error contract:** the polynomial bound printed in the source is carried
by `IsPolyErr₂`, which states the corrected sum form
`f x y ≤ C * (x ^ r + y ^ s)` with `1 ≤ C` and positive exponents on the
closed nonnegative quadrant, in place of the product form `C * (x * y) ^ C`
of the source shorthand at `04_preliminaries.tex:22-29`.  The correction and
the two-dimensional strategy that refutes the product form are recorded in
`docs/paper-gaps/qpbt_pasting-product-error.tex` and tracked by issue #196.
Here `poly(ε, md/q)` is read in that sense. -/
theorem exists_combinedLinesWitness :
    ∃ deltaQ : ℝ -> ℝ, IsPolyErr deltaQ ∧
      ∃ deltaP : ℝ -> ℝ -> ℝ, IsPolyErr₂ deltaP ∧
        ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
          ∃ points : CombinedPointsWitness S (deltaQ ε),
            Nonempty (CombinedLinesWitness S points
              (deltaP ε (((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)))) := by
  obtain ⟨deltaQ, hdeltaQ, hpoints⟩ := exists_combinedPointsWitness
  obtain ⟨deltaP, hdeltaP, hconsistent⟩ :=
    combined_line_measurement_consistency deltaQ hdeltaQ
  refine ⟨deltaQ, hdeltaQ, deltaP, hdeltaP, ?_⟩
  intro P ε S
  obtain ⟨points⟩ := hpoints P ε S
  exact ⟨points, ⟨{ T := S.combinedLineMeasurement
                    axis_degree_X := S.combinedLineMeasurement_axis_degree_X
                    axis_degree_Z := S.combinedLineMeasurement_axis_degree_Z
                    consistent := hconsistent P ε S points }⟩⟩

/-! ## Restricted line distributions -/

/-- The axis and diagonal line-point laws are uniform mixtures of their
coordinate-index restrictions.

**Source statement:** blueprint
`lem:restricted-line-mixture-bounds`, formalizing the
unlabelled observation at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1049-1051`.
`Distribution.bind` is the finite uniform-mixture operation.  The two halves
are proved from the equal-fiber decomposition of `chiIndex` and the fact that
every line conditioning map retains the shared scalar seed. -/
theorem linePointDist_eq_mixture_restricted (L : LdParams) :
    aLinePointDist L =
        Distribution.bind (uniformDistribution (Fin L.m))
          (restrictedALineDist L) ∧
      dLinePointDist L =
        Distribution.bind (uniformDistribution (Fin L.m))
          (restrictedDLineDist L) :=
  ⟨aLinePointDist_eq_bind_restricted L, dLinePointDist_eq_bind_restricted L⟩

/-- Restricting a nonnegative average from the line-point distribution to one
fixed line kind and coordinate inflates its bound by at most `2m`.

**Source statement:** item 1 of blueprint
`lem:restricted-line-mixture-bounds`, from the unlabelled
estimate at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1052-1056`.
The restricted component carries mixture weight `1 / (2m)`, so a nonnegative
average bounded by `δ` bounds it by `2mδ`. -/
theorem avg_restricted_le {P : AdmissibleParams}
    (f : (LineDesc P.toLdParams × (Fin P.m -> PauliScalar P)) -> ℝ)
    (hf : ∀ sample, 0 ≤ f sample) {δ : ℝ}
    (havg : avgOver (linePointDist P.toLdParams) f ≤ δ)
    (kind : LineKind) (i : Fin P.m) :
    avgOver (restrictedLinePointDist P kind i) f ≤
      2 * (P.m : ℝ) * δ := by
  refine (avgOver_restrictedLinePointDist_le f hf kind i).trans ?_
  exact mul_le_mul_of_nonneg_left havg (by positivity)

/-- Restricting both variables of a nonnegative average over two independent
line-point samples inflates its bound by at most `4m^2`.

**Source statement:** item 2 of blueprint
`lem:restricted-line-mixture-bounds`, from the unlabelled
estimate at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1056-1058`.
The one-variable estimate is applied successively to the two product
coordinates. -/
theorem avg_restricted_prod_le {P : AdmissibleParams}
    (f : ((LineDesc P.toLdParams × (Fin P.m -> PauliScalar P)) ×
      (LineDesc P.toLdParams × (Fin P.m -> PauliScalar P))) -> ℝ)
    (hf : ∀ sample, 0 ≤ f sample) {δ : ℝ}
    (havg : avgOver
      (Distribution.prod (linePointDist P.toLdParams)
        (linePointDist P.toLdParams)) f ≤ δ)
    (kindX kindZ : LineKind) (i j : Fin P.m) :
    avgOver
      (Distribution.prod (restrictedLinePointDist P kindX i)
        (restrictedLinePointDist P kindZ j)) f ≤
      4 * (P.m : ℝ) ^ 2 * δ := by
  refine (avgOver_prod_restrictedLinePointDist_le f hf kindX kindZ i j).trans ?_
  exact mul_le_mul_of_nonneg_left havg (by positivity)

/-- Formalization-only auxiliary for item 3 of
`lem:restricted-line-mixture-bounds`: a consistency defect of two complete
measurements placed on opposite registers inflates by at most `4m^2` when
both line-point coordinates are restricted.  Blueprint
`lem:restricted-line-mixture-bounds`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1058-1061`. -/
private theorem consistencyDefect_restricted_prod_le {P : AdmissibleParams}
    {ε δ : ℝ} {α : Type*} [Fintype α] [DecidableEq α]
    (S : ProjectiveSetting P ε) (p₁ p₂ : Placement) (hopp : p₁.IsOpposite p₂)
    (M₁ : ((LineDesc P.toLdParams × (Fin P.m -> PauliScalar P)) ×
        (LineDesc P.toLdParams × (Fin P.m -> PauliScalar P))) ->
      MIPStarRE.Quantum.Measurement α (S.ExpandedLocalSpace p₁.side))
    (M₂ : ((LineDesc P.toLdParams × (Fin P.m -> PauliScalar P)) ×
        (LineDesc P.toLdParams × (Fin P.m -> PauliScalar P))) ->
      MIPStarRE.Quantum.Measurement α (S.ExpandedLocalSpace p₂.side))
    (hbound : consistencyDefect
      (Distribution.prod (linePointDist P.toLdParams)
        (linePointDist P.toLdParams))
      (fun sample answer => S.place p₁ ((M₁ sample).effect answer))
      (fun sample answer => S.place p₂ ((M₂ sample).effect answer))
      S.psiHat ≤ δ)
    (kindX kindZ : LineKind) (i j : Fin P.m) :
    consistencyDefect
      (Distribution.prod (restrictedLinePointDist P kindX i)
        (restrictedLinePointDist P kindZ j))
      (fun sample answer => S.place p₁ ((M₁ sample).effect answer))
      (fun sample answer => S.place p₂ ((M₂ sample).effect answer))
      S.psiHat ≤ 4 * (P.m : ℝ) ^ 2 * δ := by
  unfold consistencyDefect at hbound ⊢
  refine le_trans
    (avgOver_prod_restrictedLinePointDist_le _ ?_ kindX kindZ i j) ?_
  · intro sample
    exact consistencyDefect_integrand_nonneg S p₁ p₂ hopp (M₁ sample)
      (M₂ sample)
  · exact mul_le_mul_of_nonneg_left hbound (by positivity)

/-- The evaluated joint line measurement remains consistent with the joint
point measurement on every product of restricted line distributions.

**Source statement:** item 3 and Equation `eq:qld-xz-lines-restricted` of
blueprint
`lem:restricted-line-mixture-bounds`, from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1058-1061`.
Here `consistencyDefect` is the finite POVM form of the displayed expectation
against `Id - Q` after both measurements are postprocessed by evaluation.
The universal constant is outside all strategy and parameter quantifiers, and
is the exact inflation factor `4` of `avg_restricted_prod_le`. -/
theorem restricted_lines_consistency_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ {P : AdmissibleParams} {ε δQ δP : ℝ}
        (S : ProjectiveSetting P ε)
        (points : CombinedPointsWitness S δQ)
        (lines : CombinedLinesWitness S points δP)
        (p1 p2 : Placement), p1.IsOpposite p2 ->
        ∀ (kindX kindZ : LineKind) (i j : Fin P.m),
          consistencyDefect
            (Distribution.prod (restrictedLinePointDist P kindX i)
              (restrictedLinePointDist P kindZ j))
            (fun sample answer => S.place p1
              (((lines.T p1.side sample.1.1 sample.2.1).postprocess fun fs =>
                (evalOpt sample.1.1 sample.1.2 fs.1,
                  evalOpt sample.2.1 sample.2.2 fs.2)).effect answer))
            (fun sample answer => S.place p2
              (((points.Q p2.side sample.1.2 sample.2.2).postprocess fun ab =>
                (some ab.1, some ab.2)).effect answer))
            S.psiHat ≤ C * (P.m : ℝ) ^ 2 * δP := by
  refine ⟨4, by norm_num, ?_⟩
  intro P ε δQ δP S points lines p1 p2 hopp kindX kindZ i j
  exact consistencyDefect_restricted_prod_le S p1 p2 hopp
    (fun sample => (lines.T p1.side sample.1.1 sample.2.1).postprocess fun fs =>
      (evalOpt sample.1.1 sample.1.2 fs.1, evalOpt sample.2.1 sample.2.2 fs.2))
    (fun sample => (points.Q p2.side sample.1.2 sample.2.2).postprocess fun ab =>
      (some ab.1, some ab.2))
    (lines.consistent p1 p2 hopp) kindX kindZ i j

/-! ## The sub-line distribution -/

/-- Existence of the directly indexed sub-line distribution with its two
separate projected point marginals and axis-line closure.  It supports
`lem:qld-sublines` and `rem:qld-sublines-property-three` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1069` with
its proof at lines 1071--1116.

This is a formalization auxiliary assertion, not the source-labelled
`lem:qld-sublines`.  The extended line uses the directly indexed carrier and
line-point law of `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` in
place of the seed-indexed line-point distribution over `F_q^(2m+2)` of the
source statement, so the statement carries no divisibility hypothesis and its
transport to the source carrier remains open.  Its `source_mixture` field
asserts only the separate X and Z marginal mixtures, not a stronger joint
conditional law.

The witness is the sub-line law `subLineDist` of the sampling procedure.  Its
pointwise fields follow from `subLineTripleOf_incidence`,
`subLineTripleOf_compatibility`, and `subLineTripleOf_axis_closure`, after
recovering the auxiliary sample with `exists_raw_of_mem_subLineDist_support`.
Its extended-line marginal is `subLineDist_map_fst`, and its two projected
point marginals are the separate mixtures of `subLineDist_source_mixture`. -/
theorem exists_subLineWitness (P : AdmissibleParams) :
    Nonempty (SubLineWitness P) := by
  refine ⟨{ D := subLineDist P
            isProbability := subLineDist_isProbability P
            extended_marginal := subLineDist_map_fst P
            incidence := ?_
            compatibility := ?_
            source_mixture := subLineDist_source_mixture P
            axis_closure := ?_ }⟩
  · intro sample hsample u hu
    obtain ⟨kind, k, w, hx, hz, rfl⟩ :=
      exists_raw_of_mem_subLineDist_support P hsample
    exact subLineTripleOf_incidence P kind k w hx hz hu
  · intro sample hsample
    obtain ⟨kind, k, w, hx, hz, rfl⟩ :=
      exists_raw_of_mem_subLineDist_support P hsample
    exact subLineTripleOf_compatibility P kind k w hx hz
  · intro sample hsample haxis
    obtain ⟨kind, k, w, hx, hz, rfl⟩ :=
      exists_raw_of_mem_subLineDist_support P hsample
    exact subLineTripleOf_axis_closure P kind k w haxis

end

end MIPStarRE.QPBT
