import MIPStarRE.QPBT.Combining.Points
import MIPStarRE.QPBT.Combining.ExtendedLines.Estimates
import MIPStarRE.QPBT.Combining.ErrorBounds
import MIPStarRE.QPBT.Test.SoundnessDefs

/-!
# Applying the classical low-degree test

This module states the two application obligations at the end of the Pauli-basis
combining argument.  Directly indexed combined-line measurements are recorded both
with the error form printed in the source and with the weaker estimate established by
its first proof route.  The final witness consists of a projective measurement of a
pair of global bounded individual-degree polynomials. The directly indexed
established-error construction is proved; the printed-error and global-pair
existence assertions remain open.

## References

The combined-line declarations record directly indexed auxiliary forms of
`lem:qld-4-13` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`, with paper source
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034`.
The global-pair declaration formalizes `lem:qld-4-7` in the same blueprint, with
paper source
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1274`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-- Conditional directly indexed construction of the extended-line measurements with
the error expression `poly(m^2 * epsilon, md / q)` printed in `lem:qld-4-13`, paper
lines 1020--1034. This is an auxiliary obligation, not the source-facing statement.

The printed proof does not establish this error form: its first route gives
`m * poly(epsilon, md / q)`, while its second route gives a different bound and
uses a joint-law decomposition absent from the subline lemma.  The discrepancy is
documented in `docs/paper-gaps/qpbt_combined-lines-error-term.tex` and
`rem:qld-4-13-source-defects` in the blueprint. `ExtendedLinesWitness` uses the
directly indexed question carrier and line-point law documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`, and the completed answer
alphabet documented in `docs/paper-gaps/qpbt_combined-lines-error-term.tex`.
Their conversion to the source's verifier game remains open. This declaration takes
an already constructed point witness; the companion obligation below supplies that
witness existentially.

**Error contract:** the polynomial bound printed in the source is carried
by `IsPolyErr₂`, which states the corrected sum form
`f x y ≤ C * (x ^ r + y ^ s)` with `1 ≤ C` and positive exponents on the
closed nonnegative quadrant, in place of the product form `C * (x * y) ^ C`
of the source shorthand at `04_preliminaries.tex:22-29`.  The correction and
the two-dimensional strategy that refutes the product form are recorded in
`docs/paper-gaps/qpbt_pasting-product-error.tex` and tracked by issue #196.
Here `poly(m^2 * epsilon, md / q)` is read in that sense.
-/
theorem exists_extendedLinesWitness_ofPointsWitness :
    ∃ deltaCombine : ℝ → ℝ → ℝ, IsPolyErr₂ deltaCombine ∧
      ∀ (P : AdmissibleParams) (ε δQ : ℝ) (S : ProjectiveSetting P ε)
        (points : CombinedPointsWitness S δQ),
        Nonempty (ExtendedLinesWitness S points
          (deltaCombine ((P.m : ℝ) ^ 2 * ε)
            ((P.m * P.d : ℕ) / (P.q : ℝ)))) := by
  sorry

/-! The following directly indexed obligation supplies the point witness from
`lem:qld-4-10` rather than taking it as an external hypothesis. -/

/-- Directly indexed extended-line obligation with the numerical error expression
printed in `lem:qld-4-13`, paper lines 1020--1034.

The `_ofPointsWitness` companion assumes a point witness, while this declaration
supplies one existentially. Both declarations use the directly indexed questions,
law, and completed answer alphabet, so neither is the source-facing paper statement.

**Error contract:** the polynomial bound printed in the source is carried
by `IsPolyErr₂`, which states the corrected sum form
`f x y ≤ C * (x ^ r + y ^ s)` with `1 ≤ C` and positive exponents on the
closed nonnegative quadrant, in place of the product form `C * (x * y) ^ C`
of the source shorthand at `04_preliminaries.tex:22-29`.  The correction and
the two-dimensional strategy that refutes the product form are recorded in
`docs/paper-gaps/qpbt_pasting-product-error.tex` and tracked by issue #196.
Here `poly(m^2 * epsilon, md / q)` is read in that sense. -/
theorem exists_extendedLinesWitness :
    ∃ deltaQ : ℝ → ℝ, IsPolyErr deltaQ ∧
      ∃ deltaCombine : ℝ → ℝ → ℝ, IsPolyErr₂ deltaCombine ∧
        ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
          ∃ points : CombinedPointsWitness S (deltaQ ε),
            Nonempty (ExtendedLinesWitness S points
              (deltaCombine ((P.m : ℝ) ^ 2 * ε)
                ((P.m * P.d : ℕ) / (P.q : ℝ)))) := by
  sorry

/-- Construction of the extended-line measurements with the estimate actually
delivered by the first proof route, `C * m * poly(epsilon, md / q)`.

This is an established auxiliary form of the argument, not the source-labelled
`lem:qld-4-13`; it must not be advertised as that theorem. The source discrepancy
is analyzed in `docs/paper-gaps/qpbt_combined-lines-error-term.tex`. As in the
companion directly indexed declaration, the extended questions use the directly
indexed line-space construction. This conditional declaration takes an already
constructed point witness; the obligation below supplies it existentially. Relating
its game to the source's seed-bearing game requires the transport and soundness
obligations in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.

**Error contract:** the polynomial bound printed in the source is carried
by `IsPolyErr₂`, which states the corrected sum form
`f x y ≤ C * (x ^ r + y ^ s)` with `1 ≤ C` and positive exponents on the
closed nonnegative quadrant, in place of the product form `C * (x * y) ^ C`
of the source shorthand at `04_preliminaries.tex:22-29`.  The correction and
the two-dimensional strategy that refutes the product form are recorded in
`docs/paper-gaps/qpbt_pasting-product-error.tex` and tracked by issue #196.
Here `poly(epsilon, md / q)` is read in that sense.
-/
theorem exists_extendedLinesWitness_established_ofPointsWitness :
    ∃ C : ℝ, 0 < C ∧
      ∃ deltaCombine : ℝ → ℝ → ℝ, IsPolyErr₂ deltaCombine ∧
        ∀ (P : AdmissibleParams) (ε δQ : ℝ) (S : ProjectiveSetting P ε)
          (points : CombinedPointsWitness S δQ),
          Nonempty (ExtendedLinesWitness S points
            (C * (P.m : ℝ) *
              deltaCombine ε ((P.m * P.d : ℕ) / (P.q : ℝ)))) := by
  sorry

/-- Directly indexed construction for the auxiliary estimate
`C * m * poly(epsilon, md / q)`. This has the same directly indexed estimate as
`exists_extendedLinesWitness_established_ofPointsWitness`, with the point witness
existentially supplied rather than assumed.

Its question carrier and line-point law are documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`; its `Option`-completed answer
alphabet is documented in `docs/paper-gaps/qpbt_combined-lines-error-term.tex`.
Transport to `lem:qld-4-13` must convert this completed comparison to the source's
sum over field answers, including degenerate zero-direction singleton lines.

**Error contract:** the polynomial bound printed in the source is carried
by `IsPolyErr₂`, which states the corrected sum form
`f x y ≤ C * (x ^ r + y ^ s)` with `1 ≤ C` and positive exponents on the
closed nonnegative quadrant, in place of the product form `C * (x * y) ^ C`
of the source shorthand at `04_preliminaries.tex:22-29`.  The correction and
the two-dimensional strategy that refutes the product form are recorded in
`docs/paper-gaps/qpbt_pasting-product-error.tex` and tracked by issue #196.
Here `poly(epsilon, md / q)` is read in that sense. -/
theorem exists_extendedLinesWitness_established :
    ∃ deltaQ : ℝ → ℝ, IsPolyErr deltaQ ∧
      ∃ C : ℝ, 0 < C ∧
        ∃ deltaCombine : ℝ → ℝ → ℝ, IsPolyErr₂ deltaCombine ∧
          ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
            ∃ points : CombinedPointsWitness S (deltaQ ε),
              Nonempty (ExtendedLinesWitness S points
                (C * (P.m : ℝ) *
                  deltaCombine ε ((P.m * P.d : ℕ) / (P.q : ℝ)))) := by
  classical
  obtain ⟨deltaQ, hdeltaQ, hpoints⟩ := exists_combinedPointsWitness
  obtain ⟨deltaP, hdeltaP, hlines⟩ :=
    exists_combinedLinesWitness_ofPointsWitness deltaQ hdeltaQ
  obtain ⟨constant, hconstant, hnear⟩ := subline_joint_overlap_near_one_at
  obtain ⟨deltaCombine, hdeltaCombine, hscalar⟩ :=
    exists_combining_polynomial_bound deltaQ hdeltaQ deltaP hdeltaP constant hconstant.le
  refine ⟨deltaQ, hdeltaQ, 1, by norm_num, deltaCombine, hdeltaCombine, ?_⟩
  intro P ε S
  obtain ⟨points⟩ := hpoints P ε S
  obtain ⟨lines⟩ := hlines P ε S points
  obtain ⟨sublines⟩ := exists_subLineWitness P
  have hplaced (first second : Placement) (hopposite : first.IsOpposite second) :
      consistencyDefect (directLinePointDist P.extendedDirectLd)
        (fun sample answer => S.place first
          (((sublines.extendedMeasurement lines first.side sample.1).postprocess
            (fun polynomial => (directEvalOpt sample.1 sample.2 polynomial).map
              (extendedDirectScalarEquiv P))).effect answer))
        (fun sample answer => S.place second
          (((points.Q second.side (projX (directPointToPauli P sample.2))
            (projZ (directPointToPauli P sample.2))).postprocess (fun values => some
              ((directPointToPauli P sample.2) (alphaVar P.m) * values.1 +
                (directPointToPauli P sample.2) (betaVar P.m) * values.2))).effect answer))
        S.psiHat ≤ (P.m : ℝ) * deltaCombine ε ((P.m * P.d : ℕ) / (P.q : ℝ)) := by
    refine (le_min ?_ ?_).trans
      (hscalar ε ((P.m * P.d : ℕ) / (P.q : ℝ)) (P.m : ℝ)
        S.eps_nonneg (by positivity) (by exact_mod_cast P.one_le_m))
    · unfold consistencyDefect
      calc
        _ ≤ avgOver (directLinePointDist P.extendedDirectLd) (fun _ => 1) :=
          avgOver_mono _ _ _ fun sample =>
            consistencyDefect_integrand_le_one S first second hopposite _ _
        _ = 1 := avgOver_const_of_isProbability _ (directLinePointDist_isProbability _) 1
    · refine (sublines.extended_consistencyDefect_le lines first second hopposite).trans ?_
      exact (le_abs_self _).trans (by
        simpa only [abs_sub_comm] using
          hnear P ε (deltaQ ε) (deltaP ε ((P.m * P.d : ℕ) / (P.q : ℝ)))
            S points lines sublines first second hopposite)
  refine ⟨points, ⟨{
    Qline := sublines.extendedMeasurement lines
    axis_degree := sublines.extendedMeasurement_axis_degree lines
    consistent_alice := ?_
    consistent_bob := ?_ }⟩⟩
  · simp only [one_mul]
    with_unfolding_all exact hplaced .AA' .BA'' trivial
  · simp only [one_mul]
    with_unfolding_all exact hplaced .BB' .AB'' trivial

/-- Construction of the projective global polynomial-pair measurements from
`lem:qld-4-7`, paper lines 1267--1274.  The statement has the source's universal
constants and contains no divisibility hypothesis or residual construction input.

The argument uses low-degree soundness at dimension `2 * m + 2`.  The current
direct carrier realizes the required dimension without assuming
`2 * m + 2 ∣ q`.  `exists_direct_ld_soundness` proves that soundness statement
for the directly indexed game by applying `MIPStarRE.LDT.Test.mainFormal` and
verifying `400 M d <= N` at each LDT application dimension `M`, with sampling
count `N = 2560000 M^3 d`.  The source import at seed-indexed dimension `M`
instead chooses `K = M^3 d` for a tensor-code theorem requiring
`K >= 12 M (d + 1)`.  The direct proof establishes neither that bound nor the
claimed tensor-code game correspondence.  Both source-import obligations
remain open and are documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.  Absorption of the established
combined-lines prefactor into the final universal constants is to use
`deltaQld_mono` on its stated source parameter domain.
-/
theorem exists_globalPairWitness :
    ∃ a b : ℝ, 1 < a ∧ 0 < b ∧ b < 1 ∧
      ∀ (P : AdmissibleParams) (ε : ℝ), 0 < ε →
        ∀ S : ProjectiveSetting P ε,
          Nonempty (GlobalPairWitness S (deltaQld a b ε P.m P.d P.q)) := by
  sorry

end

end MIPStarRE.QPBT
