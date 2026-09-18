import MIPStarRE.QPBT.Combining.Points
import MIPStarRE.QPBT.Combining.PairCompletion
import MIPStarRE.QPBT.Combining.ExtendedLines.Estimates
import MIPStarRE.QPBT.Combining.ActualErrorBounds
import MIPStarRE.QPBT.Combining.ExtendedLineGame.PairPointConsistency
import MIPStarRE.QPBT.Combining.PointErrorObstruction
import MIPStarRE.QPBT.Combining.ErrorObstruction
import MIPStarRE.QPBT.Test.SoundnessDefs

/-!
# Applying the classical low-degree test

This module states the two application obligations at the end of the Pauli-basis
combining argument.  Directly indexed combined-line measurements are recorded both
with the error form printed in the source and with the weaker estimate established by
its first proof route.  The final witness consists of a projective measurement of a
pair of global bounded individual-degree polynomials.  The existence assertions below
record the measurements and quantitative estimates required by the combining argument.
The established direct-line constructor, its conditional supplied-point companion,
and the source global-pair theorem are proved.  The printed error form of the
combined-line lemma remains an open source gap, tracked by issue #598.

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

/-! The directly indexed obligations below share the extended-line carrier.
The first keeps the error expression printed in the source and supplies its
point witness existentially; it is a source-gap declaration with an open proof.
The second is the conditional auxiliary for a polynomially controlled supplied
point family, carrying the error the first proof route establishes; the third
supplies that family existentially. -/

/-- Directly indexed extended-line obligation with the numerical error expression
printed in `lem:qld-4-13`, paper lines 1020--1034.

Both this declaration and the established forms below use the directly indexed
questions, law, and completed answer alphabet, so neither is the source-facing
paper statement.

The first proof route's term `m * epsilon ^ (1 / 4)` cannot be absorbed into
the printed error arguments, even after capping it by one and restricting to
admissible parameters; `not_exists_combining_quarter_power_bound` proves this
scalar obstruction. It does not refute this existence assertion, which requires
a different estimate. See `docs/paper-gaps/qpbt_combined-lines-error-term.tex`
and issues #510 and #598.

**Open source gap, carried deliberately:** the printed error form is
established by neither source route, and no route to it is known here. This
declaration is retained so that the source assertion stays visible and is
neither marked proved nor removed; its `sorry` records the gap and must not be
read as a proof. No Lean argument depends on it. Every consumer, in particular
`exists_globalPairWitness`, routes through `exists_extendedLinesWitness_established`,
whose error `C * m * poly(epsilon, md / q)` is the form the first route actually
delivers. What remains open is tracked by issue #598; the earlier issues #509
and #510 were closed by their obstruction pull requests without a proof of the
printed assertion, and are not reopened.

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

/-- Conditional existence of extended-line measurements with the first-route
estimate `C * m * poly(epsilon, md / q)`, for a polynomially controlled supplied
point family.

This conditional auxiliary uses the error form established by the first proof
route. It is not the source-labelled `lem:qld-4-13` and must not be advertised as
that theorem; the source discrepancy is analyzed in
`docs/paper-gaps/qpbt_combined-lines-error-term.tex` and tracked by issue #598.
As in the companion directly indexed declarations, the extended questions use the
directly indexed line-space construction and the comparisons use the completed
answer alphabet. Relating its game to the source's seed-bearing game requires the
transport and soundness obligations in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`. The conditional blueprint
entry is `lem:qld-4-13-established-given-points`.

**Domain repair (issue #511):** the former statement quantified over an arbitrary
scalar point error `δQ` after choosing the line error, although that line error
must depend on the supplied point error. As stated it was false: the supplied
family may answer deterministically with a quadratic in the point coordinates at
zero strategy error, whose axis-line defect stays bounded below as `q` grows,
while any `IsPolyErr₂` bound tends to zero there. The repaired domain takes the
point-error function `deltaQ` with its control hypothesis `IsPolyErr deltaQ`
before choosing the line error, and assumes a point witness at `deltaQ ε`, which
is exactly the family supplied by `exists_combinedPointsWitness`. This repeats one
level up the issue #389 repair of `exists_combinedLinesWitness_ofPointsWitness`.
The refutation of the former domain, and the provenance of the removed printed-form
companion `exists_extendedLinesWitness_ofPointsWitness` of issue #509, are preserved in
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`. The established dimension
factor `C * m` is kept explicit in the conclusion rather than absorbed.

**Error contract:** the polynomial bound printed in the source is carried
by `IsPolyErr₂`, which states the corrected sum form
`f x y ≤ C * (x ^ r + y ^ s)` with `1 ≤ C` and positive exponents on the
closed nonnegative quadrant, in place of the product form `C * (x * y) ^ C`
of the source shorthand at `04_preliminaries.tex:22-29`.  The correction and
the two-dimensional strategy that refutes the product form are recorded in
`docs/paper-gaps/qpbt_pasting-product-error.tex` and tracked by issue #196.
Here `poly(epsilon, md / q)` is read in that sense.

The proof uses the point, line, and subline constructions together with both
opposite-placement comparisons. -/
theorem exists_extendedLinesWitness_established_ofPointsWitness
    (deltaQ : ℝ → ℝ) (hdeltaQ : IsPolyErr deltaQ) :
    ∃ C : ℝ, 0 < C ∧
      ∃ deltaCombine : ℝ → ℝ → ℝ, IsPolyErr₂ deltaCombine ∧
        ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
          (points : CombinedPointsWitness S (deltaQ ε)),
          Nonempty (ExtendedLinesWitness S points
            (C * (P.m : ℝ) *
              deltaCombine ε ((P.m * P.d : ℕ) / (P.q : ℝ)))) := by
  classical
  obtain ⟨deltaP, hdeltaP, hlines⟩ :=
    exists_combinedLinesWitness_ofPointsWitness deltaQ hdeltaQ
  obtain ⟨constant, hconstant, hnear⟩ := subline_joint_overlap_near_one_at
  obtain ⟨deltaCombine, hdeltaCombine, hscalar⟩ :=
    exists_combining_polynomial_bound deltaQ hdeltaQ deltaP hdeltaP constant hconstant.le
  refine ⟨1, by norm_num, deltaCombine, hdeltaCombine, ?_⟩
  intro P ε S points
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
  refine ⟨{
    Qline := sublines.extendedMeasurement lines
    axis_degree := sublines.extendedMeasurement_axis_degree lines
    consistent_alice := ?_
    consistent_bob := ?_ }⟩
  · simp only [one_mul]
    with_unfolding_all exact hplaced .AA' .BA'' trivial
  · simp only [one_mul]
    with_unfolding_all exact hplaced .BB' .AB'' trivial

/-- Directly indexed construction for the auxiliary estimate
`C * m * poly(epsilon, md / q)`. This has the same directly indexed estimate as
`exists_extendedLinesWitness_established_ofPointsWitness`, with the point witness
existentially supplied rather than assumed.

Its question carrier and line-point law are documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`; its `Option`-completed answer
alphabet is documented in `docs/paper-gaps/qpbt_combined-lines-error-term.tex`.
Transport to `lem:qld-4-13` must convert this completed comparison to the source's
sum over field answers, including degenerate zero-direction singleton lines. The
printed error form of `lem:qld-4-13` is not claimed here and remains an open
source gap, tracked by issue #598.

**Error contract:** the polynomial bound printed in the source is carried
by `IsPolyErr₂`, which states the corrected sum form
`f x y ≤ C * (x ^ r + y ^ s)` with `1 ≤ C` and positive exponents on the
closed nonnegative quadrant, in place of the product form `C * (x * y) ^ C`
of the source shorthand at `04_preliminaries.tex:22-29`.  The correction and
the two-dimensional strategy that refutes the product form are recorded in
`docs/paper-gaps/qpbt_pasting-product-error.tex` and tracked by issue #196.
Here `poly(epsilon, md / q)` is read in that sense.

The proof constructs the polynomially controlled point family of `lem:qld-4-10`
and applies the conditional companion above to that same family. -/
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
  obtain ⟨C, hC, deltaCombine, hdeltaCombine, hlines⟩ :=
    exists_extendedLinesWitness_established_ofPointsWitness deltaQ hdeltaQ
  refine ⟨deltaQ, hdeltaQ, C, hC, deltaCombine, hdeltaCombine, ?_⟩
  intro P ε S
  obtain ⟨points⟩ := hpoints P ε S
  exact ⟨points, hlines P ε S points⟩

/-- Construction of the projective global polynomial-pair measurements from
`lem:qld-4-7`, paper lines 1267--1274.  The statement has the source's universal
constants and contains no divisibility hypothesis or residual construction input.

The argument uses low-degree soundness at dimension `2 * m + 2`.  The current
direct carrier realizes the required dimension without assuming
`2 * m + 2 ∣ q`.  `exists_direct_ld_soundness` proves that soundness statement
for the directly indexed game by applying `MIPStarRE.LDT.Test.mainFormal` and
verifying `400 M d <= N` at each LDT application dimension `M`, with sampling
count `N = 2560000 M^3 d`.  At seed-indexed dimension `M`, the source instead
chooses `K = M^3 d` while invoking a tensor-code theorem that requires
`K >= 12 M (d + 1)`, and it asserts a correspondence with the tensor-code game.
The direct proof establishes neither assertion.  Both remain open and are documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.

The independent algebraic restriction, projective completion, and retained-overlap
estimates remain available in `PairCompletion.lean`.

The proof below composes the established direct-line construction with the actual
rounded polynomial-pair construction. Its four defects are bounded both by one
and by the constructed error. `exists_actual_rounded_global_pair_error_bound`
absorbs their minimum, including the eighth-root rounding term and both point
and line errors, for every nonnegative strategy error. This alternative proof
does not require an identification with the source's seed-bearing auxiliary game.
-/
theorem exists_globalPairWitness :
    ∃ a b : ℝ, 1 < a ∧ 0 < b ∧ b < 1 ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
        Nonempty (GlobalPairWitness S (deltaQld a b ε P.m P.d P.q)) := by
  obtain ⟨pointError, hpoint, C, hC, lineError, hline, hlines⟩ :=
    exists_extendedLinesWitness_established
  obtain ⟨a, b, ha, hb, hb1, hpairs⟩ :=
    ExtendedLineGame.exists_pairWitness_of_points_lines
  obtain ⟨A, B, hA, hB, hB1, hscalar⟩ :=
    exists_actual_rounded_global_pair_error_bound pointError hpoint lineError hline
      C a b hC.le ha hb hb1
  refine ⟨A, B, hA, hB, hB1, ?_⟩
  intro P ε S
  obtain ⟨points, ⟨lines⟩⟩ := hlines P ε S
  obtain ⟨pair⟩ := hpairs P ε (pointError ε)
    (C * (P.m : ℝ) * lineError ε ((P.m * P.d : ℕ) / (P.q : ℝ))) S points lines
  have hbound := hscalar P ε S.eps_nonneg
  simp only [Nat.cast_mul] at hbound
  refine ⟨{ pair with point_consistent_alice := ?_, point_consistent_bob := ?_ }⟩
  · intro W
    refine (le_min (show _ ≤ (1 : ℝ) from ?_) (pair.point_consistent_alice W)).trans ?_
    · unfold consistencyDefect
      calc
        _ ≤ avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun _ => 1) :=
          avgOver_mono _ _ _ fun u => consistencyDefect_integrand_le_one
            S .AA' .BA'' (by trivial) _ _
        _ = 1 := avgOver_const_of_isProbability _ (uniformDistribution_isProbability _) 1
    · with_unfolding_all simpa only [Nat.cast_mul, Real.rpow_eq_pow] using hbound
  · intro W
    refine (le_min (show _ ≤ (1 : ℝ) from ?_) (pair.point_consistent_bob W)).trans ?_
    · unfold consistencyDefect
      calc
        _ ≤ avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun _ => 1) :=
          avgOver_mono _ _ _ fun u => consistencyDefect_integrand_le_one
            S .BB' .AB'' (by trivial) _ _
        _ = 1 := avgOver_const_of_isProbability _ (uniformDistribution_isProbability _) 1
    · with_unfolding_all simpa only [Nat.cast_mul, Real.rpow_eq_pow] using hbound

end

end MIPStarRE.QPBT
