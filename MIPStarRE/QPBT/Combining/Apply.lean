import MIPStarRE.QPBT.Combining.Points
import MIPStarRE.QPBT.Test.Soundness

/-!
# Applying the classical low-degree test

This module states the two application obligations at the end of the Pauli-basis
combining argument.  The combined-line measurement is recorded both with the error
form asserted by the source and with the weaker estimate established by its first
proof route.  The final witness consists of a projective measurement of a pair of
global bounded individual-degree polynomials.  The proposition-valued declarations
below are intentionally open proof obligations in this skeleton; their statement
links do not claim proof closure.

## References

The combined-line declarations formalize `lem:qld-4-13` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`, with paper source
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034`.
The global-pair declaration formalizes `lem:qld-4-7` in the same blueprint, with
paper source
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1274`.
-/

namespace MIPStarRE.QPBT

noncomputable section

/-- Conditional construction of the extended-line measurements with the source error
`poly(m^2 * epsilon, md / q)`.  This is the source-facing statement of
`lem:qld-4-13`, paper lines 1020--1034.

The printed proof does not establish this error form: its first route gives
`m * poly(epsilon, md / q)`, while its second route gives a different bound and
uses a joint-law decomposition absent from the subline lemma.  The discrepancy is
documented in `docs/paper-gaps/qpbt_combined-lines-error-term.tex` and
`rem:qld-4-13-source-defects` in the blueprint.  The directly indexed line carrier
used by `ExtendedLinesWitness` represents the required extended-dimensional
line-point law without the invalid divisibility guard; it is a directly indexed
line-space construction and does
not identify the source's seed-bearing verifier game with the directly indexed game.
This declaration takes an already constructed point witness; the
source-facing declaration below packages that witness existentially.
-/
theorem exists_extendedLinesWitness_ofPointsWitness :
    ∃ deltaCombine : ℝ → ℝ → ℝ, IsPolyErr₂ deltaCombine ∧
      ∀ (P : AdmissibleParams) (ε δQ : ℝ) (S : ProjectiveSetting P ε)
        (points : CombinedPointsWitness S δQ),
        Nonempty (ExtendedLinesWitness S points
          (deltaCombine ((P.m : ℝ) ^ 2 * ε)
            ((P.m * P.d : ℕ) / (P.q : ℝ)))) := by
  sorry

/-! The source-facing declaration packages the point witness from
`lem:qld-4-10` rather than taking it as an unproved external hypothesis. -/

/-- The source-facing extended-line construction of `lem:qld-4-13`, paper
lines 1020--1034.

The `_ofPointsWitness` companion is the conditional, Lean-only form retained
for calculations that already have a point witness. -/
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
`lem:qld-4-13`; it must not be advertised as that theorem.  The source discrepancy
is analyzed in `docs/paper-gaps/qpbt_combined-lines-error-term.tex`.  As in the
source-facing declaration, the extended questions use the directly indexed line-space
construction.  This conditional declaration takes an already constructed point witness;
the source-facing package below supplies it existentially.  Relating its game to the source's
seed-bearing game requires the transport
and soundness obligations in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.
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

/-- Source-facing package for the established auxiliary estimate.  This is
the same Lean-only bound as `exists_extendedLinesWitness_established_ofPointsWitness`,
with the point witness existentially supplied rather than assumed. -/
theorem exists_extendedLinesWitness_established :
    ∃ deltaQ : ℝ → ℝ, IsPolyErr deltaQ ∧
      ∃ C : ℝ, 0 < C ∧
        ∃ deltaCombine : ℝ → ℝ → ℝ, IsPolyErr₂ deltaCombine ∧
          ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
            ∃ points : CombinedPointsWitness S (deltaQ ε),
              Nonempty (ExtendedLinesWitness S points
                (C * (P.m : ℝ) *
                  deltaCombine ε ((P.m * P.d : ℕ) / (P.q : ℝ)))) := by
  sorry

/-- Construction of the projective global polynomial-pair measurements from
`lem:qld-4-7`, paper lines 1267--1274.  The statement has the source's universal
constants and contains no divisibility hypothesis or residual construction input.

The argument uses low-degree soundness at dimension `2 * m + 2`.  The current
direct carrier realizes the required dimension without assuming
`2 * m + 2 ∣ q`, but it does not itself prove the game-correspondence and
auxiliary-parameter estimates required by the soundness import; those obligations
are exposed by `exists_direct_ld_soundness` and documented in
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
