import MIPStarRE.QPBT.Combining.Witnesses

/-!
# Scalar claims for combining the Pauli bases

This module states the three scalar estimates used to compare the paired line
measurement with the joint and ordered point measurements.  The expectations
retain the subline law and the uniform affine parameter on each extended line
explicitly.  Line-polynomial evaluation uses the existing `Option` completion,
so no field value is substituted when an evaluation is undefined.

## References

The claims are `lem:claim-17-1`, `lem:claim-17-2`, and `lem:claim-17-3` in
`blueprint/src/chapter/ch15_qpbt_combining.tex:852-991`, with paper origin
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1140-1209`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-- Replacing the combined point measurement by the ordered `Z`-then-`X`
point product costs a square-root joint-point error.  This is
`lem:claim-17-1`, paper lines 1140--1145. -/
theorem subline_replace_by_ordered_product :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : AdmissibleParams) (ε δQ δP : ℝ)
        (S : ProjectiveSetting P ε) (points : CombinedPointsWitness S δQ)
        (lines : CombinedLinesWitness S points δP) (sublines : SubLineWitness P),
        |avgOver sublines.D (fun sample =>
            avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) (fun t =>
              let u := directPointToPauli P
                (sample.1.base + t • sample.1.direction)
              let x := projX u
              let z := projZ u
              ∑ fX, ∑ fZ,
                (inner ℂ S.psiHat ((EuclideanSpace.equiv
                  (SixReg P S.toStrategy.ιA S.toStrategy.ιB) ℂ).symm
                    ((S.place .AA'
                        ((lines.T .alice sample.2.1 sample.2.2).effect (fX, fZ)) *
                      S.place .BA''
                        (((points.Q .bob x z).postprocess fun ab =>
                          (some ab.1, some ab.2)).effect
                            (evalOpt sample.2.1 x fX,
                              evalOpt sample.2.2 z fZ))).mulVec S.psiHat))).re)) -
          avgOver sublines.D (fun sample =>
            avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) (fun t =>
              let u := directPointToPauli P
                (sample.1.base + t • sample.1.direction)
              let x := projX u
              let z := projZ u
              ∑ fX, ∑ fZ,
                (inner ℂ S.psiHat ((EuclideanSpace.equiv
                  (SixReg P S.toStrategy.ιA S.toStrategy.ιB) ℂ).symm
                    ((S.place .AA'
                        ((lines.T .alice sample.2.1 sample.2.2).effect (fX, fZ)) *
                      S.place .BA''
                        (S.expPointEffectAtLineAnswer .bob .Z sample.2.2 z fZ *
                          S.expPointEffectAtLineAnswer .bob .X sample.2.1 x fX)).mulVec
                            S.psiHat))).re))| ≤
          C * Real.rpow δQ (1 / 2 : ℝ) := by
  sorry

/-- Removing the trailing `X`-point factor costs the square root of the
line-consistency error, with the source factor `m`.  This is
`lem:claim-17-2`, paper lines 1168--1173; the right-hand point is the corrected
lowercase `z` recorded in the blueprint. -/
theorem subline_remove_X_factor :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : AdmissibleParams) (ε δQ δP : ℝ)
        (S : ProjectiveSetting P ε) (points : CombinedPointsWitness S δQ)
        (lines : CombinedLinesWitness S points δP) (sublines : SubLineWitness P),
        |avgOver sublines.D (fun sample =>
            avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) (fun t =>
              let u := directPointToPauli P
                (sample.1.base + t • sample.1.direction)
              let x := projX u
              let z := projZ u
              ∑ fX, ∑ fZ,
                (inner ℂ S.psiHat ((EuclideanSpace.equiv
                  (SixReg P S.toStrategy.ιA S.toStrategy.ιB) ℂ).symm
                    ((S.place .AA'
                        ((lines.T .alice sample.2.1 sample.2.2).effect (fX, fZ)) *
                      S.place .BA''
                        (S.expPointEffectAtLineAnswer .bob .Z sample.2.2 z fZ *
                          S.expPointEffectAtLineAnswer .bob .X sample.2.1 x fX)).mulVec
                            S.psiHat))).re)) -
          avgOver sublines.D (fun sample =>
            avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) (fun t =>
              let u := directPointToPauli P
                (sample.1.base + t • sample.1.direction)
              let z := projZ u
              ∑ fX, ∑ fZ,
                (inner ℂ S.psiHat ((EuclideanSpace.equiv
                  (SixReg P S.toStrategy.ιA S.toStrategy.ιB) ℂ).symm
                    ((S.place .AA'
                        ((lines.T .alice sample.2.1 sample.2.2).effect (fX, fZ)) *
                      S.place .BA''
                        (S.expPointEffectAtLineAnswer .bob .Z sample.2.2 z fZ)).mulVec
                          S.psiHat))).re))| ≤
          C * (P.m : ℝ) * Real.rpow (deltaLine ε) (1 / 2 : ℝ) := by
  sorry

/-- The remaining `Z`-point correlation is close to one with the fourth-root
error from the point and line constructions.  This is `lem:claim-17-3`, paper
lines 1204--1209. -/
theorem subline_Z_term_near_one :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : AdmissibleParams) (ε δQ δP : ℝ)
        (S : ProjectiveSetting P ε) (points : CombinedPointsWitness S δQ)
        (lines : CombinedLinesWitness S points δP) (sublines : SubLineWitness P),
        |avgOver sublines.D (fun sample =>
            avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) (fun t =>
              let u := directPointToPauli P
                (sample.1.base + t • sample.1.direction)
              let z := projZ u
              ∑ fX, ∑ fZ,
                (inner ℂ S.psiHat ((EuclideanSpace.equiv
                  (SixReg P S.toStrategy.ιA S.toStrategy.ιB) ℂ).symm
                    ((S.place .AA'
                        ((lines.T .alice sample.2.1 sample.2.2).effect (fX, fZ)) *
                      S.place .BA''
                        (S.expPointEffectAtLineAnswer .bob .Z sample.2.2 z fZ)).mulVec
                          S.psiHat))).re)) - 1| ≤
          C * Real.sqrt (P.m : ℝ) *
            (Real.rpow δP (1 / 4 : ℝ) + Real.rpow δQ (1 / 4 : ℝ) +
              Real.rpow ε (1 / 4 : ℝ)) := by
  sorry

end

end MIPStarRE.QPBT
