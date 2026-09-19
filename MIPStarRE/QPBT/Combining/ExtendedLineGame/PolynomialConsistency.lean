import MIPStarRE.QPBT.Combining.DirectLowDegree.PolynomialConsistency
import MIPStarRE.QPBT.Combining.ExtendedLineGame.PassingValue
import MIPStarRE.QPBT.Games.GroundCompression

/-!
# Consistency of compressed extended-polynomial POVMs

The two point-consistency conclusions of direct soundness imply polynomial
consistency on the original expanded local spaces. Ground compression preserves
the point comparisons, and the actual point branch bounds the intermediate
self-consistency error. Both the point and line errors remain in the soundness
input `directPassingErrorEnvelope (deltaQ + deltaL) (m*d/q)`.

## References

* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1278-1288`,
  before `eq:qld-g-42` and `eq:qld-g-43`.
* `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.
* Issue #513 and `audits/2026-09-12_issue-513_composition-compatibility.md`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

/-- Disagreement after the total point readout is a rejection event in the
point/point branch. Wrong-format answers also reject, so no support assumption
on the strategy is needed. -/
theorem direct_point_consistency_le_point_rejection (D : DirectLdParams)
    (S : Strategy (directLdGame D)) :
    consistencyDefect (uniformDistribution (Fin D.m → DirectScalarQ D))
      (fun u a => heteroKron (((S.A (directLdPointQuestionOf D u)).postprocess
        (directLdPointValuesOrZero D)).effect a) 1)
      (fun u a => heteroKron 1 (((S.B (directLdPointQuestionOf D u)).postprocess
        (directLdPointValuesOrZero D)).effect a)) S.ψ ≤
      directLdBranchRejectionProbability D S (.point, .point) := by
  classical
  rw [WinImplications.consistencyDefect_postprocess_eq_mismatch,
    directLdBranchRejectionProbability_point_point_eq]
  apply avgOver_mono
  intro u
  unfold outcomeEventWeight directRejectedMass
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  have hnonneg := outcomeWeight_nonneg S (directLdPointQuestionOf D u)
    (directLdPointQuestionOf D u) a b
  cases a <;> cases b <;>
    simp only [directLdWinPredicate, directLdPointQuestionOf, validDirectLdAnswer,
      directLdPointValuesOrZero, Bool.true_and, Bool.false_and, Bool.and_false,
      Bool.false_eq_true, decide_eq_true_eq, if_false, if_true] <;>
    split_ifs <;> simp_all [directLdPointQuestionOf]

namespace ExtendedLineGame

variable {P : AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
variable {setting : ProjectiveSetting P epsilon}
variable {points : CombinedPointsWitness setting deltaQ}

/-- The point measurements used in direct soundness inherit the actual joint
point self-consistency bound. This is the intermediate comparison needed to
connect the two soundness point conclusions. -/
theorem point_consistency_le (lines : ExtendedLinesWitness setting points deltaL) :
    consistencyDefect
      (uniformDistribution (Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd))
      (fun u a => heteroKron
        ((((strategy lines).A (directLdPointQuestionOf P.extendedDirectLd u)).postprocess
          (directLdPointValuesOrZero P.extendedDirectLd)).effect a) 1)
      (fun u a => heteroKron 1
        ((((strategy lines).B (directLdPointQuestionOf P.extendedDirectLd u)).postprocess
          (directLdPointValuesOrZero P.extendedDirectLd)).effect a)) (pairState setting) ≤
        deltaQ :=
  (direct_point_consistency_le_point_rejection P.extendedDirectLd (strategy lines)).trans
    (point_point_rejection_le lines)

/-- Compressing any direct-soundness polynomial POVMs gives cross-player
polynomial consistency on the original expanded spaces. The assumptions are
exactly the two evaluated point comparisons, not polynomial consistency.
The point error is derived from the supplied strategy's self-consistency.

For the actual direct soundness application take both `etaA` and `etaB` to be
`deltaLd a b (directPassingErrorEnvelope (deltaQ + deltaL) (m*d/q)) q (2*m+2) d 1`.
The two errors in this envelope must both be retained. This operator estimate
supports `lem:qld-4-7`, paper lines 1278--1288; the remaining ordered-correlation
and separation obligations are tracked by issues #515 and #598. -/
theorem compressed_polynomial_consistency_le
    (lines : ExtendedLinesWitness setting points deltaL)
    (A : DirectPolyMeasTuple P.extendedDirectLd (projectiveStrategy lines).ιA)
    (B : DirectPolyMeasTuple P.extendedDirectLd (projectiveStrategy lines).ιB)
    (etaA etaB : ℝ)
    (hA : consistencyDefect
      (uniformDistribution (Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd))
      (fun u a => heteroKron ((A.postprocess (evalDirectPolyTupleAt u)).effect a) 1)
      (fun u a => heteroKron 1
        ((((projectiveStrategy lines).B
          (directLdPointQuestionOf P.extendedDirectLd u)).postprocess
            (directLdPointValuesOrZero P.extendedDirectLd)).effect a))
      (projectiveStrategy lines).ψ ≤ etaA)
    (hB : consistencyDefect
      (uniformDistribution (Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd))
      (fun u a => heteroKron
        ((((projectiveStrategy lines).A
          (directLdPointQuestionOf P.extendedDirectLd u)).postprocess
            (directLdPointValuesOrZero P.extendedDirectLd)).effect a) 1)
      (fun u a => heteroKron 1 ((B.postprocess (evalDirectPolyTupleAt u)).effect a))
      (projectiveStrategy lines).ψ ≤ etaB) :
    consistencyDefect (uniformDistribution Unit)
      (fun _ g => heteroKron ((groundCompressMeasurement none A).effect g) 1)
      (fun _ g => heteroKron 1 ((groundCompressMeasurement none B).effect g))
      (pairState setting) ≤
        etaA + 2 * Real.sqrt (deltaQ + etaB) + ((2 * P.m + 2) * P.d : ℝ) / P.q := by
  classical
  have hAc := (consistency_defect_ground_compress_measurement_postprocess
    (uniformDistribution (Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd))
    none none (pairState setting) (fun _ => A)
    (fun u => dilatedMeasurement (default : DirectLdAnswer P.extendedDirectLd)
      ((strategy lines).B (directLdPointQuestionOf P.extendedDirectLd u)))
    (fun u => evalDirectPolyTupleAt u)
    (fun _ => directLdPointValuesOrZero P.extendedDirectLd)).symm.trans_le hA
  have hBc := (consistency_defect_ground_compress_measurement_postprocess
    (uniformDistribution (Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd))
    none none (pairState setting)
    (fun u => dilatedMeasurement (default : DirectLdAnswer P.extendedDirectLd)
      ((strategy lines).A (directLdPointQuestionOf P.extendedDirectLd u))) (fun _ => B)
    (fun _ => directLdPointValuesOrZero P.extendedDirectLd)
    (fun u => evalDirectPolyTupleAt u)).symm.trans_le hB
  simp only [ground_compress_dilated_measurement] at hAc hBc
  simpa [AdmissibleParams.extendedDirectLd, Nat.cast_add, Nat.cast_mul] using
    direct_polynomial_consistency_le_point_bounds P.extendedDirectLd
      (groundCompressMeasurement none A) (groundCompressMeasurement none B)
      (fun u => ((strategy lines).A (directLdPointQuestionOf P.extendedDirectLd u)).postprocess
        (directLdPointValuesOrZero P.extendedDirectLd))
      (fun u => ((strategy lines).B (directLdPointQuestionOf P.extendedDirectLd u)).postprocess
        (directLdPointValuesOrZero P.extendedDirectLd))
      (pairState setting) (pairState_norm setting) etaA etaB deltaQ hAc hBc
      (point_consistency_le lines)

end ExtendedLineGame

end

end MIPStarRE.QPBT
