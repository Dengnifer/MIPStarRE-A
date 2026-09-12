import MIPStarRE.QPBT.Combining.Lines.SubLineMixture
import MIPStarRE.QPBT.Combining.Lines.RestrictedAverage
import MIPStarRE.QPBT.Combining.Lines.ConsistencyPositivity

/-!
# The joint projected law of the concrete sub-line distribution

The two projected line-point pairs of `subLineDist` form a mixture of products
of restricted line-point laws. This is stronger than the two separate marginal
identities in `SubLineWitness`, and is proved for the concrete sampling law.
It gives the consistency estimate used by the second combined-lines argument.

## References

These are directly indexed auxiliary results for blueprint
`lem:qld-subline-joint-mixture`, supporting the second route in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1241-1245`.
The sampling construction is at lines 1071-1116. The source's sub-line statement
does not supply the joint identity. See
`docs/paper-gaps/qpbt_combined-lines-error-term.tex` and issue #510.
The direct carrier and law retain the scope distinction documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-- Retain both projected line-point pairs of one extended line-point sample. -/
def subLineJointProjection {P : AdmissibleParams} (sample : SubLinePointSample P) :
    (LineDesc P.toLdParams × (Fin P.m → PauliScalar P)) ×
      (LineDesc P.toLdParams × (Fin P.m → PauliScalar P)) :=
  ((sample.1.2.1, projX (directPointToPauli P sample.2)),
    (sample.1.2.2, projZ (directPointToPauli P sample.2)))

/-- At a fixed kind and extended coordinate, the two projected line-point pairs
are independent restricted samples. This reuses the joint sampling identity
`subLineBranchRaw_map_joint`, including zero directions and singleton lines. -/
theorem subLineBranchDist_map_joint_at (P : AdmissibleParams)
    (kind : LineKind) (k : Fin (2 * P.m + 2)) :
    (subLinePointDist P
        ((Distribution.prod (uniformDistribution (SubLinePointDir P))
            (Distribution.prod (subLineSeedDist P (subLineXIndex P k))
              (subLineSeedDist P (subLineZIndex P k)))).map
          fun w => subLineTripleOf P kind k w)).map subLineJointProjection =
      Distribution.prod (restrictedLinePointDist P kind (subLineXIndex P k))
        (restrictedLinePointDist P kind (subLineZIndex P k)) := by
  classical
  have h := congrArg (fun μ => μ.map
    (fun w : (LineDesc P.toLdParams × LineDesc P.toLdParams) ×
        ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)) =>
      ((w.1.1, w.2.1), (w.1.2, w.2.2)))) (subLineBranchRaw_map_joint P kind k)
  simp only [Distribution.map_map] at h
  unfold subLinePointDist
  rw [Distribution.prod_map_left, Distribution.map_map, Distribution.map_map]
  rw [restrictedLinePointDist_eq_map_prod, restrictedLinePointDist_eq_map_prod,
    Distribution.prod_map_left, Distribution.prod_map_right, Distribution.map_map]
  exact h

/-- The joint projected law of one line kind is the mixture over the source
coordinate indices assigned by the concrete extended-coordinate sampler. -/
theorem subLineBranchDist_map_joint (P : AdmissibleParams) (kind : LineKind) :
    (subLinePointDist P (subLineBranchDist P kind)).map subLineJointProjection =
      Distribution.bind (subLineComponentBranch P kind) (fun c =>
        Distribution.prod (restrictedLinePointDist P c.1 c.2.1)
          (restrictedLinePointDist P c.1 c.2.2)) := by
  classical
  rw [subLineBranchDist_eq_bind, subLinePointDist_bind, Distribution.bind_map,
    subLineComponentBranch, Distribution.bind_map_left]
  exact Distribution.bind_congr_support _ _ _ fun k _ =>
    subLineBranchDist_map_joint_at P kind k

/-- The concrete directly indexed sub-line law has the joint restricted-product
decomposition needed at paper lines 1241-1245. This is a proved property of
`subLineDist`, not an additional field assumed of arbitrary `SubLineWitness`.
Blueprint `lem:qld-subline-joint-mixture`. -/
theorem subLineDist_map_joint (P : AdmissibleParams) :
    (subLinePointDist P (subLineDist P)).map subLineJointProjection =
      Distribution.bind (subLineComponentDist P) (fun c =>
        Distribution.prod (restrictedLinePointDist P c.1 c.2.1)
          (restrictedLinePointDist P c.1 c.2.2)) := by
  classical
  rw [subLineDist, subLinePointDist_bind, Distribution.bind_map,
    subLineComponentDist, Distribution.bind_bind]
  refine Distribution.bind_congr_support _ _ _ fun c _ => ?_
  fin_cases c
  · exact subLineBranchDist_map_joint P .axis
  · exact subLineBranchDist_map_joint P .diagonal

/-- A nonnegative function of both projected line-point pairs has average at
most `4m^2` times its average over independent source line-point samples.
This proves the second-route comparison for the concrete directly indexed law,
without replacing its joint law by the separate marginal identities. -/
theorem avgOver_subLineJointProjection_le {P : AdmissibleParams}
    (f : ((LineDesc P.toLdParams × (Fin P.m → PauliScalar P)) ×
      (LineDesc P.toLdParams × (Fin P.m → PauliScalar P))) → ℝ)
    (hf : ∀ sample, 0 ≤ f sample) :
    avgOver (subLinePointDist P (subLineDist P)) (fun s => f (subLineJointProjection s)) ≤
      4 * (P.m : ℝ) ^ 2 * avgOver
        (Distribution.prod (linePointDist P.toLdParams) (linePointDist P.toLdParams)) f := by
  classical
  rw [← Distribution.avgOver_map (subLinePointDist P (subLineDist P))
    subLineJointProjection f, subLineDist_map_joint, avgOver_bind]
  calc
    _ ≤ avgOver (subLineComponentDist P) (fun _ => 4 * (P.m : ℝ) ^ 2 * avgOver
        (Distribution.prod (linePointDist P.toLdParams) (linePointDist P.toLdParams)) f) := by
      apply avgOver_mono
      intro c
      exact avgOver_prod_restrictedLinePointDist_le (P := P) f hf c.1 c.1 c.2.1 c.2.2
    _ = _ := avgOver_const_of_isProbability _ (subLineComponentDist_isProbability P) _

/-- Conditional consistency consequence of the proved joint decomposition:
given a joint line witness of error `δP`, its completed evaluations have defect
at most `4m^2 δP` at the two blocks of one sampled extended point.

This is the directly indexed form of the estimate at paper lines 1241-1245,
with the supplied line witness displayed explicitly. It does not construct that
witness or prove the printed error form of `exists_extendedLinesWitness`.
Blueprint `rem:qld-subline-joint-consistency`; issue #510. -/
theorem subLineDist_consistencyDefect_le_ofLinesWitness {P : AdmissibleParams}
    {ε δQ δP : ℝ} (S : ProjectiveSetting P ε)
    (points : CombinedPointsWitness S δQ) (lines : CombinedLinesWitness S points δP)
    (p1 p2 : Placement) (hopposite : p1.IsOpposite p2) :
    consistencyDefect (subLinePointDist P (subLineDist P))
      (fun s answer => S.place p1
        (((lines.T p1.side s.1.2.1 s.1.2.2).postprocess fun fs =>
          (evalOpt s.1.2.1 (projX (directPointToPauli P s.2)) fs.1,
            evalOpt s.1.2.2 (projZ (directPointToPauli P s.2)) fs.2)).effect answer))
      (fun s answer => S.place p2
        (((points.Q p2.side (projX (directPointToPauli P s.2))
          (projZ (directPointToPauli P s.2))).postprocess fun ab =>
            (some ab.1, some ab.2)).effect answer))
      S.psiHat ≤ 4 * (P.m : ℝ) ^ 2 * δP := by
  classical
  unfold consistencyDefect
  refine (avgOver_subLineJointProjection_le _ (fun s =>
    consistencyDefect_integrand_nonneg S p1 p2 hopposite
      ((lines.T p1.side s.1.1 s.2.1).postprocess fun fs =>
        (evalOpt s.1.1 s.1.2 fs.1, evalOpt s.2.1 s.2.2 fs.2))
      ((points.Q p2.side s.1.2 s.2.2).postprocess fun ab =>
        (some ab.1, some ab.2)))).trans ?_
  exact mul_le_mul_of_nonneg_left (lines.consistent p1 p2 hopposite) (by positivity)

end

end MIPStarRE.QPBT
