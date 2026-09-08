import MIPStarRE.QPBT.Combining.Lines.PointwiseDefect
import MIPStarRE.QPBT.Games.RestrictedAverage

/-!
# Consistency defect under finite conditioning

This module restores an ambient consistency defect from its restriction to a
positive-mass event. The discarded samples contribute at most their total
probability mass.

## References

This formalization-only finite-conditioning estimate supports the argument in
`lem:qld-xz-lines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-963`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-- The ambient consistency defect is at most the retained mass times the
conditional defect, plus the discarded probability mass.

This is a formalization-only generic finite-conditioning estimate supporting
`lem:qld-xz-lines`, paper
`14_analysis_of_the_pauli_basis_test.tex:950-963`. Completeness of the two
measurement families supplies the pointwise unit bound; no separate bound on
the consistency defect is assumed. -/
theorem consistencyDefect_le_restrict_add_discarded_mass
    {P : AdmissibleParams} {ε : ℝ}
    {Sample Outcome : Type*} [Fintype Sample] [DecidableEq Sample]
    [Fintype Outcome] [DecidableEq Outcome]
    (S : ProjectiveSetting P ε) (dist : Distribution Sample)
    (good : Sample -> Prop) [DecidablePred good]
    (hpos : 0 < ∑ sample ∈ dist.support.filter good, dist.weight sample)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2)
    (first : Sample -> Measurement Outcome (S.ExpandedLocalSpace p1.side))
    (second : Sample -> Measurement Outcome (S.ExpandedLocalSpace p2.side)) :
    consistencyDefect dist
        (fun sample answer => S.place p1 ((first sample).effect answer))
        (fun sample answer => S.place p2 ((second sample).effect answer)) S.psiHat ≤
      (∑ sample ∈ dist.support.filter good, dist.weight sample) *
        consistencyDefect (Distribution.restrict dist good hpos)
          (fun sample answer => S.place p1 ((first sample).effect answer))
          (fun sample answer => S.place p2 ((second sample).effect answer)) S.psiHat +
      ∑ sample ∈ dist.support.filter (fun sample => ¬ good sample),
        dist.weight sample := by
  unfold consistencyDefect
  apply avgOver_le_restrict_add_discarded_mass dist good hpos
  intro sample
  exact consistencyDefect_integrand_le_one S p1 p2 hopp
    (first sample) (second sample)

end

end MIPStarRE.QPBT
