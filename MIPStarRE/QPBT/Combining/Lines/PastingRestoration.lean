import MIPStarRE.QPBT.Combining.Lines.NondegeneratePastingDistribution
import MIPStarRE.QPBT.Combining.Lines.RestrictedConsistency

/-!
# Consistency restoration for nondegenerate-line pasting

This module specializes finite-conditioning restoration to the proof-only
nondegenerate line-pasting distribution.

## References

The relabeled conditioned law supports the pasting step in `lem:qld-xz-lines`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-963`, using
the pasting lemma at
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-- Restoring the original product line-point law from its nondegenerate
restriction costs exactly the discarded zero-direction mass.

This is a formalization-only normalization identity supporting
`lem:qld-xz-lines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-963`; it
does not supply the subsequent numerical bound on the discarded mass. -/
theorem consistencyDefect_le_nondegenerateLinePastingDist_add_discarded_mass
    {P : AdmissibleParams} {ε : ℝ}
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (S : ProjectiveSetting P ε) (p1 p2 : Placement) (hopp : p1.IsOpposite p2)
    (first : ((LineDesc P.toLdParams × (Fin P.m → PauliScalar P)) ×
      (LineDesc P.toLdParams × (Fin P.m → PauliScalar P))) →
        Measurement Outcome (S.ExpandedLocalSpace p1.side))
    (second : ((LineDesc P.toLdParams × (Fin P.m → PauliScalar P)) ×
      (LineDesc P.toLdParams × (Fin P.m → PauliScalar P))) →
        Measurement Outcome (S.ExpandedLocalSpace p2.side)) :
    consistencyDefect
        (Distribution.prod (linePointDist P.toLdParams)
          (linePointDist P.toLdParams))
        (fun sample answer => S.place p1 ((first sample).effect answer))
        (fun sample answer => S.place p2 ((second sample).effect answer)) S.psiHat ≤
      nondegenerateLinePastingMass P.toLdParams *
        consistencyDefect (nondegenerateLinePastingDist P.toLdParams)
          (fun question answer =>
            S.place p1 ((first (question.2, question.1.2)).effect answer))
          (fun question answer =>
            S.place p2 ((second (question.2, question.1.2)).effect answer)) S.psiHat +
      ∑ sample ∈
          (Distribution.prod (linePointDist P.toLdParams)
            (linePointDist P.toLdParams)).support.filter
              (fun sample => sample.1.1.direction = 0),
        (Distribution.prod (linePointDist P.toLdParams)
          (linePointDist P.toLdParams)).weight sample := by
  classical
  letI := lineDescFintype P
  letI := linePointFintype P
  have h := consistencyDefect_le_restrict_add_discarded_mass S
    (Distribution.prod (linePointDist P.toLdParams) (linePointDist P.toLdParams))
    (fun sample => sample.1.1.direction ≠ 0)
    (prod_linePointDist_nondegenerate_mass_pos P.toLdParams)
    p1 p2 hopp first second
  simpa only [nondegenerateLinePastingMass, nondegenerateLinePastingDist,
    consistencyDefect, Distribution.avgOver_map, Prod.eta, ne_eq, not_not] using h

end

end MIPStarRE.QPBT
