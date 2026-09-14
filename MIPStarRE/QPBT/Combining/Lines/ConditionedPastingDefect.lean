import MIPStarRE.QPBT.Combining.Lines.ConsistencyPositivity
import MIPStarRE.QPBT.Combining.Lines.NondegeneratePastingDistribution
import MIPStarRE.QPBT.Games.RestrictedAverage

/-!
# Consistency defect under nondegenerate-line conditioning

This module bounds the consistency defect after applying the proof-only
first-line nondegeneracy conditioning used in the QPBT pasting argument.

## References

The estimate supports `eq:pasting-q1` in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:936-963`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-- Conditioning the product line-point law on a nondegenerate first line
inflates the opposite-placement consistency defect by at most the inverse
retained mass. -/
theorem consistencyDefect_nondegenerateLinePastingDist_le
    {P : AdmissibleParams} {ε : ℝ}
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (S : ProjectiveSetting P ε) (p1 p2 : Placement) (hopp : p1.IsOpposite p2)
    (first : ((LineDesc P.toLdParams × (Fin P.m → PauliScalar P)) ×
      (LineDesc P.toLdParams × (Fin P.m → PauliScalar P))) →
        MIPStarRE.Quantum.Measurement Outcome (S.ExpandedLocalSpace p1.side))
    (second : ((LineDesc P.toLdParams × (Fin P.m → PauliScalar P)) ×
      (LineDesc P.toLdParams × (Fin P.m → PauliScalar P))) →
        MIPStarRE.Quantum.Measurement Outcome (S.ExpandedLocalSpace p2.side)) :
    consistencyDefect (nondegenerateLinePastingDist P.toLdParams)
      (fun question answer => S.place p1 ((first (question.2, question.1.2)).effect answer))
      (fun question answer => S.place p2 ((second (question.2, question.1.2)).effect answer))
      S.psiHat ≤
    consistencyDefect (Distribution.prod (linePointDist P.toLdParams)
      (linePointDist P.toLdParams))
      (fun sample answer => S.place p1 ((first sample).effect answer))
      (fun sample answer => S.place p2 ((second sample).effect answer)) S.psiHat /
        nondegenerateLinePastingMass P.toLdParams := by
  unfold consistencyDefect nondegenerateLinePastingDist
  rw [Distribution.avgOver_map]
  exact avgOver_restrict_le_div_mass _ _ _ _ fun sample =>
    consistencyDefect_integrand_nonneg S p1 p2 hopp (first sample) (second sample)

end

end MIPStarRE.QPBT
