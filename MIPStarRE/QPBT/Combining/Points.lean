import MIPStarRE.QPBT.Combining.Witnesses

/-!
# Combining the point measurements

This module states the construction obligation for the joint X/Z point
measurements and defines their scalar linear coarse-graining.  The latter is
the genuine postprocessing of a complete measurement on each heterogeneous
player space.

## References

The construction is `lem:qld-4-10` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`, with paper source
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:689-709`.
The coarse-graining is `lem:qld-4-12` in the same blueprint, with paper source
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:993-1011`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-- A pair of source points and the two scalar coefficients used by the
extended point measurement. -/
abbrev ExtendedPointQuestion (P : AdmissibleParams) :=
  ((Fin P.m -> PauliScalar P) × (Fin P.m -> PauliScalar P)) ×
    (PauliScalar P × PauliScalar P)

namespace CombinedPointsWitness

/-- Coarse-grain a joint point measurement by `(a,b) |-> alpha*a + beta*b`
on the selected player side.  This is the concrete measurement of
`lem:qld-4-12`, paper lines 993--1011. -/
noncomputable def extendedQ {P : AdmissibleParams} {ε δ : ℝ}
    {S : ProjectiveSetting P ε} (points : CombinedPointsWitness S δ)
    (side : PlayerSide) (x z : Fin P.m -> PauliScalar P)
    (alpha beta : PauliScalar P) :
    Measurement (PauliScalar P) (S.ExpandedLocalSpace side) :=
  (points.Q side x z).postprocess fun ab => alpha * ab.1 + beta * ab.2

end CombinedPointsWitness

/-- Construction of the projective joint point measurements of
`lem:qld-4-10`, paper lines 689--709.  The witness retains both ordered
products and all four directed heterogeneous placement comparisons. -/
theorem exists_combinedPointsWitness :
    ∃ deltaQ : ℝ -> ℝ, IsPolyErr deltaQ ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
        Nonempty (CombinedPointsWitness S (deltaQ ε)) := by
  sorry

/-- Projectivity and the three data-processed consistency guarantees for
`CombinedPointsWitness.extendedQ`.  This is `lem:qld-4-12`, paper lines
993--1011; the `XZ` and `ZX` source products remain separate. -/
theorem extendedQ_spec {P : AdmissibleParams} {ε δ : ℝ}
    {S : ProjectiveSetting P ε} (points : CombinedPointsWitness S δ) :
    (∀ side x z alpha beta,
      Measurement.IsProjective (points.extendedQ side x z alpha beta)) ∧
    (∀ p1 p2 : Placement, p1.IsOpposite p2 ->
      opFamilyDistSq (uniformDistribution (ExtendedPointQuestion P))
        (fun question c => S.place p1
          ((points.extendedQ p1.side question.1.1 question.1.2
            question.2.1 question.2.2).effect c))
        (fun question c => S.place p2
          ((points.extendedQ p2.side question.1.1 question.1.2
            question.2.1 question.2.2).effect c))
        S.psiHat <= δ) ∧
    (∀ p1 p2 : Placement, p1.IsOpposite p2 ->
      opFamilyDistSq (uniformDistribution (ExtendedPointQuestion P))
        (fun question c => S.place p1
          ((points.extendedQ p1.side question.1.1 question.1.2
            question.2.1 question.2.2).effect c))
        (fun question c => S.place p2
          (∑ ab ∈ Finset.univ.filter (fun ab : PauliScalar P × PauliScalar P =>
              question.2.1 * ab.1 + question.2.2 * ab.2 = c),
            (S.pointMeasExp p2.side .X question.1.1).effect ab.1 *
              (S.pointMeasExp p2.side .Z question.1.2).effect ab.2))
        S.psiHat <= δ) ∧
    ∀ p1 p2 : Placement, p1.IsOpposite p2 ->
      opFamilyDistSq (uniformDistribution (ExtendedPointQuestion P))
        (fun question c => S.place p1
          ((points.extendedQ p1.side question.1.1 question.1.2
            question.2.1 question.2.2).effect c))
        (fun question c => S.place p2
          (∑ ab ∈ Finset.univ.filter (fun ab : PauliScalar P × PauliScalar P =>
              question.2.1 * ab.1 + question.2.2 * ab.2 = c),
            (S.pointMeasExp p2.side .Z question.1.2).effect ab.2 *
              (S.pointMeasExp p2.side .X question.1.1).effect ab.1))
        S.psiHat <= δ := by
  sorry

end


end MIPStarRE.QPBT
