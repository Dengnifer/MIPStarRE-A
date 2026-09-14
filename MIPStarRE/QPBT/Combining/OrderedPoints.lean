import MIPStarRE.QPBT.Combining.Witnesses
import MIPStarRE.QPBT.Games.DistanceTheorems.Calculus

/-!
# The ordered point product on a single placement

The consistency guarantees carried by the joint point measurement compare it
with the ordered `Z`-then-`X` product across a pair of opposite placements.
The scalar estimates used to combine the two Pauli bases instead need the two
families on one placement.  This module obtains that form by inserting the
joint measurement on the opposite placement and applying the squared-distance
triangle inequality twice.

## References

The statement is `lem:qld-4-10-same-placement` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`; it restates the ordered
`Z`-then-`X` display of `lem:qld-4-10`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:689-709`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-- Every placement has an opposite placement, and the relation is symmetric
between the two members of each pair. -/
theorem Placement.exists_isOpposite (p : Placement) :
    ∃ q : Placement, p.IsOpposite q ∧ q.IsOpposite p := by
  cases p with
  | AA' => exact ⟨.BA'', trivial, trivial⟩
  | BA'' => exact ⟨.AA', trivial, trivial⟩
  | BB' => exact ⟨.AB'', trivial, trivial⟩
  | AB'' => exact ⟨.BB', trivial, trivial⟩

/-- On a single placement, the joint point measurement is close to the ordered
`Z`-then-`X` point product, with inflation factor four. -/
theorem CombinedPointsWitness.orderedZX_dist_le {P : AdmissibleParams}
    {ε δ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δ) (p : Placement) :
    opFamilyDistSq
        (uniformDistribution
          ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
        (fun xz ab => S.place p ((points.Q p.side xz.1 xz.2).effect ab))
        (fun xz ab => S.place p
          ((S.pointMeasExp p.side .Z xz.2).effect ab.2 *
            (S.pointMeasExp p.side .X xz.1).effect ab.1))
        S.psiHat ≤ 4 * δ := by
  obtain ⟨q, hpq, hqp⟩ := p.exists_isOpposite
  have htri := opFamilyDistSq_le_of_le_of_le
    (uniformDistribution
      ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
    (fun xz ab => S.place p ((points.Q p.side xz.1 xz.2).effect ab))
    (fun xz ab => S.place q ((points.Q q.side xz.1 xz.2).effect ab))
    (fun xz ab => S.place p
      ((S.pointMeasExp p.side .Z xz.2).effect ab.2 *
        (S.pointMeasExp p.side .X xz.1).effect ab.1))
    S.psiHat δ δ (points.self_consistent p q hpq)
    (points.consistent_ZX q p hqp)
  linarith

end

end MIPStarRE.QPBT
