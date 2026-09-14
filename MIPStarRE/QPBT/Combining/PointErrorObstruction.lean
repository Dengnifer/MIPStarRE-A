import MIPStarRE.QPBT.Combining.Witnesses

/-!
# Unrestricted point errors in the extended-line obligation

Every projective joint point family satisfies the fields of `CombinedPointsWitness`
at some finite error. A quadratic deterministic answer, however, has small agreement
with every linear coefficient answer. These facts support the obstruction to the
unrestricted supplied-point domain; they do not construct extended-line witnesses.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:993-1034`.
- `docs/paper-gaps/qpbt_combined-lines-error-term.tex`, the extended-line
  supplied-point obstruction, tracked by issue #509.
- The coefficient collision estimate is reused from
  `directCoefficientCollision_avg_le`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-- An unrestricted scalar error admits every projective joint point family.
The finitely many placement comparisons have a common real upper bound. This is
a Lean-only observation about the witness domain, not the point construction of
`lem:qld-4-10`: no dependence of the bound on the strategy error is asserted. -/
theorem CombinedPointsWitness.exists_error_of_projective
    {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε)
    (Q : (side : PlayerSide) → (Fin P.m → PauliScalar P) →
      (Fin P.m → PauliScalar P) →
      Quantum.Measurement (PauliScalar P × PauliScalar P) (S.ExpandedLocalSpace side))
    (hQ : ∀ side x z, Measurement.IsProjective (Q side x z)) :
    ∃ δ : ℝ, ∃ points : CombinedPointsWitness S δ, points.Q = Q := by
  let law := uniformDistribution
    ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P))
  let selfError (p : Placement × Placement) := opFamilyDistSq law
    (fun xz ab => S.place p.1 ((Q p.1.side xz.1 xz.2).effect ab))
    (fun xz ab => S.place p.2 ((Q p.2.side xz.1 xz.2).effect ab)) S.psiHat
  let xzError (p : Placement × Placement) := opFamilyDistSq law
    (fun xz ab => S.place p.1 ((Q p.1.side xz.1 xz.2).effect ab))
    (fun xz ab => S.place p.2
      ((S.pointMeasExp p.2.side .X xz.1).effect ab.1 *
        (S.pointMeasExp p.2.side .Z xz.2).effect ab.2)) S.psiHat
  let zxError (p : Placement × Placement) := opFamilyDistSq law
    (fun xz ab => S.place p.1 ((Q p.1.side xz.1 xz.2).effect ab))
    (fun xz ab => S.place p.2
      ((S.pointMeasExp p.2.side .Z xz.2).effect ab.2 *
        (S.pointMeasExp p.2.side .X xz.1).effect ab.1)) S.psiHat
  obtain ⟨δ, hδ⟩ := Finite.bddAbove_range
    (fun p => max (selfError p) (max (xzError p) (zxError p)))
  have hbound (p : Placement × Placement) := hδ (Set.mem_range_self p)
  refine ⟨δ, ⟨Q, hQ, ?_, ?_, ?_⟩, rfl⟩
  · intro p1 p2 _
    exact (le_max_left _ _).trans (hbound (p1, p2))
  · intro p1 p2 _
    exact ((le_max_left _ _).trans (le_max_right _ _)).trans (hbound (p1, p2))
  · intro p1 p2 _
    exact ((le_max_right _ _).trans (le_max_right _ _)).trans (hbound (p1, p2))

/-- A coefficient answer with zero quadratic coefficient agrees with a nonzero
multiple of the square function on at most a `2 / q` fraction of the field.
This is the Lean-only scalar part of the X-axis obstruction for `m = d = 1` in issue #509;
the existing coefficient collision theorem supplies the root count. -/
theorem linear_quadratic_agreement_le (D : DirectLdParams)
    (f : DirectDegPoly D 2) (hf : f 2 = 0)
    (α : DirectScalarQ D) (hα : α ≠ 0) :
    avgOver (uniformDistribution (DirectScalarQ D))
      (fun t => if evalCoefficient f t = α * t ^ 2 then (1 : ℝ) else 0) ≤
      2 / (D.q : ℝ) := by
  classical
  let quadratic : DirectDegPoly D 2 := fun i => if i = 2 then α else 0
  have hne : f ≠ quadratic := by
    intro heq
    have hcoeff := congrFun heq 2
    simp only [quadratic, ite_true, hf] at hcoeff
    exact hα hcoeff.symm
  have heval (t : DirectScalarQ D) : evalCoefficient quadratic t = α * t ^ 2 := by
    simp [evalCoefficient, quadratic, ite_mul]
  simpa only [heval, Nat.cast_ofNat] using directCoefficientCollision_avg_le D 2 f quadratic hne

end

end MIPStarRE.QPBT
