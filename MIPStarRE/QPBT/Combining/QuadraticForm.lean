import MIPStarRE.QPBT.Games.DistanceTheorems.Support

/-!
# Conjugation identity for the state quadratic form

The combining layer evaluates the real quadratic form
`stateQForm ψ M = ⟪ψ, M ψ⟫.re` of
`MIPStarRE/QPBT/Games/DistanceTheorems/Support.lean` against operators that are
conjugated by a further operator `W`.  Two independent consumers need the same
transfer identity: the overlap-gap estimate of
`MIPStarRE/QPBT/Combining/OverlapGap.lean`, where `W` is a projection of one
placed measurement, and the sandwich self-consistency argument of
`MIPStarRE/QPBT/Combining/Points/Consistency.lean`, where `W` is the product of
the two placed `Z` effects.  This module owns the shared identity so that it has
a single declaration site.

## Main results

* `stateQForm_conjTranspose_mul_mul`: conjugating an operator by `W` transfers
  `W` to the state vector.

## References

Formalization-only infrastructure for the quadratic-form manipulations behind
`lem:qld-4-10` and `lem:overlap-gap-distance`,
`blueprint/src/chapter/ch15_qpbt_combining.tex`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:743-790` and
`:1147-1166`.  It introduces no new mathematical assumptions.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum DistanceCalculus

/-- Conjugating an operator transfers the outer operator to the state vector:
the quadratic form of `Wᴴ M W` in `ψ` is the quadratic form of `M` in `W ψ`. -/
theorem stateQForm_conjTranspose_mul_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (W M : Op ι) :
    stateQForm ψ (Wᴴ * M * W) = stateQForm (applyOperatorToState W ψ) M := by
  unfold stateQForm
  rw [DistanceCalculus.applyOperatorToState_mul,
    DistanceCalculus.applyOperatorToState_mul]
  congr 1
  change inner ℂ ψ (Matrix.toEuclideanLin Wᴴ _) =
    inner ℂ (Matrix.toEuclideanLin W ψ) _
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_right]

end MIPStarRE.QPBT
