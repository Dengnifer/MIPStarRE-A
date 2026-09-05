import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.BranchComparison
import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Combining.QuestionLaw

/-!
# Index-conditioned rejection probabilities of the directly indexed game

`lem:ld-combined-value` transports the value of a strategy along
`def:ld-combined-strategy` by splitting each branch of the combined game
according to the event of `lem:ld-combined-question-law`, that is according to
whether the stored coordinate index of the common sample is a point coordinate
or a combining coordinate.  This module provides the corresponding refinement
of the branch rejection probability: the uniform average over the common sample
is the uniform average over the stored coordinate index of the average over the
sampled point and the sampled direction alone.

The point-versus-point branch is recorded separately, because it is the branch
that the combining coordinates of the combined game reduce to: both of its
questions are the point question at the sampled point, so its rejected mass
depends on neither the stored coordinate index nor the sampled direction.

All declarations below are formalization-only support derived from the game
value; none is a paper-labelled result.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1409-1503`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:517-568`
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.Quantum

noncomputable section

/-! ## The index-conditioned branch rejection probability -/

/-- The rejection probability of an ordered pair of low-degree question types
conditioned on the stored coordinate index of the common sample, averaged over
the sampled point and the sampled direction alone. -/
def directLdIndexedBranchRejectionProbability
    (D : DirectLdParams) (S : Strategy (directLdGame D))
    (types : LdType × LdType) (i : Fin D.m) : ℝ :=
  avgOver (uniformDistribution
      ((Fin D.m → DirectScalarQ D) × (Fin D.m → DirectScalarQ D)))
    fun pd => directRejectedMass D S
      (types.1, directLdMap D types.1 ⟨pd.1, i, pd.2⟩)
      (types.2, directLdMap D types.2 ⟨pd.1, i, pd.2⟩)

/-- Every index-conditioned rejection probability is nonnegative. -/
theorem directLdIndexedBranchRejectionProbability_nonneg
    (D : DirectLdParams) (S : Strategy (directLdGame D))
    (types : LdType × LdType) (i : Fin D.m) :
    0 ≤ directLdIndexedBranchRejectionProbability D S types i := by
  refine avgOver_nonneg _ _ fun pd => ?_
  exact directRejectedMass_nonneg D S _ _

/-- The branch rejection probability of an ordered type pair is the uniform
average over the stored coordinate index of the index-conditioned rejection
probabilities.  This is the refinement used to split a branch of the combined
game according to the event of `lem:ld-combined-question-law`, whose two cases
are the point coordinates and the combining coordinates of the combined
dimension. -/
theorem directLdBranchRejectionProbability_eq_avgOver_index
    (D : DirectLdParams) (S : Strategy (directLdGame D))
    (types : LdType × LdType) :
    directLdBranchRejectionProbability D S types =
      avgOver (uniformDistribution (Fin D.m))
        (directLdIndexedBranchRejectionProbability D S types) := by
  rw [directLdBranchRejectionProbability_eq_avgOver]
  exact avgOver_uniform_equiv_prod (e := directLdSpaceIndexEquiv D) _

/-! ## The point-versus-point branch -/

/-- Both questions of a point-versus-point branch are the point question at the
sampled point, so the index-conditioned rejection probability of that branch is
the average over the sampled point alone, for every stored coordinate index. -/
theorem directLdIndexedBranchRejectionProbability_point_point
    (D : DirectLdParams) (S : Strategy (directLdGame D)) (i : Fin D.m) :
    directLdIndexedBranchRejectionProbability D S (.point, .point) i =
      avgOver (uniformDistribution (Fin D.m → DirectScalarQ D)) fun u =>
        directRejectedMass D S (directLdPointQuestionOf D u)
          (directLdPointQuestionOf D u) := by
  have hsplit : directLdIndexedBranchRejectionProbability D S (.point, .point) i =
      avgOver (uniformDistribution
          ((Fin D.m → DirectScalarQ D) × (Fin D.m → DirectScalarQ D)))
        (fun pd => (fun (u _ : Fin D.m → DirectScalarQ D) =>
          directRejectedMass D S (directLdPointQuestionOf D u)
            (directLdPointQuestionOf D u)) pd.1 pd.2) := rfl
  rw [hsplit,
    avgOver_uniform_prod (f := fun (u _ : Fin D.m → DirectScalarQ D) =>
      directRejectedMass D S (directLdPointQuestionOf D u)
        (directLdPointQuestionOf D u))]
  apply avgOver_congr
  intro _
  exact avgOver_uniform_const _

/-- The point-versus-point branch rejection probability is the uniform average
over the sampled point of the rejected mass at the two equal point questions.
This is the branch to which the combining coordinates of the combined game
reduce, by `directCombined_measuredQuestion_of_coefficientVar`. -/
theorem directLdBranchRejectionProbability_point_point_eq
    (D : DirectLdParams) (S : Strategy (directLdGame D)) :
    directLdBranchRejectionProbability D S (.point, .point) =
      avgOver (uniformDistribution (Fin D.m → DirectScalarQ D)) fun u =>
        directRejectedMass D S (directLdPointQuestionOf D u)
          (directLdPointQuestionOf D u) := by
  rw [directLdBranchRejectionProbability_eq_avgOver_index,
    show directLdIndexedBranchRejectionProbability D S (.point, .point) =
      fun _ => avgOver (uniformDistribution (Fin D.m → DirectScalarQ D)) fun u =>
        directRejectedMass D S (directLdPointQuestionOf D u)
          (directLdPointQuestionOf D u) from
      funext (directLdIndexedBranchRejectionProbability_point_point D S)]
  exact avgOver_uniform_const _

end

end MIPStarRE.QPBT
