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

/-! ## The rejected mass of the combined strategy -/

/-- The Born weight of an answer pair of the combined strategy is the total
Born weight, at the measured questions, of the answer pairs of the original
strategy that the relabelling of `def:ld-combined-strategy` sends to it.  Each
measurement of the combined strategy is a coarse-graining of a measurement of
the original strategy, so its effects are the fiber sums of the original
effects. -/
theorem outcomeWeight_directCombinedStrategy (D : DirectLdParams)
    (S : Strategy (directLdGame D)) (x y : DirectLdQuestion D.combined)
    (a' b' : DirectLdAnswer D.combined) :
    outcomeWeight (directCombinedStrategy D S) x y a' b' =
      ∑ a ∈ Finset.univ.filter (fun a => directCombinedAnswerMap D x a = a'),
        ∑ b ∈ Finset.univ.filter (fun b => directCombinedAnswerMap D y b = b'),
          outcomeWeight S (directCombinedMeasuredQuestion D x)
            (directCombinedMeasuredQuestion D y) a b := by
  classical
  show DistanceCalculus.stateQForm S.ψ
      (heteroKron
        (((S.A (directCombinedMeasuredQuestion D x)).postprocess
            (directCombinedAnswerMap D x)).effect a')
        (((S.B (directCombinedMeasuredQuestion D y)).postprocess
            (directCombinedAnswerMap D y)).effect b')) = _
  rw [Measurement.postprocess_effect, Measurement.postprocess_effect,
    DistanceCalculus.heteroKron_finset_sum_left,
    DistanceCalculus.stateQForm_finset_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [DistanceCalculus.heteroKron_finset_sum_right,
    DistanceCalculus.stateQForm_finset_sum]
  exact Finset.sum_congr rfl fun b _ => rfl

/-- Rejected-mass comparison for `def:ld-combined-strategy`.  If every answer
pair accepted by the win predicate of the original game at the measured
questions is relabelled to an answer pair accepted by the win predicate of the
combined game, then the rejected mass of the combined strategy at a question
pair of the combined game is at most the rejected mass of the original strategy
at the measured question pair.  This reduces the branch-wise estimates of
`lem:ld-combined-value` to the win-predicate implications of that lemma. -/
theorem directRejectedMass_directCombinedStrategy_le (D : DirectLdParams)
    (S : Strategy (directLdGame D)) (x y : DirectLdQuestion D.combined)
    (himp : ∀ a b : DirectLdAnswer D,
      directLdWinPredicate D (directCombinedMeasuredQuestion D x)
          (directCombinedMeasuredQuestion D y) a b = true →
        directLdWinPredicate D.combined x y
          (directCombinedAnswerMap D x a) (directCombinedAnswerMap D y b) = true) :
    directRejectedMass D.combined (directCombinedStrategy D S) x y ≤
      directRejectedMass D S (directCombinedMeasuredQuestion D x)
        (directCombinedMeasuredQuestion D y) := by
  classical
  set mx := directCombinedMeasuredQuestion D x with hmx
  set my := directCombinedMeasuredQuestion D y with hmy
  set F : DirectLdAnswer D → DirectLdAnswer D → ℝ := fun a b =>
    if directLdWinPredicate D.combined x y
        (directCombinedAnswerMap D x a) (directCombinedAnswerMap D y b) then 0
    else outcomeWeight S mx my a b with hF
  have hmass : directRejectedMass D.combined (directCombinedStrategy D S) x y =
      ∑ a : DirectLdAnswer D, ∑ b : DirectLdAnswer D, F a b := by
    have step : ∀ a' b' : DirectLdAnswer D.combined,
        (if directLdWinPredicate D.combined x y a' b' then 0
          else outcomeWeight (directCombinedStrategy D S) x y a' b') =
          ∑ a ∈ Finset.univ.filter (fun a => directCombinedAnswerMap D x a = a'),
            ∑ b ∈ Finset.univ.filter (fun b => directCombinedAnswerMap D y b = b'),
              F a b := by
      intro a' b'
      by_cases hw : directLdWinPredicate D.combined x y a' b' = true
      · rw [if_pos hw]
        refine (Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => ?_).symm
        rw [Finset.mem_filter] at ha hb
        rw [hF]
        simp only [ha.2, hb.2, hw, if_true]
      · rw [if_neg hw, outcomeWeight_directCombinedStrategy]
        refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
        rw [Finset.mem_filter] at ha hb
        simp [hF, ha.2, hb.2, hw, hmx, hmy]
    rw [directRejectedMass]
    simp_rw [step]
    rw [← Finset.sum_fiberwise Finset.univ (directCombinedAnswerMap D x)
      (fun a => ∑ b : DirectLdAnswer D, F a b)]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ =>
      Finset.sum_fiberwise Finset.univ (directCombinedAnswerMap D y) (F a)
  rw [hmass, directRejectedMass]
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  simp only [hF]
  by_cases hw : directLdWinPredicate D mx my a b = true
  · simp only [if_pos hw, if_pos (himp a b hw), le_refl]
  · rw [if_neg hw]
    split_ifs
    · exact outcomeWeight_nonneg S mx my a b
    · exact le_rfl

end

end MIPStarRE.QPBT
