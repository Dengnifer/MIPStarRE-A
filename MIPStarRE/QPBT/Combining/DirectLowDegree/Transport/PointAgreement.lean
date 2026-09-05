import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.BranchComparison
import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Consistency.Compression
import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.SeedFiberValue

/-!
# The point-agreement branch as a consistency estimate

The low-degree game asks both players a point question in one of its nine
ordered type branches and accepts only equal point answers.  This module reads
that branch as a quantitative consistency relation between the two point
readouts, first for the directly indexed game and then, through the correlated
seed-residue dilation, for the seed-indexed game.

The estimate is the third input, besides the two conclusions of the low
individual degree theorem, from which the global polynomial relation of
`lem:ld-soundness` is obtained after the seed-residue ancilla has been
compressed away: the compressed polynomial measurements are consistent with
the point measurements of the *opposite* player only, and the point-agreement
branch is what links the two point measurements to each other.

## Main results

* `directLdPointPair_consistencyDefect_le` bounds the point-readout
  consistency defect of a direct strategy of value at least `1 - ε` by
  `9 ε`, the loss being the uniform weight of one of the nine ordered type
  branches.
* `ldPointPair_consistencyDefect_le` is the same estimate for the
  seed-indexed game, obtained from the direct one because the point
  measurements of the dilated strategy act trivially on the correlated
  residue register.

## References

* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:137-167`
* `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.Quantum

noncomputable section

/-! ## The point-agreement branch of the directly indexed game -/

/-- On the point-agreement branch an accepted pair of answers has equal
simultaneous point readouts.  This is the tuple-valued form of
`directPointAnswerReadout_eq_of_win`. -/
private theorem directLdPointValuesOrZero_eq_of_win (D : DirectLdParams)
    (p : Fin D.m → DirectScalarQ D) (a b : DirectLdAnswer D)
    (hwin : directLdWinPredicate D (directLdPointQuestionOf D p)
      (directLdPointQuestionOf D p) a b = true) :
    directLdPointValuesOrZero D a = directLdPointValuesOrZero D b := by
  cases a with
  | pointVals u =>
      cases b with
      | pointVals v =>
          have huv : u = v := by
            simpa [directLdWinPredicate, directLdPointQuestionOf,
              validDirectLdAnswer] using hwin
          subst huv
          rfl
      | alinePolys _ =>
          simp [directLdWinPredicate, directLdPointQuestionOf,
            validDirectLdAnswer] at hwin
      | dlinePolys _ =>
          simp [directLdWinPredicate, directLdPointQuestionOf,
            validDirectLdAnswer] at hwin
  | alinePolys _ =>
      simp [directLdWinPredicate, directLdPointQuestionOf,
        validDirectLdAnswer] at hwin
  | dlinePolys _ =>
      simp [directLdWinPredicate, directLdPointQuestionOf,
        validDirectLdAnswer] at hwin

/-- Postprocessing the associated projective measurement has the same effects
as postprocessing the original measurement. -/
private theorem projMeas_postprocess_outcome_eq
    {alpha beta iota : Type*} [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta] [Fintype iota] [DecidableEq iota]
    (M : MIPStarRE.Quantum.Measurement alpha iota)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) (f : alpha → beta)
    (b : beta) :
    (ProjMeas.postprocess (matrixMeasurementToLDTProjMeas M hM) f).outcome b =
      (M.postprocess f).effect b := by
  classical
  simp only [ProjMeas.postprocess, SubMeas.postprocess_outcome,
    matrixMeasurementToLDTProjMeas_outcome,
    MIPStarRE.Quantum.Measurement.postprocess_effect]

/-- The uniform average of the rejected mass at the canonical point questions
is the point-agreement branch rejection probability. -/
private theorem avgOver_directRejectedMass_point_eq (D : DirectLdParams)
    (S : Strategy (directLdGame D)) :
    avgOver (uniformDistribution (Fin D.m → DirectScalarQ D))
        (fun u => directRejectedMass D S (directLdPointQuestionOf D u)
          (directLdPointQuestionOf D u)) =
      directLdBranchRejectionProbability D S (.point, .point) := by
  rw [directLdBranchRejectionProbability_eq_avgOver]
  let f : (Fin D.m → DirectScalarQ D) → ℝ := fun p =>
    directRejectedMass D S (directLdPointQuestionOf D p)
      (directLdPointQuestionOf D p)
  calc avgOver (uniformDistribution (Fin D.m → DirectScalarQ D)) f
      = avgOver (uniformDistribution ((Fin D.m → DirectScalarQ D) × Fin D.m))
          (fun pi => f pi.1) := (avgOver_uniform_fst f).symm
    _ = avgOver (uniformDistribution (DirectLdSpace D))
          (fun sample => f ((directLdSpaceSplitEquiv D sample).1).1) :=
        (avgOver_uniform_equiv_fst (directLdSpaceSplitEquiv D)
          (fun pi => f pi.1)).symm
    _ = _ := by
        apply avgOver_congr
        intro sample
        rfl

/-- One of the nine ordered type branches carries at most nine times the
uniformly weighted rejection probability. -/
private theorem directLdBranchRejectionProbability_le_nine_mul
    (D : DirectLdParams) (S : Strategy (directLdGame D))
    (types : LdType × LdType) (ε : ℝ) (hwin : 1 - ε ≤ S.value) :
    directLdBranchRejectionProbability D S types ≤ 9 * ε := by
  have hcard : Fintype.card (LdType × LdType) = 9 := by
    rw [Fintype.card_prod, show Fintype.card LdType = 3 from by decide]
  have hsum : directLdRejectionProbability D S =
      (Fintype.card (LdType × LdType) : ℝ)⁻¹ *
        ∑ t : LdType × LdType, directLdBranchRejectionProbability D S t :=
    avgOver_uniform_eq_inv_card_mul_sum _
  rw [hcard] at hsum
  have hsingle : directLdBranchRejectionProbability D S types ≤
      ∑ t : LdType × LdType, directLdBranchRejectionProbability D S t :=
    Finset.single_le_sum
      (f := fun t => directLdBranchRejectionProbability D S t)
      (fun t _ => directLdBranchRejectionProbability_nonneg D S t)
      (Finset.mem_univ types)
  have hrej : directLdRejectionProbability D S ≤ ε := by
    rw [directLdRejectionProbability_eq_one_sub_value]
    linarith
  norm_num at hsum
  linarith

set_option maxHeartbeats 1000000 in
/-- The two point readouts of a projective direct strategy of value at least
`1 - ε` are consistent up to `9 ε` on a uniformly random point.

The direct game accepts the point-agreement branch only for equal point
answers, so the off-diagonal Born mass of the two readouts at a fixed point
question is at most the rejected mass there; averaging over the common direct
sample turns this into the point-agreement branch rejection probability, which
is at most nine times the uniformly weighted rejection because the nine
ordered type branches carry equal weight.  Blueprint
`ch13_qpbt_test.tex:137-167`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`. -/
theorem directLdPointPair_consistencyDefect_le
    (D : DirectLdParams) (S : Strategy (directLdGame D)) (hS : S.IsProjective)
    (ε : ℝ) (hwin : 1 - ε ≤ S.value) :
    consistencyDefect (uniformDistribution (Fin D.m → DirectScalarQ D))
        (fun u a => heteroKron
          (((S.A (directLdPointQuestionOf D u)).postprocess
            (directLdPointValuesOrZero D)).effect a) 1)
        (fun u a => heteroKron 1
          (((S.B (directLdPointQuestionOf D u)).postprocess
            (directLdPointValuesOrZero D)).effect a)) S.ψ ≤ 9 * ε := by
  classical
  let PA : (Fin D.m → DirectScalarQ D) →
      ProjMeas (Fin D.k → DirectScalarQ D) S.ιA := fun u =>
    ProjMeas.postprocess
      (matrixMeasurementToLDTProjMeas (S.A (directLdPointQuestionOf D u))
        (hS.1 (directLdPointQuestionOf D u)))
      (directLdPointValuesOrZero D)
  let PB : (Fin D.m → DirectScalarQ D) →
      ProjMeas (Fin D.k → DirectScalarQ D) S.ιB := fun u =>
    ProjMeas.postprocess
      (matrixMeasurementToLDTProjMeas (S.B (directLdPointQuestionOf D u))
        (hS.2 (directLdPointQuestionOf D u)))
      (directLdPointValuesOrZero D)
  have hpoint : ∀ u : Fin D.m → DirectScalarQ D,
      qBipartiteConsDefect (strategyQuantumState S)
          (PA u).toSubMeas (PB u).toSubMeas ≤
        directRejectedMass D S (directLdPointQuestionOf D u)
          (directLdPointQuestionOf D u) := by
    intro u
    exact qBipartiteConsDefect_le_directRejectedMass D S hS
      (directLdPointQuestionOf D u) (directLdPointQuestionOf D u)
      (directLdPointValuesOrZero D) (directLdPointValuesOrZero D)
      (fun a b hab => directLdPointValuesOrZero_eq_of_win D u a b hab)
  have hconsrel : ConsRel (strategyQuantumState S)
      (uniformDistribution (Fin D.m → DirectScalarQ D))
      (fun u => (PA u).toSubMeas) (fun u => (PB u).toSubMeas) (9 * ε) := by
    refine ⟨?_⟩
    unfold bipartiteConsError
    calc avgOver (uniformDistribution (Fin D.m → DirectScalarQ D))
          (fun u => qBipartiteConsDefect (strategyQuantumState S)
            (PA u).toSubMeas (PB u).toSubMeas)
        ≤ avgOver (uniformDistribution (Fin D.m → DirectScalarQ D))
            (fun u => directRejectedMass D S (directLdPointQuestionOf D u)
              (directLdPointQuestionOf D u)) := avgOver_mono _ _ _ hpoint
      _ = directLdBranchRejectionProbability D S (.point, .point) :=
          avgOver_directRejectedMass_point_eq D S
      _ ≤ 9 * ε :=
          directLdBranchRejectionProbability_le_nine_mul D S _ ε hwin
  have hfinal := strategyConsRel_consistencyDefect_le S
    (uniformDistribution (Fin D.m → DirectScalarQ D))
    (uniformDistribution_isProbability _) PA PB (9 * ε) hconsrel
  refine le_trans (le_of_eq ?_) hfinal
  refine consistencyDefect_congr _ _ _ _ _ S.ψ (fun u a => ?_) (fun u a => ?_)
  · rw [projMeas_postprocess_outcome_eq]
  · rw [projMeas_postprocess_outcome_eq]

/-! ## Transport through the correlated seed-residue dilation -/

/-- The diagonal-block average of a block-diagonal amplification is the
amplified operator.  Formalization-only support for the seed-residue
compression of `Transport.Consistency.Compression`. -/
theorem averageDiagonalBlock_blockDiagonal_const
    {iota block : Type*} [Fintype iota]
    [Fintype block] [DecidableEq block] [Nonempty block] (M : Op iota) :
    averageDiagonalBlock (Matrix.blockDiagonal fun _ : block => M) = M := by
  classical
  have hsub : ∀ r : block,
      (Matrix.blockDiagonal fun _ : block => M).submatrix
        (fun i => (i, r)) (fun i => (i, r)) = M := by
    intro r
    ext i j
    simp [Matrix.blockDiagonal_apply_eq]
  have hcard : ((Fintype.card block : ℝ)) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := block))
  unfold averageDiagonalBlock
  simp only [hsub, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hcard, one_smul]

/-- The point-readout consistency defect of the correlated seed-residue
dilation is exactly that of the original seed-indexed strategy.  Both point
measurements of the dilation are block-diagonal amplifications, so compressing
one of the two correlated ancillas leaves the other one's amplification to be
averaged back to itself. -/
theorem ldStrategyToDirect_pointPair_compression
    (L : LdParams) (S : Strategy (ldGame L)) :
    consistencyDefect (uniformDistribution (Fin L.m → ScalarQ L))
        (fun u a => heteroKron
          ((((ldStrategyToDirect L S).A
            (directLdPointQuestionOf L.toDirectLdParams u)).postprocess
              (directLdPointValuesOrZero L.toDirectLdParams)).effect a) 1)
        (fun u a => heteroKron 1
          ((((ldStrategyToDirect L S).B
            (directLdPointQuestionOf L.toDirectLdParams u)).postprocess
              (directLdPointValuesOrZero L.toDirectLdParams)).effect a))
        (ldStrategyToDirect L S).ψ =
      consistencyDefect (uniformDistribution (Fin L.m → ScalarQ L))
        (fun u a => heteroKron
          (((S.A (ldPointQuestionOf L u)).postprocess
            (ldPointValuesOrZero L)).effect a) 1)
        (fun u a => heteroKron 1
          (((S.B (ldPointQuestionOf L u)).postprocess
            (ldPointValuesOrZero L)).effect a)) S.ψ := by
  classical
  letI : Nonempty (Fin (L.q / L.m)) :=
    Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  have hA : ∀ (u : Fin L.m → ScalarQ L) (a : Fin L.k → ScalarQ L),
      (((ldStrategyToDirect L S).A
        (directLdPointQuestionOf L.toDirectLdParams u)).postprocess
          (directLdPointValuesOrZero L.toDirectLdParams)).effect a =
        Matrix.blockDiagonal fun _ : Fin (L.q / L.m) =>
          ((S.A (ldPointQuestionOf L u)).postprocess
            (ldPointValuesOrZero L)).effect a := by
    intro u a
    rw [ldStrategyToDirect_pointMeasurementA, blockDiagonalMeasurement_effect]
  have hB : ∀ (u : Fin L.m → ScalarQ L) (a : Fin L.k → ScalarQ L),
      (((ldStrategyToDirect L S).B
        (directLdPointQuestionOf L.toDirectLdParams u)).postprocess
          (directLdPointValuesOrZero L.toDirectLdParams)).effect a =
        Matrix.blockDiagonal fun _ : Fin (L.q / L.m) =>
          ((S.B (ldPointQuestionOf L u)).postprocess
            (ldPointValuesOrZero L)).effect a := by
    intro u a
    rw [ldStrategyToDirect_pointMeasurementB, blockDiagonalMeasurement_effect]
  calc consistencyDefect (uniformDistribution (Fin L.m → ScalarQ L))
        (fun u a => heteroKron
          ((((ldStrategyToDirect L S).A
            (directLdPointQuestionOf L.toDirectLdParams u)).postprocess
              (directLdPointValuesOrZero L.toDirectLdParams)).effect a) 1)
        (fun u a => heteroKron 1
          ((((ldStrategyToDirect L S).B
            (directLdPointQuestionOf L.toDirectLdParams u)).postprocess
              (directLdPointValuesOrZero L.toDirectLdParams)).effect a))
        (ldStrategyToDirect L S).ψ
      = consistencyDefect (uniformDistribution (Fin L.m → ScalarQ L))
          (fun u a => heteroKron
            (Matrix.blockDiagonal fun _ : Fin (L.q / L.m) =>
              ((S.A (ldPointQuestionOf L u)).postprocess
                (ldPointValuesOrZero L)).effect a) 1)
          (fun u a => heteroKron 1
            (Matrix.blockDiagonal fun _ : Fin (L.q / L.m) =>
              ((S.B (ldPointQuestionOf L u)).postprocess
                (ldPointValuesOrZero L)).effect a))
          (seedFiberLiftedState S L) :=
        consistencyDefect_congr _ _ _ _ _ (seedFiberLiftedState S L)
          (fun u a => by rw [hA u a]; rfl) (fun u a => by rw [hB u a]; rfl)
    _ = consistencyDefect (uniformDistribution (Fin L.m → ScalarQ L))
          (fun u a => heteroKron
            (((S.A (ldPointQuestionOf L u)).postprocess
              (ldPointValuesOrZero L)).effect a) 1)
          (fun u a => heteroKron 1
            (averageDiagonalBlock
              (Matrix.blockDiagonal fun _ : Fin (L.q / L.m) =>
                ((S.B (ldPointQuestionOf L u)).postprocess
                  (ldPointValuesOrZero L)).effect a))) S.ψ :=
        consistencyDefect_seedFiber_compress_right S L _ _ _
    _ = _ :=
        consistencyDefect_congr _ _ _ _ _ S.ψ (fun _ _ => rfl)
          (fun _ _ => by rw [averageDiagonalBlock_blockDiagonal_const])

/-- The two point readouts of a projective seed-indexed strategy of value at
least `1 - ε` are consistent up to `9 ε` on a uniformly random point.

The correlated seed-residue dilation has the same value, and its point
measurements are the block-diagonal amplifications of the original ones, so
the estimate transports back verbatim.  Blueprint
`ch13_qpbt_test.tex:137-167`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`. -/
theorem ldPointPair_consistencyDefect_le
    (L : LdParams) (S : Strategy (ldGame L)) (hS : S.IsProjective)
    (ε : ℝ) (hwin : 1 - ε ≤ S.value) :
    consistencyDefect (uniformDistribution (Fin L.m → ScalarQ L))
        (fun u a => heteroKron
          (((S.A (ldPointQuestionOf L u)).postprocess
            (ldPointValuesOrZero L)).effect a) 1)
        (fun u a => heteroKron 1
          (((S.B (ldPointQuestionOf L u)).postprocess
            (ldPointValuesOrZero L)).effect a)) S.ψ ≤ 9 * ε := by
  rw [← ldStrategyToDirect_pointPair_compression L S]
  refine directLdPointPair_consistencyDefect_le L.toDirectLdParams
    (ldStrategyToDirect L S) (ldStrategyToDirect_isProjective L S hS) ε ?_
  rw [ldStrategyToDirect_value_eq]
  exact hwin

end

end MIPStarRE.QPBT
