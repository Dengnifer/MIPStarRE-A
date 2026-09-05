import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Combining.QuestionLaw

/-!
# Branch-wise acceptance transport for the combined strategy

By `directRejectedMass_directCombinedStrategy_le`, the branch-wise estimates of
`lem:ld-combined-value` reduce to the following statement: the relabelling of
`def:ld-combined-strategy` sends an answer pair accepted by the win predicate
of the original game at the measured questions to an answer pair accepted by
the win predicate of the combined game.  This module proves that statement for
each of the nine ordered type pairs of the combined game.

Three of the nine branches are deterministic.  The two questions of a branch
whose type pair is diagonal are equal, so the acceptance clause of the original
game forces the two measured outcomes to be equal, and the relabelling, being a
function, sends them to equal combined outcomes.  The two branches pairing an
axis-parallel line with a diagonal line impose no condition in either game.

The six remaining branches pair a line with a point, and split according to
whether the stored coordinate index of the common sample is a point coordinate
or a combining coordinate.  On a point coordinate the acceptance clause of the
combined game is obtained from the acceptance clause of the original game by
the affine change of parameter `directCombinedRebaseParameter`: the parameter
presenting the sampled point on the sampled line of the combined space presents
the point part of the sampled point on the image line, after the shift.  On a
combining coordinate the sampled line lies in a fiber of the projection to the
point coordinates, the combining part of the sampled point is the affine
function `α₀ + t w` of the parameter, and the acceptance clause of the combined
game is the identity `∑ r (α₀ + t w)_r b_r = ∑ r α_r b_r`.

All declarations below are formalization-only support for
`lem:ld-combined-value`; none is a paper-labelled result.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1409-1503`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:526-568`
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries

noncomputable section

/-! ## The two parts of a point along a line -/

theorem directCombinedPointPart_add_smul (D : DirectLdParams)
    (p V : Fin D.combined.m → DirectScalarQ D) (t : DirectScalarQ D) :
    directCombinedPointPart D (p + t • V) =
      directCombinedPointPart D p + t • directCombinedPointPart D V := rfl

theorem directCombinedCoefficientPart_add_smul (D : DirectLdParams)
    (p V : Fin D.combined.m → DirectScalarQ D) (t : DirectScalarQ D) :
    directCombinedCoefficientPart D (p + t • V) =
      directCombinedCoefficientPart D p + t • directCombinedCoefficientPart D V := rfl

/-- The coordinate direction of a point coordinate of the combined dimension
has vanishing combining part. -/
@[simp] theorem directCombinedCoefficientPart_coordinateDirection_pointVar
    (D : DirectLdParams) (j : Fin D.m) :
    directCombinedCoefficientPart D
        (coordinateDirection (combinedPointVar D.m D.k j)) = 0 := by
  funext r
  show (coordinateDirection (combinedPointVar D.m D.k j) :
      Fin (D.m + D.k) → DirectScalarQ D) (combinedCoefficientVar D.m D.k r) = 0
  rw [coordinateDirection,
    Pi.single_eq_of_ne (combinedCoefficientVar_ne_combinedPointVar D.m D.k r j)]

/-! ## Degree bounds at the combined parameters -/

private theorem diagonalDegreeBound (D : DirectLdParams) :
    D.m * D.d + 1 ≤ D.combined.m * D.combined.d := by
  have h1 : 1 ≤ D.k * D.d := by simpa using Nat.mul_le_mul D.hk D.hd
  calc D.m * D.d + 1 ≤ D.m * D.d + D.k * D.d := Nat.add_le_add_left h1 _
    _ = (D.m + D.k) * D.d := (Nat.add_mul _ _ _).symm

private theorem oneLeCombinedDlineDegree (D : DirectLdParams) :
    1 ≤ D.combined.m * D.combined.d := by
  simpa using Nat.mul_le_mul D.combined.hm D.combined.hd

/-! ## Evaluation of the combined answers -/

/-- Evaluation of the answer of cases 3 and 5 of `def:ld-combined-strategy`:
along a line contained in a fiber of the projection to the point coordinates,
the combining part of the point at parameter `t` is `α₀ + t w`, so the affine
answer built from the measured point answer `b` takes at `t` the combined
value of `b` at that point. -/
private theorem fiberAnswerEval (D : DirectLdParams) (n : ℕ) (hn : 1 ≤ n)
    (z base dirn : Fin D.combined.m → DirectScalarQ D)
    (b : Fin D.k → DirectScalarQ D) (t : DirectScalarQ D)
    (ht : z = base + t • dirn) :
    evalCoefficient
        (coefficientsOfPolynomial n
          (fiberLinePolynomial (directCombinedCoefficientPart D base)
            (directCombinedCoefficientPart D dirn) b)) t =
      ∑ r : Fin D.k, directCombinedCoefficientPart D z r * b r := by
  have hz : directCombinedCoefficientPart D z =
      directCombinedCoefficientPart D base +
        t • directCombinedCoefficientPart D dirn := by
    conv_lhs => rw [ht]
    exact directCombinedCoefficientPart_add_smul D base dirn t
  rw [evalCoefficient_coefficientsOfPolynomial
      (le_trans (fiberLinePolynomial_natDegree_le _ _ _) hn),
    fiberLinePolynomial_eval, hz]
  exact Finset.sum_congr rfl fun r _ => by simp

/-- Evaluation of the answer of case 2 of `def:ld-combined-strategy`: along an
axis-parallel line of the combined space with a point coordinate as stored
index, the combining part of the sampled point equals that of the canonical
base, and the shifted parameter presents the point part of the sampled point on
the measured line. -/
private theorem axisAnswerEval (D : DirectLdParams)
    (z base dirn : Fin D.combined.m → DirectScalarQ D)
    (hdir : directCombinedCoefficientPart D dirn = 0) (s t : DirectScalarQ D)
    (f : Fin D.k → Fin (D.d + 1) → DirectScalarQ D) (c : Fin D.k → DirectScalarQ D)
    (hf : ∀ r, evalCoefficient (f r) (t + s) = c r)
    (ht : z = base + t • dirn) :
    evalCoefficient
        (coefficientsOfPolynomial D.combined.d
          (combinedAxisPolynomial (directCombinedCoefficientPart D base) s f)) t =
      ∑ r : Fin D.k, directCombinedCoefficientPart D z r * c r := by
  have hz : directCombinedCoefficientPart D z = directCombinedCoefficientPart D base := by
    conv_lhs => rw [ht]
    rw [directCombinedCoefficientPart_add_smul, hdir, smul_zero, add_zero]
  rw [evalCoefficient_coefficientsOfPolynomial
      (le_trans (combinedAxisPolynomial_natDegree_le _ _ _)
        (le_of_eq (DirectLdParams.combined_d D).symm)),
    combinedAxisPolynomial_eval, hz]
  exact Finset.sum_congr rfl fun r _ => by rw [hf]

/-- Evaluation of the answer of case 4 of `def:ld-combined-strategy`: along a
diagonal line of the combined space with a point coordinate as stored index,
the combining part of the point at parameter `t` is `α₀ + t w`, and the shifted
parameter presents the point part of that point on the measured line. -/
private theorem diagonalAnswerEval (D : DirectLdParams)
    (z base dirn : Fin D.combined.m → DirectScalarQ D) (s t : DirectScalarQ D)
    (f : Fin D.k → Fin (D.m * D.d + 1) → DirectScalarQ D)
    (c : Fin D.k → DirectScalarQ D)
    (hf : ∀ r, evalCoefficient (f r) (t + s) = c r)
    (ht : z = base + t • dirn) :
    evalCoefficient
        (coefficientsOfPolynomial (D.combined.m * D.combined.d)
          (combinedDiagonalPolynomial (directCombinedCoefficientPart D base)
            (directCombinedCoefficientPart D dirn) s f)) t =
      ∑ r : Fin D.k, directCombinedCoefficientPart D z r * c r := by
  have hz : directCombinedCoefficientPart D z =
      directCombinedCoefficientPart D base +
        t • directCombinedCoefficientPart D dirn := by
    conv_lhs => rw [ht]
    exact directCombinedCoefficientPart_add_smul D base dirn t
  rw [evalCoefficient_coefficientsOfPolynomial
      (le_trans (combinedDiagonalPolynomial_natDegree_le _ _ _ _)
        (diagonalDegreeBound D)),
    combinedDiagonalPolynomial_eval, hz]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [hf]
  simp

/-! ## Structural clauses of the win predicate -/

/-- An answer pair accepted at two equal questions of the directly indexed game
consists of two equal answers: the three diagonal clauses of
`def:ld-win-predicate` are equalities of answers. -/
theorem directLdAnswer_eq_of_win_self (D : DirectLdParams)
    (q : DirectLdQuestion D) {a b : DirectLdAnswer D}
    (hwin : directLdWinPredicate D q q a b = true) : a = b := by
  obtain ⟨t, xq⟩ := q
  cases t <;> cases a <;> cases b <;>
    simp_all [directLdWinPredicate, validDirectLdAnswer]

/-- Two equal answers of the correct constructor are accepted at two equal
questions of the directly indexed game. -/
theorem directLdWinPredicate_self (D : DirectLdParams) (q : DirectLdQuestion D)
    (a : DirectLdAnswer D) (hvalid : validDirectLdAnswer q.1 a = true) :
    directLdWinPredicate D q q a a = true := by
  obtain ⟨t, xq⟩ := q
  cases t <;> cases a <;>
    simp_all [directLdWinPredicate, validDirectLdAnswer]

/-- The relabelling of `def:ld-combined-strategy` always produces an answer of
the constructor required by the type of the combined question. -/
theorem validDirectLdAnswer_directCombinedAnswerMap (D : DirectLdParams)
    (q : DirectLdQuestion D.combined) (a : DirectLdAnswer D) :
    validDirectLdAnswer q.1 (directCombinedAnswerMap D q a) = true := by
  obtain ⟨t, xq⟩ := q
  cases t
  · rfl
  · rcases hsplit : directCombinedIndexSplit D xq.index with j | r <;>
      simp only [directCombinedAnswerMap, hsplit, validDirectLdAnswer]
  · rcases hsplit : directCombinedIndexSplit D xq.index with j | r <;>
      simp only [directCombinedAnswerMap, hsplit, validDirectLdAnswer]

/-- An ordered pair of a well-formed axis-parallel line answer and a well-formed
diagonal line answer is accepted: `def:ld-win-predicate` imposes no condition on
that ordered type pair. -/
theorem directLdWinPredicate_aline_dline (D : DirectLdParams)
    (xq yq : DirectLdSpace D) (a b : DirectLdAnswer D)
    (ha : validDirectLdAnswer LdType.aline a = true)
    (hb : validDirectLdAnswer LdType.dline b = true) :
    directLdWinPredicate D (.aline, xq) (.dline, yq) a b = true := by
  cases a <;> cases b <;> simp_all [directLdWinPredicate, validDirectLdAnswer]

/-- The mirror of `directLdWinPredicate_aline_dline`. -/
theorem directLdWinPredicate_dline_aline (D : DirectLdParams)
    (xq yq : DirectLdSpace D) (a b : DirectLdAnswer D)
    (ha : validDirectLdAnswer LdType.dline a = true)
    (hb : validDirectLdAnswer LdType.aline b = true) :
    directLdWinPredicate D (.dline, xq) (.aline, yq) a b = true := by
  cases a <;> cases b <;> simp_all [directLdWinPredicate, validDirectLdAnswer]

/-- A coordinate index of the combined dimension split off as a point
coordinate is that point coordinate. -/
theorem eq_combinedPointVar_of_indexSplit (D : DirectLdParams)
    {i : Fin D.combined.m} {j : Fin D.m}
    (h : directCombinedIndexSplit D i = Sum.inl j) :
    i = combinedPointVar D.m D.k j := by
  have hi : finSumFinEquiv (directCombinedIndexSplit D i) =
      finSumFinEquiv (Sum.inl j) := congrArg _ h
  rw [directCombinedIndexSplit, Equiv.apply_symm_apply] at hi
  exact hi

/-- A coordinate index of the combined dimension split off as a combining
coordinate is that combining coordinate. -/
theorem eq_combinedCoefficientVar_of_indexSplit (D : DirectLdParams)
    {i : Fin D.combined.m} {r : Fin D.k}
    (h : directCombinedIndexSplit D i = Sum.inr r) :
    i = combinedCoefficientVar D.m D.k r := by
  have hi : finSumFinEquiv (directCombinedIndexSplit D i) =
      finSumFinEquiv (Sum.inr r) := congrArg _ h
  rw [directCombinedIndexSplit, Equiv.apply_symm_apply] at hi
  exact hi

/-! ## The acceptance clause on a point coordinate -/

/-- Case 2 of `def:ld-combined-strategy` at the parameter presenting the
sampled point: the affine shift `s` relating the two presentations of the image
line carries the acceptance clause of the original game at the shifted
parameter to the acceptance clause of the combined game. -/
theorem directCombinedAxisAnswer_eval (D : DirectLdParams)
    (z dir : Fin D.combined.m → DirectScalarQ D)
    (hcoef : directCombinedCoefficientPart D dir = 0) (s T : DirectScalarQ D)
    (hs : directCombinedPointPart D (lineRepMap dir z) =
      lineRepMap (directCombinedPointPart D dir)
          (directCombinedPointPart D (lineRepMap dir z)) +
        s • directCombinedPointPart D dir)
    (f : Fin D.k → Fin (D.d + 1) → DirectScalarQ D) (c : Fin D.k → DirectScalarQ D)
    (hT : z = lineRepMap dir z + T • dir)
    (hcond : ∀ t : DirectScalarQ D,
      directCombinedPointPart D z =
          lineRepMap (directCombinedPointPart D dir) (directCombinedPointPart D z) +
            t • directCombinedPointPart D dir →
        ∀ r, evalCoefficient (f r) t = c r) :
    evalCoefficient
        (coefficientsOfPolynomial D.combined.d
          (combinedAxisPolynomial
            (directCombinedCoefficientPart D (lineRepMap dir z)) s f)) T =
      ∑ r : Fin D.k, directCombinedCoefficientPart D z r * c r := by
  have hbase := lineRepMap_directCombinedPointPart_lineRepMap D dir z
  have hpt : directCombinedPointPart D z =
      lineRepMap (directCombinedPointPart D dir) (directCombinedPointPart D z) +
        (T + s) • directCombinedPointPart D dir := by
    conv_lhs => rw [hT]
    rw [directCombinedPointPart_add_smul, hs, hbase]
    module
  exact axisAnswerEval D z (lineRepMap dir z) dir hcoef s T f c (hcond (T + s) hpt) hT

/-- Case 4 of `def:ld-combined-strategy` at the parameter presenting the
sampled point. -/
theorem directCombinedDiagonalAnswer_eval (D : DirectLdParams)
    (z dir : Fin D.combined.m → DirectScalarQ D) (s T : DirectScalarQ D)
    (hs : directCombinedPointPart D (lineRepMap dir z) =
      lineRepMap (directCombinedPointPart D dir)
          (directCombinedPointPart D (lineRepMap dir z)) +
        s • directCombinedPointPart D dir)
    (f : Fin D.k → Fin (D.m * D.d + 1) → DirectScalarQ D)
    (c : Fin D.k → DirectScalarQ D)
    (hT : z = lineRepMap dir z + T • dir)
    (hcond : ∀ t : DirectScalarQ D,
      directCombinedPointPart D z =
          lineRepMap (directCombinedPointPart D dir) (directCombinedPointPart D z) +
            t • directCombinedPointPart D dir →
        ∀ r, evalCoefficient (f r) t = c r) :
    evalCoefficient
        (coefficientsOfPolynomial (D.combined.m * D.combined.d)
          (combinedDiagonalPolynomial
            (directCombinedCoefficientPart D (lineRepMap dir z))
            (directCombinedCoefficientPart D dir) s f)) T =
      ∑ r : Fin D.k, directCombinedCoefficientPart D z r * c r := by
  have hbase := lineRepMap_directCombinedPointPart_lineRepMap D dir z
  have hpt : directCombinedPointPart D z =
      lineRepMap (directCombinedPointPart D dir) (directCombinedPointPart D z) +
        (T + s) • directCombinedPointPart D dir := by
    conv_lhs => rw [hT]
    rw [directCombinedPointPart_add_smul, hs, hbase]
    module
  exact diagonalAnswerEval D z (lineRepMap dir z) dir s T f c (hcond (T + s) hpt) hT

/-! ## The branch-wise acceptance transport -/

/-- The acceptance transport of `lem:ld-combined-value` on one ordered type
pair: the relabelling of `def:ld-combined-strategy` sends an answer pair
accepted by the win predicate of the original game at the measured questions to
an answer pair accepted by the win predicate of the combined game. -/
def DirectCombinedWinTransport (D : DirectLdParams) (t₁ t₂ : LdType)
    (sample : DirectLdSpace D.combined) : Prop :=
  ∀ a b : DirectLdAnswer D,
    directLdWinPredicate D
        (directCombinedMeasuredQuestion D (t₁, directLdMap D.combined t₁ sample))
        (directCombinedMeasuredQuestion D (t₂, directLdMap D.combined t₂ sample))
        a b = true →
      directLdWinPredicate D.combined
        (t₁, directLdMap D.combined t₁ sample) (t₂, directLdMap D.combined t₂ sample)
        (directCombinedAnswerMap D (t₁, directLdMap D.combined t₁ sample) a)
        (directCombinedAnswerMap D (t₂, directLdMap D.combined t₂ sample) b) = true

/-- The axis-parallel-line versus point branch. -/
theorem directCombinedWinTransport_aline_point (D : DirectLdParams)
    (sample : DirectLdSpace D.combined) :
    DirectCombinedWinTransport D .aline .point sample := by
  intro a b hwin
  rcases hsplit : directCombinedIndexSplit D sample.index with j | r₀
  · have hindex : sample.index = combinedPointVar D.m D.k j :=
      eq_combinedPointVar_of_indexSplit D hsplit
    rw [directCombined_measuredQuestion_of_pointVar D .aline j sample hindex,
      directCombined_measuredQuestion_of_pointVar D .point j sample hindex] at hwin
    cases a with
    | pointVals _ => simp [directLdWinPredicate, validDirectLdAnswer] at hwin
    | dlinePolys _ => simp [directLdWinPredicate, validDirectLdAnswer] at hwin
    | alinePolys f =>
      cases b with
      | alinePolys _ => simp [directLdWinPredicate, validDirectLdAnswer] at hwin
      | dlinePolys _ => simp [directLdWinPredicate, validDirectLdAnswer] at hwin
      | pointVals c =>
        have hsplitL : directCombinedIndexSplit D
            (directLdMap D.combined LdType.aline sample).index = Sum.inl j := hsplit
        have hcond : directAlinePointCondition D
            (directLdMap D .aline (directCombinedSampleProjection D j sample))
            (directLdMap D .point (directCombinedSampleProjection D j sample))
            f c := by
          simpa [directLdWinPredicate, validDirectLdAnswer] using hwin
        have hdirpt : directCombinedPointPart D (coordinateDirection sample.index) =
            coordinateDirection j := by
          rw [hindex]
          exact directCombinedPointPart_coordinateDirection_pointVar D j
        have hcoef : directCombinedCoefficientPart D
            (coordinateDirection sample.index) = 0 := by
          rw [hindex]
          exact directCombinedCoefficientPart_coordinateDirection_pointVar D j
        have hmdir : directCombinedMeasuredDirection D
            (LdType.aline, directLdMap D.combined LdType.aline sample) =
            directCombinedPointPart D (coordinateDirection sample.index) := by
          simp only [directCombinedMeasuredDirection, directLdMap, hindex,
            directCombinedIndexSplit_combinedPointVar,
            directCombinedPointPart_coordinateDirection_pointVar]
        have hs : directCombinedPointPart D
              (lineRepMap (coordinateDirection sample.index) sample.point) =
            lineRepMap (directCombinedPointPart D (coordinateDirection sample.index))
                (directCombinedPointPart D
                  (lineRepMap (coordinateDirection sample.index) sample.point)) +
              directCombinedRebaseParameter D
                  (LdType.aline, directLdMap D.combined LdType.aline sample) •
                directCombinedPointPart D (coordinateDirection sample.index) := by
          rw [← hmdir]
          exact directLineRepParameter_spec _ _
        have hgoal : directAlinePointCondition D.combined
            (directLdMap D.combined LdType.aline sample)
            (directLdMap D.combined LdType.point sample)
            (fun _ => coefficientsOfPolynomial D.combined.d
                (combinedAxisPolynomial
                  (directCombinedCoefficientPart D
                    (directLdMap D.combined LdType.aline sample).point)
                  (directCombinedRebaseParameter D
                    (LdType.aline, directLdMap D.combined LdType.aline sample)) f))
            (fun _ => ∑ r : Fin D.k, directCombinedCoefficientPart D
              (directLdMap D.combined LdType.point sample).point r * c r) := by
          intro T hT _
          refine directCombinedAxisAnswer_eval D sample.point
            (coordinateDirection sample.index) hcoef _ T hs f c hT ?_
          rw [hdirpt]
          exact hcond
        have hmapA : directCombinedAnswerMap D
            (LdType.aline, directLdMap D.combined LdType.aline sample) (.alinePolys f) =
            .alinePolys (fun _ => coefficientsOfPolynomial D.combined.d
                (combinedAxisPolynomial
                  (directCombinedCoefficientPart D
                    (directLdMap D.combined LdType.aline sample).point)
                  (directCombinedRebaseParameter D
                    (LdType.aline, directLdMap D.combined LdType.aline sample)) f)) := by
          simp only [directCombinedAnswerMap, hsplitL]
        have hmapB : directCombinedAnswerMap D
            (LdType.point, directLdMap D.combined LdType.point sample) (.pointVals c) =
            .pointVals (fun _ => ∑ r : Fin D.k, directCombinedCoefficientPart D
              (directLdMap D.combined LdType.point sample).point r * c r) := rfl
        rw [hmapA, hmapB]
        simpa [directLdWinPredicate, validDirectLdAnswer] using hgoal
  · have hindex : sample.index = combinedCoefficientVar D.m D.k r₀ :=
      eq_combinedCoefficientVar_of_indexSplit D hsplit
    rw [directCombined_measuredQuestion_of_coefficientVar D .aline r₀ sample hindex,
      directCombined_measuredQuestion_of_coefficientVar D .point r₀ sample hindex] at hwin
    have hab : a = b := directLdAnswer_eq_of_win_self D _ hwin
    subst hab
    cases a with
    | alinePolys _ =>
      simp [directLdWinPredicate, directLdPointQuestionOf, validDirectLdAnswer] at hwin
    | dlinePolys _ =>
      simp [directLdWinPredicate, directLdPointQuestionOf, validDirectLdAnswer] at hwin
    | pointVals bv =>
      have hsplitL : directCombinedIndexSplit D
          (directLdMap D.combined LdType.aline sample).index = Sum.inr r₀ := hsplit
      have hgoal : directAlinePointCondition D.combined
          (directLdMap D.combined LdType.aline sample)
          (directLdMap D.combined LdType.point sample)
          (fun _ => coefficientsOfPolynomial D.combined.d
              (fiberLinePolynomial
                (directCombinedCoefficientPart D (directLdMap D.combined LdType.aline sample).point)
                (directCombinedCoefficientPart D
                  (directCombinedQuestionDirection D (LdType.aline, directLdMap D.combined
                    LdType.aline sample))) bv))
          (fun _ => ∑ r : Fin D.k, directCombinedCoefficientPart D
            (directLdMap D.combined LdType.point sample).point r * bv r) := by
        intro T hT _
        exact fiberAnswerEval D D.combined.d D.hd
          (directLdMap D.combined LdType.point sample).point
          (directLdMap D.combined LdType.aline sample).point
          (directCombinedQuestionDirection D (LdType.aline, directLdMap D.combined LdType.aline
            sample)) bv T hT
      have hmapA : directCombinedAnswerMap D
          (LdType.aline, directLdMap D.combined LdType.aline sample) (.pointVals bv) =
          .alinePolys (fun _ => coefficientsOfPolynomial D.combined.d
              (fiberLinePolynomial
                (directCombinedCoefficientPart D (directLdMap D.combined LdType.aline sample).point)
                (directCombinedCoefficientPart D
                  (directCombinedQuestionDirection D (LdType.aline, directLdMap D.combined
                    LdType.aline sample))) bv)) := by
        simp only [directCombinedAnswerMap, hsplitL]
      have hmapB : directCombinedAnswerMap D
          (LdType.point, directLdMap D.combined LdType.point sample) (.pointVals bv) =
          .pointVals (fun _ => ∑ r : Fin D.k, directCombinedCoefficientPart D
            (directLdMap D.combined LdType.point sample).point r * bv r) := rfl
      rw [hmapA, hmapB]
      simpa [directLdWinPredicate, validDirectLdAnswer] using hgoal

/-- The point versus axis-parallel-line branch. -/
theorem directCombinedWinTransport_point_aline (D : DirectLdParams)
    (sample : DirectLdSpace D.combined) :
    DirectCombinedWinTransport D .point .aline sample := by
  intro a b hwin
  rcases hsplit : directCombinedIndexSplit D sample.index with j | r₀
  · have hindex : sample.index = combinedPointVar D.m D.k j :=
      eq_combinedPointVar_of_indexSplit D hsplit
    rw [directCombined_measuredQuestion_of_pointVar D .point j sample hindex,
      directCombined_measuredQuestion_of_pointVar D .aline j sample hindex] at hwin
    cases a with
    | alinePolys _ => simp [directLdWinPredicate, validDirectLdAnswer] at hwin
    | dlinePolys _ => simp [directLdWinPredicate, validDirectLdAnswer] at hwin
    | pointVals c =>
      cases b with
      | pointVals _ => simp [directLdWinPredicate, validDirectLdAnswer] at hwin
      | dlinePolys _ => simp [directLdWinPredicate, validDirectLdAnswer] at hwin
      | alinePolys f =>
        have hsplitL : directCombinedIndexSplit D
            (directLdMap D.combined LdType.aline sample).index = Sum.inl j := hsplit
        have hcond : directAlinePointCondition D
            (directLdMap D .aline (directCombinedSampleProjection D j sample))
            (directLdMap D .point (directCombinedSampleProjection D j sample))
            f c := by
          simpa [directLdWinPredicate, validDirectLdAnswer] using hwin
        have hdirpt : directCombinedPointPart D (coordinateDirection sample.index) =
            coordinateDirection j := by
          rw [hindex]
          exact directCombinedPointPart_coordinateDirection_pointVar D j
        have hcoef : directCombinedCoefficientPart D
            (coordinateDirection sample.index) = 0 := by
          rw [hindex]
          exact directCombinedCoefficientPart_coordinateDirection_pointVar D j
        have hmdir : directCombinedMeasuredDirection D
            (LdType.aline, directLdMap D.combined LdType.aline sample) =
            directCombinedPointPart D (coordinateDirection sample.index) := by
          simp only [directCombinedMeasuredDirection, directLdMap, hindex,
            directCombinedIndexSplit_combinedPointVar,
            directCombinedPointPart_coordinateDirection_pointVar]
        have hs : directCombinedPointPart D
              (lineRepMap (coordinateDirection sample.index) sample.point) =
            lineRepMap (directCombinedPointPart D (coordinateDirection sample.index))
                (directCombinedPointPart D
                  (lineRepMap (coordinateDirection sample.index) sample.point)) +
              directCombinedRebaseParameter D
                  (LdType.aline, directLdMap D.combined LdType.aline sample) •
                directCombinedPointPart D (coordinateDirection sample.index) := by
          rw [← hmdir]
          exact directLineRepParameter_spec _ _
        have hgoal : directAlinePointCondition D.combined
            (directLdMap D.combined LdType.aline sample)
            (directLdMap D.combined LdType.point sample)
            (fun _ => coefficientsOfPolynomial D.combined.d
                (combinedAxisPolynomial
                  (directCombinedCoefficientPart D
                    (directLdMap D.combined LdType.aline sample).point)
                  (directCombinedRebaseParameter D
                    (LdType.aline, directLdMap D.combined LdType.aline sample)) f))
            (fun _ => ∑ r : Fin D.k, directCombinedCoefficientPart D
              (directLdMap D.combined LdType.point sample).point r * c r) := by
          intro T hT _
          refine directCombinedAxisAnswer_eval D sample.point
            (coordinateDirection sample.index) hcoef _ T hs f c hT ?_
          rw [hdirpt]
          exact hcond
        have hmapA : directCombinedAnswerMap D
            (LdType.point, directLdMap D.combined LdType.point sample) (.pointVals c) =
            .pointVals (fun _ => ∑ r : Fin D.k, directCombinedCoefficientPart D
              (directLdMap D.combined LdType.point sample).point r * c r) := rfl
        have hmapB : directCombinedAnswerMap D
            (LdType.aline, directLdMap D.combined LdType.aline sample) (.alinePolys f) =
            .alinePolys (fun _ => coefficientsOfPolynomial D.combined.d
                (combinedAxisPolynomial
                  (directCombinedCoefficientPart D
                    (directLdMap D.combined LdType.aline sample).point)
                  (directCombinedRebaseParameter D
                    (LdType.aline, directLdMap D.combined LdType.aline sample)) f)) := by
          simp only [directCombinedAnswerMap, hsplitL]
        rw [hmapA, hmapB]
        simpa [directLdWinPredicate, validDirectLdAnswer] using hgoal
  · have hindex : sample.index = combinedCoefficientVar D.m D.k r₀ :=
      eq_combinedCoefficientVar_of_indexSplit D hsplit
    rw [directCombined_measuredQuestion_of_coefficientVar D .point r₀ sample hindex,
      directCombined_measuredQuestion_of_coefficientVar D .aline r₀ sample hindex] at hwin
    have hab : a = b := directLdAnswer_eq_of_win_self D _ hwin
    subst hab
    cases a with
    | alinePolys _ =>
      simp [directLdWinPredicate, directLdPointQuestionOf, validDirectLdAnswer] at hwin
    | dlinePolys _ =>
      simp [directLdWinPredicate, directLdPointQuestionOf, validDirectLdAnswer] at hwin
    | pointVals bv =>
      have hsplitL : directCombinedIndexSplit D
          (directLdMap D.combined LdType.aline sample).index = Sum.inr r₀ := hsplit
      have hgoal : directAlinePointCondition D.combined
          (directLdMap D.combined LdType.aline sample)
          (directLdMap D.combined LdType.point sample)
          (fun _ => coefficientsOfPolynomial D.combined.d
              (fiberLinePolynomial
                (directCombinedCoefficientPart D (directLdMap D.combined LdType.aline sample).point)
                (directCombinedCoefficientPart D
                  (directCombinedQuestionDirection D (LdType.aline, directLdMap D.combined
                    LdType.aline sample))) bv))
          (fun _ => ∑ r : Fin D.k, directCombinedCoefficientPart D
            (directLdMap D.combined LdType.point sample).point r * bv r) := by
        intro T hT _
        exact fiberAnswerEval D D.combined.d D.hd
          (directLdMap D.combined LdType.point sample).point
          (directLdMap D.combined LdType.aline sample).point
          (directCombinedQuestionDirection D (LdType.aline, directLdMap D.combined LdType.aline
            sample)) bv T hT
      have hmapA : directCombinedAnswerMap D
          (LdType.point, directLdMap D.combined LdType.point sample) (.pointVals bv) =
          .pointVals (fun _ => ∑ r : Fin D.k, directCombinedCoefficientPart D
            (directLdMap D.combined LdType.point sample).point r * bv r) := rfl
      have hmapB : directCombinedAnswerMap D
          (LdType.aline, directLdMap D.combined LdType.aline sample) (.pointVals bv) =
          .alinePolys (fun _ => coefficientsOfPolynomial D.combined.d
              (fiberLinePolynomial
                (directCombinedCoefficientPart D (directLdMap D.combined LdType.aline sample).point)
                (directCombinedCoefficientPart D
                  (directCombinedQuestionDirection D (LdType.aline, directLdMap D.combined
                    LdType.aline sample))) bv)) := by
        simp only [directCombinedAnswerMap, hsplitL]
      rw [hmapA, hmapB]
      simpa [directLdWinPredicate, validDirectLdAnswer] using hgoal

/-- The diagonal-line versus point branch. -/
theorem directCombinedWinTransport_dline_point (D : DirectLdParams)
    (sample : DirectLdSpace D.combined) :
    DirectCombinedWinTransport D .dline .point sample := by
  intro a b hwin
  rcases hsplit : directCombinedIndexSplit D sample.index with j | r₀
  · have hindex : sample.index = combinedPointVar D.m D.k j :=
      eq_combinedPointVar_of_indexSplit D hsplit
    rw [directCombined_measuredQuestion_of_pointVar D .dline j sample hindex,
      directCombined_measuredQuestion_of_pointVar D .point j sample hindex] at hwin
    cases a with
    | pointVals _ => simp [directLdWinPredicate, validDirectLdAnswer] at hwin
    | alinePolys _ => simp [directLdWinPredicate, validDirectLdAnswer] at hwin
    | dlinePolys f =>
      cases b with
      | alinePolys _ => simp [directLdWinPredicate, validDirectLdAnswer] at hwin
      | dlinePolys _ => simp [directLdWinPredicate, validDirectLdAnswer] at hwin
      | pointVals c =>
        have hsplitL : directCombinedIndexSplit D
            (directLdMap D.combined LdType.dline sample).index = Sum.inl j := hsplit
        have hcond : directDlinePointCondition D
            (directLdMap D .dline (directCombinedSampleProjection D j sample))
            (directLdMap D .point (directCombinedSampleProjection D j sample))
            f c := by
          simpa [directLdWinPredicate, validDirectLdAnswer] using hwin
        have hdirpt : directCombinedPointPart D (directPrefixProjection sample.index
          sample.direction) =
            directPrefixProjection j
              (directCombinedPointPart D sample.direction) := by
          rw [hindex]
          exact directCombinedPointPart_directPrefixProjection_pointVar D j
            sample.direction
        have hmdir : directCombinedMeasuredDirection D
            (LdType.dline, directLdMap D.combined LdType.dline sample) =
            directCombinedPointPart D (directPrefixProjection sample.index sample.direction) := by
          simp only [directCombinedMeasuredDirection, directLdMap, hindex,
            directCombinedIndexSplit_combinedPointVar,
            directCombinedPointPart_directPrefixProjection_pointVar,
            directPrefixProjection_idempotent]
        have hs : directCombinedPointPart D
              (lineRepMap (directPrefixProjection sample.index sample.direction) sample.point) =
            lineRepMap (directCombinedPointPart D (directPrefixProjection sample.index
              sample.direction))
                (directCombinedPointPart D
                  (lineRepMap (directPrefixProjection sample.index sample.direction) sample.point))
                    +
              directCombinedRebaseParameter D
                  (LdType.dline, directLdMap D.combined LdType.dline sample) •
                directCombinedPointPart D (directPrefixProjection sample.index sample.direction) :=
                  by
          rw [← hmdir]
          exact directLineRepParameter_spec _ _
        have hgoal : directDlinePointCondition D.combined
            (directLdMap D.combined LdType.dline sample)
            (directLdMap D.combined LdType.point sample)
            (fun _ => coefficientsOfPolynomial (D.combined.m * D.combined.d)
                (combinedDiagonalPolynomial
                  (directCombinedCoefficientPart D (directLdMap D.combined LdType.dline
                    sample).point)
                  (directCombinedCoefficientPart D
                    (directCombinedQuestionDirection D (LdType.dline, directLdMap D.combined
                      LdType.dline sample)))
                  (directCombinedRebaseParameter D
                    (LdType.dline, directLdMap D.combined LdType.dline sample)) f))
            (fun _ => ∑ r : Fin D.k, directCombinedCoefficientPart D
              (directLdMap D.combined LdType.point sample).point r * c r) := by
          intro T hT _
          refine directCombinedDiagonalAnswer_eval D sample.point
            (directPrefixProjection sample.index sample.direction) _ T hs f c hT ?_
          rw [hdirpt]
          exact hcond
        have hmapA : directCombinedAnswerMap D
            (LdType.dline, directLdMap D.combined LdType.dline sample) (.dlinePolys f) =
            .dlinePolys (fun _ => coefficientsOfPolynomial (D.combined.m * D.combined.d)
                (combinedDiagonalPolynomial
                  (directCombinedCoefficientPart D (directLdMap D.combined LdType.dline
                    sample).point)
                  (directCombinedCoefficientPart D
                    (directCombinedQuestionDirection D (LdType.dline, directLdMap D.combined
                      LdType.dline sample)))
                  (directCombinedRebaseParameter D
                    (LdType.dline, directLdMap D.combined LdType.dline sample)) f)) := by
          simp only [directCombinedAnswerMap, hsplitL]
        have hmapB : directCombinedAnswerMap D
            (LdType.point, directLdMap D.combined LdType.point sample) (.pointVals c) =
            .pointVals (fun _ => ∑ r : Fin D.k, directCombinedCoefficientPart D
              (directLdMap D.combined LdType.point sample).point r * c r) := rfl
        rw [hmapA, hmapB]
        simpa [directLdWinPredicate, validDirectLdAnswer] using hgoal
  · have hindex : sample.index = combinedCoefficientVar D.m D.k r₀ :=
      eq_combinedCoefficientVar_of_indexSplit D hsplit
    rw [directCombined_measuredQuestion_of_coefficientVar D .dline r₀ sample hindex,
      directCombined_measuredQuestion_of_coefficientVar D .point r₀ sample hindex] at hwin
    have hab : a = b := directLdAnswer_eq_of_win_self D _ hwin
    subst hab
    cases a with
    | alinePolys _ =>
      simp [directLdWinPredicate, directLdPointQuestionOf, validDirectLdAnswer] at hwin
    | dlinePolys _ =>
      simp [directLdWinPredicate, directLdPointQuestionOf, validDirectLdAnswer] at hwin
    | pointVals bv =>
      have hsplitL : directCombinedIndexSplit D
          (directLdMap D.combined LdType.dline sample).index = Sum.inr r₀ := hsplit
      have hgoal : directDlinePointCondition D.combined
          (directLdMap D.combined LdType.dline sample)
          (directLdMap D.combined LdType.point sample)
          (fun _ => coefficientsOfPolynomial (D.combined.m * D.combined.d)
              (fiberLinePolynomial
                (directCombinedCoefficientPart D (directLdMap D.combined LdType.dline sample).point)
                (directCombinedCoefficientPart D
                  (directCombinedQuestionDirection D (LdType.dline, directLdMap D.combined
                    LdType.dline sample))) bv))
          (fun _ => ∑ r : Fin D.k, directCombinedCoefficientPart D
            (directLdMap D.combined LdType.point sample).point r * bv r) := by
        intro T hT _
        exact fiberAnswerEval D (D.combined.m * D.combined.d) (oneLeCombinedDlineDegree D)
          (directLdMap D.combined LdType.point sample).point
          (directLdMap D.combined LdType.dline sample).point
          (directCombinedQuestionDirection D (LdType.dline, directLdMap D.combined LdType.dline
            sample)) bv T hT
      have hmapA : directCombinedAnswerMap D
          (LdType.dline, directLdMap D.combined LdType.dline sample) (.pointVals bv) =
          .dlinePolys (fun _ => coefficientsOfPolynomial (D.combined.m * D.combined.d)
              (fiberLinePolynomial
                (directCombinedCoefficientPart D (directLdMap D.combined LdType.dline sample).point)
                (directCombinedCoefficientPart D
                  (directCombinedQuestionDirection D (LdType.dline, directLdMap D.combined
                    LdType.dline sample))) bv)) := by
        simp only [directCombinedAnswerMap, hsplitL]
      have hmapB : directCombinedAnswerMap D
          (LdType.point, directLdMap D.combined LdType.point sample) (.pointVals bv) =
          .pointVals (fun _ => ∑ r : Fin D.k, directCombinedCoefficientPart D
            (directLdMap D.combined LdType.point sample).point r * bv r) := rfl
      rw [hmapA, hmapB]
      simpa [directLdWinPredicate, validDirectLdAnswer] using hgoal

/-- The point versus diagonal-line branch. -/
theorem directCombinedWinTransport_point_dline (D : DirectLdParams)
    (sample : DirectLdSpace D.combined) :
    DirectCombinedWinTransport D .point .dline sample := by
  intro a b hwin
  rcases hsplit : directCombinedIndexSplit D sample.index with j | r₀
  · have hindex : sample.index = combinedPointVar D.m D.k j :=
      eq_combinedPointVar_of_indexSplit D hsplit
    rw [directCombined_measuredQuestion_of_pointVar D .point j sample hindex,
      directCombined_measuredQuestion_of_pointVar D .dline j sample hindex] at hwin
    cases a with
    | alinePolys _ => simp [directLdWinPredicate, validDirectLdAnswer] at hwin
    | dlinePolys _ => simp [directLdWinPredicate, validDirectLdAnswer] at hwin
    | pointVals c =>
      cases b with
      | pointVals _ => simp [directLdWinPredicate, validDirectLdAnswer] at hwin
      | alinePolys _ => simp [directLdWinPredicate, validDirectLdAnswer] at hwin
      | dlinePolys f =>
        have hsplitL : directCombinedIndexSplit D
            (directLdMap D.combined LdType.dline sample).index = Sum.inl j := hsplit
        have hcond : directDlinePointCondition D
            (directLdMap D .dline (directCombinedSampleProjection D j sample))
            (directLdMap D .point (directCombinedSampleProjection D j sample))
            f c := by
          simpa [directLdWinPredicate, validDirectLdAnswer] using hwin
        have hdirpt : directCombinedPointPart D (directPrefixProjection sample.index
          sample.direction) =
            directPrefixProjection j
              (directCombinedPointPart D sample.direction) := by
          rw [hindex]
          exact directCombinedPointPart_directPrefixProjection_pointVar D j
            sample.direction
        have hmdir : directCombinedMeasuredDirection D
            (LdType.dline, directLdMap D.combined LdType.dline sample) =
            directCombinedPointPart D (directPrefixProjection sample.index sample.direction) := by
          simp only [directCombinedMeasuredDirection, directLdMap, hindex,
            directCombinedIndexSplit_combinedPointVar,
            directCombinedPointPart_directPrefixProjection_pointVar,
            directPrefixProjection_idempotent]
        have hs : directCombinedPointPart D
              (lineRepMap (directPrefixProjection sample.index sample.direction) sample.point) =
            lineRepMap (directCombinedPointPart D (directPrefixProjection sample.index
              sample.direction))
                (directCombinedPointPart D
                  (lineRepMap (directPrefixProjection sample.index sample.direction) sample.point))
                    +
              directCombinedRebaseParameter D
                  (LdType.dline, directLdMap D.combined LdType.dline sample) •
                directCombinedPointPart D (directPrefixProjection sample.index sample.direction) :=
                  by
          rw [← hmdir]
          exact directLineRepParameter_spec _ _
        have hgoal : directDlinePointCondition D.combined
            (directLdMap D.combined LdType.dline sample)
            (directLdMap D.combined LdType.point sample)
            (fun _ => coefficientsOfPolynomial (D.combined.m * D.combined.d)
                (combinedDiagonalPolynomial
                  (directCombinedCoefficientPart D (directLdMap D.combined LdType.dline
                    sample).point)
                  (directCombinedCoefficientPart D
                    (directCombinedQuestionDirection D (LdType.dline, directLdMap D.combined
                      LdType.dline sample)))
                  (directCombinedRebaseParameter D
                    (LdType.dline, directLdMap D.combined LdType.dline sample)) f))
            (fun _ => ∑ r : Fin D.k, directCombinedCoefficientPart D
              (directLdMap D.combined LdType.point sample).point r * c r) := by
          intro T hT _
          refine directCombinedDiagonalAnswer_eval D sample.point
            (directPrefixProjection sample.index sample.direction) _ T hs f c hT ?_
          rw [hdirpt]
          exact hcond
        have hmapA : directCombinedAnswerMap D
            (LdType.point, directLdMap D.combined LdType.point sample) (.pointVals c) =
            .pointVals (fun _ => ∑ r : Fin D.k, directCombinedCoefficientPart D
              (directLdMap D.combined LdType.point sample).point r * c r) := rfl
        have hmapB : directCombinedAnswerMap D
            (LdType.dline, directLdMap D.combined LdType.dline sample) (.dlinePolys f) =
            .dlinePolys (fun _ => coefficientsOfPolynomial (D.combined.m * D.combined.d)
                (combinedDiagonalPolynomial
                  (directCombinedCoefficientPart D (directLdMap D.combined LdType.dline
                    sample).point)
                  (directCombinedCoefficientPart D
                    (directCombinedQuestionDirection D (LdType.dline, directLdMap D.combined
                      LdType.dline sample)))
                  (directCombinedRebaseParameter D
                    (LdType.dline, directLdMap D.combined LdType.dline sample)) f)) := by
          simp only [directCombinedAnswerMap, hsplitL]
        rw [hmapA, hmapB]
        simpa [directLdWinPredicate, validDirectLdAnswer] using hgoal
  · have hindex : sample.index = combinedCoefficientVar D.m D.k r₀ :=
      eq_combinedCoefficientVar_of_indexSplit D hsplit
    rw [directCombined_measuredQuestion_of_coefficientVar D .point r₀ sample hindex,
      directCombined_measuredQuestion_of_coefficientVar D .dline r₀ sample hindex] at hwin
    have hab : a = b := directLdAnswer_eq_of_win_self D _ hwin
    subst hab
    cases a with
    | alinePolys _ =>
      simp [directLdWinPredicate, directLdPointQuestionOf, validDirectLdAnswer] at hwin
    | dlinePolys _ =>
      simp [directLdWinPredicate, directLdPointQuestionOf, validDirectLdAnswer] at hwin
    | pointVals bv =>
      have hsplitL : directCombinedIndexSplit D
          (directLdMap D.combined LdType.dline sample).index = Sum.inr r₀ := hsplit
      have hgoal : directDlinePointCondition D.combined
          (directLdMap D.combined LdType.dline sample)
          (directLdMap D.combined LdType.point sample)
          (fun _ => coefficientsOfPolynomial (D.combined.m * D.combined.d)
              (fiberLinePolynomial
                (directCombinedCoefficientPart D (directLdMap D.combined LdType.dline sample).point)
                (directCombinedCoefficientPart D
                  (directCombinedQuestionDirection D (LdType.dline, directLdMap D.combined
                    LdType.dline sample))) bv))
          (fun _ => ∑ r : Fin D.k, directCombinedCoefficientPart D
            (directLdMap D.combined LdType.point sample).point r * bv r) := by
        intro T hT _
        exact fiberAnswerEval D (D.combined.m * D.combined.d) (oneLeCombinedDlineDegree D)
          (directLdMap D.combined LdType.point sample).point
          (directLdMap D.combined LdType.dline sample).point
          (directCombinedQuestionDirection D (LdType.dline, directLdMap D.combined LdType.dline
            sample)) bv T hT
      have hmapA : directCombinedAnswerMap D
          (LdType.point, directLdMap D.combined LdType.point sample) (.pointVals bv) =
          .pointVals (fun _ => ∑ r : Fin D.k, directCombinedCoefficientPart D
            (directLdMap D.combined LdType.point sample).point r * bv r) := rfl
      have hmapB : directCombinedAnswerMap D
          (LdType.dline, directLdMap D.combined LdType.dline sample) (.pointVals bv) =
          .dlinePolys (fun _ => coefficientsOfPolynomial (D.combined.m * D.combined.d)
              (fiberLinePolynomial
                (directCombinedCoefficientPart D (directLdMap D.combined LdType.dline sample).point)
                (directCombinedCoefficientPart D
                  (directCombinedQuestionDirection D (LdType.dline, directLdMap D.combined
                    LdType.dline sample))) bv)) := by
        simp only [directCombinedAnswerMap, hsplitL]
      rw [hmapA, hmapB]
      simpa [directLdWinPredicate, validDirectLdAnswer] using hgoal

/-- A branch whose ordered type pair is diagonal: the two questions of the
combined game are equal, so the acceptance clause of the original game at the
two equal measured questions forces the two measured outcomes to be equal, and
the relabelling sends them to equal combined outcomes. -/
theorem directCombinedWinTransport_diagonal (D : DirectLdParams) (t : LdType)
    (sample : DirectLdSpace D.combined) :
    DirectCombinedWinTransport D t t sample := by
  intro a b hwin
  have hab : a = b := directLdAnswer_eq_of_win_self D _ hwin
  subst hab
  exact directLdWinPredicate_self D.combined (t, directLdMap D.combined t sample) _
    (validDirectLdAnswer_directCombinedAnswerMap D
      (t, directLdMap D.combined t sample) a)

/-- The axis-parallel-line versus diagonal-line branch: the win predicate of
the combined game imposes no condition on that ordered type pair. -/
theorem directCombinedWinTransport_aline_dline (D : DirectLdParams)
    (sample : DirectLdSpace D.combined) :
    DirectCombinedWinTransport D .aline .dline sample := by
  intro a b _
  exact directLdWinPredicate_aline_dline D.combined _ _ _ _
    (validDirectLdAnswer_directCombinedAnswerMap D
      (LdType.aline, directLdMap D.combined LdType.aline sample) a)
    (validDirectLdAnswer_directCombinedAnswerMap D
      (LdType.dline, directLdMap D.combined LdType.dline sample) b)

/-- The diagonal-line versus axis-parallel-line branch. -/
theorem directCombinedWinTransport_dline_aline (D : DirectLdParams)
    (sample : DirectLdSpace D.combined) :
    DirectCombinedWinTransport D .dline .aline sample := by
  intro a b _
  exact directLdWinPredicate_dline_aline D.combined _ _ _ _
    (validDirectLdAnswer_directCombinedAnswerMap D
      (LdType.dline, directLdMap D.combined LdType.dline sample) a)
    (validDirectLdAnswer_directCombinedAnswerMap D
      (LdType.aline, directLdMap D.combined LdType.aline sample) b)

/-- The acceptance transport of `lem:ld-combined-value` on every one of the
nine ordered type pairs of the combined game.  This is the hypothesis of
`directRejectedMass_directCombinedStrategy_le` at the question pair attached to
a sample of the combined game. -/
theorem directCombinedWinTransport_all (D : DirectLdParams) (t₁ t₂ : LdType)
    (sample : DirectLdSpace D.combined) :
    DirectCombinedWinTransport D t₁ t₂ sample := by
  cases t₁ <;> cases t₂
  · exact directCombinedWinTransport_diagonal D .point sample
  · exact directCombinedWinTransport_point_aline D sample
  · exact directCombinedWinTransport_point_dline D sample
  · exact directCombinedWinTransport_aline_point D sample
  · exact directCombinedWinTransport_diagonal D .aline sample
  · exact directCombinedWinTransport_aline_dline D sample
  · exact directCombinedWinTransport_dline_point D sample
  · exact directCombinedWinTransport_dline_aline D sample
  · exact directCombinedWinTransport_diagonal D .dline sample

end

end MIPStarRE.QPBT
