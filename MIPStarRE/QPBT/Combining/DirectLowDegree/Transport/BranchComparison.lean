import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Strategy
import MIPStarRE.QPBT.Combining.DirectLowDegree.GameValue
import MIPStarRE.LDT.Test.StrategyBiProj.Measurements

/-!
# Branch comparison for the coordinate strategies of the direct low-degree game

Every branch of the mature low individual degree failure probability of a
coordinate strategy `directCoordinateProjStrat` is compared with the ordered
type-pair branch of the direct game asking the same questions.  An accepted
direct answer pair reads out to equal mature answers: the line answer, rebased
to the mature line and evaluated at the mature base point, is the point
answer, and the zero-direction convention reads the constant value at the base
point.  Hence the mature inconsistency mass at a question pair is at most the
rejected direct Born mass there.  The point-agreement and axis-line branches
then compare exactly after the coordinate reindexing of `directPointEquiv`;
the diagonal branches are treated in `Transport.DiagonalRecursion`.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:214-458`
- `references/ldt-paper/test_definition.tex:130-151`
- `blueprint/src/chapter/ch13_qpbt_test.tex:38-121,139-166`
- `MIPStarRE/LDT/Test/StrategyFailures.lean:18-130`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.Quantum

noncomputable section

/-- Admissible field sizes are positive, so mature points over a direct
parameter tuple form a nonempty type. -/
instance (D : DirectLdParams) : NeZero D.q :=
  ⟨Nat.ne_of_gt D.toLDTParameters.hq⟩

/-! ## Rejected Born mass at a fixed question pair -/

/-- The Born mass of the rejected answer pairs at a fixed pair of direct
questions.  Its uniform average over the common direct sample of an ordered
type pair is `directLdBranchRejectionProbability`. -/
def directRejectedMass (D : DirectLdParams) (S : Strategy (directLdGame D))
    (x y : DirectLdQuestion D) : ℝ :=
  ∑ a : DirectLdAnswer D, ∑ b : DirectLdAnswer D,
    if directLdWinPredicate D x y a b then 0 else outcomeWeight S x y a b

theorem directRejectedMass_nonneg (D : DirectLdParams)
    (S : Strategy (directLdGame D)) (x y : DirectLdQuestion D) :
    0 ≤ directRejectedMass D S x y := by
  refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
  split_ifs
  · exact le_rfl
  · exact outcomeWeight_nonneg S x y a b

/-- The branch rejection probability of an ordered type pair is the uniform
average of the rejected Born mass at the canonical questions of the common
direct sample. -/
theorem directLdBranchRejectionProbability_eq_avgOver (D : DirectLdParams)
    (S : Strategy (directLdGame D)) (types : LdType × LdType) :
    directLdBranchRejectionProbability D S types =
      avgOver (uniformDistribution (DirectLdSpace D)) fun sample =>
        directRejectedMass D S
          (types.1, directLdMap D types.1 sample)
          (types.2, directLdMap D types.2 sample) :=
  rfl

/-- When every accepted direct answer pair reads out to equal mature answers,
the bipartite consistency defect of the two readouts at a fixed question pair
is at most the rejected direct Born mass there.  The matched mass of the
readouts is the Born mass of the pairs with equal readouts, and the total
overlap is the full Born mass, which is one. -/
theorem qBipartiteConsDefect_le_directRejectedMass
    (D : DirectLdParams) (S : Strategy (directLdGame D))
    (hS : S.IsProjective)
    {Outcome : Type*} [Fintype Outcome]
    (x y : DirectLdQuestion D)
    (readA readB : DirectLdAnswer D → Outcome)
    (hwin : ∀ a b, directLdWinPredicate D x y a b = true → readA a = readB b) :
    qBipartiteConsDefect (strategyQuantumState S)
        (ProjMeas.postprocess
          (matrixMeasurementToLDTProjMeas (S.A x) (hS.1 x)) readA).toSubMeas
        (ProjMeas.postprocess
          (matrixMeasurementToLDTProjMeas (S.B y) (hS.2 y)) readB).toSubMeas ≤
      directRejectedMass D S x y := by
  classical
  have hmatch :
      qBipartiteMatchMass (strategyQuantumState S)
          (ProjMeas.postprocess
            (matrixMeasurementToLDTProjMeas (S.A x) (hS.1 x)) readA).toSubMeas
          (ProjMeas.postprocess
            (matrixMeasurementToLDTProjMeas (S.B y) (hS.2 y)) readB).toSubMeas =
        ∑ a : DirectLdAnswer D, ∑ b : DirectLdAnswer D,
          if readA a = readB b then outcomeWeight S x y a b else 0 := by
    unfold qBipartiteMatchMass
    calc
      ∑ c : Outcome, ev (strategyQuantumState S)
          (opTensor
            ((ProjMeas.postprocess
              (matrixMeasurementToLDTProjMeas (S.A x) (hS.1 x)) readA).outcome c)
            ((ProjMeas.postprocess
              (matrixMeasurementToLDTProjMeas (S.B y) (hS.2 y)) readB).outcome c)) =
          ∑ c : Outcome,
            ∑ a ∈ Finset.univ.filter (fun a => readA a = c),
              ∑ b ∈ Finset.univ.filter (fun b => readB b = c),
                outcomeWeight S x y a b := by
        refine Finset.sum_congr rfl ?_
        intro c _
        exact directPostprocessBornWeight D S hS x y readA readB c c
      _ = ∑ c : Outcome, ∑ a : DirectLdAnswer D,
            if readA a = c then
              ∑ b : DirectLdAnswer D,
                if readB b = c then outcomeWeight S x y a b else 0
            else 0 := by
        simp only [Finset.sum_filter]
      _ = ∑ a : DirectLdAnswer D, ∑ c : Outcome,
            if readA a = c then
              ∑ b : DirectLdAnswer D,
                if readB b = c then outcomeWeight S x y a b else 0
            else 0 := Finset.sum_comm
      _ = ∑ a : DirectLdAnswer D, ∑ b : DirectLdAnswer D,
            if readA a = readB b then outcomeWeight S x y a b else 0 := by
        refine Finset.sum_congr rfl ?_
        intro a _
        rw [Finset.sum_ite_eq]
        simp only [Finset.mem_univ, if_true]
        refine Finset.sum_congr rfl ?_
        intro b _
        by_cases hab : readA a = readB b
        · simp [hab]
        · have hba : ¬ readB b = readA a := fun h => hab h.symm
          simp [hab, hba]
  have hone : ∑ a : DirectLdAnswer D, ∑ b : DirectLdAnswer D,
      outcomeWeight S x y a b = 1 :=
    outcomeWeight_sum_eq_one S x y
  have htotal :
      ev (strategyQuantumState S)
        (opTensor
          (ProjMeas.postprocess
            (matrixMeasurementToLDTProjMeas (S.A x) (hS.1 x)) readA).toSubMeas.total
          (ProjMeas.postprocess
            (matrixMeasurementToLDTProjMeas (S.B y) (hS.2 y)) readB).toSubMeas.total) =
        1 := by
    change ev (strategyQuantumState S)
      (Matrix.kroneckerMap (fun x1 x2 => x1 * x2) (1 : Op S.ιA) (1 : Op S.ιB)) = 1
    rw [Matrix.one_kronecker_one]
    exact ev_one_of_isNormalized _ (strategyQuantumState_isNormalized S)
  simp only [qBipartiteConsDefect]
  refine max_le (directRejectedMass_nonneg D S x y) ?_
  rw [htotal, hmatch, ← hone, ← Finset.sum_sub_distrib]
  unfold directRejectedMass
  refine Finset.sum_le_sum fun a _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun b _ => ?_
  have hw := outcomeWeight_nonneg S x y a b
  by_cases hacc : directLdWinPredicate D x y a b = true
  · have hread := hwin a b hacc
    simp [hacc, hread]
  · rw [if_neg hacc]
    split_ifs <;> linarith

/-! ## Accepted answer pairs read out consistently

An accepted answer pair of the direct game consists of well-formed answers
satisfying the line-versus-point clause or the consistency clause of
`def:ld-win-predicate`.  The readouts of `Transport.Questions` evaluate the
rebased line polynomial at the mature base point, which is the direct point
at the canonical rebase parameter; the accepted clause forces this value to
be the point answer.  Zero directions use the constant readout at the base
point, where the universal clause of `rem:ld-win-zero-direction` gives the
value at parameter zero. -/

/-- On the point-agreement branch, an accepted pair of point answers has
equal readouts in every simultaneous coordinate. -/
theorem directPointAnswerReadout_eq_of_win (D : DirectLdParams) (r : Fin D.k)
    (p : Fin D.m → DirectScalarQ D) (a b : DirectLdAnswer D)
    (hwin : directLdWinPredicate D (directLdPointQuestionOf D p)
      (directLdPointQuestionOf D p) a b = true) :
    letI := D.toLDTFieldModel
    directPointAnswerReadout D r a = directPointAnswerReadout D r b := by
  letI := D.toLDTFieldModel
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

/-- The axis-line acceptance clause at the canonical rebase parameter gives
the rebased polynomial its point value at the mature base point. -/
private theorem axis_readout_of_condition (D : DirectLdParams) (r : Fin D.k)
    (line : AxisParallelLine D.toLDTParameters)
    (f : Fin D.k → Fin (D.d + 1) → DirectScalarQ D)
    (c : Fin D.k → DirectScalarQ D)
    (hcond : directAlinePointCondition D
      ⟨lineRepMap (coordinateDirection (Fin.rev line.direction))
          (ldtPointToDirect D line.base),
        Fin.rev line.direction, 0⟩
      ⟨ldtPointToDirect D line.base, D.firstIndex, 0⟩ f c) :
    letI := D.toLDTFieldModel
    directAxisAnswerReadout D r line (.alinePolys f) zeroCoord =
      directScalarEquiv D (c r) := by
  letI := D.toLDTFieldModel
  have heval : evalCoefficient (f r) (directAxisRebaseParameter D line) = c r :=
    hcond (directAxisRebaseParameter D line)
      (directLineRepParameter_spec
        (coordinateDirection (Fin.rev line.direction))
        (ldtPointToDirect D line.base)) r
  simp only [directAxisAnswerReadout]
  rw [AxisLinePolynomial.reparamAt_apply_zero, directAxisAnswerEquiv_apply, heval]

/-- The diagonal-line acceptance clause gives the readout its point value at
the mature base point, using the canonical rebase parameter for a nonzero
direction and the parameter zero for the zero direction. -/
private theorem diagonal_readout_of_condition (D : DirectLdParams) (r : Fin D.k)
    (line : DiagonalLine D.toLDTParameters)
    (f : Fin D.k → Fin (D.m * D.d + 1) → DirectScalarQ D)
    (c : Fin D.k → DirectScalarQ D)
    (hcond : directDlinePointCondition D
      ⟨lineRepMap (ldtPointToDirect D line.direction) (ldtPointToDirect D line.base),
        directDiagonalIndexOf D (ldtPointToDirect D line.direction),
        ldtPointToDirect D line.direction⟩
      ⟨ldtPointToDirect D line.base, D.firstIndex, 0⟩ f c) :
    letI := D.toLDTFieldModel
    directDiagonalAnswerReadout D r line (.dlinePolys f) zeroCoord =
      directScalarEquiv D (c r) := by
  letI := D.toLDTFieldModel
  by_cases hdir : ldtPointToDirect D line.direction = 0
  · have hbase : ldtPointToDirect D line.base =
        lineRepMap (0 : Fin D.m → DirectScalarQ D) (ldtPointToDirect D line.base) := by
      have hspec := directLineRepParameter_spec
        (ldtPointToDirect D line.direction) (ldtPointToDirect D line.base)
      rwa [hdir, smul_zero, add_zero] at hspec
    rw [hdir] at hcond
    have heval : evalCoefficient (f r) 0 = c r := by
      refine hcond 0 ?_ r
      change ldtPointToDirect D line.base =
        lineRepMap (0 : Fin D.m → DirectScalarQ D) (ldtPointToDirect D line.base) +
          (0 : DirectScalarQ D) • (0 : Fin D.m → DirectScalarQ D)
      rw [smul_zero, add_zero]
      exact hbase
    simp only [directDiagonalAnswerReadout, hdir, if_true]
    rw [constantDiagonalAnswer_apply, heval]
  · have heval :
        evalCoefficient (f r) (directDiagonalRebaseParameter D line) = c r :=
      hcond (directDiagonalRebaseParameter D line)
        (directLineRepParameter_spec
          (ldtPointToDirect D line.direction) (ldtPointToDirect D line.base)) r
    simp only [directDiagonalAnswerReadout, hdir, if_false]
    rw [DiagonalLinePolynomial.reparamAt_apply_zero,
      directDiagonalAnswerEquiv_apply, heval]

/-- On the axis-line branch with the line on the left, an accepted direct
answer pair has the rebased line answer, evaluated at the mature base point,
equal to the point readout. -/
theorem directAxisAnswerReadout_zeroCoord_eq_of_win (D : DirectLdParams)
    (r : Fin D.k) (line : AxisParallelLine D.toLDTParameters)
    (a b : DirectLdAnswer D)
    (hwin : directLdWinPredicate D (directAxisQuestionOf D line)
      (directPointQuestionOf D line.base) a b = true) :
    letI := D.toLDTFieldModel
    directAxisAnswerReadout D r line a zeroCoord =
      directPointAnswerReadout D r b := by
  letI := D.toLDTFieldModel
  cases a with
  | alinePolys f =>
      cases b with
      | pointVals c =>
          refine axis_readout_of_condition D r line f c ?_
          simpa [directLdWinPredicate, directAxisQuestionOf, directPointQuestionOf,
            directLdPointQuestionOf, validDirectLdAnswer] using hwin
      | alinePolys _ =>
          simp [directLdWinPredicate, directAxisQuestionOf, directPointQuestionOf,
            directLdPointQuestionOf, validDirectLdAnswer] at hwin
      | dlinePolys _ =>
          simp [directLdWinPredicate, directAxisQuestionOf, directPointQuestionOf,
            directLdPointQuestionOf, validDirectLdAnswer] at hwin
  | pointVals _ =>
      simp [directLdWinPredicate, directAxisQuestionOf, directPointQuestionOf,
        directLdPointQuestionOf, validDirectLdAnswer] at hwin
  | dlinePolys _ =>
      simp [directLdWinPredicate, directAxisQuestionOf, directPointQuestionOf,
        directLdPointQuestionOf, validDirectLdAnswer] at hwin

/-- On the axis-line branch with the point on the left, an accepted direct
answer pair has the point readout equal to the rebased line answer evaluated
at the mature base point. -/
theorem directPointAnswerReadout_eq_axis_zeroCoord_of_win (D : DirectLdParams)
    (r : Fin D.k) (line : AxisParallelLine D.toLDTParameters)
    (a b : DirectLdAnswer D)
    (hwin : directLdWinPredicate D (directPointQuestionOf D line.base)
      (directAxisQuestionOf D line) a b = true) :
    letI := D.toLDTFieldModel
    directPointAnswerReadout D r a =
      directAxisAnswerReadout D r line b zeroCoord := by
  letI := D.toLDTFieldModel
  cases a with
  | pointVals c =>
      cases b with
      | alinePolys f =>
          refine (axis_readout_of_condition D r line f c ?_).symm
          simpa [directLdWinPredicate, directAxisQuestionOf, directPointQuestionOf,
            directLdPointQuestionOf, validDirectLdAnswer] using hwin
      | pointVals _ =>
          simp [directLdWinPredicate, directAxisQuestionOf, directPointQuestionOf,
            directLdPointQuestionOf, validDirectLdAnswer] at hwin
      | dlinePolys _ =>
          simp [directLdWinPredicate, directAxisQuestionOf, directPointQuestionOf,
            directLdPointQuestionOf, validDirectLdAnswer] at hwin
  | alinePolys _ =>
      simp [directLdWinPredicate, directAxisQuestionOf, directPointQuestionOf,
        directLdPointQuestionOf, validDirectLdAnswer] at hwin
  | dlinePolys _ =>
      simp [directLdWinPredicate, directAxisQuestionOf, directPointQuestionOf,
        directLdPointQuestionOf, validDirectLdAnswer] at hwin

/-- On the diagonal-line branch with the line on the left, an accepted direct
answer pair has the rebased line answer, evaluated at the mature base point,
equal to the point readout. -/
theorem directDiagonalAnswerReadout_zeroCoord_eq_of_win (D : DirectLdParams)
    (r : Fin D.k) (line : DiagonalLine D.toLDTParameters)
    (a b : DirectLdAnswer D)
    (hwin : directLdWinPredicate D (directDiagonalQuestionOf D line)
      (directPointQuestionOf D line.base) a b = true) :
    letI := D.toLDTFieldModel
    directDiagonalAnswerReadout D r line a zeroCoord =
      directPointAnswerReadout D r b := by
  letI := D.toLDTFieldModel
  cases a with
  | dlinePolys f =>
      cases b with
      | pointVals c =>
          refine diagonal_readout_of_condition D r line f c ?_
          simpa [directLdWinPredicate, directDiagonalQuestionOf,
            directPointQuestionOf, directLdPointQuestionOf,
            validDirectLdAnswer] using hwin
      | alinePolys _ =>
          simp [directLdWinPredicate, directDiagonalQuestionOf, directPointQuestionOf,
            directLdPointQuestionOf, validDirectLdAnswer] at hwin
      | dlinePolys _ =>
          simp [directLdWinPredicate, directDiagonalQuestionOf, directPointQuestionOf,
            directLdPointQuestionOf, validDirectLdAnswer] at hwin
  | pointVals _ =>
      simp [directLdWinPredicate, directDiagonalQuestionOf, directPointQuestionOf,
        directLdPointQuestionOf, validDirectLdAnswer] at hwin
  | alinePolys _ =>
      simp [directLdWinPredicate, directDiagonalQuestionOf, directPointQuestionOf,
        directLdPointQuestionOf, validDirectLdAnswer] at hwin

/-- On the diagonal-line branch with the point on the left, an accepted
direct answer pair has the point readout equal to the rebased line answer
evaluated at the mature base point. -/
theorem directPointAnswerReadout_eq_diagonal_zeroCoord_of_win (D : DirectLdParams)
    (r : Fin D.k) (line : DiagonalLine D.toLDTParameters)
    (a b : DirectLdAnswer D)
    (hwin : directLdWinPredicate D (directPointQuestionOf D line.base)
      (directDiagonalQuestionOf D line) a b = true) :
    letI := D.toLDTFieldModel
    directPointAnswerReadout D r a =
      directDiagonalAnswerReadout D r line b zeroCoord := by
  letI := D.toLDTFieldModel
  cases a with
  | pointVals c =>
      cases b with
      | dlinePolys f =>
          refine (diagonal_readout_of_condition D r line f c ?_).symm
          simpa [directLdWinPredicate, directDiagonalQuestionOf,
            directPointQuestionOf, directLdPointQuestionOf,
            validDirectLdAnswer] using hwin
      | pointVals _ =>
          simp [directLdWinPredicate, directDiagonalQuestionOf, directPointQuestionOf,
            directLdPointQuestionOf, validDirectLdAnswer] at hwin
      | alinePolys _ =>
          simp [directLdWinPredicate, directDiagonalQuestionOf, directPointQuestionOf,
            directLdPointQuestionOf, validDirectLdAnswer] at hwin
  | alinePolys _ =>
      simp [directLdWinPredicate, directDiagonalQuestionOf, directPointQuestionOf,
        directLdPointQuestionOf, validDirectLdAnswer] at hwin
  | dlinePolys _ =>
      simp [directLdWinPredicate, directDiagonalQuestionOf, directPointQuestionOf,
        directLdPointQuestionOf, validDirectLdAnswer] at hwin

/-- A uniform average over a finite type is the normalized sum.
Formalization-only support for the branch bookkeeping. -/
theorem avgOver_uniform_eq_inv_card_mul_sum {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α] (f : α → ℝ) :
    avgOver (uniformDistribution α) f = (Fintype.card α : ℝ)⁻¹ * ∑ a, f a := by
  unfold avgOver uniformDistribution Distribution.uniformOnFinset
  simp only [Finset.mem_univ, if_true, Finset.card_univ, one_div, Finset.mul_sum]

/-! ## Direct samples as products -/

/-- A direct sample as its point-index pair together with its direction.
Formalization-only reindexing of the direct sample space. -/
def directLdSpaceSplitEquiv (D : DirectLdParams) :
    DirectLdSpace D ≃
      ((Fin D.m → DirectScalarQ D) × Fin D.m) × (Fin D.m → DirectScalarQ D) where
  toFun s := ((s.point, s.index), s.direction)
  invFun x := ⟨x.1.1, x.1.2, x.2⟩
  left_inv s := by cases s; rfl
  right_inv x := rfl

/-- A direct sample as its index together with its point-direction pair.
Formalization-only reindexing of the direct sample space. -/
def directLdSpaceIndexSplitEquiv (D : DirectLdParams) :
    DirectLdSpace D ≃
      Fin D.m × ((Fin D.m → DirectScalarQ D) × (Fin D.m → DirectScalarQ D)) where
  toFun s := (s.index, s.point, s.direction)
  invFun x := ⟨x.2.1, x.1, x.2.2⟩
  left_inv s := by cases s; rfl
  right_inv x := rfl

/-! ## The point-agreement and axis-line branches -/

section PointAxisBranches

variable (D : DirectLdParams) (S : Strategy (directLdGame D))
  (hS : S.IsProjective) (r : Fin D.k)

/-- Point-agreement defect at a mature point is at most the rejected direct
mass at the direct point question. -/
private theorem point_defect_le (u : Point D.toLDTParameters) :
    letI := D.toLDTFieldModel
    qBipartiteConsDefect (directCoordinateProjStrat D S hS r).state
        ((directCoordinateProjStrat D S hS r).pointMeasurementA u).toSubMeas
        ((directCoordinateProjStrat D S hS r).pointMeasurementB u).toSubMeas ≤
      directRejectedMass D S
        (directLdPointQuestionOf D (ldtPointToDirect D u))
        (directLdPointQuestionOf D (ldtPointToDirect D u)) := by
  letI := D.toLDTFieldModel
  exact qBipartiteConsDefect_le_directRejectedMass D S hS
    (directPointQuestionOf D u) (directPointQuestionOf D u)
    (directPointAnswerReadout D r) (directPointAnswerReadout D r)
    (fun a b hab =>
      directPointAnswerReadout_eq_of_win D r (ldtPointToDirect D u) a b hab)

/-- The point-agreement failure of the coordinate strategy is at most the
point-point branch rejection of the direct game. -/
theorem directCoordinate_point_agreement_le :
    letI := D.toLDTFieldModel
    (directCoordinateProjStrat D S hS r).pointAgreementFailureProbability ≤
      directLdBranchRejectionProbability D S (.point, .point) := by
  letI := D.toLDTFieldModel
  unfold ProjStrat.pointAgreementFailureProbability bipartiteConsError
  refine le_trans (avgOver_mono _ _ _ fun u => point_defect_le D S hS r u)
    (le_of_eq ?_)
  rw [directLdBranchRejectionProbability_eq_avgOver]
  let f : (Fin D.m → DirectScalarQ D) → ℝ := fun p =>
    directRejectedMass D S (directLdPointQuestionOf D p) (directLdPointQuestionOf D p)
  calc
    avgOver (uniformDistribution (Point D.toLDTParameters))
        (fun u => f (ldtPointToDirect D u)) =
        avgOver (uniformDistribution (Fin D.m → DirectScalarQ D)) f :=
      (avgOver_uniform_equiv (directPointEquiv D) f).symm
    _ = avgOver (uniformDistribution ((Fin D.m → DirectScalarQ D) × Fin D.m))
        (fun pi => f pi.1) :=
      (avgOver_uniform_fst f).symm
    _ = avgOver (uniformDistribution (DirectLdSpace D))
        (fun sample => f ((directLdSpaceSplitEquiv D sample).1).1) :=
      (avgOver_uniform_equiv_fst (directLdSpaceSplitEquiv D) (fun pi => f pi.1)).symm
    _ = _ := by
      apply avgOver_congr
      intro sample
      rfl

/-- Axis-line defect with the line on the left is at most the rejected direct
mass at the canonical direct questions of the reindexed sample. -/
private theorem axis_line_point_defect_le
    (s : AxisParallelTestSample D.toLDTParameters) :
    letI := D.toLDTFieldModel
    qBipartiteConsDefect (directCoordinateProjStrat D S hS r).state
        ((directCoordinateProjStrat D S hS r).axisParallelLineAnswerFamilyA s)
        ((directCoordinateProjStrat D S hS r).axisParallelPointAnswerFamilyB s) ≤
      directRejectedMass D S
        (.aline, ⟨lineRepMap (coordinateDirection (Fin.rev s.2))
          (ldtPointToDirect D s.1), Fin.rev s.2, 0⟩)
        (directLdPointQuestionOf D (ldtPointToDirect D s.1)) := by
  letI := D.toLDTFieldModel
  have h := qBipartiteConsDefect_le_directRejectedMass D S hS
    (directAxisQuestionOf D ⟨s.1, s.2⟩) (directPointQuestionOf D s.1)
    (fun a => directAxisAnswerReadout D r ⟨s.1, s.2⟩ a zeroCoord)
    (directPointAnswerReadout D r)
    (fun a b hab =>
      directAxisAnswerReadout_zeroCoord_eq_of_win D r ⟨s.1, s.2⟩ a b hab)
  change qBipartiteConsDefect (strategyQuantumState S)
      (postprocess
        (ProjMeas.postprocess
          (matrixMeasurementToLDTProjMeas
            (S.A (directAxisQuestionOf D ⟨s.1, s.2⟩))
            (hS.1 (directAxisQuestionOf D ⟨s.1, s.2⟩)))
          (directAxisAnswerReadout D r ⟨s.1, s.2⟩)).toSubMeas
        (fun g => g zeroCoord))
      (ProjMeas.postprocess
        (matrixMeasurementToLDTProjMeas
          (S.B (directPointQuestionOf D s.1))
          (hS.2 (directPointQuestionOf D s.1)))
        (directPointAnswerReadout D r)).toSubMeas ≤ _
  simp only [ProjMeas.postprocess_toSubMeas, SubMeas.postprocess_comp] at h ⊢
  exact h

/-- Axis-line defect with the point on the left is at most the rejected direct
mass at the canonical direct questions of the reindexed sample. -/
private theorem axis_point_line_defect_le
    (s : AxisParallelTestSample D.toLDTParameters) :
    letI := D.toLDTFieldModel
    qBipartiteConsDefect (directCoordinateProjStrat D S hS r).state
        ((directCoordinateProjStrat D S hS r).axisParallelPointAnswerFamilyA s)
        ((directCoordinateProjStrat D S hS r).axisParallelLineAnswerFamilyB s) ≤
      directRejectedMass D S
        (directLdPointQuestionOf D (ldtPointToDirect D s.1))
        (.aline, ⟨lineRepMap (coordinateDirection (Fin.rev s.2))
          (ldtPointToDirect D s.1), Fin.rev s.2, 0⟩) := by
  letI := D.toLDTFieldModel
  have h := qBipartiteConsDefect_le_directRejectedMass D S hS
    (directPointQuestionOf D s.1) (directAxisQuestionOf D ⟨s.1, s.2⟩)
    (directPointAnswerReadout D r)
    (fun b => directAxisAnswerReadout D r ⟨s.1, s.2⟩ b zeroCoord)
    (fun a b hab =>
      directPointAnswerReadout_eq_axis_zeroCoord_of_win D r ⟨s.1, s.2⟩ a b hab)
  change qBipartiteConsDefect (strategyQuantumState S)
      (ProjMeas.postprocess
        (matrixMeasurementToLDTProjMeas
          (S.A (directPointQuestionOf D s.1))
          (hS.1 (directPointQuestionOf D s.1)))
        (directPointAnswerReadout D r)).toSubMeas
      (postprocess
        (ProjMeas.postprocess
          (matrixMeasurementToLDTProjMeas
            (S.B (directAxisQuestionOf D ⟨s.1, s.2⟩))
            (hS.2 (directAxisQuestionOf D ⟨s.1, s.2⟩)))
          (directAxisAnswerReadout D r ⟨s.1, s.2⟩)).toSubMeas
        (fun g => g zeroCoord)) ≤ _
  simp only [ProjMeas.postprocess_toSubMeas, SubMeas.postprocess_comp] at h ⊢
  exact h

/-- Reindex a uniform average over mature axis samples to the direct sample
space; the averaged function depends only on the decoded point and the
reversed coordinate index. -/
private theorem avgOver_axis_sample_eq
    (f : (Fin D.m → DirectScalarQ D) × Fin D.m → ℝ) :
    avgOver (uniformDistribution (AxisParallelTestSample D.toLDTParameters))
        (fun s => f (ldtPointToDirect D s.1, Fin.rev s.2)) =
      avgOver (uniformDistribution (DirectLdSpace D))
        (fun sample => f (sample.point, sample.index)) := by
  calc
    avgOver (uniformDistribution (AxisParallelTestSample D.toLDTParameters))
        (fun s => f (ldtPointToDirect D s.1, Fin.rev s.2)) =
        avgOver (uniformDistribution ((Fin D.m → DirectScalarQ D) × Fin D.m)) f := by
      rw [avgOver_uniform_equiv ((directPointEquiv D).prodCongr Fin.revPerm) f]
      apply avgOver_congr
      intro s
      rfl
    _ = avgOver (uniformDistribution (DirectLdSpace D))
        (fun sample => f (directLdSpaceSplitEquiv D sample).1) :=
      (avgOver_uniform_equiv_fst (directLdSpaceSplitEquiv D) f).symm
    _ = _ := by
      apply avgOver_congr
      intro sample
      rfl

/-- The axis-line failure with the line on the left is at most the
axis-line/point branch rejection of the direct game. -/
theorem directCoordinate_axis_line_point_le :
    letI := D.toLDTFieldModel
    (directCoordinateProjStrat D S hS r).axisParallelLineLeftPointRightFailureProbability ≤
      directLdBranchRejectionProbability D S (.aline, .point) := by
  letI := D.toLDTFieldModel
  unfold ProjStrat.axisParallelLineLeftPointRightFailureProbability bipartiteConsError
  refine le_trans
    (avgOver_mono _ _ _ fun s => axis_line_point_defect_le D S hS r s) (le_of_eq ?_)
  rw [directLdBranchRejectionProbability_eq_avgOver]
  exact avgOver_axis_sample_eq D (fun pi =>
    directRejectedMass D S
      (.aline, ⟨lineRepMap (coordinateDirection pi.2) pi.1, pi.2, 0⟩)
      (directLdPointQuestionOf D pi.1))

/-- The axis-line failure with the point on the left is at most the
point/axis-line branch rejection of the direct game. -/
theorem directCoordinate_axis_point_line_le :
    letI := D.toLDTFieldModel
    (directCoordinateProjStrat D S hS r).axisParallelPointLeftLineRightFailureProbability ≤
      directLdBranchRejectionProbability D S (.point, .aline) := by
  letI := D.toLDTFieldModel
  unfold ProjStrat.axisParallelPointLeftLineRightFailureProbability bipartiteConsError
  refine le_trans
    (avgOver_mono _ _ _ fun s => axis_point_line_defect_le D S hS r s) (le_of_eq ?_)
  rw [directLdBranchRejectionProbability_eq_avgOver]
  exact avgOver_axis_sample_eq D (fun pi =>
    directRejectedMass D S
      (directLdPointQuestionOf D pi.1)
      (.aline, ⟨lineRepMap (coordinateDirection pi.2) pi.1, pi.2, 0⟩))

end PointAxisBranches

end

end MIPStarRE.QPBT
