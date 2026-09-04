import MIPStarRE.QPBT.Observables.WinImplications.Commuting

/-!
# Magic Square winning implications

This module proves the exact induced Magic Square value and variable
consistency bounds on anticommuting Pauli tuples.

## References

The proof infrastructure in this module supports `lem:qld-win-implications`
from `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:192-267`
and `blueprint/src/chapter/ch14_qpbt_observables.tex:505-660`.
-/

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace WinImplications

local instance pauliEdgeNonemptyMagicSquare : Nonempty PauliEdge := pauliEdge_nonempty

/-- Select the Magic Square variable used by one Pauli basis. -/
def selectedMsVar : PauliKind → Fin 9
  | .X => 0
  | .Z => 4

/-- The verifier edge comparing a point trace with its Magic Square variable. -/
def pointMsImplicationEdge : PauliKind → PauliEdge
  | .X => ⟨(.point .X, .ms (.var 0)), by simp [pauliEdges]⟩
  | .Z => ⟨(.point .Z, .ms (.var 4)), by simp [pauliEdges]⟩

/-- Winning the anticommuting point/variable branch forces equality of trace bits. -/
theorem pointMsLabels_eq_of_win (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) (A B : PauliAnswer P)
    (hanti : IsAnticommuting (pauliSharedSplit P z).1)
    (hwin : pauliWinPredicate P
      ((.point W), pauliCL P (.point W) z)
      ((.ms (.var (selectedMsVar W))),
        pauliCL P (.ms (.var (selectedMsVar W))) z) A B = true) :
    pointTraceLabel P W (pauliSharedSplit P z).1 A =
      ProjectiveSetting.pairWAnswerOrZero B := by
  cases A <;> cases B <;>
    simp only [pauliWinPredicate, validPauliAnswer, Bool.and_true,
      Bool.and_self, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
      reduceCtorEq, decide_eq_true_eq] at hwin
  rename_i a bit
  simp only [pointTraceLabel, ProjectiveSetting.pointAnswerOrZero,
    ProjectiveSetting.pairWAnswerOrZero]
  have hgamma : pauliPairGamma P
      (pauliCL P (.ms (.var (selectedMsVar W))) z) ≠ 0 := by
    change gammaValue P (pauliXBlock z) (pauliZBlock z)
      (pauliRXBlock z) (pauliRZBlock z) ≠ 0 at hanti
    rw [pauliCL_shared_eq P (.ms (.var (selectedMsVar W))) rfl]
    change gammaValue P (pauliXBlock z) (pauliZBlock z)
      (pauliRXBlock z) (pauliRZBlock z) ≠ 0
    exact hanti
  rw [pauliCL_shared_eq P (.ms (.var (selectedMsVar W))) rfl] at hgamma
  rw [pauliCL_shared_eq P (.ms (.var (selectedMsVar W))) rfl] at hwin
  cases W with
  | X =>
      simp only [pauliPointVariableCondition] at hwin
      rcases hwin with hzero | hrest
      · exact (hgamma hzero).elim
      · rcases hrest with hX | hZ
        · simpa [selectedTupleScalar, pauliSharedSplit, pauliRXBlock,
            ProjectiveSetting.contentOfTuple] using hX.2.2
        · simp at hZ
  | Z =>
      simp only [pauliPointVariableCondition] at hwin
      rcases hwin with hzero | hrest
      · exact (hgamma hzero).elim
      · rcases hrest with hX | hZ
        · simp at hX
        · simpa [selectedTupleScalar, pauliSharedSplit, pauliRZBlock,
            ProjectiveSetting.contentOfTuple] using hZ.2.2

/-- Anticommuting point-trace/variable mismatch is contained in rejection. -/
theorem pointMsMismatch_le_rejection {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind) (z : PauliSpace P)
    (hanti : IsAnticommuting (pauliSharedSplit P z).1) :
    outcomeEventWeight S.toStrategy
        ((.point W), pauliCL P (.point W) z)
        ((.ms (.var (selectedMsVar W))),
          pauliCL P (.ms (.var (selectedMsVar W))) z)
        (fun A B => pointTraceLabel P W (pauliSharedSplit P z).1 A ≠
          ProjectiveSetting.pairWAnswerOrZero B) ≤
      pauliRejectionAt S.toStrategy (pointMsImplicationEdge W) z := by
  cases W <;>
    apply outcome_event_weight_mono <;>
    intro A B hne <;>
    change pauliWinPredicate P _ _ A B = false <;>
    apply Bool.eq_false_iff.mpr <;>
    intro htrue <;>
    exact hne (pointMsLabels_eq_of_win P _ z A B hanti htrue)

/-- Point-trace/variable consistency is the mismatch probability of source answers. -/
theorem msConsConsistency_eq_mismatch {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind) :
    consistencyDefect (anticommTupleDist P)
        (fun ω a => heteroKron
          ((S.pointTraceMeas .alice W (selectedTuplePoint W ω)
            (selectedTupleScalar W ω)).effect a) 1)
        (fun ω a => heteroKron 1
          ((S.msVarBitMeas .bob (selectedMsVar W) ω).effect a))
        S.toStrategy.ψ =
      avgOver (anticommTupleDist P) (fun ω =>
        outcomeEventWeight S.toStrategy
          (ProjectiveSetting.pointQuestion P W (selectedTuplePoint W ω))
          (ProjectiveSetting.msQuestion P (.var (selectedMsVar W))
            ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
          (fun A B => pointTraceLabel P W ω A ≠
            ProjectiveSetting.pairWAnswerOrZero B)) := by
  let qA : PauliTuple P → PauliQuestion P := fun ω =>
    ProjectiveSetting.pointQuestion P W (selectedTuplePoint W ω)
  let qB : PauliTuple P → PauliQuestion P := fun ω =>
    ProjectiveSetting.msQuestion P (.var (selectedMsVar W))
      ω.1 ω.2.1 ω.2.2.1 ω.2.2.2
  let fA : PauliTuple P → PauliAnswer P → ZMod 2 := fun ω A =>
    pointTraceLabel P W ω A
  let fB : PauliTuple P → PauliAnswer P → ZMod 2 := fun _ =>
    ProjectiveSetting.pairWAnswerOrZero
  have h := consistencyDefect_postprocess_eq_mismatch
    (anticommTupleDist P) S.toStrategy qA qB fA fB
  have hA : ∀ ω c,
      heteroKron
          ((S.pointTraceMeas .alice W (selectedTuplePoint W ω)
            (selectedTupleScalar W ω)).effect c)
          (1 : Op S.toStrategy.ιB) =
        heteroKron (((S.toStrategy.A (qA ω)).postprocess (fA ω)).effect c)
          (1 : Op S.toStrategy.ιB) := by
    intro ω c
    congr 1
    unfold ProjectiveSetting.pointTraceMeas ProjectiveSetting.pointMeas fA
    rw [measurement_postprocess_comp_effect]
    rfl
  have hB : ∀ ω c,
      heteroKron (1 : Op S.toStrategy.ιA)
          ((S.msVarBitMeas .bob (selectedMsVar W) ω).effect c) =
        heteroKron (1 : Op S.toStrategy.ιA)
          (((S.toStrategy.B (qB ω)).postprocess (fB ω)).effect c) := by
    intro ω c
    congr 1
    unfold ProjectiveSetting.msVarBitMeas ProjectiveSetting.msMeas fB qB
    rw [measurement_postprocess_comp_effect]
    have hmap : (msBitOrZero ∘
        ProjectiveSetting.msAnswerOrZero (P := P) (.var (selectedMsVar W))) =
        ProjectiveSetting.pairWAnswerOrZero (P := P) := by
      funext B
      cases B <;> rfl
    rw [hmap]
    rfl
  calc
    _ = consistencyDefect (anticommTupleDist P)
        (fun ω c => heteroKron
          (((S.toStrategy.A (qA ω)).postprocess (fA ω)).effect c) 1)
        (fun ω c => heteroKron 1
          (((S.toStrategy.B (qB ω)).postprocess (fB ω)).effect c))
        S.toStrategy.ψ := consistencyDefect_congr _ _ _ _ _ _ hA hB
    _ = avgOver (anticommTupleDist P) (fun ω =>
        outcomeEventWeight S.toStrategy (qA ω) (qB ω)
          (fun A B => fA ω A ≠ fB ω B)) := h
    _ = _ := by rfl

/-- On anticommuting tuples, the X and Z point traces agree respectively with
Magic Square variables 1 and 5. This is item 7 of
`lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:250-263`, blueprint
`ch14_qpbt_observables.tex:626-660`. -/
theorem win_ms_cons_proof :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : PauliKind,
      consistencyDefect (anticommTupleDist P)
        (fun ω a => heteroKron
          ((S.pointTraceMeas .alice W
            (match W with | .X => ω.1 | .Z => ω.2.1)
            (match W with | .X => ω.2.2.1 | .Z => ω.2.2.2)).effect a) 1)
        (fun ω a => heteroKron 1
          ((S.msVarBitMeas .bob (match W with | .X => 0 | .Z => 4) ω).effect a))
        S.toStrategy.ψ ≤ C * ε := by
  refine ⟨16 * (Fintype.card PauliEdge : ℝ), ?_, ?_⟩
  · have hcard : (1 : ℝ) ≤ Fintype.card PauliEdge := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card PauliEdge)
    linarith
  intro P ε S _ W
  change consistencyDefect (anticommTupleDist P)
      (fun ω a => heteroKron
        ((S.pointTraceMeas .alice W (selectedTuplePoint W ω)
          (selectedTupleScalar W ω)).effect a) 1)
      (fun ω a => heteroKron 1
        ((S.msVarBitMeas .bob (selectedMsVar W) ω).effect a))
      S.toStrategy.ψ ≤ _
  rw [msConsConsistency_eq_mismatch]
  calc
    _ ≤ 16 * avgOver (uniformDistribution (PauliTuple P)) (fun ω =>
        if IsAnticommuting ω then
          outcomeEventWeight S.toStrategy
            (ProjectiveSetting.pointQuestion P W (selectedTuplePoint W ω))
            (ProjectiveSetting.msQuestion P (.var (selectedMsVar W))
              ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
            (fun A B => pointTraceLabel P W ω A ≠
              ProjectiveSetting.pairWAnswerOrZero B)
        else 0) := by
      apply avgOver_anticomm_le_sixteen_mul_gated
      intro ω
      exact outcome_event_weight_nonneg S.toStrategy _ _ _
    _ ≤ 16 * avgOver (uniformDistribution (PauliSpace P))
        (pauliRejectionAt S.toStrategy (pointMsImplicationEdge W)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [← avgOver_pauliTuple_uniform]
      apply avgOver_mono
      intro z
      by_cases hanti : IsAnticommuting (pauliSharedSplit P z).1
      · simp only [if_pos hanti]
        have hs := pointMsMismatch_le_rejection S W z hanti
        rw [pauliCL_point_eq,
          pauliCL_shared_eq P (.ms (.var (selectedMsVar W))) rfl] at hs
        rw [pauliToLd_point_eq_selected] at hs
        simpa [pauliSharedSplit, selectedTuplePoint, selectedMsVar,
          ProjectiveSetting.pointQuestion, ProjectiveSetting.msQuestion]
          using hs
      · simp only [if_neg hanti]
        exact pauliRejectionAt_nonneg S.toStrategy _ z
    _ ≤ 16 * (Fintype.card PauliEdge : ℝ) * ε := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (fixedEdgeRejection_le_error S _) (by norm_num)

/-- Relabeling both Pauli answer measurements gives the induced Magic Square event mass. -/
theorem msRejection_eq_source {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (ω : PauliTuple P) (x y : MsType) :
    outcomeEventWeight (S.msStrategyAt ω) x y
        (fun a b => msWinPredicate x y a b = false) =
      outcomeEventWeight S.toStrategy
        (ProjectiveSetting.msQuestion P x ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
        (ProjectiveSetting.msQuestion P y ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
        (fun A B => msWinPredicate x y
          (ProjectiveSetting.msAnswerOrZero x A)
          (ProjectiveSetting.msAnswerOrZero y B) = false) := by
  let qx := ProjectiveSetting.msQuestion P x
    ω.1 ω.2.1 ω.2.2.1 ω.2.2.2
  let qy := ProjectiveSetting.msQuestion P y
    ω.1 ω.2.1 ω.2.2.1 ω.2.2.2
  let fA : (pauliBasisTest P).AnswerA → MsAnswer :=
    ProjectiveSetting.msAnswerOrZero (P := P) x
  let fB : (pauliBasisTest P).AnswerB → MsAnswer :=
    ProjectiveSetting.msAnswerOrZero (P := P) y
  have hmass (a b : MsAnswer) :
      outcomeWeight (S.msStrategyAt ω) x y a b =
        ∑ A ∈ Finset.univ.filter (fun A => fA A = a),
          ∑ B ∈ Finset.univ.filter (fun B => fB B = b),
            outcomeWeight S.toStrategy qx qy A B := by
    have hop :
        heteroKron
            (∑ A ∈ Finset.univ.filter (fun A => fA A = a),
              (S.toStrategy.A qx).effect A)
            (∑ B ∈ Finset.univ.filter (fun B => fB B = b),
              (S.toStrategy.B qy).effect B) =
          ∑ A ∈ Finset.univ.filter (fun A => fA A = a),
            ∑ B ∈ Finset.univ.filter (fun B => fB B = b),
              heteroKron ((S.toStrategy.A qx).effect A)
                ((S.toStrategy.B qy).effect B) := by
      ext i j
      simp only [Matrix.sum_apply, heteroKron, Matrix.kronecker,
        Matrix.kroneckerMap_apply]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro A _
      rw [Finset.mul_sum]
    change DistanceCalculus.stateQForm S.toStrategy.ψ
        (heteroKron
          (((S.toStrategy.A qx).postprocess fA).effect a)
          (((S.toStrategy.B qy).postprocess fB).effect b)) = _
    simp only [MIPStarRE.Quantum.Measurement.postprocess_effect]
    rw [hop]
    simp [DistanceCalculus.stateQForm, applyOperatorToState, outcomeWeight]
  unfold outcomeEventWeight
  simp_rw [hmass]
  symm
  calc
    (∑ A, ∑ B, if msWinPredicate x y (fA A) (fB B) = false then
        outcomeWeight S.toStrategy qx qy A B else 0) =
        ∑ a : MsAnswer, ∑ A ∈ Finset.univ.filter (fun A => fA A = a),
          ∑ B, if msWinPredicate x y (fA A) (fB B) = false then
            outcomeWeight S.toStrategy qx qy A B else 0 := by
      exact (Finset.sum_fiberwise Finset.univ fA (fun A =>
        ∑ B, if msWinPredicate x y (fA A) (fB B) = false then
          outcomeWeight S.toStrategy qx qy A B else 0)).symm
    _ = ∑ a : MsAnswer, ∑ A ∈ Finset.univ.filter (fun A => fA A = a),
        ∑ B, if msWinPredicate x y a (fB B) = false then
          outcomeWeight S.toStrategy qx qy A B else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro A hA
      rw [(Finset.mem_filter.mp hA).2]
    _ = ∑ a : MsAnswer, ∑ A ∈ Finset.univ.filter (fun A => fA A = a),
        ∑ b : MsAnswer, ∑ B ∈ Finset.univ.filter (fun B => fB B = b),
          if msWinPredicate x y a (fB B) = false then
            outcomeWeight S.toStrategy qx qy A B else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro A _
      exact (Finset.sum_fiberwise Finset.univ fB (fun B =>
        if msWinPredicate x y a (fB B) = false then
          outcomeWeight S.toStrategy qx qy A B else 0)).symm
    _ = ∑ a : MsAnswer, ∑ A ∈ Finset.univ.filter (fun A => fA A = a),
        ∑ b : MsAnswer, ∑ B ∈ Finset.univ.filter (fun B => fB B = b),
          if msWinPredicate x y a b = false then
            outcomeWeight S.toStrategy qx qy A B else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro B hB
      rw [(Finset.mem_filter.mp hB).2]
    _ = ∑ a : MsAnswer, ∑ b : MsAnswer,
        ∑ A ∈ Finset.univ.filter (fun A => fA A = a),
          ∑ B ∈ Finset.univ.filter (fun B => fB B = b),
            if msWinPredicate x y a b = false then
              outcomeWeight S.toStrategy qx qy A B else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ a : MsAnswer, ∑ b : MsAnswer,
        if msWinPredicate x y a b = false then
          ∑ A ∈ Finset.univ.filter (fun A => fA A = a),
            ∑ B ∈ Finset.univ.filter (fun B => fB B = b),
              outcomeWeight S.toStrategy qx qy A B
        else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      by_cases hab : msWinPredicate x y a b = false <;> simp [hab]

/-- Lift a supported Magic Square incidence to the corresponding Pauli verifier edge. -/
def msImplicationEdge (xy : MsType × MsType)
    (hxy : xy ∈ (graphDistribution msEdges msEdges_nonempty).support) : PauliEdge :=
  ⟨((.ms xy.1), (.ms xy.2)), by
    have hedge : Sym2.mk xy.1 xy.2 ∈ msEdges :=
      (Finset.mem_filter.mp hxy).2
    simp only [pauliEdges, Finset.union_assoc, Fin.zero_eta, Fin.isValue,
      Fin.reduceFinMk, Finset.union_insert, Finset.union_singleton,
      Finset.insert_union, Finset.mem_insert, Sym2.eq, Sym2.rel_iff',
      Prod.mk.injEq, reduceCtorEq, PauliType.ms.injEq, false_and,
      Prod.swap_prod_mk, and_false, or_self, Finset.mem_union,
      Finset.mem_image, Finset.mem_univ, true_and, and_self, exists_const,
      Finset.mem_filter, Prod.exists, false_or]
    exact Or.inr ⟨xy.1, xy.2, hedge, Or.inl ⟨rfl, rfl⟩⟩⟩

/-- A relabeled Magic Square rejection on an anticommuting tuple is a Pauli rejection. -/
theorem msRejection_implies_pauliRejection
    (P : AdmissibleParams) (z : PauliSpace P) (xy : MsType × MsType)
    (hxy : xy ∈ (graphDistribution msEdges msEdges_nonempty).support)
    (hanti : IsAnticommuting (pauliSharedSplit P z).1)
    (A B : PauliAnswer P)
    (hreject : msWinPredicate xy.1 xy.2
      (ProjectiveSetting.msAnswerOrZero xy.1 A)
      (ProjectiveSetting.msAnswerOrZero xy.2 B) = false) :
    pauliWinPredicate P
      ((.ms xy.1), pauliCL P (.ms xy.1) z)
      ((.ms xy.2), pauliCL P (.ms xy.2) z) A B = false := by
  have hedge : Sym2.mk xy.1 xy.2 ∈ msEdges :=
    (Finset.mem_filter.mp hxy).2
  rcases Finset.mem_image.mp hedge with ⟨ik, _, heq⟩
  have hor :
      ((.constraint ik.1, .var (msConstraintVars ik.1 ik.2)) :
          MsType × MsType) = xy ∨
        ((.constraint ik.1, .var (msConstraintVars ik.1 ik.2)) :
          MsType × MsType) = xy.swap :=
    (Sym2.mk_eq_mk_iff (α := MsType)).mp heq
  have hgamma (t : MsType) : pauliPairGamma P (pauliCL P (.ms t) z) ≠ 0 := by
    change gammaValue P (pauliXBlock z) (pauliZBlock z)
      (pauliRXBlock z) (pauliRZBlock z) ≠ 0 at hanti
    rw [pauliCL_shared_eq P (.ms t) rfl]
    change gammaValue P (pauliXBlock z) (pauliZBlock z)
      (pauliRXBlock z) (pauliRZBlock z) ≠ 0
    exact hanti
  rcases hor with hforward | hreverse
  · subst xy
    cases A <;> cases B <;>
      simp_all [pauliWinPredicate, validPauliAnswer,
        ProjectiveSetting.msAnswerOrZero]
  · have hswap := congrArg Prod.swap hreverse
    have hxy : xy =
        ((.var (msConstraintVars ik.1 ik.2), .constraint ik.1) :
          MsType × MsType) := by
      simpa using hswap.symm
    subst xy
    clear hreverse hswap hedge heq
    cases A <;> cases B <;>
      simp_all [pauliWinPredicate, validPauliAnswer,
        ProjectiveSetting.msAnswerOrZero]

/-- At a supported Magic Square incidence, the induced rejection is contained in
the rejection at the corresponding fixed Pauli edge. -/
theorem msRejection_le_pauliRejection {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (z : PauliSpace P) (xy : MsType × MsType)
    (hxy : xy ∈ (graphDistribution msEdges msEdges_nonempty).support)
    (hanti : IsAnticommuting (pauliSharedSplit P z).1) :
    outcomeEventWeight S.toStrategy
        ((.ms xy.1), pauliCL P (.ms xy.1) z)
        ((.ms xy.2), pauliCL P (.ms xy.2) z)
        (fun A B => msWinPredicate xy.1 xy.2
          (ProjectiveSetting.msAnswerOrZero xy.1 A)
          (ProjectiveSetting.msAnswerOrZero xy.2 B) = false) ≤
      pauliRejectionAt S.toStrategy (msImplicationEdge xy hxy) z := by
  apply outcome_event_weight_mono
  intro A B hreject
  exact msRejection_implies_pauliRejection P z xy hxy hanti A B hreject

/-- Rejection mass of the induced Magic Square strategy at one tuple and question pair. -/
noncomputable def inducedMsRejection {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (ω : PauliTuple P) (xy : MsType × MsType) : ℝ :=
  outcomeEventWeight (S.msStrategyAt ω) xy.1 xy.2
    (fun a b => msWinPredicate xy.1 xy.2 a b = false)

/-- The gated rejection average at a supported Magic Square incidence is bounded by
the rejection average of its fixed Pauli edge. -/
theorem gatedMsRejection_le_fixedEdge {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (xy : MsType × MsType)
    (hxy : xy ∈ (graphDistribution msEdges msEdges_nonempty).support) :
    avgOver (uniformDistribution (PauliTuple P)) (fun ω =>
        if IsAnticommuting ω then inducedMsRejection S ω xy else 0) ≤
      (Fintype.card PauliEdge : ℝ) * ε := by
  calc
    _ = avgOver (uniformDistribution (PauliSpace P)) (fun z =>
        if IsAnticommuting (pauliSharedSplit P z).1 then
          inducedMsRejection S (pauliSharedSplit P z).1 xy
        else 0) := by
      exact (avgOver_pauliTuple_uniform P (fun ω =>
        if IsAnticommuting ω then inducedMsRejection S ω xy else 0)).symm
    _ ≤ avgOver (uniformDistribution (PauliSpace P))
        (pauliRejectionAt S.toStrategy (msImplicationEdge xy hxy)) := by
      apply avgOver_mono
      intro z
      by_cases hanti : IsAnticommuting (pauliSharedSplit P z).1
      · simp only [if_pos hanti]
        rw [inducedMsRejection, msRejection_eq_source]
        have hs := msRejection_le_pauliRejection S z xy hxy hanti
        rw [pauliCL_shared_eq P (.ms xy.1) rfl,
          pauliCL_shared_eq P (.ms xy.2) rfl] at hs
        simpa [pauliSharedSplit, ProjectiveSetting.msQuestion] using hs
      · simp only [if_neg hanti]
        exact pauliRejectionAt_nonneg S.toStrategy _ z
    _ ≤ (Fintype.card PauliEdge : ℝ) * ε :=
      fixedEdgeRejection_le_error S _

/-- The average value of the actual induced Magic Square strategies is close
to one on anticommuting tuples. This is item 6 of
`lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:240-249`, blueprint
`ch14_qpbt_observables.tex:599-625`. -/
theorem win_magic_square_proof :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε →
      |1 - avgOver (anticommTupleDist P) S.msValueAt| ≤ C * ε := by
  refine ⟨16 * (Fintype.card PauliEdge : ℝ), ?_, ?_⟩
  · have hcard : (1 : ℝ) ≤ Fintype.card PauliEdge := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card PauliEdge)
    linarith
  intro P ε S _
  let ν := graphDistribution msEdges msEdges_nonempty
  have hpoint (ω : PauliTuple P) :
      avgOver ν (inducedMsRejection S ω) = 1 - S.msValueAt ω := by
    change avgOver (graphDistribution msEdges msEdges_nonempty)
        (fun questions : MsType × MsType =>
          outcomeEventWeight (S.msStrategyAt ω) questions.1 questions.2
            (fun a b => msWinPredicate questions.1 questions.2 a b = false)) =
      1 - S.msValueAt ω
    convert rejectionMass_eq_one_sub_value (S.msStrategyAt ω) using 1 <;>
      rfl
  have hvalue :
      1 - avgOver (anticommTupleDist P) S.msValueAt =
        avgOver (anticommTupleDist P) (fun ω =>
          avgOver ν (inducedMsRejection S ω)) := by
    calc
      _ = avgOver (anticommTupleDist P) (fun ω => 1 - S.msValueAt ω) := by
        symm
        rw [avgOver_sub, avgOver_const_of_isProbability _
          (anticommTupleDist_isProbability P)]
      _ = _ := by
        apply avgOver_congr
        intro ω
        exact (hpoint ω).symm
  rw [hvalue, abs_of_nonneg]
  · calc
      avgOver (anticommTupleDist P) (fun ω =>
          avgOver ν (inducedMsRejection S ω)) ≤
          16 * avgOver (uniformDistribution (PauliTuple P)) (fun ω =>
            if IsAnticommuting ω then
              avgOver ν (inducedMsRejection S ω)
            else 0) := by
        apply avgOver_anticomm_le_sixteen_mul_gated
        intro ω
        exact avgOver_nonneg ν _ fun xy =>
          outcome_event_weight_nonneg (S.msStrategyAt ω) xy.1 xy.2 _
      _ = 16 * avgOver ν (fun xy =>
          avgOver (uniformDistribution (PauliTuple P)) (fun ω =>
            if IsAnticommuting ω then inducedMsRejection S ω xy else 0)) := by
        congr 1
        calc
          avgOver (uniformDistribution (PauliTuple P)) (fun ω =>
              if IsAnticommuting ω then
                avgOver ν (inducedMsRejection S ω)
              else 0) =
              avgOver (uniformDistribution (PauliTuple P)) (fun ω =>
                avgOver ν (fun xy => if IsAnticommuting ω then
                  inducedMsRejection S ω xy else 0)) := by
            apply avgOver_congr
            intro ω
            by_cases hanti : IsAnticommuting ω <;>
              simp [hanti, avgOver_zero]
          _ = _ := avgOver_comm _ _ _
      _ ≤ 16 * avgOver ν
          (fun _ => (Fintype.card PauliEdge : ℝ) * ε) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply avgOver_mono_on_support
        intro xy hxy
        exact gatedMsRejection_le_fixedEdge S xy hxy
      _ = 16 * (Fintype.card PauliEdge : ℝ) * ε := by
        rw [avgOver_const_of_isProbability ν]
        · ring
        · exact graphDistribution_isProbability msEdges msEdges_nonempty
  · exact avgOver_nonneg (anticommTupleDist P) _ fun ω =>
      avgOver_nonneg ν _ fun xy =>
        outcome_event_weight_nonneg (S.msStrategyAt ω) xy.1 xy.2 _


end WinImplications

end

end MIPStarRE.QPBT
