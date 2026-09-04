import MIPStarRE.QPBT.Observables.WinImplications.Averages

/-!
# Low-degree winning implications

This module proves the exact line-point and Pauli-basis consistency bounds.

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

local instance pauliEdgeNonemptyLowDegree : Nonempty PauliEdge := pauliEdge_nonempty

/-- Coordinates outside one low-degree register in the Pauli seed. -/
abbrev PauliLdRemainder (P : AdmissibleParams) :=
  (Fin P.m → PauliScalar P) × PauliScalar P × PauliScalar P

/-- Split a Pauli seed into a basis-selected low-degree seed and unused coordinates. -/
def pauliLdSplit (P : AdmissibleParams) (W : PauliKind) :
    PauliSpace P ≃ LdSpace P.toLdParams × PauliLdRemainder P where
  toFun z :=
    (pauliToLd P W z,
      (match W with | .X => pauliZBlock z | .Z => pauliXBlock z,
        pauliRXBlock z, pauliRZBlock z))
  invFun zr := fun i =>
    match i with
    | .inl (.inl (.inl (.inl (.inl j)))) =>
        match W with
        | .X => zr.1 (.inl (.inl j))
        | .Z => zr.2.1 j
    | .inl (.inl (.inl (.inl (.inr j)))) =>
        match W with
        | .X => zr.2.1 j
        | .Z => zr.1 (.inl (.inl j))
    | .inl (.inl (.inl (.inr _))) => zr.1 (.inl (.inr ()))
    | .inl (.inl (.inr j)) => zr.1 (.inr j)
    | .inl (.inr _) => zr.2.2.1
    | .inr _ => zr.2.2.2
  left_inv z := by
    funext i
    rcases i with ((((j | j) | u) | j) | u) | u <;> cases W <;> rfl
  right_inv zr := by
    rcases zr with ⟨z, other, rX, rZ⟩
    apply Prod.ext
    · funext i
      rcases i with (j | u) | j <;> cases W <;> rfl
    · cases W <;> rfl

/-- Coordinates discarded by the shared Pair and Magic Square projection. -/
abbrev PauliSharedRemainder (P : AdmissibleParams) :=
  PauliScalar P × (Fin P.m → PauliScalar P)

/-- Split a Pauli seed into its shared tuple and discarded scalar/direction blocks. -/
def pauliSharedSplit (P : AdmissibleParams) :
    PauliSpace P ≃ PauliTuple P × PauliSharedRemainder P where
  toFun z :=
    ((pauliXBlock z, pauliZBlock z, pauliRXBlock z, pauliRZBlock z),
      pauliScalarBlock z, pauliDirectionBlock z)
  invFun zr := fun i =>
    match i with
    | .inl (.inl (.inl (.inl (.inl j)))) => zr.1.1 j
    | .inl (.inl (.inl (.inl (.inr j)))) => zr.1.2.1 j
    | .inl (.inl (.inl (.inr _))) => zr.2.1
    | .inl (.inl (.inr j)) => zr.2.2 j
    | .inl (.inr _) => zr.1.2.2.1
    | .inr _ => zr.1.2.2.2
  left_inv z := by
    funext i
    rcases i with ((((j | j) | u) | j) | u) | u <;> rfl
  right_inv zr := by
    rcases zr with ⟨⟨uX, uZ, rX, rZ⟩, scalar, direction⟩
    rfl

/-- Split a low-degree seed into its point and unused scalar/direction blocks. -/
def ldPointSplit (L : LdParams) :
    LdSpace L ≃ (Fin L.m → ScalarQ L) × (ScalarQ L × (Fin L.m → ScalarQ L)) where
  toFun z := (z.point, z.seed, z.direction)
  invFun zr := fun i =>
    match i with
    | .inl (.inl j) => zr.1 j
    | .inl (.inr _) => zr.2.1
    | .inr j => zr.2.2 j
  left_inv z := by
    funext i
    rcases i with (j | u) | j <;> rfl
  right_inv zr := by
    rcases zr with ⟨point, seed, direction⟩
    rfl

/-- Uniform Pauli seeds have the uniform low-degree marginal in either basis. -/
theorem avgOver_pauliToLd_uniform (P : AdmissibleParams) (W : PauliKind)
    (f : LdSpace P.toLdParams → ℝ) :
    avgOver (uniformDistribution (PauliSpace P)) (fun z => f (pauliToLd P W z)) =
      avgOver (uniformDistribution (LdSpace P.toLdParams)) f := by
  exact avgOver_uniform_equiv_fst (pauliLdSplit P W) f

/-- Uniform Pauli seeds have the uniform shared-tuple marginal. -/
theorem avgOver_pauliTuple_uniform (P : AdmissibleParams)
    (f : PauliTuple P → ℝ) :
    avgOver (uniformDistribution (PauliSpace P))
        (fun z => f (pauliSharedSplit P z).1) =
      avgOver (uniformDistribution (PauliTuple P)) f := by
  exact avgOver_uniform_equiv_fst (pauliSharedSplit P) f

/-- The point block of a uniform low-degree seed is uniform. -/
theorem avgOver_ldPoint_uniform (L : LdParams)
    (f : (Fin L.m → ScalarQ L) → ℝ) :
    avgOver (uniformDistribution (LdSpace L)) (fun z => f z.point) =
      avgOver (uniformDistribution (Fin L.m → ScalarQ L)) f := by
  exact avgOver_uniform_equiv_fst (ldPointSplit L) f

/-- The point conditioning map produces the typed point content. -/
theorem pauliCL_point_eq (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) :
    pauliCL P (.point W) z =
      ProjectiveSetting.contentOfPoint P W (pauliToLd P W z).point := by
  funext i
  rcases i with ((((j | j) | u) | j) | u) | u <;> cases W <;> rfl

/-- The shared conditioning map produces the typed tuple content. -/
theorem pauliCL_shared_eq (P : AdmissibleParams) (t : PauliType)
    (ht : pauliCL P t = pauliSharedProjection) (z : PauliSpace P) :
    pauliCL P t z = ProjectiveSetting.contentOfTuple P
      (pauliXBlock z) (pauliZBlock z) (pauliRXBlock z) (pauliRZBlock z) := by
  rw [ht]
  funext i
  rcases i with ((((j | j) | u) | j) | u) | u <;> rfl

/-- Reading a typed point content recovers its point block. -/
theorem pauliPointBlock_contentOfPoint (P : AdmissibleParams)
    (W : PauliKind) (u : Fin P.m → PauliScalar P) :
    pauliPointBlock W (ProjectiveSetting.contentOfPoint P W u) = u := by
  funext j
  cases W <;> rfl

/-- Reading a typed line content recovers its canonical base. -/
theorem pauliPointBlock_contentOfLine (P : AdmissibleParams)
    (W : PauliKind) (line : LineDesc P.toLdParams) :
    pauliPointBlock W (ProjectiveSetting.contentOfLine P W line) = line.base := by
  funext j
  cases W <;> rfl

/-- Reading a typed line content recovers its seed. -/
theorem pauliScalarBlock_contentOfLine (P : AdmissibleParams)
    (W : PauliKind) (line : LineDesc P.toLdParams) :
    pauliScalarBlock (ProjectiveSetting.contentOfLine P W line) = line.seed := by
  cases W <;> rfl

/-- Reading a typed line content recovers its geometric direction. -/
theorem pauliDirectionBlock_contentOfLine (P : AdmissibleParams)
    (W : PauliKind) (line : LineDesc P.toLdParams)
    (hline : line.kind = .diagonal) :
    pauliDirectionBlock (ProjectiveSetting.contentOfLine P W line) = line.direction := by
  funext j
  cases line with
  | axis => simp [LineDesc.kind] at hline
  | diagonal => cases W <;> rfl

/-- Prefix projection is idempotent at a fixed cutoff. -/
theorem prefixProjection_idem (L : LdParams) (i : Fin L.m)
    (v : Fin L.m → ScalarQ L) :
    prefixProjection i (prefixProjection i v) = prefixProjection i v := by
  funext j
  by_cases h : j.val < i.val <;> simp [prefixProjection, h]

/-- Zero-padding a coefficient list does not change its polynomial value. -/
theorem evalCoefficient_padTo {L : LdParams} {c c' : ℕ} (h : c ≤ c')
    (f : DegPoly L c) (t : ScalarQ L) :
    evalCoefficient (DegPoly.padTo h f) t = evalCoefficient f t := by
  classical
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero =>
      have heq : DegPoly.padTo h f = f := by
        funext i
        simp [DegPoly.padTo, i.isLt]
      rw [heq]
  | succ k ih =>
      rw [evalCoefficient, Fin.sum_univ_castSucc]
      have hk : c ≤ c + k := Nat.le_add_right c k
      have hcast :
          (∑ i : Fin (c + (k + 1)),
              DegPoly.padTo h f i.castSucc * t ^ i.castSucc.val) =
            evalCoefficient (DegPoly.padTo hk f) t := by
        unfold evalCoefficient
        apply Finset.sum_congr rfl
        intro i _
        congr 1
      rw [hcast, ih]
      rw [show DegPoly.padTo h f (Fin.last (c + (k + 1))) = 0 by
        simp [DegPoly.padTo]]
      simp

/-- A uniquely determined line evaluation is returned by `evalOpt`. -/
theorem evalOpt_eq_some_of_evaluatesTo {L : LdParams} {c : ℕ}
    (line : LineDesc L) (f : DegPoly L c) (u : Fin L.m → ScalarQ L)
    (a : ScalarQ L) (h : EvaluatesTo line f u a) :
    evalOpt line u f = some a := by
  unfold evalOpt
  rw [dif_pos ⟨a, h⟩]
  apply congrArg some
  obtain ⟨t, ht⟩ := h.1
  exact ((Classical.choose_spec ⟨a, h⟩).2 t ht).symm.trans (h.2 t ht)

/-- The sampled point lies on its canonical axis line. -/
theorem point_mem_sampled_aline (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) :
    (pauliToLd P W z).point ∈
      (aLineDescOf P.toLdParams
        (ldALineCL P.toLdParams (pauliToLd P W z))).pointSet := by
  change (pauliToLd P W z).point ∈ linePoints
    (lineRepMap
      (coordinateDirection (chiIndex P.toLdParams (pauliToLd P W z).seed))
      (lineRepMap
        (coordinateDirection (chiIndex P.toLdParams (pauliToLd P W z).seed))
        (pauliToLd P W z).point))
    (coordinateDirection (chiIndex P.toLdParams (pauliToLd P W z).seed))
  rw [lineRepMap_apply_self]
  exact mem_linePoints_lineRepMap _ _

/-- The sampled point lies on its canonical diagonal line. -/
theorem point_mem_sampled_dline (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) :
    (pauliToLd P W z).point ∈
      (dLineDescOf P.toLdParams
        (ldDLineCL P.toLdParams (pauliToLd P W z))).pointSet := by
  change (pauliToLd P W z).point ∈ linePoints
    (lineRepMap
      (prefixProjection (chiIndex P.toLdParams (pauliToLd P W z).seed)
        (prefixProjection (chiIndex P.toLdParams (pauliToLd P W z).seed)
          (pauliToLd P W z).direction))
      (lineRepMap
        (prefixProjection (chiIndex P.toLdParams (pauliToLd P W z).seed)
          (pauliToLd P W z).direction) (pauliToLd P W z).point))
    (prefixProjection (chiIndex P.toLdParams (pauliToLd P W z).seed)
      (prefixProjection (chiIndex P.toLdParams (pauliToLd P W z).seed)
        (pauliToLd P W z).direction))
  rw [prefixProjection_idem, lineRepMap_apply_self]
  exact mem_linePoints_lineRepMap _ _

/-- The axis-line conditioning map produces the typed canonical line content. -/
theorem pauliCL_aline_eq (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) :
    pauliCL P (.aline W) z = ProjectiveSetting.contentOfLine P W
      (aLineDescOf P.toLdParams (ldALineCL P.toLdParams (pauliToLd P W z))) := by
  apply congrArg (embedLd P W)
  funext i
  rcases i with (j | u) | j
  · change (lineRepMap
        (coordinateDirection (chiIndex P.toLdParams (pauliToLd P W z).seed))
        (pauliToLd P W z).point) j =
      (lineRepMap
        (coordinateDirection (chiIndex P.toLdParams (pauliToLd P W z).seed))
        (lineRepMap
          (coordinateDirection (chiIndex P.toLdParams (pauliToLd P W z).seed))
          (pauliToLd P W z).point)) j
    rw [lineRepMap_apply_self]
  · rfl
  · rfl

/-- The diagonal-line conditioning map produces the typed canonical line content. -/
theorem pauliCL_dline_eq (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) :
    pauliCL P (.dline W) z = ProjectiveSetting.contentOfLine P W
      (dLineDescOf P.toLdParams (ldDLineCL P.toLdParams (pauliToLd P W z))) := by
  apply congrArg (embedLd P W)
  funext i
  rcases i with (j | u) | j
  · change (lineRepMap
        (prefixProjection (chiIndex P.toLdParams (pauliToLd P W z).seed)
          (pauliToLd P W z).direction) (pauliToLd P W z).point) j =
      (lineRepMap
        (prefixProjection (chiIndex P.toLdParams (pauliToLd P W z).seed)
          (prefixProjection (chiIndex P.toLdParams (pauliToLd P W z).seed)
            (pauliToLd P W z).direction))
        (lineRepMap
          (prefixProjection (chiIndex P.toLdParams (pauliToLd P W z).seed)
            (pauliToLd P W z).direction) (pauliToLd P W z).point)) j
    rw [prefixProjection_idem, lineRepMap_apply_self]
  · rfl
  · change prefixProjection (chiIndex P.toLdParams (pauliToLd P W z).seed)
        (pauliToLd P W z).direction j =
      prefixProjection (chiIndex P.toLdParams (pauliToLd P W z).seed)
        (prefixProjection (chiIndex P.toLdParams (pauliToLd P W z).seed)
          (pauliToLd P W z).direction) j
    rw [prefixProjection_idem]

/-- A successful sampled axis-line check gives the corresponding evaluation identity. -/
theorem alineWinningCondition (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) (f : Fin (P.d + 1) → PauliScalar P)
    (a : PauliScalar P)
    (hwin : pauliWinPredicate P
      ((.aline W), pauliCL P (.aline W) z)
      ((.point W), pauliCL P (.point W) z)
      (.alinePoly f) (.value a) = true) :
    ∀ t : ScalarQ P.toLdParams,
      (pauliToLd P W z).point =
          (aLineDescOf P.toLdParams
            (ldALineCL P.toLdParams (pauliToLd P W z))).base +
            t • (aLineDescOf P.toLdParams
              (ldALineCL P.toLdParams (pauliToLd P W z))).direction →
        evalCoefficient f (scalarToPauli P t) = a := by
  rw [pauliCL_aline_eq, pauliCL_point_eq] at hwin
  have hc : pauliAlinePointCondition P W
      (ProjectiveSetting.contentOfLine P W
        (aLineDescOf P.toLdParams (ldALineCL P.toLdParams (pauliToLd P W z))))
      (ProjectiveSetting.contentOfPoint P W (pauliToLd P W z).point) f a := by
    simpa [pauliWinPredicate, validPauliAnswer] using hwin
  intro t ht
  apply hc (scalarToPauli P t)
  rw [pauliPointBlock_contentOfPoint, pauliPointBlock_contentOfLine,
    pauliScalarBlock_contentOfLine]
  funext j
  have hj := congrFun ht j
  have hp := congrArg (scalarToPauli P) hj
  change scalarToPauli P ((pauliToLd P W z).point j) =
    scalarToPauli P
      ((aLineDescOf P.toLdParams
        (ldALineCL P.toLdParams (pauliToLd P W z))).base j +
        t * (aLineDescOf P.toLdParams
          (ldALineCL P.toLdParams (pauliToLd P W z))).direction j)
  exact hp

/-- A successful sampled diagonal-line check gives the corresponding evaluation identity. -/
theorem dlineWinningCondition (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) (f : Fin (P.m * P.d + 1) → PauliScalar P)
    (a : PauliScalar P)
    (hwin : pauliWinPredicate P
      ((.dline W), pauliCL P (.dline W) z)
      ((.point W), pauliCL P (.point W) z)
      (.dlinePoly f) (.value a) = true) :
    ∀ t : ScalarQ P.toLdParams,
      (pauliToLd P W z).point =
          (dLineDescOf P.toLdParams
            (ldDLineCL P.toLdParams (pauliToLd P W z))).base +
            t • (dLineDescOf P.toLdParams
              (ldDLineCL P.toLdParams (pauliToLd P W z))).direction →
        evalCoefficient f (scalarToPauli P t) = a := by
  rw [pauliCL_dline_eq, pauliCL_point_eq] at hwin
  have hc : pauliDlinePointCondition P W
      (ProjectiveSetting.contentOfLine P W
        (dLineDescOf P.toLdParams (ldDLineCL P.toLdParams (pauliToLd P W z))))
      (ProjectiveSetting.contentOfPoint P W (pauliToLd P W z).point) f a := by
    simpa [pauliWinPredicate, validPauliAnswer] using hwin
  intro t ht
  apply hc (scalarToPauli P t)
  rw [pauliPointBlock_contentOfPoint, pauliPointBlock_contentOfLine,
    pauliDirectionBlock_contentOfLine P W
      (dLineDescOf P.toLdParams (ldDLineCL P.toLdParams (pauliToLd P W z)))
      (by rfl)]
  funext j
  have hj := congrFun ht j
  have hp := congrArg (scalarToPauli P) hj
  change scalarToPauli P ((pauliToLd P W z).point j) =
    scalarToPauli P
      ((dLineDescOf P.toLdParams
        (ldDLineCL P.toLdParams (pauliToLd P W z))).base j +
        t * (dLineDescOf P.toLdParams
          (ldDLineCL P.toLdParams (pauliToLd P W z))).direction j)
  exact hp

/-- Winning the sampled axis-line branch forces equality of the exposed labels. -/
theorem alineLabels_eq_of_win (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) (A B : PauliAnswer P)
    (hwin : pauliWinPredicate P
      ((.aline W), pauliCL P (.aline W) z)
      ((.point W), pauliCL P (.point W) z) A B = true) :
    evalOpt
        (aLineDescOf P.toLdParams (ldALineCL P.toLdParams (pauliToLd P W z)))
        (pauliToLd P W z).point
        (ProjectiveSetting.lineAnswerOrZero P
          (aLineDescOf P.toLdParams (ldALineCL P.toLdParams (pauliToLd P W z))) A) =
      some (ProjectiveSetting.pointAnswerOrZero B) := by
  cases A <;> cases B <;>
    simp only [pauliWinPredicate, validPauliAnswer, Bool.and_true,
      Bool.and_self, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
      reduceCtorEq, decide_eq_true_eq] at hwin
  rename_i f a
  apply evalOpt_eq_some_of_evaluatesTo
  refine ⟨point_mem_sampled_aline P W z, ?_⟩
  intro t ht
  let hpad : P.d ≤ P.m * P.d :=
    Nat.le_mul_of_pos_left P.d (Nat.zero_lt_of_lt P.one_le_m)
  rw [show ProjectiveSetting.lineAnswerOrZero P
      (aLineDescOf P.toLdParams (ldALineCL P.toLdParams (pauliToLd P W z)))
      (.alinePoly f) = DegPoly.padTo hpad f by rfl]
  rw [evalCoefficient_padTo hpad]
  change evalCoefficient f (scalarToPauli P t) = a
  exact alineWinningCondition P W z f a (by
    simpa [pauliWinPredicate, validPauliAnswer] using hwin) t ht

/-- Winning the sampled diagonal-line branch forces equality of exposed labels. -/
theorem dlineLabels_eq_of_win (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) (A B : PauliAnswer P)
    (hwin : pauliWinPredicate P
      ((.dline W), pauliCL P (.dline W) z)
      ((.point W), pauliCL P (.point W) z) A B = true) :
    evalOpt
        (dLineDescOf P.toLdParams (ldDLineCL P.toLdParams (pauliToLd P W z)))
        (pauliToLd P W z).point
        (ProjectiveSetting.lineAnswerOrZero P
          (dLineDescOf P.toLdParams (ldDLineCL P.toLdParams (pauliToLd P W z))) A) =
      some (ProjectiveSetting.pointAnswerOrZero B) := by
  cases A <;> cases B <;>
    simp only [pauliWinPredicate, validPauliAnswer, Bool.and_true,
      Bool.and_self, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
      reduceCtorEq, decide_eq_true_eq] at hwin
  rename_i f a
  apply evalOpt_eq_some_of_evaluatesTo
  refine ⟨point_mem_sampled_dline P W z, ?_⟩
  intro t ht
  rw [show ProjectiveSetting.lineAnswerOrZero P
      (dLineDescOf P.toLdParams (ldDLineCL P.toLdParams (pauliToLd P W z)))
      (.dlinePoly f) = f by rfl]
  change evalCoefficient f (scalarToPauli P t) = a
  exact dlineWinningCondition P W z f a (by
    simpa [pauliWinPredicate, validPauliAnswer] using hwin) t ht

/-- The axis-line/point verifier edge in one Pauli basis. -/
def alinePointEdge (W : PauliKind) : PauliEdge :=
  ⟨(.aline W, .point W), by simp [pauliEdges]⟩

/-- The diagonal-line/point verifier edge in one Pauli basis. -/
def dlinePointEdge (W : PauliKind) : PauliEdge :=
  ⟨(.dline W, .point W), by simp [pauliEdges]⟩

/-- The point/Pauli verifier edge in one Pauli basis. -/
def pointPauliEdge (W : PauliKind) : PauliEdge :=
  ⟨(.point W, .pauli W), by simp [pauliEdges]⟩

/-- The Pair-W/Pair verifier edge in one Pauli basis. -/
def pairWPairEdge (W : PauliKind) : PauliEdge :=
  ⟨(.pairW W, .pair), by simp [pauliEdges]⟩

/-- The point/Pair-W verifier edge in one Pauli basis. -/
def pointPairWEdge (W : PauliKind) : PauliEdge :=
  ⟨(.point W, .pairW W), by simp [pauliEdges]⟩

/-- Mismatch in the sampled axis-line branch is contained in rejection. -/
theorem alineMismatch_le_rejection {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind) (z : PauliSpace P) :
    outcomeEventWeight S.toStrategy
        ((.aline W), pauliCL P (.aline W) z)
        ((.point W), pauliCL P (.point W) z)
        (fun A B =>
          evalOpt
              (aLineDescOf P.toLdParams
                (ldALineCL P.toLdParams (pauliToLd P W z)))
              (pauliToLd P W z).point
              (ProjectiveSetting.lineAnswerOrZero P
                (aLineDescOf P.toLdParams
                  (ldALineCL P.toLdParams (pauliToLd P W z))) A) ≠
            some (ProjectiveSetting.pointAnswerOrZero B)) ≤
      pauliRejectionAt S.toStrategy (alinePointEdge W) z := by
  apply outcome_event_weight_mono
  intro A B hne
  change pauliWinPredicate P _ _ A B = false
  apply Bool.eq_false_iff.mpr
  intro htrue
  exact hne (alineLabels_eq_of_win P W z A B htrue)

/-- Mismatch in the sampled diagonal-line branch is contained in rejection. -/
theorem dlineMismatch_le_rejection {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind) (z : PauliSpace P) :
    outcomeEventWeight S.toStrategy
        ((.dline W), pauliCL P (.dline W) z)
        ((.point W), pauliCL P (.point W) z)
        (fun A B =>
          evalOpt
              (dLineDescOf P.toLdParams
                (ldDLineCL P.toLdParams (pauliToLd P W z)))
              (pauliToLd P W z).point
              (ProjectiveSetting.lineAnswerOrZero P
                (dLineDescOf P.toLdParams
                  (ldDLineCL P.toLdParams (pauliToLd P W z))) A) ≠
            some (ProjectiveSetting.pointAnswerOrZero B)) ≤
      pauliRejectionAt S.toStrategy (dlinePointEdge W) z := by
  apply outcome_event_weight_mono
  intro A B hne
  change pauliWinPredicate P _ _ A B = false
  apply Bool.eq_false_iff.mpr
  intro htrue
  exact hne (dlineLabels_eq_of_win P W z A B htrue)

/-- Source-answer mismatch mass for the completed line and point readouts. -/
noncomputable def lowDegreeMismatchMass {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind)
    (sample : LineDesc P.toLdParams × (Fin P.m → PauliScalar P)) : ℝ :=
  outcomeEventWeight S.toStrategy
    (ProjectiveSetting.lineQuestion P W sample.1)
    (ProjectiveSetting.pointQuestion P W sample.2)
    (fun A B =>
      evalOpt sample.1 sample.2
          (ProjectiveSetting.lineAnswerOrZero P sample.1 A) ≠
        some (ProjectiveSetting.pointAnswerOrZero B))

/-- The axis component of the exposed line sampler is the corresponding Pauli branch. -/
theorem avg_alineMismatch_eq_source {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind) :
    avgOver (aLinePointDist P.toLdParams) (lowDegreeMismatchMass S W) =
      avgOver (uniformDistribution (PauliSpace P)) (fun z =>
        outcomeEventWeight S.toStrategy
          ((.aline W), pauliCL P (.aline W) z)
          ((.point W), pauliCL P (.point W) z)
          (fun A B =>
            evalOpt
                (aLineDescOf P.toLdParams
                  (ldALineCL P.toLdParams (pauliToLd P W z)))
                (pauliToLd P W z).point
                (ProjectiveSetting.lineAnswerOrZero P
                  (aLineDescOf P.toLdParams
                    (ldALineCL P.toLdParams (pauliToLd P W z))) A) ≠
              some (ProjectiveSetting.pointAnswerOrZero B))) := by
  unfold aLinePointDist clDistribution
  rw [Distribution.avgOver_map, Distribution.avgOver_map]
  rw [← avgOver_pauliToLd_uniform P W]
  apply avgOver_congr
  intro z
  rw [pauliCL_aline_eq, pauliCL_point_eq]
  rfl

/-- The diagonal component of the exposed line sampler is the corresponding Pauli branch. -/
theorem avg_dlineMismatch_eq_source {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind) :
    avgOver (dLinePointDist P.toLdParams) (lowDegreeMismatchMass S W) =
      avgOver (uniformDistribution (PauliSpace P)) (fun z =>
        outcomeEventWeight S.toStrategy
          ((.dline W), pauliCL P (.dline W) z)
          ((.point W), pauliCL P (.point W) z)
          (fun A B =>
            evalOpt
                (dLineDescOf P.toLdParams
                  (ldDLineCL P.toLdParams (pauliToLd P W z)))
                (pauliToLd P W z).point
                (ProjectiveSetting.lineAnswerOrZero P
                  (dLineDescOf P.toLdParams
                    (ldDLineCL P.toLdParams (pauliToLd P W z))) A) ≠
              some (ProjectiveSetting.pointAnswerOrZero B))) := by
  unfold dLinePointDist clDistribution
  rw [Distribution.avgOver_map, Distribution.avgOver_map]
  rw [← avgOver_pauliToLd_uniform P W]
  apply avgOver_congr
  intro z
  rw [pauliCL_dline_eq, pauliCL_point_eq]
  rfl

/-- The completed low-degree consistency defect is its source-answer mismatch mass. -/
theorem lowDegreeConsistency_eq_mismatch {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind) :
    consistencyDefect (linePointDist P.toLdParams)
        (fun sample a => heteroKron
          ((S.lineEvalMeas .alice W sample.1 sample.2).effect a) 1)
        (fun sample a => heteroKron 1
          ((S.pointMeasOption .bob W sample.2).effect a))
        S.toStrategy.ψ =
      avgOver (linePointDist P.toLdParams) (fun sample =>
        outcomeEventWeight S.toStrategy
          (ProjectiveSetting.lineQuestion P W sample.1)
          (ProjectiveSetting.pointQuestion P W sample.2)
          (fun A B =>
            evalOpt sample.1 sample.2
                (ProjectiveSetting.lineAnswerOrZero P sample.1 A) ≠
              some (ProjectiveSetting.pointAnswerOrZero B))) := by
  let X := LineDesc P.toLdParams × (Fin P.m → PauliScalar P)
  let qA : X → PauliQuestion P := fun sample =>
    ProjectiveSetting.lineQuestion P W sample.1
  let qB : X → PauliQuestion P := fun sample =>
    ProjectiveSetting.pointQuestion P W sample.2
  let fA : X → PauliAnswer P → Option (PauliScalar P) := fun sample A =>
    evalOpt sample.1 sample.2 (ProjectiveSetting.lineAnswerOrZero P sample.1 A)
  let fB : X → PauliAnswer P → Option (PauliScalar P) := fun _ B =>
    some (ProjectiveSetting.pointAnswerOrZero B)
  have h := consistencyDefect_postprocess_eq_mismatch
    (X := X) (linePointDist P.toLdParams) S.toStrategy qA qB fA fB
  have hA : ∀ (sample : X) c,
      heteroKron ((S.lineEvalMeas .alice W sample.1 sample.2).effect c)
          (1 : Op S.toStrategy.ιB) =
        heteroKron
          (((S.toStrategy.A (qA sample)).postprocess (fA sample)).effect c)
          (1 : Op S.toStrategy.ιB) := by
    intro sample c
    congr 1
    unfold ProjectiveSetting.lineEvalMeas ProjectiveSetting.lineMeas qA fA
    rw [measurement_postprocess_comp_effect]
    rfl
  have hB : ∀ (sample : X) c,
      heteroKron (1 : Op S.toStrategy.ιA)
          ((S.pointMeasOption .bob W sample.2).effect c) =
        heteroKron (1 : Op S.toStrategy.ιA)
          (((S.toStrategy.B (qB sample)).postprocess (fB sample)).effect c) := by
    intro sample c
    congr 1
    unfold ProjectiveSetting.pointMeasOption ProjectiveSetting.pointMeas qB fB
    rw [measurement_postprocess_comp_effect]
    rfl
  calc
    consistencyDefect (linePointDist P.toLdParams)
        (fun sample a => heteroKron
          ((S.lineEvalMeas .alice W sample.1 sample.2).effect a) 1)
        (fun sample a => heteroKron 1
          ((S.pointMeasOption .bob W sample.2).effect a))
        S.toStrategy.ψ =
        consistencyDefect (linePointDist P.toLdParams)
          (fun sample c => heteroKron
            (((S.toStrategy.A (qA sample)).postprocess (fA sample)).effect c) 1)
          (fun sample c => heteroKron 1
            (((S.toStrategy.B (qB sample)).postprocess (fB sample)).effect c))
          S.toStrategy.ψ := consistencyDefect_congr _ _ _ _ _ _ hA hB
    _ = avgOver (linePointDist P.toLdParams) (fun sample =>
        outcomeEventWeight S.toStrategy (qA sample) (qB sample)
          (fun A B => fA sample A ≠ fB sample B)) := h
    _ = _ := by rfl

/-- The low-degree subtest bounds completed line-evaluation classes against
completed point measurements. This is item 2 of
`lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:200-204`, blueprint
`ch14_qpbt_observables.tex:523-548`. -/
theorem win_low_degree_proof :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : PauliKind,
      consistencyDefect (linePointDist P.toLdParams)
        (fun sample a => heteroKron
          ((S.lineEvalMeas .alice W sample.1 sample.2).effect a) 1)
        (fun sample a => heteroKron 1
          ((S.pointMeasOption .bob W sample.2).effect a))
        S.toStrategy.ψ ≤ C * ε := by
  refine ⟨(Fintype.card PauliEdge : ℝ), ?_, ?_⟩
  · exact_mod_cast (Fintype.card_pos : 0 < Fintype.card PauliEdge)
  intro P ε S hε W
  rw [lowDegreeConsistency_eq_mismatch]
  change avgOver (linePointDist P.toLdParams) (lowDegreeMismatchMass S W) ≤ _
  have ha : avgOver (aLinePointDist P.toLdParams) (lowDegreeMismatchMass S W) ≤
      (Fintype.card PauliEdge : ℝ) * ε := by
    rw [avg_alineMismatch_eq_source]
    calc
      _ ≤ avgOver (uniformDistribution (PauliSpace P))
          (pauliRejectionAt S.toStrategy
            (alinePointEdge W)) := by
        apply avgOver_mono
        intro z
        exact alineMismatch_le_rejection S W z
      _ ≤ (Fintype.card PauliEdge : ℝ) * ε :=
        fixedEdgeRejection_le_error S _
  have hd : avgOver (dLinePointDist P.toLdParams) (lowDegreeMismatchMass S W) ≤
      (Fintype.card PauliEdge : ℝ) * ε := by
    rw [avg_dlineMismatch_eq_source]
    calc
      _ ≤ avgOver (uniformDistribution (PauliSpace P))
          (pauliRejectionAt S.toStrategy
            (dlinePointEdge W)) := by
        apply avgOver_mono
        intro z
        exact dlineMismatch_le_rejection S W z
      _ ≤ (Fintype.card PauliEdge : ℝ) * ε :=
        fixedEdgeRejection_le_error S _
  rw [linePointDist, avgOver_mix]
  linarith

/-- Winning the point-versus-Pauli branch forces equality of evaluated labels. -/
theorem pauliBasisLabels_eq_of_win (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) (A B : PauliAnswer P)
    (hwin : pauliWinPredicate P
      ((.point W), pauliCL P (.point W) z)
      ((.pauli W), pauliCL P (.pauli W) z) A B = true) :
    ProjectiveSetting.pointAnswerOrZero A =
      lowDegreeEnc (pauliAnswerOrZero B) (pauliToLd P W z).point := by
  cases A <;> cases B <;>
    simp [pauliWinPredicate, validPauliAnswer] at hwin
  rename_i a h
  change a = lowDegreeEnc h (pauliToLd P W z).point
  simpa [pauliCL_point_eq, pauliPointPauliCondition,
    pauliPointBlock_contentOfPoint] using hwin.symm

/-- Point/Pauli label mismatch is contained in rejection. -/
theorem pauliBasisMismatch_le_rejection {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind) (z : PauliSpace P) :
    outcomeEventWeight S.toStrategy
        ((.point W), pauliCL P (.point W) z)
        ((.pauli W), pauliCL P (.pauli W) z)
        (fun A B => ProjectiveSetting.pointAnswerOrZero A ≠
          lowDegreeEnc (pauliAnswerOrZero B) (pauliToLd P W z).point) ≤
      pauliRejectionAt S.toStrategy
        (pointPauliEdge W) z := by
  apply outcome_event_weight_mono
  intro A B hne
  change pauliWinPredicate P _ _ A B = false
  apply Bool.eq_false_iff.mpr
  intro htrue
  exact hne (pauliBasisLabels_eq_of_win P W z A B htrue)

/-- The uniform point mismatch average is the sampled point/Pauli branch average. -/
theorem avg_pauliBasisMismatch_eq_source {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind) :
    avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun u =>
        outcomeEventWeight S.toStrategy
          (ProjectiveSetting.pointQuestion P W u) (pauliQuestion P W)
          (fun A B => ProjectiveSetting.pointAnswerOrZero A ≠
            lowDegreeEnc (pauliAnswerOrZero B) u)) =
      avgOver (uniformDistribution (PauliSpace P)) (fun z =>
        outcomeEventWeight S.toStrategy
          (ProjectiveSetting.pointQuestion P W (pauliToLd P W z).point)
          (pauliQuestion P W)
          (fun A B => ProjectiveSetting.pointAnswerOrZero A ≠
            lowDegreeEnc (pauliAnswerOrZero B) (pauliToLd P W z).point)) := by
  let f : (Fin P.m → PauliScalar P) → ℝ := fun u =>
    outcomeEventWeight S.toStrategy
      (ProjectiveSetting.pointQuestion P W u) (pauliQuestion P W)
      (fun A B => ProjectiveSetting.pointAnswerOrZero A ≠
        lowDegreeEnc (pauliAnswerOrZero B) u)
  have hld := avgOver_pauliToLd_uniform P W
    (fun z => f z.point)
  have hpoint := avgOver_ldPoint_uniform P.toLdParams f
  exact (hld.trans hpoint).symm

/-- Pauli-basis consistency is the mismatch probability of the source answers. -/
theorem pauliBasisConsistency_eq_mismatch {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind) :
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u a => heteroKron ((S.pointMeas .alice W u).effect a) 1)
        (fun u a => heteroKron 1 ((S.pauliEvalMeas .bob W u).effect a))
        S.toStrategy.ψ =
      avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun u =>
        outcomeEventWeight S.toStrategy
          (ProjectiveSetting.pointQuestion P W u) (pauliQuestion P W)
          (fun A B => ProjectiveSetting.pointAnswerOrZero A ≠
            lowDegreeEnc (pauliAnswerOrZero B) u)) := by
  let X := Fin P.m → PauliScalar P
  let qA : X → PauliQuestion P := fun u => ProjectiveSetting.pointQuestion P W u
  let qB : X → PauliQuestion P := fun _ => pauliQuestion P W
  let fA : X → PauliAnswer P → PauliScalar P := fun _ =>
    ProjectiveSetting.pointAnswerOrZero
  let fB : X → PauliAnswer P → PauliScalar P := fun u B =>
    lowDegreeEnc (pauliAnswerOrZero B) u
  have h := consistencyDefect_postprocess_eq_mismatch
    (X := X) (uniformDistribution X) S.toStrategy qA qB fA fB
  have hA : ∀ (u : X) c,
      heteroKron ((S.pointMeas .alice W u).effect c)
          (1 : Op S.toStrategy.ιB) =
        heteroKron (((S.toStrategy.A (qA u)).postprocess (fA u)).effect c)
          (1 : Op S.toStrategy.ιB) := by
    intro u c
    rfl
  have hB : ∀ (u : X) c,
      heteroKron (1 : Op S.toStrategy.ιA) ((S.pauliEvalMeas .bob W u).effect c) =
        heteroKron (1 : Op S.toStrategy.ιA)
          (((S.toStrategy.B (qB u)).postprocess (fB u)).effect c) := by
    intro u c
    congr 1
    unfold ProjectiveSetting.pauliEvalMeas ProjectiveSetting.pauliMeas fB qB
    rw [measurement_postprocess_comp_effect]
    rfl
  calc
    _ = consistencyDefect (uniformDistribution X)
        (fun u c => heteroKron
          (((S.toStrategy.A (qA u)).postprocess (fA u)).effect c) 1)
        (fun u c => heteroKron 1
          (((S.toStrategy.B (qB u)).postprocess (fB u)).effect c))
        S.toStrategy.ψ := consistencyDefect_congr _ _ _ _ _ _ hA hB
    _ = avgOver (uniformDistribution X) (fun u =>
        outcomeEventWeight S.toStrategy (qA u) (qB u)
          (fun A B => fA u A ≠ fB u B)) := h
    _ = _ := by rfl

/-- The Pauli-basis consistency subtest compares point values with evaluated
low-degree encodings of Pauli answers. This is item 3 of
`lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:205-209`, blueprint
`ch14_qpbt_observables.tex:549-566`. -/
theorem win_pauli_basis_cons_proof :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : PauliKind,
      consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u a => heteroKron ((S.pointMeas .alice W u).effect a) 1)
        (fun u a => heteroKron 1 ((S.pauliEvalMeas .bob W u).effect a))
        S.toStrategy.ψ ≤ C * ε := by
  refine ⟨(Fintype.card PauliEdge : ℝ), ?_, ?_⟩
  · exact_mod_cast (Fintype.card_pos : 0 < Fintype.card PauliEdge)
  intro P ε S _ W
  rw [pauliBasisConsistency_eq_mismatch, avg_pauliBasisMismatch_eq_source]
  calc
    _ ≤ avgOver (uniformDistribution (PauliSpace P))
        (pauliRejectionAt S.toStrategy
          (pointPauliEdge W)) := by
      apply avgOver_mono
      intro z
      have hs := pauliBasisMismatch_le_rejection S W z
      rw [pauliCL_point_eq] at hs
      simpa only [pauliCL, ProjectiveSetting.pointQuestion, pauliQuestion] using hs
    _ ≤ (Fintype.card PauliEdge : ℝ) * ε :=
      fixedEdgeRejection_le_error S _


end WinImplications

end

end MIPStarRE.QPBT
