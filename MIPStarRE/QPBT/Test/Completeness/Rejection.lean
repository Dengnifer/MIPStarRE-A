import MIPStarRE.QPBT.Test.Completeness.Commutation

/-!
# Rejection of wrong answers by the honest Pauli measurements

This module shows that the honest measurement family of
`MIPStarRE.QPBT.Test.Completeness.HonestStrategy.Assembly` assigns the zero
operator product to every answer pair rejected by the Pauli win predicate on a
question pair of positive weight for the Pauli question sampler.  Together with
the normalisation of the Born weights this yields the value-one assertion of
`lem:pauli-completeness`.

## References

Blueprint `blueprint/src/chapter/ch13_qpbt_test.tex:390-395`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1383-1421`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

set_option maxRecDepth 8000

/-! ### Answers carrying the wrong constructor -/

/-- The honest Point/W measurement assigns the zero effect to every answer that
is not a field value; part of the constructor-shape rejection clause of
`def:pauli-win-predicate`. -/
theorem honestPointMeasurement_effect_eq_zero (P : AdmissibleParams)
    (W : PauliKind) (z : PauliSpace P) {a : PauliAnswer P}
    (ha : validPauliAnswer (.point W) a = false) :
    (honestPointMeasurement P W z).effect a = 0 := by
  refine placedPauliMeasurement_effect_eq_zero_of_notMem _ _ ?_
  rintro ⟨u, rfl⟩
  simp [validPauliAnswer] at ha

/-- The honest Axis-line/W measurement assigns the zero effect to every answer
that is not a degree-`d` coefficient list; part of the constructor-shape
rejection clause of `def:pauli-win-predicate`. -/
theorem honestALineMeasurement_effect_eq_zero (P : AdmissibleParams)
    (W : PauliKind) (z : PauliSpace P) {a : PauliAnswer P}
    (ha : validPauliAnswer (.aline W) a = false) :
    (honestALineMeasurement P W z).effect a = 0 := by
  refine placedPauliMeasurement_effect_eq_zero_of_notMem _ _ ?_
  rintro ⟨u, rfl⟩
  simp [validPauliAnswer] at ha

/-- The honest Diagonal-line/W measurement assigns the zero effect to every
answer that is not a degree-`m d` coefficient list; part of the
constructor-shape rejection clause of `def:pauli-win-predicate`. -/
theorem honestDLineMeasurement_effect_eq_zero (P : AdmissibleParams)
    (W : PauliKind) (z : PauliSpace P) {a : PauliAnswer P}
    (ha : validPauliAnswer (.dline W) a = false) :
    (honestDLineMeasurement P W z).effect a = 0 := by
  refine placedPauliMeasurement_effect_eq_zero_of_notMem _ _ ?_
  rintro ⟨u, rfl⟩
  simp [validPauliAnswer] at ha

/-- The honest Pauli/W measurement assigns the zero effect to every answer that
is not a Pauli label; part of the constructor-shape rejection clause of
`def:pauli-win-predicate`. -/
theorem honestPauliMeasurement_effect_eq_zero (P : AdmissibleParams)
    (W : PauliKind) {a : PauliAnswer P}
    (ha : validPauliAnswer (.pauli W) a = false) :
    (honestPauliMeasurement P W).effect a = 0 := by
  refine placedPauliMeasurement_effect_eq_zero_of_notMem _ _ ?_
  rintro ⟨u, rfl⟩
  simp [validPauliAnswer] at ha

/-- The honest Pair/W measurement assigns the zero effect to every answer that
is not a bit; part of the constructor-shape rejection clause of
`def:pauli-win-predicate`. -/
theorem honestPairWMeasurement_effect_eq_zero (P : AdmissibleParams)
    (W : PauliKind) (z : PauliSpace P) {a : PauliAnswer P}
    (ha : validPauliAnswer (.pairW W) a = false) :
    (honestPairWMeasurement P W z).effect a = 0 := by
  refine placedPauliMeasurement_effect_eq_zero_of_notMem _ _ ?_
  rintro ⟨u, rfl⟩
  simp [validPauliAnswer] at ha

/-- The honest Pair measurement assigns the zero effect to every answer that is
not a pair of bits; part of the constructor-shape rejection clause of
`def:pauli-win-predicate`. -/
theorem honestPairMeasurement_effect_eq_zero (P : AdmissibleParams)
    (z : PauliSpace P) {a : PauliAnswer P}
    (ha : validPauliAnswer .pair a = false) :
    (honestPairMeasurement P z).effect a = 0 := by
  classical
  by_cases hg : pauliPairGamma P z = 0
  · have h1 : honestPairMeasurement P z =
        placedPauliMeasurement (pauliPairMeasurement P z hg)
          (fun c => PauliAnswer.pairBits c) := by
      simp [honestPairMeasurement, hg]
    rw [h1]
    refine placedPauliMeasurement_effect_eq_zero_of_notMem _ _ ?_
    rintro ⟨u, rfl⟩
    simp [validPauliAnswer] at ha
  · have h1 : honestPairMeasurement P z =
        deterministicMeasurement (V := HonestIndex P)
          (PauliAnswer.pairBits (0, 0)) := by
      simp [honestPairMeasurement, hg]
    rw [h1]
    refine deterministicMeasurement_effect_eq_zero_of_ne ?_
    rintro rfl
    simp [validPauliAnswer] at ha

/-- The honest Magic Square measurement assigns the zero effect to every answer
that is not the one prescribed by its Magic Square question type; part of the
constructor-shape rejection clause of `def:pauli-win-predicate`. -/
theorem honestMagicMeasurement_effect_eq_zero (P : AdmissibleParams)
    (s : MsType) (z : PauliSpace P) {a : PauliAnswer P}
    (ha : validPauliAnswer (.ms s) a = false) :
    (honestMagicMeasurement P s z).effect a = 0 := by
  classical
  cases s with
  | constraint i =>
      by_cases hg : pauliPairGamma P z = 0
      · have h1 : honestMagicMeasurement P (.constraint i) z =
            deterministicMeasurement (V := HonestIndex P)
              (PauliAnswer.msTriple 0 : PauliAnswer P) := by
          simp [honestMagicMeasurement, hg]
        rw [h1]
        refine deterministicMeasurement_effect_eq_zero_of_ne ?_
        rintro rfl
        simp [validPauliAnswer] at ha
      · have h1 : honestMagicMeasurement P (.constraint i) z =
            (pauliMagicMeasurement P z hg (.constraint i)).postprocess
              (pauliAnswerOfMs (P := P)) := by
          simp [honestMagicMeasurement, hg]
        rw [h1, Measurement.postprocess_effect]
        refine Finset.sum_eq_zero fun c hc => ?_
        have hca : pauliAnswerOfMs c = a := (Finset.mem_filter.mp hc).2
        cases c with
        | triple β =>
            exact absurd ha (by rw [← hca]; simp [pauliAnswerOfMs, validPauliAnswer])
        | bit β =>
            refine msStrategyMeasurement_constraint_zero _ _ _ i ?_
            rintro ⟨ab, hab⟩
            exact MsAnswer.noConfusion hab
  | var j =>
      by_cases hg : pauliPairGamma P z = 0
      · have h1 : honestMagicMeasurement P (.var j) z =
            deterministicMeasurement (V := HonestIndex P)
              (PauliAnswer.bit 0 : PauliAnswer P) := by
          simp [honestMagicMeasurement, hg]
        rw [h1]
        refine deterministicMeasurement_effect_eq_zero_of_ne ?_
        rintro rfl
        simp [validPauliAnswer] at ha
      · have h1 : honestMagicMeasurement P (.var j) z =
            (pauliMagicMeasurement P z hg (.var j)).postprocess
              (pauliAnswerOfMs (P := P)) := by
          simp [honestMagicMeasurement, hg]
        rw [h1, Measurement.postprocess_effect]
        refine Finset.sum_eq_zero fun c hc => ?_
        have hca : pauliAnswerOfMs c = a := (Finset.mem_filter.mp hc).2
        cases c with
        | triple β =>
            refine msStrategyMeasurement_var_zero _ _ _ j ?_
            rintro ⟨b, hb⟩
            exact MsAnswer.noConfusion hb
        | bit β =>
            exact absurd ha (by rw [← hca]; simp [pauliAnswerOfMs, validPauliAnswer])

/-- The honest measurement family assigns the zero effect to every answer whose
constructor is not the one prescribed by its question type; this is the
constructor-shape rejection clause of `def:pauli-win-predicate`, blueprint
`blueprint/src/chapter/ch13_qpbt_test.tex:410-449`. -/
theorem honestMeasurement_effect_eq_zero_of_invalid (P : AdmissibleParams)
    (t : PauliType) (z : PauliSpace P) {a : PauliAnswer P}
    (ha : validPauliAnswer t a = false) :
    (honestMeasurement P t z).effect a = 0 := by
  cases t with
  | point W => exact honestPointMeasurement_effect_eq_zero P W z ha
  | aline W => exact honestALineMeasurement_effect_eq_zero P W z ha
  | dline W => exact honestDLineMeasurement_effect_eq_zero P W z ha
  | pauli W => exact honestPauliMeasurement_effect_eq_zero P W ha
  | pairW W => exact honestPairWMeasurement_effect_eq_zero P W z ha
  | pair => exact honestPairMeasurement_effect_eq_zero P z ha
  | ms s => exact honestMagicMeasurement_effect_eq_zero P s z ha

/-! ### Coordinate invariants of the typed Pauli conditionally linear maps -/

/-- Reading the low-degree register back from its embedding in the
basis-selected Pauli blocks returns the original vector; this is the coordinate
bookkeeping of `def:pauli-question-distribution`. -/
theorem pauliToLd_embedLd (P : AdmissibleParams) (W : PauliKind)
    (u : LdSpace P.toLdParams) : pauliToLd P W (embedLd P W u) = u := by
  funext i
  cases W <;> rcases i with (j | ⟨⟩) | j <;> rfl

/-- The point block of a Point/W question is the point block of the ambient
coefficient vector; `def:pauli-question-distribution`. -/
theorem pauliPointBlock_pauliCL_point (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) :
    pauliPointBlock W (pauliCL P (.point W) z) = pauliPointBlock W z := by
  cases W <;> rfl

/-- The point block is preserved by the shared projection of the Pair, Pair/W
and Magic Square question types; `def:pauli-question-distribution`. -/
theorem pauliPointBlock_pauliSharedProjection (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) :
    pauliPointBlock W (pauliSharedProjection z) = pauliPointBlock W z := by
  cases W <;> rfl

/-- The axis-line conditionally linear map of `def:ld-question-distribution` is
idempotent. -/
theorem ldALineCL_idempotent (L : LdParams) (w : LdSpace L) :
    ldALineCL L (ldALineCL L w) = ldALineCL L w := by
  funext i
  rcases i with (j | ⟨⟩) | j
  · exact congrFun (lineRepMap_apply_self
      (coordinateDirection (chiIndex L w.seed)) w.point) j
  · rfl
  · rfl

/-- The diagonal-line conditionally linear map of `def:ld-question-distribution`
is idempotent. -/
theorem ldDLineCL_idempotent (L : LdParams) (w : LdSpace L) :
    ldDLineCL L (ldDLineCL L w) = ldDLineCL L w := by
  funext i
  rcases i with (j | ⟨⟩) | j
  · show (lineRepMap (prefixProjection (chiIndex L w.seed)
        (prefixProjection (chiIndex L w.seed) w.direction))
          (lineRepMap (prefixProjection (chiIndex L w.seed) w.direction) w.point)) j =
      (lineRepMap (prefixProjection (chiIndex L w.seed) w.direction) w.point) j
    rw [prefixProjection_idempotent]
    exact congrFun (lineRepMap_apply_self _ _) j
  · rfl
  · show prefixProjection (chiIndex L w.seed)
        (prefixProjection (chiIndex L w.seed) w.direction) j =
      prefixProjection (chiIndex L w.seed) w.direction j
    rw [prefixProjection_idempotent]

/-- The low-degree register carried by an Axis-line/W question is already fixed
by the axis-line conditionally linear map; `def:pauli-question-distribution`. -/
theorem ldALineCL_pauliToLd_pauliCL_aline (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) :
    ldALineCL P.toLdParams (pauliToLd P W (pauliCL P (.aline W) z)) =
      ldALineCL P.toLdParams (pauliToLd P W z) := by
  rw [show pauliToLd P W (pauliCL P (.aline W) z) =
      ldALineCL P.toLdParams (pauliToLd P W z) from pauliToLd_embedLd P W _,
    ldALineCL_idempotent]

/-- The low-degree register carried by a Diagonal-line/W question is already
fixed by the diagonal-line conditionally linear map;
`def:pauli-question-distribution`. -/
theorem ldDLineCL_pauliToLd_pauliCL_dline (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) :
    ldDLineCL P.toLdParams (pauliToLd P W (pauliCL P (.dline W) z)) =
      ldDLineCL P.toLdParams (pauliToLd P W z) := by
  rw [show pauliToLd P W (pauliCL P (.dline W) z) =
      ldDLineCL P.toLdParams (pauliToLd P W z) from pauliToLd_embedLd P W _,
    ldDLineCL_idempotent]

/-- The base of the canonical axis-line description of an Axis-line/W question
is the point block carried by that question;
`def:pauli-question-distribution`. -/
theorem aLineDescOf_base_eq (P : AdmissibleParams) (W : PauliKind) (z : PauliSpace P) :
    (aLineDescOf P.toLdParams
        (ldALineCL P.toLdParams (pauliToLd P W z))).base =
      pauliPointBlock W (pauliCL P (.aline W) z) := by
  cases W <;> exact lineRepMap_apply_self _ _

/-- The direction of the canonical axis-line description of an Axis-line/W
question is the coordinate direction selected by the scalar block of that
question; `def:pauli-question-distribution`. -/
theorem aLineDescOf_direction_eq (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) :
    (aLineDescOf P.toLdParams
        (ldALineCL P.toLdParams (pauliToLd P W z))).direction =
      coordinateDirection
        (chiIndex P.toLdParams (pauliScalarBlock (pauliCL P (.aline W) z))) := by
  cases W <;> rfl

/-- The direction of the canonical diagonal-line description of a
Diagonal-line/W question is the direction block carried by that question;
`def:pauli-question-distribution`. -/
theorem dLineDescOf_direction_eq (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) :
    (dLineDescOf P.toLdParams
        (ldDLineCL P.toLdParams (pauliToLd P W z))).direction =
      pauliDirectionBlock (pauliCL P (.dline W) z) := by
  exact prefixProjection_idempotent _ _

/-- The point block of a Diagonal-line/W question is the point coordinate of
the diagonal-line conditionally linear image; `def:pauli-question-distribution`. -/
theorem pauliPointBlock_pauliCL_dline (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) :
    pauliPointBlock W (pauliCL P (.dline W) z) =
      (ldDLineCL P.toLdParams (pauliToLd P W z)).point := by
  cases W <;> rfl

/-- The base of the canonical diagonal-line description of a Diagonal-line/W
question is the point block carried by that question;
`def:pauli-question-distribution`. -/
theorem dLineDescOf_base_eq (P : AdmissibleParams) (W : PauliKind) (z : PauliSpace P) :
    (dLineDescOf P.toLdParams
        (ldDLineCL P.toLdParams (pauliToLd P W z))).base =
      pauliPointBlock W (pauliCL P (.dline W) z) := by
  rw [pauliPointBlock_pauliCL_dline]
  show lineRepMap (prefixProjection (chiIndex P.toLdParams (pauliToLd P W z).seed)
        (prefixProjection (chiIndex P.toLdParams (pauliToLd P W z).seed)
          (pauliToLd P W z).direction))
        (lineRepMap (prefixProjection (chiIndex P.toLdParams (pauliToLd P W z).seed)
          (pauliToLd P W z).direction) (pauliToLd P W z).point) =
      lineRepMap (prefixProjection (chiIndex P.toLdParams (pauliToLd P W z).seed)
        (pauliToLd P W z).direction) (pauliToLd P W z).point
  rw [prefixProjection_idempotent]
  exact lineRepMap_apply_self _ _

/-! ### The honest measurements as coarse-grainings of one Pauli basis -/

/-- The honest Point/W measurement at a sampled Point/W question reports the
value of the low-degree encoding of the measured Pauli label at the point block
of the ambient vector. -/
theorem honestMeasurement_point_eq (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) :
    honestMeasurement P (.point W) (pauliCL P (.point W) z) =
      placedPauliMeasurement (pauliBasisMeasurement W)
        (fun h => PauliAnswer.value (lowDegreeEnc h (pauliPointBlock W z))) := by
  have h1 : honestMeasurement P (.point W) (pauliCL P (.point W) z) =
      placedPauliMeasurement (pauliBasisMeasurement W)
        (fun h => PauliAnswer.value
          (lowDegreeEnc h (pauliPointBlock W (pauliCL P (.point W) z)))) :=
    placedPauliMeasurement_postprocess_eq (pauliBasisMeasurement W)
      (fun h => lowDegreeEnc h (pauliPointBlock W (pauliCL P (.point W) z)))
      (fun a => PauliAnswer.value a)
  rw [h1, pauliPointBlock_pauliCL_point]

/-- The honest Axis-line/W measurement at a sampled Axis-line/W question reports
the degree-`d` restriction to the canonical line of the ambient vector. -/
theorem honestMeasurement_aline_eq (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) :
    honestMeasurement P (.aline W) (pauliCL P (.aline W) z) =
      placedPauliMeasurement (pauliBasisMeasurement W)
        (fun h => PauliAnswer.alinePoly (restrictToAxisLine P.toLdParams
          (aLineDescOf P.toLdParams (ldALineCL P.toLdParams (pauliToLd P W z)))
          (lowDegreeEncoding h))) := by
  have h1 : honestMeasurement P (.aline W) (pauliCL P (.aline W) z) =
      placedPauliMeasurement (pauliBasisMeasurement W)
        (fun h => PauliAnswer.alinePoly (restrictToAxisLine P.toLdParams
          (aLineDescOf P.toLdParams (ldALineCL P.toLdParams
            (pauliToLd P W (pauliCL P (.aline W) z))))
          (lowDegreeEncoding h))) :=
    placedPauliMeasurement_postprocess_eq (pauliBasisMeasurement W)
      (fun h => restrictToAxisLine P.toLdParams
        (aLineDescOf P.toLdParams (ldALineCL P.toLdParams
          (pauliToLd P W (pauliCL P (.aline W) z)))) (lowDegreeEncoding h))
      (fun a => PauliAnswer.alinePoly a)
  rw [h1, ldALineCL_pauliToLd_pauliCL_aline]

/-- The honest Diagonal-line/W measurement at a sampled Diagonal-line/W question
reports the degree-`m d` restriction to the canonical line of the ambient
vector. -/
theorem honestMeasurement_dline_eq (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) :
    honestMeasurement P (.dline W) (pauliCL P (.dline W) z) =
      placedPauliMeasurement (pauliBasisMeasurement W)
        (fun h => PauliAnswer.dlinePoly (restrictToLine P.toLdParams
          (dLineDescOf P.toLdParams (ldDLineCL P.toLdParams (pauliToLd P W z)))
          (lowDegreeEncoding h))) := by
  have h1 : honestMeasurement P (.dline W) (pauliCL P (.dline W) z) =
      placedPauliMeasurement (pauliBasisMeasurement W)
        (fun h => PauliAnswer.dlinePoly (restrictToLine P.toLdParams
          (dLineDescOf P.toLdParams (ldDLineCL P.toLdParams
            (pauliToLd P W (pauliCL P (.dline W) z))))
          (lowDegreeEncoding h))) :=
    placedPauliMeasurement_postprocess_eq (pauliBasisMeasurement W)
      (fun h => restrictToLine P.toLdParams
        (dLineDescOf P.toLdParams (ldDLineCL P.toLdParams
          (pauliToLd P W (pauliCL P (.dline W) z)))) (lowDegreeEncoding h))
      (fun a => PauliAnswer.dlinePoly a)
  rw [h1, ldDLineCL_pauliToLd_pauliCL_dline]

/-- The honest Pauli/W measurement reports the measured Pauli label itself. -/
theorem honestMeasurement_pauli_eq (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) :
    honestMeasurement P (.pauli W) (pauliCL P (.pauli W) z) =
      placedPauliMeasurement (pauliBasisMeasurement W)
        (fun h => PauliAnswer.pauliOutcome h) := rfl

/-- The honest Pair/X measurement at a sampled Pair/X question reports the
binary trace of the low-degree encoding of the measured Pauli label. -/
theorem honestMeasurement_pairW_X_eq (P : AdmissibleParams) (z : PauliSpace P) :
    honestMeasurement P (.pairW .X) (pauliCL P (.pairW .X) z) =
      placedPauliMeasurement (pauliBasisMeasurement .X)
        (fun h => PauliAnswer.bit
          (pauliTraceBit P (pauliXBlock z) (pauliRXBlock z) h)) :=
  placedPauliMeasurement_postprocess_eq _ _ _

/-- The honest Pair/Z measurement at a sampled Pair/Z question reports the
binary trace of the low-degree encoding of the measured Pauli label. -/
theorem honestMeasurement_pairW_Z_eq (P : AdmissibleParams) (z : PauliSpace P) :
    honestMeasurement P (.pairW .Z) (pauliCL P (.pairW .Z) z) =
      placedPauliMeasurement (pauliBasisMeasurement .Z)
        (fun h => PauliAnswer.bit
          (pauliTraceBit P (pauliZBlock z) (pauliRZBlock z) h)) :=
  placedPauliMeasurement_postprocess_eq _ _ _

/-- Two honest measurements coarse-graining one Pauli basis measurement have
zero operator product at every rejected answer pair, because a single Pauli
label produces an accepted pair. -/
theorem placedBasis_rejected_mul (P : AdmissibleParams) (W : PauliKind)
    (x y : PauliQuestion P) (f g : PauliRegister P → PauliAnswer P)
    (hacc : ∀ h : PauliRegister P, pauliWinPredicate P x y (f h) (g h) = true)
    (a b : PauliAnswer P) (hrej : pauliWinPredicate P x y a b = false) :
    (placedPauliMeasurement (pauliBasisMeasurement W) f).effect a *
      (placedPauliMeasurement (pauliBasisMeasurement W) g).effect b = 0 := by
  refine placedPauliMeasurement_mul_eq_zero_of_incompatible _
    (fun h => pauliProj_isProj W h) f g a b ?_
  intro h h1 h2
  rw [← h1, ← h2, hacc h] at hrej
  exact Bool.noConfusion hrej

/-! ### The consistency clauses along the incidence forms -/

/-- The honest Axis-line/W answer evaluates, at every line parameter of the
sampled point, to the honest Point/W value; this is the axis-line clause of
`def:pauli-win-predicate`. -/
theorem honest_alinePointCondition (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) (h : PauliRegister P) :
    pauliAlinePointCondition P W (pauliCL P (.aline W) z) (pauliCL P (.point W) z)
      (restrictToAxisLine P.toLdParams
        (aLineDescOf P.toLdParams (ldALineCL P.toLdParams (pauliToLd P W z)))
        (lowDegreeEncoding h))
      (lowDegreeEnc h (pauliPointBlock W z)) := by
  intro t ht
  rw [pauliPointBlock_pauliCL_point] at ht
  have hkey := evalCoefficient_restrictToAxisLine_lowDegreeEncoding P.toLdParams
    (aLineDescOf P.toLdParams (ldALineCL P.toLdParams (pauliToLd P W z))) rfl h t
  rw [aLineDescOf_base_eq, aLineDescOf_direction_eq] at hkey
  rw [ht]
  exact hkey

/-- The honest Diagonal-line/W answer evaluates, at every line parameter of the
sampled point, to the honest Point/W value; this is the diagonal-line clause of
`def:pauli-win-predicate`. -/
theorem honest_dlinePointCondition (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) (h : PauliRegister P) :
    pauliDlinePointCondition P W (pauliCL P (.dline W) z) (pauliCL P (.point W) z)
      (restrictToLine P.toLdParams
        (dLineDescOf P.toLdParams (ldDLineCL P.toLdParams (pauliToLd P W z)))
        (lowDegreeEncoding h))
      (lowDegreeEnc h (pauliPointBlock W z)) := by
  intro t ht
  rw [pauliPointBlock_pauliCL_point] at ht
  have hkey := evalCoefficient_restrictToLine P.toLdParams
    (dLineDescOf P.toLdParams (ldDLineCL P.toLdParams (pauliToLd P W z)))
    (lowDegreeEncoding h)
    (polynomialOnLine_lowDegreeEncoding_natDegree_le P.toLdParams _ h) t
  have hkey2 := eval_polynomialOnLine P.toLdParams
    (dLineDescOf P.toLdParams (ldDLineCL P.toLdParams (pauliToLd P W z)))
    (lowDegreeEncoding h) t
  rw [dLineDescOf_base_eq, dLineDescOf_direction_eq] at hkey2
  rw [ht]
  exact hkey.trans hkey2

end

end MIPStarRE.QPBT
