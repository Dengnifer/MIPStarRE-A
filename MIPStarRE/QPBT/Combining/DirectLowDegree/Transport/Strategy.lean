import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.SeedFiber

/-!
# Strategy transport for the directly indexed low-degree game

This module reads one coordinate of a projective directly indexed strategy as
a two-space mature low individual degree strategy.  Canonical line
representatives and answer reparametrization establish all four covariance
conditions.  It also records exact Born-weight formulas for both directions
of strategy transport.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-458`
- `references/ldt-paper/test_definition.tex:98-151`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.Quantum

noncomputable section

/-! ## Canonical line rebasing for the mature LDT interface -/

/-- A point differs from its canonical representative by a scalar multiple of
the line direction. -/
theorem mem_linePoints_direct_lineRepMap
    {K : Type*} [Field K] {m : ℕ} (v u : Fin m → K) :
    u ∈ linePoints (lineRepMap v u) v := by
  let W : Submodule K (Fin m → K) := Submodule.span K ({v} : Set (Fin m → K))
  let T : Submodule K (Fin m → K) :=
    registerSubmodule K (canonicalComplement W)
  have hdiff : u - lineRepMap v u ∈ W := by
    simpa [lineRepMap, canonicalProjOfKernel, W, T, LinearMap.comp_apply] using
      (Submodule.sub_projection_mem
        (isCompl_registerSubmodule_canonicalComplement W).symm u)
  rcases Submodule.mem_span_singleton.mp hdiff with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  rw [ht]
  abel

/-- A chosen affine parameter expressing a point relative to its canonical
line representative. -/
noncomputable def directLineRepParameter
    {K : Type*} [Field K] {m : ℕ} (v u : Fin m → K) : K :=
  Classical.choose (mem_linePoints_direct_lineRepMap v u)

/-- The chosen canonical rebase parameter reconstructs the original point. -/
theorem directLineRepParameter_spec
    {K : Type*} [Field K] {m : ℕ} (v u : Fin m → K) :
    u = lineRepMap v u + directLineRepParameter v u • v :=
  Classical.choose_spec (mem_linePoints_direct_lineRepMap v u)

/-- Canonical line representatives are unchanged by translation along their
direction. -/
theorem lineRepMap_add_smul
    {K : Type*} [Field K] {m : ℕ}
    (v u : Fin m → K) (t : K) :
    lineRepMap v (u + t • v) = lineRepMap v u := by
  let W : Submodule K (Fin m → K) := Submodule.span K ({v} : Set (Fin m → K))
  have hv : v ∈ W := Submodule.subset_span (Set.mem_singleton v)
  have hzero : lineRepMap v v = 0 := by
    simp [lineRepMap, canonicalProjOfKernel, W, LinearMap.comp_apply,
      Submodule.projectionOnto_apply_of_mem_right
        (isCompl_registerSubmodule_canonicalComplement W).symm hv]
  simp [map_add, map_smul, hzero]

/-- For a nonzero direction, the canonical rebase parameter is unique. -/
theorem directLineRepParameter_eq_of_nonzero
    {K : Type*} [Field K] {m : ℕ}
    {v u : Fin m → K} (hv : v ≠ 0) {t : K}
    (ht : u = lineRepMap v u + t • v) :
    directLineRepParameter v u = t := by
  have hfun : directLineRepParameter v u • v = t • v := by
    apply add_left_cancel (a := lineRepMap v u)
    exact (directLineRepParameter_spec v u).symm.trans ht
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    apply hv
    funext i
    simpa using not_exists.mp h i
  have hcoord := congrFun hfun i
  simp only [Pi.smul_apply, smul_eq_mul] at hcoord
  exact mul_right_cancel₀ hi hcoord

/-- Translating a point on a nonzero line adds the translation to its
canonical rebase parameter. -/
theorem directLineRepParameter_add_smul
    {K : Type*} [Field K] {m : ℕ}
    {v u : Fin m → K} (hv : v ≠ 0) (t : K) :
    directLineRepParameter v (u + t • v) =
      directLineRepParameter v u + t := by
  apply directLineRepParameter_eq_of_nonzero hv
  rw [lineRepMap_add_smul]
  calc
    u + t • v =
        (lineRepMap v u + directLineRepParameter v u • v) + t • v := by
      rw [← directLineRepParameter_spec v u]
    _ = lineRepMap v u + (directLineRepParameter v u + t) • v := by
      module

/-- Decode a mature LDT point into the fixed direct scalar field. -/
abbrev ldtPointToDirect (D : DirectLdParams) :
    Point D.toLDTParameters → Fin D.m → DirectScalarQ D :=
  (directPointEquiv D).symm

/-- The direct canonical axis question represented by a mature axis line. -/
noncomputable def directAxisQuestionOf (D : DirectLdParams)
    (line : AxisParallelLine D.toLDTParameters) : DirectLdQuestion D :=
  let u := ldtPointToDirect D line.base
  let v : Fin D.m → DirectScalarQ D := coordinateDirection line.direction
  (.aline, ⟨lineRepMap v u, line.direction, 0⟩)

/-- The direct canonical diagonal question represented by a mature diagonal
line.  The first direct index is valid for every direction. -/
noncomputable def directDiagonalQuestionOf (D : DirectLdParams)
    (line : DiagonalLine D.toLDTParameters) : DirectLdQuestion D :=
  let u := ldtPointToDirect D line.base
  let v := ldtPointToDirect D line.direction
  (.dline, ⟨lineRepMap v u, D.firstIndex, v⟩)

/-- The direct point question represented by a mature LDT point. -/
noncomputable def directPointQuestionOf (D : DirectLdParams)
    (u : Point D.toLDTParameters) : DirectLdQuestion D :=
  directLdPointQuestionOf D (ldtPointToDirect D u)

/-- Decoding an axis-line rebase is translation by the decoded scalar along
the corresponding direct coordinate direction. -/
theorem ldtPointToDirect_axis_rebase (D : DirectLdParams)
    (line : AxisParallelLine D.toLDTParameters)
    (t : Fq D.toLDTParameters) :
    letI := D.toLDTFieldModel
    ldtPointToDirect D (line.rebaseAt t).base =
      ldtPointToDirect D line.base +
        (directScalarEquiv D).symm t •
          coordinateDirection line.direction := by
  letI := D.toLDTFieldModel
  funext i
  simp only [ldtPointToDirect, directPointEquiv_symm_apply,
    AxisParallelLine.rebaseAt, AxisParallelLine.pointAt, Pi.add_apply,
    Pi.smul_apply]
  by_cases hi : i = line.direction
  · subst i
    simp only [coordinateDirection, if_pos, smul_eq_mul]
    rw [Pi.single_eq_same, mul_one]
    exact (FieldModel.equiv (q := D.q)).symm_apply_apply _
  · simp [hi, coordinateDirection]

/-- Decoding a diagonal-line rebase is translation by the decoded scalar
along the decoded direct direction. -/
theorem ldtPointToDirect_diagonal_rebase (D : DirectLdParams)
    (line : DiagonalLine D.toLDTParameters)
    (t : Fq D.toLDTParameters) :
    letI := D.toLDTFieldModel
    ldtPointToDirect D (line.rebaseAt t).base =
      ldtPointToDirect D line.base +
        (directScalarEquiv D).symm t • ldtPointToDirect D line.direction := by
  letI := D.toLDTFieldModel
  funext i
  change decodeScalar
      (addCoord (line.base i) (mulCoord t (line.direction i))) =
    decodeScalar (line.base i) + decodeScalar t * decodeScalar (line.direction i)
  simp [addCoord, mulCoord]

/-- Canonical direct axis questions do not depend on the chosen base point of
the mature line. -/
theorem directAxisQuestionOf_rebase (D : DirectLdParams)
    (line : AxisParallelLine D.toLDTParameters)
    (t : Fq D.toLDTParameters) :
    letI := D.toLDTFieldModel
    directAxisQuestionOf D (line.rebaseAt t) = directAxisQuestionOf D line := by
  letI := D.toLDTFieldModel
  simp only [directAxisQuestionOf, AxisParallelLine.rebaseAt_direction]
  rw [ldtPointToDirect_axis_rebase, lineRepMap_add_smul]

/-- Canonical direct diagonal questions do not depend on the chosen base point
of the mature line. -/
theorem directDiagonalQuestionOf_rebase (D : DirectLdParams)
    (line : DiagonalLine D.toLDTParameters)
    (t : Fq D.toLDTParameters) :
    letI := D.toLDTFieldModel
    directDiagonalQuestionOf D (line.rebaseAt t) =
      directDiagonalQuestionOf D line := by
  letI := D.toLDTFieldModel
  simp only [directDiagonalQuestionOf, DiagonalLine.rebaseAt]
  have hrebase := ldtPointToDirect_diagonal_rebase D line t
  change ldtPointToDirect D (line.pointAt t) =
      ldtPointToDirect D line.base +
        (directScalarEquiv D).symm t • ldtPointToDirect D line.direction at hrebase
  rw [hrebase, lineRepMap_add_smul]

/-- The fixed scalar coding transports field addition to mature coordinate
addition. -/
theorem directScalarEquiv_add (D : DirectLdParams)
    (x y : DirectScalarQ D) :
    letI := D.toLDTFieldModel
    directScalarEquiv D (x + y) =
      addCoord (directScalarEquiv D x) (directScalarEquiv D y) := by
  letI := D.toLDTFieldModel
  change FieldModel.equiv (x + y) =
    FieldModel.equiv
      (FieldModel.equiv.symm (FieldModel.equiv x) +
        FieldModel.equiv.symm (FieldModel.equiv y))
  rw [FieldModel.equiv.symm_apply_apply, FieldModel.equiv.symm_apply_apply]

private theorem coordinateDirection_ne_zero
    {K : Type*} [Field K] {m : ℕ} (i : Fin m) :
    (coordinateDirection i : Fin m → K) ≠ 0 := by
  intro h
  have hi := congrFun h i
  simp [coordinateDirection] at hi

/-- Canonical rebase parameter for a mature axis-parallel line. -/
noncomputable def directAxisRebaseParameter (D : DirectLdParams)
    (line : AxisParallelLine D.toLDTParameters) : DirectScalarQ D :=
  directLineRepParameter (coordinateDirection line.direction)
    (ldtPointToDirect D line.base)

/-- Canonical rebase parameter for a mature diagonal line. -/
noncomputable def directDiagonalRebaseParameter (D : DirectLdParams)
    (line : DiagonalLine D.toLDTParameters) : DirectScalarQ D :=
  directLineRepParameter (ldtPointToDirect D line.direction)
    (ldtPointToDirect D line.base)

/-- Axis-line canonical parameters add under mature rebasing. -/
theorem directAxisRebaseParameter_rebase (D : DirectLdParams)
    (line : AxisParallelLine D.toLDTParameters)
    (t : Fq D.toLDTParameters) :
    letI := D.toLDTFieldModel
    directAxisRebaseParameter D (line.rebaseAt t) =
      directAxisRebaseParameter D line + (directScalarEquiv D).symm t := by
  letI := D.toLDTFieldModel
  unfold directAxisRebaseParameter
  rw [ldtPointToDirect_axis_rebase]
  exact directLineRepParameter_add_smul
    (coordinateDirection_ne_zero line.direction) _

/-- Nonzero diagonal-line canonical parameters add under mature rebasing. -/
theorem directDiagonalRebaseParameter_rebase (D : DirectLdParams)
    (line : DiagonalLine D.toLDTParameters)
    (t : Fq D.toLDTParameters)
    (hdir : ldtPointToDirect D line.direction ≠ 0) :
    letI := D.toLDTFieldModel
    directDiagonalRebaseParameter D (line.rebaseAt t) =
      directDiagonalRebaseParameter D line + (directScalarEquiv D).symm t := by
  letI := D.toLDTFieldModel
  unfold directDiagonalRebaseParameter
  rw [ldtPointToDirect_diagonal_rebase]
  exact directLineRepParameter_add_smul hdir _

/-- Read one simultaneous coordinate from a direct point answer. -/
noncomputable def directPointAnswerReadout (D : DirectLdParams) (r : Fin D.k) :
    letI := D.toLDTFieldModel
    DirectLdAnswer D → Fq D.toLDTParameters := by
  letI := D.toLDTFieldModel
  intro answer
  exact match answer with
    | .pointVals a => directScalarEquiv D (a r)
    | .alinePolys _ => directScalarEquiv D 0
    | .dlinePolys _ => directScalarEquiv D 0

/-- Read one simultaneous coordinate from a direct axis-line answer and
rebase its polynomial from the canonical direct line to the mature line. -/
noncomputable def directAxisAnswerReadout (D : DirectLdParams) (r : Fin D.k)
    (line : AxisParallelLine D.toLDTParameters) :
    letI := D.toLDTFieldModel
    DirectLdAnswer D → AxisLinePolynomial D.toLDTParameters := by
  letI := D.toLDTFieldModel
  intro answer
  exact match answer with
    | .alinePolys a => AxisLinePolynomial.reparamAt
        (directAxisAnswerEquiv D (a r))
        (directScalarEquiv D (directAxisRebaseParameter D line))
    | .pointVals _ => default
    | .dlinePolys _ => default

/-- Read one simultaneous coordinate from a direct diagonal-line answer.  A
zero direction is a singleton geometric line, so it is sent to the
translation-fixed default polynomial; nonzero directions use canonical
rebasing. -/
noncomputable def directDiagonalAnswerReadout (D : DirectLdParams) (r : Fin D.k)
    (line : DiagonalLine D.toLDTParameters) :
    letI := D.toLDTFieldModel
    DirectLdAnswer D → DiagonalLinePolynomial D.toLDTParameters := by
  letI := D.toLDTFieldModel
  intro answer
  by_cases hdir : ldtPointToDirect D line.direction = 0
  · exact default
  · exact match answer with
    | .dlinePolys a => DiagonalLinePolynomial.reparamAt
        (directDiagonalAnswerEquiv D (a r))
        (directScalarEquiv D (directDiagonalRebaseParameter D line))
    | .pointVals _ => default
    | .alinePolys _ => default

/-- Axis answer readout is covariant under mature line rebasing. -/
theorem directAxisAnswerReadout_rebase (D : DirectLdParams) (r : Fin D.k)
    (line : AxisParallelLine D.toLDTParameters)
    (t : Fq D.toLDTParameters) (answer : DirectLdAnswer D) :
    letI := D.toLDTFieldModel
    directAxisAnswerReadout D r (line.rebaseAt t) answer =
      AxisLinePolynomial.reparamAt (directAxisAnswerReadout D r line answer) t := by
  letI := D.toLDTFieldModel
  cases answer with
  | pointVals a => simp [directAxisAnswerReadout]
  | dlinePolys a => simp [directAxisAnswerReadout]
  | alinePolys a =>
      simp only [directAxisAnswerReadout]
      rw [directAxisRebaseParameter_rebase, directScalarEquiv_add]
      rw [(directScalarEquiv D).apply_symm_apply]
      exact (AxisLinePolynomial.reparamAt_reparamAt
        (directAxisAnswerEquiv D (a r)) _ _).symm

/-- Diagonal answer readout is covariant under mature line rebasing, including
the singleton zero-direction convention. -/
theorem directDiagonalAnswerReadout_rebase (D : DirectLdParams) (r : Fin D.k)
    (line : DiagonalLine D.toLDTParameters)
    (t : Fq D.toLDTParameters) (answer : DirectLdAnswer D) :
    letI := D.toLDTFieldModel
    directDiagonalAnswerReadout D r (line.rebaseAt t) answer =
      DiagonalLinePolynomial.reparamAt
        (directDiagonalAnswerReadout D r line answer) t := by
  letI := D.toLDTFieldModel
  by_cases hdir : ldtPointToDirect D line.direction = 0
  · have hrebase : ldtPointToDirect D (line.rebaseAt t).direction = 0 := by
      simpa [DiagonalLine.rebaseAt] using hdir
    simp [directDiagonalAnswerReadout, hdir, hrebase]
  · have hrebase : ldtPointToDirect D (line.rebaseAt t).direction ≠ 0 := by
      simpa [DiagonalLine.rebaseAt] using hdir
    cases answer with
    | pointVals a =>
        simp [directDiagonalAnswerReadout, hdir, hrebase]
    | alinePolys a =>
        simp [directDiagonalAnswerReadout, hdir, hrebase]
    | dlinePolys a =>
        simp only [directDiagonalAnswerReadout, hdir, hrebase, dite_false]
        rw [directDiagonalRebaseParameter_rebase D line t hdir,
          directScalarEquiv_add, (directScalarEquiv D).apply_symm_apply]
        exact (DiagonalLinePolynomial.reparamAt_reparamAt
          (directDiagonalAnswerEquiv D (a r)) _ _).symm

/-! ## From a direct strategy to a mature LDT strategy -/

/-- Regard a matrix-valued projective measurement as a projective measurement
in the mature LDT interface. -/
noncomputable def matrixMeasurementToLDTProjMeas
    {alpha iota : Type*} [Fintype alpha] [Fintype iota] [DecidableEq iota]
    (M : MIPStarRE.Quantum.Measurement alpha iota)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) :
    MIPStarRE.LDT.ProjMeas alpha iota where
  toMeasurement := {
    toSubMeas := {
      outcome := M.effect
      total := 1
      outcome_pos := M.pos
      sum_eq_total := M.sum_eq_one
      total_le_one := le_rfl
    }
    total_eq_one := rfl
  }
  proj a := (hM a).isIdempotentElem.eq

@[simp] theorem matrixMeasurementToLDTProjMeas_outcome
    {alpha iota : Type*} [Fintype alpha] [Fintype iota] [DecidableEq iota]
    (M : MIPStarRE.Quantum.Measurement alpha iota)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) (a : alpha) :
    (matrixMeasurementToLDTProjMeas M hM).outcome a = M.effect a :=
  rfl

/-- Point measurements obtained by querying the direct strategy and reading
one simultaneous coordinate. -/
noncomputable def directCoordinatePointMeasurement
    (D : DirectLdParams) (r : Fin D.k)
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (M : DirectLdQuestion D →
      MIPStarRE.Quantum.Measurement (DirectLdAnswer D) iota)
    (hM : ∀ q, MIPStarRE.QPBT.Measurement.IsProjective (M q)) :
    letI := D.toLDTFieldModel
    IdxProjMeas (Point D.toLDTParameters) (Fq D.toLDTParameters) iota := by
  letI := D.toLDTFieldModel
  intro u
  exact ProjMeas.postprocess
    (matrixMeasurementToLDTProjMeas (M (directPointQuestionOf D u))
      (hM (directPointQuestionOf D u)))
    (directPointAnswerReadout D r)

/-- Axis-line measurements obtained by querying the canonical direct line and
rebasing one coordinate polynomial to the mature line parametrization. -/
noncomputable def directCoordinateAxisMeasurement
    (D : DirectLdParams) (r : Fin D.k)
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (M : DirectLdQuestion D →
      MIPStarRE.Quantum.Measurement (DirectLdAnswer D) iota)
    (hM : ∀ q, MIPStarRE.QPBT.Measurement.IsProjective (M q)) :
    letI := D.toLDTFieldModel
    IdxProjMeas (AxisParallelLine D.toLDTParameters)
      (AxisLinePolynomial D.toLDTParameters) iota := by
  letI := D.toLDTFieldModel
  intro line
  exact ProjMeas.postprocess
    (matrixMeasurementToLDTProjMeas (M (directAxisQuestionOf D line))
      (hM (directAxisQuestionOf D line)))
    (directAxisAnswerReadout D r line)

/-- Diagonal-line measurements obtained by querying the canonical direct line
and rebasing one coordinate polynomial to the mature line parametrization. -/
noncomputable def directCoordinateDiagonalMeasurement
    (D : DirectLdParams) (r : Fin D.k)
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (M : DirectLdQuestion D →
      MIPStarRE.Quantum.Measurement (DirectLdAnswer D) iota)
    (hM : ∀ q, MIPStarRE.QPBT.Measurement.IsProjective (M q)) :
    letI := D.toLDTFieldModel
    IdxProjMeas (DiagonalLine D.toLDTParameters)
      (DiagonalLinePolynomial D.toLDTParameters) iota := by
  letI := D.toLDTFieldModel
  intro line
  exact ProjMeas.postprocess
    (matrixMeasurementToLDTProjMeas (M (directDiagonalQuestionOf D line))
      (hM (directDiagonalQuestionOf D line)))
    (directDiagonalAnswerReadout D r line)

/-- The coordinate axis-line family is independent of the chosen affine
parametrization of a mature line. -/
theorem directCoordinateAxisMeasurement_reparam
    (D : DirectLdParams) (r : Fin D.k)
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (M : DirectLdQuestion D →
      MIPStarRE.Quantum.Measurement (DirectLdAnswer D) iota)
    (hM : ∀ q, MIPStarRE.QPBT.Measurement.IsProjective (M q)) :
    letI := D.toLDTFieldModel
    AxisParallelMeasurementReparamInvariant D.toLDTParameters
      (directCoordinateAxisMeasurement D r M hM) := by
  letI := D.toLDTFieldModel
  classical
  intro line t f
  simp only [directCoordinateAxisMeasurement, ProjMeas.postprocess,
    SubMeas.postprocess_outcome, matrixMeasurementToLDTProjMeas_outcome]
  rw [directAxisQuestionOf_rebase]
  have hfiber :
      Finset.univ.filter (fun answer =>
        directAxisAnswerReadout D r (line.rebaseAt t) answer =
          AxisLinePolynomial.reparamAt f t) =
        Finset.univ.filter (fun answer =>
          directAxisAnswerReadout D r line answer = f) := by
    ext answer
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [directAxisAnswerReadout_rebase]
    exact (AxisLinePolynomial.reparamAtEquiv t).injective.eq_iff
  rw [hfiber]

/-- The coordinate diagonal-line family is independent of the chosen affine
parametrization, including the zero-direction convention. -/
theorem directCoordinateDiagonalMeasurement_reparam
    (D : DirectLdParams) (r : Fin D.k)
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (M : DirectLdQuestion D →
      MIPStarRE.Quantum.Measurement (DirectLdAnswer D) iota)
    (hM : ∀ q, MIPStarRE.QPBT.Measurement.IsProjective (M q)) :
    letI := D.toLDTFieldModel
    DiagonalMeasurementReparamInvariant D.toLDTParameters
      (directCoordinateDiagonalMeasurement D r M hM) := by
  letI := D.toLDTFieldModel
  classical
  intro line t f
  simp only [directCoordinateDiagonalMeasurement, ProjMeas.postprocess,
    SubMeas.postprocess_outcome, matrixMeasurementToLDTProjMeas_outcome]
  rw [directDiagonalQuestionOf_rebase]
  have hfiber :
      Finset.univ.filter (fun answer =>
        directDiagonalAnswerReadout D r (line.rebaseAt t) answer =
          DiagonalLinePolynomial.reparamAt f t) =
        Finset.univ.filter (fun answer =>
          directDiagonalAnswerReadout D r line answer = f) := by
    ext answer
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [directDiagonalAnswerReadout_rebase]
    exact (DiagonalLinePolynomial.reparamAtEquiv t).injective.eq_iff
  rw [hfiber]

private theorem strategy_carrier_nonempty {G : Game} (S : Strategy G) :
    Nonempty (S.ιA × S.ιB) := by
  by_contra h
  rw [not_nonempty_iff] at h
  letI := h
  have hzero : S.ψ = 0 := Subsingleton.elim _ _
  have hnorm := S.ψ_norm
  rw [hzero, norm_zero] at hnorm
  exact zero_ne_one hnorm

/-- The pure LDT state represented by a game's unit strategy vector. -/
private noncomputable def strategyPureState {G : Game} (S : Strategy G)
    [Nonempty (S.ιA × S.ιB)] : PureState (S.ιA × S.ιB) where
  vector := S.ψ
  unit := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
      inner_self_eq_norm_sq_to_K, S.ψ_norm]
    norm_num

/-- The mature density-matrix state represented by a game's unit strategy
vector. -/
noncomputable def strategyQuantumState {G : Game} (S : Strategy G) :
    QuantumState (S.ιA × S.ιB) := by
  letI : Nonempty (S.ιA × S.ιB) := strategy_carrier_nonempty S
  exact PureState.toQuantumState (strategyPureState S)

/-- The density-matrix state associated with a game strategy is normalized. -/
theorem strategyQuantumState_isNormalized {G : Game} (S : Strategy G) :
    (strategyQuantumState S).IsNormalized := by
  letI : Nonempty (S.ιA × S.ιB) := strategy_carrier_nonempty S
  simpa [strategyQuantumState] using
    PureState.toQuantumState_isNormalized (strategyPureState S)

/-- The complex Born amplitude of a vector and two local effects. -/
noncomputable def vectorBornAmplitude
    {iotaA iotaB : Type*}
    [Fintype iotaA] [DecidableEq iotaA]
    [Fintype iotaB] [DecidableEq iotaB]
    (psi : EuclideanSpace ℂ (iotaA × iotaB))
    (A : Op iotaA) (B : Op iotaB) : ℂ :=
  inner ℂ psi (applyOperatorToState (heteroKron A B) psi)

/-- The real Born quadratic form of a vector and two local effects. -/
noncomputable def vectorBornWeight
    {iotaA iotaB : Type*}
    [Fintype iotaA] [DecidableEq iotaA]
    [Fintype iotaB] [DecidableEq iotaB]
    (psi : EuclideanSpace ℂ (iotaA × iotaB))
    (A : Op iotaA) (B : Op iotaB) : ℝ :=
  (vectorBornAmplitude psi A B).re

/-- Public outcome-level Born weight for a finite game strategy. -/
noncomputable def strategyBornWeight {G : Game} (S : Strategy G)
    (x : G.QuestionA) (y : G.QuestionB)
    (a : G.AnswerA) (b : G.AnswerB) : ℝ :=
  vectorBornWeight S.ψ ((S.A x).effect a) ((S.B y).effect b)

private theorem vectorBornAmplitude_add_left
    {iotaA iotaB : Type*}
    [Fintype iotaA] [DecidableEq iotaA]
    [Fintype iotaB] [DecidableEq iotaB]
    (psi : EuclideanSpace ℂ (iotaA × iotaB))
    (A₁ A₂ : Op iotaA) (B : Op iotaB) :
    vectorBornAmplitude psi (A₁ + A₂) B =
      vectorBornAmplitude psi A₁ B + vectorBornAmplitude psi A₂ B := by
  unfold vectorBornAmplitude applyOperatorToState heteroKron Matrix.kronecker
  rw [Matrix.add_kronecker]
  simp

private theorem vectorBornAmplitude_add_right
    {iotaA iotaB : Type*}
    [Fintype iotaA] [DecidableEq iotaA]
    [Fintype iotaB] [DecidableEq iotaB]
    (psi : EuclideanSpace ℂ (iotaA × iotaB))
    (A : Op iotaA) (B₁ B₂ : Op iotaB) :
    vectorBornAmplitude psi A (B₁ + B₂) =
      vectorBornAmplitude psi A B₁ + vectorBornAmplitude psi A B₂ := by
  unfold vectorBornAmplitude applyOperatorToState heteroKron Matrix.kronecker
  rw [Matrix.kronecker_add]
  simp

private theorem vectorBornAmplitude_zero_left
    {iotaA iotaB : Type*}
    [Fintype iotaA] [DecidableEq iotaA]
    [Fintype iotaB] [DecidableEq iotaB]
    (psi : EuclideanSpace ℂ (iotaA × iotaB)) (B : Op iotaB) :
    vectorBornAmplitude psi 0 B = 0 := by
  unfold vectorBornAmplitude applyOperatorToState heteroKron Matrix.kronecker
  rw [Matrix.zero_kronecker]
  simp

private theorem vectorBornAmplitude_zero_right
    {iotaA iotaB : Type*}
    [Fintype iotaA] [DecidableEq iotaA]
    [Fintype iotaB] [DecidableEq iotaB]
    (psi : EuclideanSpace ℂ (iotaA × iotaB)) (A : Op iotaA) :
    vectorBornAmplitude psi A 0 = 0 := by
  unfold vectorBornAmplitude applyOperatorToState heteroKron Matrix.kronecker
  rw [Matrix.kronecker_zero]
  simp

private theorem vectorBornWeight_add_left
    {iotaA iotaB : Type*}
    [Fintype iotaA] [DecidableEq iotaA]
    [Fintype iotaB] [DecidableEq iotaB]
    (psi : EuclideanSpace ℂ (iotaA × iotaB))
    (A₁ A₂ : Op iotaA) (B : Op iotaB) :
    vectorBornWeight psi (A₁ + A₂) B =
      vectorBornWeight psi A₁ B + vectorBornWeight psi A₂ B := by
  unfold vectorBornWeight
  rw [vectorBornAmplitude_add_left, Complex.add_re]

private theorem vectorBornWeight_add_right
    {iotaA iotaB : Type*}
    [Fintype iotaA] [DecidableEq iotaA]
    [Fintype iotaB] [DecidableEq iotaB]
    (psi : EuclideanSpace ℂ (iotaA × iotaB))
    (A : Op iotaA) (B₁ B₂ : Op iotaB) :
    vectorBornWeight psi A (B₁ + B₂) =
      vectorBornWeight psi A B₁ + vectorBornWeight psi A B₂ := by
  unfold vectorBornWeight
  rw [vectorBornAmplitude_add_right, Complex.add_re]

private theorem vectorBornWeight_finset_sum_left
    {alpha iotaA iotaB : Type*}
    [Fintype iotaA] [DecidableEq iotaA]
    [Fintype iotaB] [DecidableEq iotaB]
    (psi : EuclideanSpace ℂ (iotaA × iotaB))
    (s : Finset alpha) (A : alpha → Op iotaA) (B : Op iotaB) :
    vectorBornWeight psi (∑ a ∈ s, A a) B =
      ∑ a ∈ s, vectorBornWeight psi (A a) B := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [vectorBornWeight, vectorBornAmplitude_zero_left]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        vectorBornWeight_add_left, ih]

private theorem vectorBornWeight_finset_sum_right
    {beta iotaA iotaB : Type*}
    [Fintype iotaA] [DecidableEq iotaA]
    [Fintype iotaB] [DecidableEq iotaB]
    (psi : EuclideanSpace ℂ (iotaA × iotaB))
    (A : Op iotaA) (s : Finset beta) (B : beta → Op iotaB) :
    vectorBornWeight psi A (∑ b ∈ s, B b) =
      ∑ b ∈ s, vectorBornWeight psi A (B b) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [vectorBornWeight, vectorBornAmplitude_zero_right]
  | @insert b s hb ih =>
      rw [Finset.sum_insert hb, Finset.sum_insert hb,
        vectorBornWeight_add_right, ih]

/-- Expectations in the density state associated with a strategy agree with
the strategy's vector Born quadratic form. -/
theorem strategyQuantumState_ev_eq_vectorBornWeight
    {G : Game} (S : Strategy G) (A : Op S.ιA) (B : Op S.ιB) :
    ev (strategyQuantumState S) (opTensor A B) =
      vectorBornWeight S.ψ A B := by
  letI : Nonempty (S.ιA × S.ιB) := strategy_carrier_nonempty S
  rw [show strategyQuantumState S =
      PureState.toQuantumState (strategyPureState S) by
        simp [strategyQuantumState],
    PureState.ev_eq_re_inner]
  unfold vectorBornWeight vectorBornAmplitude applyOperatorToState heteroKron opTensor
  simp_rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (star S.ψ ⬝ᵥ
      (Matrix.kronecker A B *ᵥ S.ψ)).re =
    ((Matrix.kronecker A B *ᵥ S.ψ) ⬝ᵥ star S.ψ).re
  rw [dotProduct_comm]

/-- Postprocessing both local measurements gives the exact double sum of the
original Born weights over the two answer fibers. -/
theorem directPostprocessBornWeight
    (D : DirectLdParams) (S : Strategy (directLdGame D))
    (hS : S.IsProjective)
    {alpha beta : Type*} [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    (x y : DirectLdQuestion D)
    (readA : DirectLdAnswer D → alpha)
    (readB : DirectLdAnswer D → beta)
    (a : alpha) (b : beta) :
    ev (strategyQuantumState S)
        (opTensor
          ((ProjMeas.postprocess
            (matrixMeasurementToLDTProjMeas (S.A x) (hS.1 x)) readA).outcome a)
          ((ProjMeas.postprocess
            (matrixMeasurementToLDTProjMeas (S.B y) (hS.2 y)) readB).outcome b)) =
      ∑ directA ∈ Finset.univ.filter (fun answer => readA answer = a),
        ∑ directB ∈ Finset.univ.filter (fun answer => readB answer = b),
          strategyBornWeight S x y directA directB := by
  rw [strategyQuantumState_ev_eq_vectorBornWeight]
  simp only [ProjMeas.postprocess, SubMeas.postprocess_outcome,
    matrixMeasurementToLDTProjMeas_outcome]
  rw [vectorBornWeight_finset_sum_left]
  apply Finset.sum_congr rfl
  intro directA _
  rw [vectorBornWeight_finset_sum_right]
  rfl

/-- Correlated residue registers turn two block-diagonal effects into the
uniform average of their matching source-block Born weights. -/
private theorem seedFiberBlockBornAmplitude
    {G : Game} (S : Strategy G) (L : LdParams)
    (A : Fin (L.q / L.m) → Op S.ιA)
    (B : Fin (L.q / L.m) → Op S.ιB) :
    vectorBornAmplitude (seedFiberLiftedState S L)
        (Matrix.blockDiagonal A) (Matrix.blockDiagonal B) =
      (Fintype.card (Fin (L.q / L.m)) : ℂ)⁻¹ *
        ∑ residue, vectorBornAmplitude S.ψ (A residue) (B residue) := by
  classical
  letI : Nonempty (Fin (L.q / L.m)) :=
    Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  unfold vectorBornAmplitude applyOperatorToState heteroKron Matrix.kronecker
  simp_rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    dotProduct, Matrix.mulVec]
  simp_rw [← Finset.univ_product_univ, Finset.sum_product]
  simp [seedFiberLiftedState_apply, Matrix.blockDiagonal_apply,
    mul_assoc, mul_comm]
  ring_nf
  simp_rw [mul_assoc, ← Finset.mul_sum]
  ring_nf
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [← mul_assoc]
  congr 1
  rw [← pow_two, inv_pow, ← Complex.ofReal_pow,
    Real.sq_sqrt (Nat.cast_nonneg (L.q / L.m))]
  norm_cast
  exact Complex.ofReal_inv _

/-- Correlated residue registers give the uniform average of the source-block
Born weights. -/
private theorem seedFiberBlockBornWeight
    {G : Game} (S : Strategy G) (L : LdParams)
    (A : Fin (L.q / L.m) → Op S.ιA)
    (B : Fin (L.q / L.m) → Op S.ιB) :
    vectorBornWeight (seedFiberLiftedState S L)
        (Matrix.blockDiagonal A) (Matrix.blockDiagonal B) =
      (Fintype.card (Fin (L.q / L.m)) : ℝ)⁻¹ *
        ∑ residue, vectorBornWeight S.ψ (A residue) (B residue) := by
  unfold vectorBornWeight
  rw [seedFiberBlockBornAmplitude]
  simp [Complex.mul_re, Complex.inv_re, Complex.inv_im]

/-- The Born weight of the seed-bearing direct adapter is the uniform average
of the original seed-dependent Born weights over the correlated residue. -/
theorem ldStrategyToDirect_bornWeight
    (L : LdParams) (S : Strategy (ldGame L))
    (x y : DirectLdQuestion L.toDirectLdParams)
    (a b : DirectLdAnswer L.toDirectLdParams) :
    strategyBornWeight (ldStrategyToDirect L S) x y a b =
      (Fintype.card (Fin (L.q / L.m)) : ℝ)⁻¹ *
        ∑ residue,
          strategyBornWeight S
            (seededLdQuestion L x residue)
            (seededLdQuestion L y residue)
            ((ldDirectAnswerEquiv L).symm a)
            ((ldDirectAnswerEquiv L).symm b) := by
  change vectorBornWeight (seedFiberLiftedState S L)
      (Matrix.blockDiagonal fun residue =>
        (S.A (seededLdQuestion L x residue)).effect
          ((ldDirectAnswerEquiv L).symm a))
      (Matrix.blockDiagonal fun residue =>
        (S.B (seededLdQuestion L y residue)).effect
          ((ldDirectAnswerEquiv L).symm b)) = _
  exact seedFiberBlockBornWeight S L _ _

/-- Read coordinate `r` of a projective direct-game strategy as a two-space
projective strategy for the mature low individual degree interface. -/
noncomputable def directCoordinateProjStrat
    (D : DirectLdParams) (S : Strategy (directLdGame D))
    (hS : S.IsProjective) (r : Fin D.k) :
    letI := D.toLDTFieldModel
    ProjStrat D.toLDTParameters S.ιA S.ιB := by
  letI := D.toLDTFieldModel
  exact {
    state := strategyQuantumState S
    isNormalized := strategyQuantumState_isNormalized S
    pointMeasurementA := directCoordinatePointMeasurement D r S.A hS.1
    axisParallelMeasurementA := directCoordinateAxisMeasurement D r S.A hS.1
    axisParallelReparamInvariantA :=
      directCoordinateAxisMeasurement_reparam D r S.A hS.1
    diagonalMeasurementA := directCoordinateDiagonalMeasurement D r S.A hS.1
    diagonalReparamInvariantA :=
      directCoordinateDiagonalMeasurement_reparam D r S.A hS.1
    pointMeasurementB := directCoordinatePointMeasurement D r S.B hS.2
    axisParallelMeasurementB := directCoordinateAxisMeasurement D r S.B hS.2
    axisParallelReparamInvariantB :=
      directCoordinateAxisMeasurement_reparam D r S.B hS.2
    diagonalMeasurementB := directCoordinateDiagonalMeasurement D r S.B hS.2
    diagonalReparamInvariantB :=
      directCoordinateDiagonalMeasurement_reparam D r S.B hS.2
  }

/-- Point Born weights of the coordinate strategy are exactly the sums over
the corresponding direct-answer readout fibers. -/
theorem directCoordinateProjStrat_point_bornWeight
    (D : DirectLdParams) (S : Strategy (directLdGame D))
    (hS : S.IsProjective) (r : Fin D.k)
    (u v : Point D.toLDTParameters)
    (a b : Fq D.toLDTParameters) :
    letI := D.toLDTFieldModel
    ev (directCoordinateProjStrat D S hS r).state
        (opTensor
          (((directCoordinateProjStrat D S hS r).pointMeasurementA u).outcome a)
          (((directCoordinateProjStrat D S hS r).pointMeasurementB v).outcome b)) =
      ∑ directA ∈ Finset.univ.filter (fun answer =>
          directPointAnswerReadout D r answer = a),
        ∑ directB ∈ Finset.univ.filter (fun answer =>
            directPointAnswerReadout D r answer = b),
          strategyBornWeight S (directPointQuestionOf D u)
            (directPointQuestionOf D v) directA directB := by
  letI := D.toLDTFieldModel
  change ev (strategyQuantumState S)
      (opTensor
        ((ProjMeas.postprocess
          (matrixMeasurementToLDTProjMeas
            (S.A (directPointQuestionOf D u))
            (hS.1 (directPointQuestionOf D u)))
          (directPointAnswerReadout D r)).outcome a)
        ((ProjMeas.postprocess
          (matrixMeasurementToLDTProjMeas
            (S.B (directPointQuestionOf D v))
            (hS.2 (directPointQuestionOf D v)))
          (directPointAnswerReadout D r)).outcome b)) = _
  exact directPostprocessBornWeight D S hS
    (directPointQuestionOf D u) (directPointQuestionOf D v)
    (directPointAnswerReadout D r) (directPointAnswerReadout D r) a b

/-- Axis-line Born weights of the coordinate strategy are exactly the sums
over the corresponding rebased direct-answer fibers. -/
theorem directCoordinateProjStrat_axis_bornWeight
    (D : DirectLdParams) (S : Strategy (directLdGame D))
    (hS : S.IsProjective) (r : Fin D.k) :
    letI := D.toLDTFieldModel
    ∀ (lineA lineB : AxisParallelLine D.toLDTParameters)
      (f g : AxisLinePolynomial D.toLDTParameters),
    ev (directCoordinateProjStrat D S hS r).state
        (opTensor
          (((directCoordinateProjStrat D S hS r).axisParallelMeasurementA
            lineA).outcome f)
          (((directCoordinateProjStrat D S hS r).axisParallelMeasurementB
            lineB).outcome g)) =
      ∑ directA ∈ Finset.univ.filter (fun answer =>
          directAxisAnswerReadout D r lineA answer = f),
        ∑ directB ∈ Finset.univ.filter (fun answer =>
            directAxisAnswerReadout D r lineB answer = g),
          strategyBornWeight S (directAxisQuestionOf D lineA)
            (directAxisQuestionOf D lineB) directA directB := by
  letI := D.toLDTFieldModel
  classical
  intro lineA lineB f g
  change ev (strategyQuantumState S)
      (opTensor
        ((ProjMeas.postprocess
          (matrixMeasurementToLDTProjMeas
            (S.A (directAxisQuestionOf D lineA))
            (hS.1 (directAxisQuestionOf D lineA)))
          (directAxisAnswerReadout D r lineA)).outcome f)
        ((ProjMeas.postprocess
          (matrixMeasurementToLDTProjMeas
            (S.B (directAxisQuestionOf D lineB))
            (hS.2 (directAxisQuestionOf D lineB)))
          (directAxisAnswerReadout D r lineB)).outcome g)) = _
  exact directPostprocessBornWeight D S hS
    (directAxisQuestionOf D lineA) (directAxisQuestionOf D lineB)
    (directAxisAnswerReadout D r lineA)
    (directAxisAnswerReadout D r lineB) f g

open Classical in
/-- Diagonal-line Born weights of the coordinate strategy are exactly the
sums over the corresponding rebased direct-answer fibers. -/
theorem directCoordinateProjStrat_diagonal_bornWeight
    (D : DirectLdParams) (S : Strategy (directLdGame D))
    (hS : S.IsProjective) (r : Fin D.k) :
    letI := D.toLDTFieldModel
    ∀ (lineA lineB : DiagonalLine D.toLDTParameters)
      (f g : DiagonalLinePolynomial D.toLDTParameters),
    ev (directCoordinateProjStrat D S hS r).state
        (opTensor
          (((directCoordinateProjStrat D S hS r).diagonalMeasurementA
            lineA).outcome f)
          (((directCoordinateProjStrat D S hS r).diagonalMeasurementB
            lineB).outcome g)) =
      ∑ directA ∈ Finset.univ.filter (fun answer =>
          directDiagonalAnswerReadout D r lineA answer = f),
        ∑ directB ∈ Finset.univ.filter (fun answer =>
            directDiagonalAnswerReadout D r lineB answer = g),
          strategyBornWeight S (directDiagonalQuestionOf D lineA)
            (directDiagonalQuestionOf D lineB) directA directB := by
  letI := D.toLDTFieldModel
  classical
  intro lineA lineB f g
  change ev (strategyQuantumState S)
      (opTensor
        ((ProjMeas.postprocess
          (matrixMeasurementToLDTProjMeas
            (S.A (directDiagonalQuestionOf D lineA))
            (hS.1 (directDiagonalQuestionOf D lineA)))
          (directDiagonalAnswerReadout D r lineA)).outcome f)
        ((ProjMeas.postprocess
          (matrixMeasurementToLDTProjMeas
            (S.B (directDiagonalQuestionOf D lineB))
            (hS.2 (directDiagonalQuestionOf D lineB)))
          (directDiagonalAnswerReadout D r lineB)).outcome g)) = _
  exact directPostprocessBornWeight D S hS
    (directDiagonalQuestionOf D lineA) (directDiagonalQuestionOf D lineB)
    (directDiagonalAnswerReadout D r lineA)
    (directDiagonalAnswerReadout D r lineB) f g

end

end MIPStarRE.QPBT
