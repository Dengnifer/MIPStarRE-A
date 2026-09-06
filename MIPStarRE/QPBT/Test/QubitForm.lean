import MIPStarRE.QPBT.Algebra.PauliTheorems
import MIPStarRE.QPBT.Test.SoundnessDefs

/-!
# Qubit form of Pauli basis test soundness

The fixed self-dual normal basis converts the qudit EPR register and generalized
Pauli projectors into qubit coordinates. The conversion uses only the basis
stored in the canonical `FixedFieldModel`.

`PauliSoundnessWitness.toQubit` transports supplied existential data, and the
three `qubit_*_to_qubit` identities preserve its comparison quantities exactly.
These are Lean-only transport results, not soundness existence theorems. This
module does not import or use `pauli_soundness`; the source corollary remains open.

## References

The conversion is blueprint
`lem:pauli-binary`, from
`references/qpbt-paper/04_preliminaries.tex:1163-1208`. The resulting
statement is blueprint `cor:pauli-binary`,
from `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1450-1491`.
-/

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-- The bit register obtained by expanding every Pauli-register field element
in the basis stored by `P.model`. -/
abbrev QubitRegister (P : AdmissibleParams) :=
  Cube P.m × Fin P.model.basisDim → ZMod 2

/-- The ideal auxiliary state tensored with the qubit EPR register, in the
local-player ordering used by `cor:pauli-binary`. -/
noncomputable def idealQubitState (P : AdmissibleParams)
    {ιA' ιB' : Type*} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB']
    (aux : EuclideanSpace ℂ (ιA' × ιB')) :
    EuclideanSpace ℂ
      ((ιA' × QubitRegister P) × (ιB' × QubitRegister P)) :=
  (EuclideanSpace.equiv
      ((ιA' × QubitRegister P) × (ιB' × QubitRegister P)) ℂ).symm
    (fun p =>
      (EuclideanSpace.equiv (ιA' × ιB') ℂ aux (p.1.1, p.2.1)) *
        (EuclideanSpace.equiv (QubitRegister P × QubitRegister P) ℂ
          (eprState (QubitRegister P)) (p.1.2, p.2.2)))

/-- The local isometries, auxiliary spaces, and unit auxiliary state in
`cor:pauli-binary`; this structure introduces no hypothesis beyond the paper
theorem. -/
structure QubitSoundnessWitness (P : AdmissibleParams)
    (S : Strategy (pauliBasisTest P)) where
  ιA' : Type
  ιB' : Type
  [ιAFintype : Fintype ιA']
  [ιBFintype : Fintype ιB']
  [ιADecidableEq : DecidableEq ιA']
  [ιBDecidableEq : DecidableEq ιB']
  φA : EuclideanSpace ℂ S.ιA →ₗᵢ[ℂ]
    EuclideanSpace ℂ (ιA' × QubitRegister P)
  φB : EuclideanSpace ℂ S.ιB →ₗᵢ[ℂ]
    EuclideanSpace ℂ (ιB' × QubitRegister P)
  aux : EuclideanSpace ℂ (ιA' × ιB')
  aux_norm : ‖aux‖ = 1

attribute [instance] QubitSoundnessWitness.ιAFintype
  QubitSoundnessWitness.ιBFintype QubitSoundnessWitness.ιADecidableEq
  QubitSoundnessWitness.ιBDecidableEq

/-- Alice's ideal qubit projector placed on the joint target space. -/
noncomputable def qubitProjOnA'' (P : AdmissibleParams)
    {ιA' ιB' : Type*} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB'] (W : PauliKind)
    (u : PauliRegister P) :
    Op ((ιA' × QubitRegister P) × (ιB' × QubitRegister P)) :=
  fun p q =>
    if p.1.1 = q.1.1 ∧ p.2 = q.2 then
      qubitPauliProj W (kappaVec P.model u) p.1.2 q.1.2
    else 0

/-- Bob's ideal qubit projector placed on the joint target space. -/
noncomputable def qubitProjOnB'' (P : AdmissibleParams)
    {ιA' ιB' : Type*} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB'] (W : PauliKind)
    (u : PauliRegister P) :
    Op ((ιA' × QubitRegister P) × (ιB' × QubitRegister P)) :=
  fun p q =>
    if p.1 = q.1 ∧ p.2.1 = q.2.1 then
      qubitPauliProj W (kappaVec P.model u) p.2.2 q.2.2
    else 0

/-- Lift a conjugated Alice effect to the full qubit target space. -/
noncomputable def liftedQubitAEffect {P : AdmissibleParams} {G : Game}
    (S : Strategy G) {ιA' ιB' : Type*} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB']
    (φA : EuclideanSpace ℂ S.ιA →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ιA' × QubitRegister P))
    (M : Op S.ιA) :
    Op ((ιA' × QubitRegister P) × (ιB' × QubitRegister P)) :=
  heteroKron (conjIsometry φA M) 1

/-- Lift a conjugated Bob effect to the full qubit target space. -/
noncomputable def liftedQubitBEffect {P : AdmissibleParams} {G : Game}
    (S : Strategy G) {ιA' ιB' : Type*} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB']
    (φB : EuclideanSpace ℂ S.ιB →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ιB' × QubitRegister P))
    (M : Op S.ιB) :
    Op ((ιA' × QubitRegister P) × (ιB' × QubitRegister P)) :=
  heteroKron 1 (conjIsometry φB M)

/-- Alice's qubit-projector family distance in `cor:pauli-binary`. -/
noncomputable def qubitOperatorDistanceA
    (P : AdmissibleParams) (S : Strategy (pauliBasisTest P))
    (w : QubitSoundnessWitness P S) (W : PauliKind) : ℝ :=
  ∑ u : PauliRegister P,
    ‖applyOperatorToState
      (liftedQubitAEffect S w.φA
          (((S.A (pauliQuestion P W)).postprocess pauliAnswerOrZero).effect u) -
        qubitProjOnA'' P W u)
      (idealQubitState P w.aux)‖ ^ 2

/-- Bob's qubit-projector family distance in `cor:pauli-binary`. -/
noncomputable def qubitOperatorDistanceB
    (P : AdmissibleParams) (S : Strategy (pauliBasisTest P))
    (w : QubitSoundnessWitness P S) (W : PauliKind) : ℝ :=
  ∑ u : PauliRegister P,
    ‖applyOperatorToState
      (liftedQubitBEffect S w.φB
          (((S.B (pauliQuestion P W)).postprocess pauliAnswerOrZero).effect u) -
        qubitProjOnB'' P W u)
      (idealQubitState P w.aux)‖ ^ 2

namespace BinaryWitnessTransport

/-- The fixed binary coordinate equivalence on an arbitrary register index
type. This Lean-only construction implements the basis identification in the
proof of `lem:pauli-binary`, including the cube-indexed soundness register. -/
noncomputable def labelEquiv {q : ℕ} {ι : Type*} (F : FixedFieldModel q) :
    (ι → F.K) ≃ (ι × Fin F.basisDim → ZMod 2) :=
  (Equiv.piCongrRight (fun _ : ι => F.binaryCoordinates.toEquiv)).trans
    (Equiv.curry ι (Fin F.basisDim) (ZMod 2)).symm

/-- The coordinate equivalence evaluates to the existing fixed-basis map. -/
theorem label_equiv_apply {q : ℕ} {ι : Type*} (F : FixedFieldModel q)
    (label : ι → F.K) : labelEquiv F label = kappaVec F label := rfl

/-- Self-duality identifies the field trace pairing with the binary dot product
on all register coordinates, as in `eq:qudit-to-qubit-pauli-1`. -/
private theorem trace_pairing {q : ℕ} {ι : Type*} [Fintype ι]
    (F : FixedFieldModel q) (left right : ι → F.K) :
    binTrace F.K (dotProduct left right) =
      binTrace (ZMod 2) (dotProduct (labelEquiv F left) (kappaVec F right)) := by
  simp only [dotProduct, map_sum, binTrace_mul_eq_dotProduct F,
    Algebra.trace_self_apply, Fintype.sum_prod_type, labelEquiv,
    Equiv.trans_apply, Equiv.curry_symm_apply, kappaVec, basisCoordVec]
  rfl

/-- Coordinate expansion preserves addition at every register position. -/
private theorem label_equiv_add {q : ℕ} {ι : Type*} (F : FixedFieldModel q)
    (left right : ι → F.K) :
    labelEquiv F (left + right) = labelEquiv F left + labelEquiv F right := by
  ext position
  change F.binaryCoordinates (left position.1 + right position.1) position.2 =
    F.binaryCoordinates (left position.1) position.2 +
      F.binaryCoordinates (right position.1) position.2
  simp

/-- A tensor-product shift has the computational-basis entries of translation
by its complete register label. -/
private theorem shift_entry {K ι : Type*} [Field K] [DecidableEq K]
    [Algebra (ZMod 2) K] [Fintype ι] [DecidableEq ι]
    (label row col : ι → K) :
    tauObservable .X label row col = if row = col + label then 1 else 0 := by
  change (∏ position : ι,
    if row position = col position + label position then (1 : ℂ) else 0) = _
  rw [Fintype.prod_boole]
  simp only [← funext_iff, ← Pi.add_apply]

/-- A tensor-product phase is diagonal, with phase given by the trace pairing
of its label and the computational-basis coordinate. -/
private theorem phase_entry {K ι : Type*} [Field K] [DecidableEq K]
    [Algebra (ZMod 2) K] [Fintype ι] [DecidableEq ι]
    (label row col : ι → K) :
    tauObservable .Z label row col =
      if row = col then phaseSign (binTrace K (dotProduct label col)) else 0 := by
  change (∏ position : ι, if row position = col position then
    phaseSign (binTrace K (label position * col position)) else 0) = _
  rw [Fintype.prod_ite_zero, prod_phaseSign_binTrace_dotProduct]
  simp only [← funext_iff]

/-- Binary coordinates transport the shift and phase observables exactly.
This is the basis-state comparison in the proof of `lem:pauli-binary`. -/
private theorem observable_reindex {q : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (F : FixedFieldModel q)
    (W : PauliKind) (label : ι → F.K) :
    tauObservable W label =
      Matrix.reindex (labelEquiv F).symm (labelEquiv F).symm
        (tauObservable W (labelEquiv F label)) := by
  classical
  ext row col
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
  cases W with
  | X =>
      rw [shift_entry, shift_entry, ← label_equiv_add]
      simp only [Equiv.apply_eq_iff_eq]
  | Z =>
      rw [phase_entry, phase_entry]
      simp only [Equiv.apply_eq_iff_eq]
      rw [trace_pairing F]
      simp only [label_equiv_apply]

/-- Exact forward transport of a generalized Pauli projector to the existing
binary projector. This Lean-only arbitrary-index form of the calculation in
`lem:pauli-binary` uses self-duality and finite Fourier inversion, without a
soundness or projector-intertwining hypothesis. -/
theorem pauli_projector_reindex {q : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (F : FixedFieldModel q)
    (W : PauliKind) (label : ι → F.K) :
    Matrix.reindex (labelEquiv F) (labelEquiv F) (pauliProj W label) =
      qubitPauliProj W (kappaVec F label) := by
  classical
  have hinverse : pauliProj W label =
      Matrix.reindex (labelEquiv F).symm (labelEquiv F).symm
        (pauliProj W (kappaVec F label)) := by
    rw [pauliProj_eq_avg_tauObservable, pauliProj_eq_avg_tauObservable]
    ext row col
    simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
      Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
    rw [Fintype.card_congr (labelEquiv (ι := ι) F)]
    congr 1
    apply Fintype.sum_equiv (labelEquiv F)
    intro frequency
    have hphase := congrArg phaseSign (trace_pairing F frequency label)
    have hentry := congrFun (congrFun (observable_reindex F W frequency) row) col
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm] at hentry
    rw [hphase, hentry]
  ext row col
  simpa only [Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, Equiv.apply_symm_apply] using
    congrFun (congrFun hinverse ((labelEquiv F).symm row)) ((labelEquiv F).symm col)

/-- Reindexing a vector agrees with Mathlib's Euclidean permutation isometry. -/
theorem reindex_state_eq {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (equiv : ι ≃ κ) (state : EuclideanSpace ℂ ι) :
    reindexState equiv state = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ equiv state := rfl

/-- Simultaneous coordinate transport intertwines matrix action on a state. -/
theorem operator_action_reindex {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (equiv : ι ≃ κ) (operator : Op ι)
    (state : EuclideanSpace ℂ ι) :
    applyOperatorToState (Matrix.reindex equiv equiv operator) (reindexState equiv state) =
      reindexState equiv (applyOperatorToState operator state) := by
  ext position
  change (operator.submatrix equiv.symm equiv.symm *ᵥ
      (fun index => state (equiv.symm index))) position =
    (operator *ᵥ (fun index => state index)) (equiv.symm position)
  rw [Matrix.submatrix_mulVec_equiv]
  simp [Function.comp_def]

/-- Simultaneous transport of two operators and their reference state preserves
the norm of their difference applied to that state. -/
theorem operator_error_reindex {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (equiv : ι ≃ κ) (left right : Op ι)
    (state : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState (Matrix.reindex equiv equiv left -
        Matrix.reindex equiv equiv right) (reindexState equiv state)‖ =
      ‖applyOperatorToState (left - right) state‖ := by
  change ‖applyOperatorToState (Matrix.reindex equiv equiv (left - right))
    (reindexState equiv state)‖ = _
  rw [operator_action_reindex, reindexState_norm_eq]

/-- The paired EPR vector is invariant under simultaneous computational-basis
relabeling. This uses a permutation, not an arbitrary complex unitary. -/
theorem epr_reindex {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ] (equiv : ι ≃ κ) :
    reindexState (Equiv.prodCongr equiv equiv) (eprState ι) = eprState κ := by
  ext position
  change (if equiv.symm position.1 = equiv.symm position.2 then
      (Real.sqrt (Fintype.card ι : ℝ) : ℂ)⁻¹ else 0) =
    if position.1 = position.2 then (Real.sqrt (Fintype.card κ : ℝ) : ℂ)⁻¹ else 0
  rw [Fintype.card_congr equiv]
  simp only [Equiv.apply_eq_iff_eq]

/-- Post-composing both local maps with coordinate permutations reindexes their
joint image. This is the permutation specialization of local isometry composition. -/
theorem tensor_reindex_comp {ιA ιB κA κB νA νB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]
    [Fintype νA] [DecidableEq νA] [Fintype νB] [DecidableEq νB]
    (equivA : κA ≃ νA) (equivB : κB ≃ νB)
    (mapA : EuclideanSpace ℂ ιA →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (mapB : EuclideanSpace ℂ ιB →ₗᵢ[ℂ] EuclideanSpace ℂ κB)
    (state : EuclideanSpace ℂ (ιA × ιB)) :
    isometryTensor
        ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ equivA).toLinearIsometry.comp mapA)
        ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ equivB).toLinearIsometry.comp mapB)
        state = reindexState (Equiv.prodCongr equivA equivB)
          (isometryTensor mapA mapB state) := rfl

/-- Conjugation by a post-composed local coordinate permutation is matrix
reindexing of the original conjugated effect. -/
theorem conjugate_reindex_comp {ι κ ν : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype ν] [DecidableEq ν] (equiv : κ ≃ ν)
    (map : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ) (operator : Op ι) :
    conjIsometry
        ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ equiv).toLinearIsometry.comp map)
        operator = Matrix.reindex equiv equiv (conjIsometry map operator) := by
  ext row col
  rfl

/-- The local label equivalence leaves the auxiliary coordinate unchanged. -/
noncomputable def localEquiv (P : AdmissibleParams) (auxIndex : Type*) :
    (auxIndex × PauliRegister P) ≃ (auxIndex × QubitRegister P) :=
  Equiv.prodCongr (Equiv.refl auxIndex) (labelEquiv P.model)

/-- The two local coordinate equivalences, in the existing player ordering. -/
noncomputable def jointEquiv (P : AdmissibleParams) (auxA auxB : Type*) :
    ((auxA × PauliRegister P) × (auxB × PauliRegister P)) ≃
      ((auxA × QubitRegister P) × (auxB × QubitRegister P)) :=
  Equiv.prodCongr (localEquiv P auxA) (localEquiv P auxB)

/-- Binary reindexing preserves the auxiliary factor and transports the EPR
factor exactly after the four-factor shuffle into local-player order. -/
theorem ideal_state_reindex (P : AdmissibleParams)
    {auxA auxB : Type*} [Fintype auxA] [DecidableEq auxA]
    [Fintype auxB] [DecidableEq auxB] (aux : EuclideanSpace ℂ (auxA × auxB)) :
    reindexState (jointEquiv P auxA auxB) (idealState P aux) = idealQubitState P aux := by
  ext position
  exact congrArg (fun state : EuclideanSpace ℂ (QubitRegister P × QubitRegister P) =>
    aux (position.1.1, position.2.1) * state (position.1.2, position.2.2))
    (epr_reindex (labelEquiv (ι := Cube P.m) P.model))

/-- Forward binary transport of Alice's lifted effect, including the identity
on Bob's entire local register. -/
theorem lifted_effect_a_reindex {P : AdmissibleParams} {G : Game} (S : Strategy G)
    {auxA auxB : Type*} [Fintype auxA] [DecidableEq auxA]
    [Fintype auxB] [DecidableEq auxB]
    (mapA : EuclideanSpace ℂ S.ιA →ₗᵢ[ℂ] EuclideanSpace ℂ (auxA × PauliRegister P))
    (operator : Op S.ιA) :
    Matrix.reindex (jointEquiv P auxA auxB) (jointEquiv P auxA auxB)
        (liftedAEffect S mapA operator) =
      liftedQubitAEffect S
        ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (localEquiv P auxA)).toLinearIsometry.comp mapA) operator := by
  classical
  rw [liftedQubitAEffect, conjugate_reindex_comp]
  ext row col
  change (if (localEquiv P auxB).symm row.2 = (localEquiv P auxB).symm col.2 then
      conjIsometry mapA operator ((localEquiv P auxA).symm row.1)
        ((localEquiv P auxA).symm col.1) else 0) =
    conjIsometry mapA operator ((localEquiv P auxA).symm row.1)
      ((localEquiv P auxA).symm col.1) * (if row.2 = col.2 then 1 else 0)
  simp only [Equiv.apply_eq_iff_eq, mul_ite, mul_one, mul_zero]

/-- Forward binary transport of Bob's lifted effect, including the identity
on Alice's entire local register. -/
theorem lifted_effect_b_reindex {P : AdmissibleParams} {G : Game} (S : Strategy G)
    {auxA auxB : Type*} [Fintype auxA] [DecidableEq auxA]
    [Fintype auxB] [DecidableEq auxB]
    (mapB : EuclideanSpace ℂ S.ιB →ₗᵢ[ℂ] EuclideanSpace ℂ (auxB × PauliRegister P))
    (operator : Op S.ιB) :
    Matrix.reindex (jointEquiv P auxA auxB) (jointEquiv P auxA auxB)
        (liftedBEffect S mapB operator) =
      liftedQubitBEffect S
        ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (localEquiv P auxB)).toLinearIsometry.comp mapB) operator := by
  classical
  rw [liftedQubitBEffect, conjugate_reindex_comp]
  ext row col
  change (if (localEquiv P auxA).symm row.1 = (localEquiv P auxA).symm col.1 then
      conjIsometry mapB operator ((localEquiv P auxB).symm row.2)
        ((localEquiv P auxB).symm col.2) else 0) =
    (if row.1 = col.1 then 1 else 0) *
      conjIsometry mapB operator ((localEquiv P auxB).symm row.2)
        ((localEquiv P auxB).symm col.2)
  simp only [Equiv.apply_eq_iff_eq, ite_mul, one_mul, zero_mul]

/-- Forward binary transport of the ideal projector on Alice's extracted
register, with the other three tensor factors fixed. -/
theorem ideal_projector_a_reindex (P : AdmissibleParams)
    {auxA auxB : Type*} [Fintype auxA] [DecidableEq auxA]
    [Fintype auxB] [DecidableEq auxB] (W : PauliKind) (label : PauliRegister P) :
    Matrix.reindex (jointEquiv P auxA auxB) (jointEquiv P auxA auxB)
        (pauliProjOnA'' P W label) = qubitProjOnA'' P W label := by
  classical
  ext row col
  change (if row.1.1 = col.1.1 ∧
      (localEquiv P auxB).symm row.2 = (localEquiv P auxB).symm col.2 then
      (Matrix.reindex (labelEquiv P.model) (labelEquiv P.model)
        (pauliProj W label)) row.1.2 col.1.2 else 0) =
    if row.1.1 = col.1.1 ∧ row.2 = col.2 then
      qubitPauliProj W (kappaVec P.model label) row.1.2 col.1.2 else 0
  rw [pauli_projector_reindex]
  simp only [Equiv.apply_eq_iff_eq]

/-- Forward binary transport of the ideal projector on Bob's extracted
register, with the other three tensor factors fixed. -/
theorem ideal_projector_b_reindex (P : AdmissibleParams)
    {auxA auxB : Type*} [Fintype auxA] [DecidableEq auxA]
    [Fintype auxB] [DecidableEq auxB] (W : PauliKind) (label : PauliRegister P) :
    Matrix.reindex (jointEquiv P auxA auxB) (jointEquiv P auxA auxB)
        (pauliProjOnB'' P W label) = qubitProjOnB'' P W label := by
  classical
  ext row col
  change (if (localEquiv P auxA).symm row.1 = (localEquiv P auxA).symm col.1 ∧
      row.2.1 = col.2.1 then
      (Matrix.reindex (labelEquiv P.model) (labelEquiv P.model)
        (pauliProj W label)) row.2.2 col.2.2 else 0) =
    if row.1 = col.1 ∧ row.2.1 = col.2.1 then
      qubitPauliProj W (kappaVec P.model label) row.2.2 col.2.2 else 0
  rw [pauli_projector_reindex]
  simp only [Equiv.apply_eq_iff_eq]

end BinaryWitnessTransport

/-- Convert a supplied Pauli witness by post-composing each extraction map with
the fixed binary coordinate permutation. The auxiliary spaces, vector, and
normalization proof are unchanged. This is the exact given-witness construction
in the proof of `cor:pauli-binary`, not a proof of soundness existence. -/
noncomputable def PauliSoundnessWitness.toQubit
    {P : AdmissibleParams} {S : Strategy (pauliBasisTest P)}
    (w : PauliSoundnessWitness P S) : QubitSoundnessWitness P S where
  ιA' := w.ιA'
  ιB' := w.ιB'
  φA := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (BinaryWitnessTransport.localEquiv P w.ιA')).toLinearIsometry.comp w.φA
  φB := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (BinaryWitnessTransport.localEquiv P w.ιB')).toLinearIsometry.comp w.φB
  aux := w.aux
  aux_norm := w.aux_norm

/-- Exact preservation of state error for a supplied witness. This Lean-only
transport identity has no success assumption or error bound and does not assert
the existence conclusion of `cor:pauli-binary`. -/
theorem qubit_state_error_to_qubit
    (P : AdmissibleParams) (S : Strategy (pauliBasisTest P))
    (w : PauliSoundnessWitness P S) :
    ‖isometryTensor w.toQubit.φA w.toQubit.φB S.ψ -
        idealQubitState P w.toQubit.aux‖ =
      ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ := by
  change ‖isometryTensor
      ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (BinaryWitnessTransport.localEquiv P w.ιA')).toLinearIsometry.comp w.φA)
      ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (BinaryWitnessTransport.localEquiv P w.ιB')).toLinearIsometry.comp w.φB)
      S.ψ - idealQubitState P w.aux‖ = _
  rw [BinaryWitnessTransport.tensor_reindex_comp,
    ← BinaryWitnessTransport.ideal_state_reindex]
  rw [BinaryWitnessTransport.reindex_state_eq, BinaryWitnessTransport.reindex_state_eq]
  rw [BinaryWitnessTransport.jointEquiv, ← map_sub, LinearIsometryEquiv.norm_map]

/-- Exact preservation of Alice's squared operator-family distance for a
supplied witness. The answer sum is still field-valued, and both distances are
evaluated on their ideal auxiliary-EPR state. No soundness bound is assumed. -/
theorem qubit_operator_distance_a_to_qubit
    (P : AdmissibleParams) (S : Strategy (pauliBasisTest P))
    (w : PauliSoundnessWitness P S) (W : PauliKind) :
    qubitOperatorDistanceA P S w.toQubit W = pauliOperatorDistanceA P S w W := by
  unfold qubitOperatorDistanceA pauliOperatorDistanceA
  refine Finset.sum_congr rfl fun label _ => ?_
  have hnorm := BinaryWitnessTransport.operator_error_reindex
    (BinaryWitnessTransport.jointEquiv P w.ιA' w.ιB')
    (liftedAEffect S w.φA
      (((S.A (pauliQuestion P W)).postprocess pauliAnswerOrZero).effect label))
    (pauliProjOnA'' P W label) (idealState P w.aux)
  rw [BinaryWitnessTransport.lifted_effect_a_reindex,
    BinaryWitnessTransport.ideal_projector_a_reindex,
    BinaryWitnessTransport.ideal_state_reindex] at hnorm
  exact congrArg (fun error : ℝ => error ^ 2) hnorm

/-- Exact preservation of Bob's squared operator-family distance for a supplied
witness. This is a given-witness transport identity, independent of the open
existence conclusion of `cor:pauli-binary`. -/
theorem qubit_operator_distance_b_to_qubit
    (P : AdmissibleParams) (S : Strategy (pauliBasisTest P))
    (w : PauliSoundnessWitness P S) (W : PauliKind) :
    qubitOperatorDistanceB P S w.toQubit W = pauliOperatorDistanceB P S w W := by
  unfold qubitOperatorDistanceB pauliOperatorDistanceB
  refine Finset.sum_congr rfl fun label _ => ?_
  have hnorm := BinaryWitnessTransport.operator_error_reindex
    (BinaryWitnessTransport.jointEquiv P w.ιA' w.ιB')
    (liftedBEffect S w.φB
      (((S.B (pauliQuestion P W)).postprocess pauliAnswerOrZero).effect label))
    (pauliProjOnB'' P W label) (idealState P w.aux)
  rw [BinaryWitnessTransport.lifted_effect_b_reindex,
    BinaryWitnessTransport.ideal_projector_b_reindex,
    BinaryWitnessTransport.ideal_state_reindex] at hnorm
  exact congrArg (fun error : ℝ => error ^ 2) hnorm

/-- `cor:pauli-binary`: soundness of the Pauli basis test in qubit
coordinates. Blueprint `cor:pauli-binary`, paper
`08_classical_and_quantum_low_degree_tests.tex:1450-1491`.

The theorem assumes a nonnegative error parameter, as in the source, and uses
only `P.model` and its stored basis dimension. -/
theorem pauli_soundness_qubit :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b < 1 ∧
      ∀ (P : AdmissibleParams) (ε : ℝ), 0 ≤ ε →
        ∀ S : Strategy (pauliBasisTest P), 1 - ε ≤ S.value →
          ∃ w : QubitSoundnessWitness P S,
            ‖isometryTensor w.φA w.φB S.ψ - idealQubitState P w.aux‖ ≤
                deltaQld a b ε P.m P.d P.q ∧
            (∀ W : PauliKind,
              qubitOperatorDistanceA P S w W ≤
                deltaQld a b ε P.m P.d P.q) ∧
            ∀ W : PauliKind,
              qubitOperatorDistanceB P S w W ≤
                deltaQld a b ε P.m P.d P.q := by
  sorry

end

end MIPStarRE.QPBT
