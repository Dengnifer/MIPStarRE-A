import MIPStarRE.QPBT.Observables.ExpandedPlacement
import MIPStarRE.QPBT.Observables.LineMeasurement.Restriction

/-!
# Pauli-register line projectors

This module constructs the projective measurement `tau^{W,line}` of one
generalized-Pauli register whose outcome is the restriction to a canonical
line of the low-degree encoding of the measured basis label. It records that
the outcome projectors are orthogonal projections summing to the identity,
that they are symmetric matrices (so that they act identically on either half
of an EPR pair), and that on an axis-parallel line they vanish outside the
embedded degree-`d` subspace.

## References

The projectors are `tau^{W,line}_{f''}` in `def:expanded-line-measurement`,
`blueprint/src/chapter/ch14_qpbt_observables.tex:1034-1080`, with paper source
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:535-557`. Their
perfect self-consistency on an EPR pair is the ancillary input to item 1 of
`lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:559-568`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-- The Pauli-register projector onto labels whose low-degree encoding
restricts to `f` on `line`. This is `tau^{W,line}_f` in the proof of
`lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:535-557`, blueprint
`ch14_qpbt_observables.tex:1034-1080`. -/
noncomputable def tauLineProj (P : AdmissibleParams) (W : PauliKind)
    (line : LineDesc P.toLdParams) (f : DegPoly P.toLdParams (P.m * P.d)) :
    Op (PauliRegister P) :=
  ∑ h ∈ Finset.univ.filter (fun h : PauliRegister P =>
      restrictToLine P.toLdParams line (lowDegreeEncoding h) = f),
    pauliProj W h

/-- Each generalized Pauli eigenspace projector is positive semidefinite. A
private copy of this statement belongs to `Observables/ExpandedDefs.lean`
(`pauliProj_nonneg`); it is restated here because that copy is not exported. -/
private theorem pauliProj_nonneg (P : AdmissibleParams) (W : PauliKind)
    (e : PauliRegister P) : 0 ≤ pauliProj W e :=
  Matrix.nonneg_iff_posSemidef.mpr
    (Matrix.posSemidef_vecMulVec_self_star (pauliVec W e))

/-- Pauli line projectors are positive semidefinite. This is the positivity of
the ancillary measurement in `def:expanded-line-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:535-557`. -/
theorem tauLineProj_nonneg (P : AdmissibleParams) (W : PauliKind)
    (line : LineDesc P.toLdParams) (f : DegPoly P.toLdParams (P.m * P.d)) :
    0 ≤ tauLineProj P W line f := by
  classical
  unfold tauLineProj
  exact Finset.sum_nonneg fun e _ => pauliProj_nonneg P W e

/-- The line coarse-graining of the generalized Pauli projectors is symmetric.
This is the EPR-transport identity used for the perfect ancilla consistency in
item 1 of `lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:559-568`. -/
theorem tauLineProj_transpose (P : AdmissibleParams) (W : PauliKind)
    (line : LineDesc P.toLdParams) (f : DegPoly P.toLdParams (P.m * P.d)) :
    (tauLineProj P W line f)ᵀ = tauLineProj P W line f := by
  classical
  simp only [tauLineProj, Matrix.transpose_sum, pauliProj_transpose]

/-- Pauli line projectors belonging to distinct line polynomials are
orthogonal, while each projector is idempotent. This is the ancillary product
calculation in `def:expanded-line-measurement` and item 1 of
`lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:535-568`. -/
theorem tauLineProj_mul_tauLineProj (P : AdmissibleParams) (W : PauliKind)
    (line : LineDesc P.toLdParams) (f g : DegPoly P.toLdParams (P.m * P.d)) :
    tauLineProj P W line f * tauLineProj P W line g =
      if f = g then tauLineProj P W line f else 0 := by
  classical
  unfold tauLineProj
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  by_cases hfg : f = g
  · subst g
    rw [if_pos rfl]
    apply Finset.sum_congr rfl
    intro e he
    rw [Finset.sum_eq_single e]
    · rw [pauliProj_mul_pauliProj, if_pos rfl]
    · intro e' he' hee'
      rw [pauliProj_mul_pauliProj, if_neg hee'.symm]
    · exact fun h => (h he).elim
  · rw [if_neg hfg]
    apply Finset.sum_eq_zero
    intro e he
    apply Finset.sum_eq_zero
    intro e' he'
    rw [pauliProj_mul_pauliProj, if_neg]
    intro hee'
    apply hfg
    rw [← (Finset.mem_filter.mp he).2, ← (Finset.mem_filter.mp he').2, hee']

/-- The generalized Pauli eigenspace projectors of one register sum to the
identity. Private copies of this fact (`tauObservable_zero`,
`sum_pauliProj_eq_one`) belong to `Observables/ExpandedDefs.lean`; the
argument is restated here because those copies are not exported. -/
private theorem sum_pauliProj_eq_one (P : AdmissibleParams) (W : PauliKind) :
    ∑ e : PauliRegister P, pauliProj W e = 1 := by
  have hzero : tauObservable W (0 : PauliRegister P) = 1 := by
    have hmul := tauObservable_mul W (0 : PauliRegister P) 0
    rw [add_zero, tauObservable_sq] at hmul
    exact hmul.symm
  have h := tauObservable_eq_sum_pauliProj W (0 : PauliRegister P)
  rw [hzero] at h
  simpa [dotProduct, phaseSign] using h.symm

/-- The line fibers partition the complete family of Pauli eigenspace
projectors. This is the completeness of the ancillary measurement in
`def:expanded-line-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:535-557`. -/
theorem sum_tauLineProj_eq_one (P : AdmissibleParams) (W : PauliKind)
    (line : LineDesc P.toLdParams) :
    ∑ f, tauLineProj P W line f = 1 := by
  classical
  rw [show (∑ f, tauLineProj P W line f) =
      ∑ e : PauliRegister P, pauliProj W e by
    simp only [tauLineProj]
    exact Finset.sum_fiberwise Finset.univ
      (fun e : PauliRegister P =>
        restrictToLine P.toLdParams line (lowDegreeEncoding e))
      (fun e => pauliProj W e)]
  exact sum_pauliProj_eq_one P W

/-- The projective line measurement on one Pauli register obtained by
measuring the generalized Pauli basis and restricting the low-degree encoding
of the outcome to `line`. This is the ancillary measurement of
`def:expanded-line-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:535-557`, blueprint
`ch14_qpbt_observables.tex:1034-1080`. -/
noncomputable def tauLineMeas (P : AdmissibleParams) (W : PauliKind)
    (line : LineDesc P.toLdParams) :
    Measurement (DegPoly P.toLdParams (P.m * P.d)) (PauliRegister P) :=
  Measurement.ofSumEqOne (tauLineProj P W line) (tauLineProj_nonneg P W line)
    (sum_tauLineProj_eq_one P W line)

/-- The effects of the Pauli line measurement are the line projectors. -/
@[simp] theorem tauLineMeas_effect (P : AdmissibleParams) (W : PauliKind)
    (line : LineDesc P.toLdParams) (f : DegPoly P.toLdParams (P.m * P.d)) :
    (tauLineMeas P W line).effect f = tauLineProj P W line f := rfl

/-- On an axis-parallel line, Pauli line projectors vanish outside the
embedded degree-`d` subspace, because every restricted low-degree encoding has
degree at most `d` there. This is the ancillary half of the last assertion of
`def:expanded-line-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:548-557`. -/
theorem tauLineProj_eq_zero_of_axis (P : AdmissibleParams) (W : PauliKind)
    (line : LineDesc P.toLdParams) (haxis : line.kind = .axis)
    (f : DegPoly P.toLdParams (P.m * P.d)) (hf : ¬ f.FitsDegree P.d) :
    tauLineProj P W line f = 0 := by
  classical
  unfold tauLineProj
  apply Finset.sum_eq_zero
  intro e he
  exfalso
  apply hf
  rw [← (Finset.mem_filter.mp he).2]
  exact restrictToLine_lowDegreeEncoding_fitsDegree_of_axis P.toLdParams line
    haxis e

/-! ## Interaction with the point projectors -/

/-- On a point of the line, Pauli line projectors of non-evaluating
polynomials vanish: every restricted low-degree encoding evaluates there.
Formalization-only auxiliary for items 2 and 3 of `lem:qld-comm-line-cons`,
paper `14_analysis_of_the_pauli_basis_test.tex:569-620`. -/
theorem tauLineProj_eq_zero_of_evalOpt_none (P : AdmissibleParams)
    (W : PauliKind) (line : LineDesc P.toLdParams)
    (u : Fin P.m → PauliScalar P) (hu : u ∈ line.pointSet)
    (f : DegPoly P.toLdParams (P.m * P.d)) (hf : evalOpt line u f = none) :
    tauLineProj P W line f = 0 := by
  classical
  unfold tauLineProj
  apply Finset.sum_eq_zero
  intro e he
  exfalso
  have hev := evalOpt_restrictToLine_lowDegreeEncoding P.toLdParams line e u hu
  rw [(Finset.mem_filter.mp he).2] at hev
  have hev' : evalOpt line u f = some (dotProduct e (indicatorVec u)) := hev
  rw [hf] at hev'
  exact absurd hev' (by simp)

/-- A Pauli line projector followed by a Pauli point projector at a point of
the line is the line projector when the line polynomial evaluates to the
point value, and zero otherwise. This is the exact consistency
`tau^{W,line}_{f''}` versus `tau^{W,u}_{f''(u)}` in items 2 and 3 of
`lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:569-620`. -/
theorem tauLineProj_mul_tauPointProj (P : AdmissibleParams) (W : PauliKind)
    (line : LineDesc P.toLdParams) (u : Fin P.m → PauliScalar P)
    (hu : u ∈ line.pointSet) (f : DegPoly P.toLdParams (P.m * P.d))
    (b : PauliScalar P) :
    tauLineProj P W line f * ProjectiveSetting.tauPointProj W u b =
      if evalOpt line u f = some b then tauLineProj P W line f else 0 := by
  classical
  unfold tauLineProj ProjectiveSetting.tauPointProj
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum, pauliProj_mul_pauliProj]
  calc
    (∑ e ∈ Finset.univ.filter (fun e : PauliRegister P =>
        restrictToLine P.toLdParams line (lowDegreeEncoding e) = f),
        ∑ e' ∈ Finset.univ.filter (fun e' : PauliRegister P =>
          dotProduct e' (indicatorVec u) = b),
          if e = e' then pauliProj W e else 0) =
      ∑ e ∈ Finset.univ.filter (fun e : PauliRegister P =>
        restrictToLine P.toLdParams line (lowDegreeEncoding e) = f),
        if evalOpt line u f = some b then pauliProj W e else 0 := by
      refine Finset.sum_congr rfl fun e he => ?_
      rw [Finset.sum_ite_eq]
      have hev := evalOpt_restrictToLine_lowDegreeEncoding P.toLdParams line e u hu
      rw [(Finset.mem_filter.mp he).2] at hev
      have hev' : evalOpt line u f = some (dotProduct e (indicatorVec u)) := hev
      by_cases hb : evalOpt line u f = some b
      · rw [if_pos hb, if_pos]
        have hbe : dotProduct e (indicatorVec u) = b :=
          Option.some.inj (hev'.symm.trans hb)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbe⟩
      · rw [if_neg hb, if_neg]
        intro hmem
        apply hb
        exact hev'.trans (congrArg some (Finset.mem_filter.mp hmem).2)
    _ = _ := by
      split_ifs <;> simp

/-- Pauli line and point projectors commute. -/
theorem tauPointProj_mul_tauLineProj (P : AdmissibleParams) (W : PauliKind)
    (line : LineDesc P.toLdParams) (u : Fin P.m → PauliScalar P)
    (f : DegPoly P.toLdParams (P.m * P.d)) (b : PauliScalar P) :
    ProjectiveSetting.tauPointProj W u b * tauLineProj P W line f =
      tauLineProj P W line f * ProjectiveSetting.tauPointProj W u b := by
  classical
  unfold tauLineProj ProjectiveSetting.tauPointProj
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun e' _ => ?_
  rw [pauliProj_mul_pauliProj, pauliProj_mul_pauliProj]
  by_cases h : e = e'
  · subst h
    simp
  · rw [if_neg (Ne.symm h), if_neg h]

/-- Acting with a Pauli line projector on one half of the EPR state and a
Pauli point projector on the other half equals acting with their product on
the first half. Formalization-only support for the exact ancillary
consistency in items 2 and 3 of `lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:569-620`. -/
theorem tauLineProj_tauPointProj_mulVec_eprState (P : AdmissibleParams)
    (W : PauliKind) (line : LineDesc P.toLdParams)
    (u : Fin P.m → PauliScalar P) (f : DegPoly P.toLdParams (P.m * P.d))
    (b : PauliScalar P) :
    (heteroKron (tauLineProj P W line f)
        (ProjectiveSetting.tauPointProj W u b)).mulVec
        (eprState (PauliRegister P)) =
      (heteroKron (tauLineProj P W line f * ProjectiveSetting.tauPointProj W u b)
        1).mulVec (eprState (PauliRegister P)) := by
  let T := tauLineProj P W line f
  let T' := ProjectiveSetting.tauPointProj W u b
  have hfactor : heteroKron T T' = heteroKron T 1 * heteroKron 1 T' := by
    rw [heteroKron_mul, Matrix.mul_one, Matrix.one_mul]
  rw [hfactor, ← Matrix.mulVec_mulVec,
    ← epr_action_eq_of_transpose T'
      (ProjectiveSetting.tauPointProj_transpose W u b),
    Matrix.mulVec_mulVec, heteroKron_mul, Matrix.mul_one]

/-- The reversed placement of the previous identity. -/
theorem tauPointProj_tauLineProj_mulVec_eprState (P : AdmissibleParams)
    (W : PauliKind) (line : LineDesc P.toLdParams)
    (u : Fin P.m → PauliScalar P) (f : DegPoly P.toLdParams (P.m * P.d))
    (b : PauliScalar P) :
    (heteroKron (ProjectiveSetting.tauPointProj W u b)
        (tauLineProj P W line f)).mulVec
        (eprState (PauliRegister P)) =
      (heteroKron (tauLineProj P W line f * ProjectiveSetting.tauPointProj W u b)
        1).mulVec (eprState (PauliRegister P)) := by
  let T := tauLineProj P W line f
  let T' := ProjectiveSetting.tauPointProj W u b
  have hfactor : heteroKron T' T = heteroKron T' 1 * heteroKron 1 T := by
    rw [heteroKron_mul, Matrix.mul_one, Matrix.one_mul]
  rw [hfactor, ← Matrix.mulVec_mulVec,
    ← epr_action_eq_of_transpose T (tauLineProj_transpose P W line f),
    Matrix.mulVec_mulVec, heteroKron_mul, Matrix.mul_one,
    tauPointProj_mul_tauLineProj]

/-- The EPR quadratic form of a line projector on one half and a point
projector on the other half is the EPR quadratic form of the line projector
alone when the line polynomial evaluates to the point value, and zero
otherwise. This is the exact ancillary consistency in items 2 and 3 of
`lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:569-620`. -/
theorem stateQForm_eprState_tauLineProj_tauPointProj (P : AdmissibleParams)
    (W : PauliKind) (line : LineDesc P.toLdParams)
    (u : Fin P.m → PauliScalar P) (hu : u ∈ line.pointSet)
    (f : DegPoly P.toLdParams (P.m * P.d)) (b : PauliScalar P) :
    DistanceCalculus.stateQForm (eprState (PauliRegister P))
        (heteroKron (tauLineProj P W line f)
          (ProjectiveSetting.tauPointProj W u b)) =
      if evalOpt line u f = some b then
        DistanceCalculus.stateQForm (eprState (PauliRegister P))
          (heteroKron (tauLineProj P W line f) (1 : Op (PauliRegister P)))
      else 0 := by
  have h : DistanceCalculus.stateQForm (eprState (PauliRegister P))
      (heteroKron (tauLineProj P W line f)
        (ProjectiveSetting.tauPointProj W u b)) =
      DistanceCalculus.stateQForm (eprState (PauliRegister P))
        (heteroKron (tauLineProj P W line f *
          ProjectiveSetting.tauPointProj W u b) (1 : Op (PauliRegister P))) := by
    unfold DistanceCalculus.stateQForm
    congr 2
    ext p
    simpa [applyOperatorToState] using
      congrFun (tauLineProj_tauPointProj_mulVec_eprState P W line u f b) p
  rw [h, tauLineProj_mul_tauPointProj P W line u hu f b]
  split_ifs
  · rfl
  · simp [DistanceCalculus.stateQForm, applyOperatorToState, heteroKron]

/-- The reversed placement of the previous identity. -/
theorem stateQForm_eprState_tauPointProj_tauLineProj (P : AdmissibleParams)
    (W : PauliKind) (line : LineDesc P.toLdParams)
    (u : Fin P.m → PauliScalar P) (hu : u ∈ line.pointSet)
    (f : DegPoly P.toLdParams (P.m * P.d)) (b : PauliScalar P) :
    DistanceCalculus.stateQForm (eprState (PauliRegister P))
        (heteroKron (ProjectiveSetting.tauPointProj W u b)
          (tauLineProj P W line f)) =
      if evalOpt line u f = some b then
        DistanceCalculus.stateQForm (eprState (PauliRegister P))
          (heteroKron (tauLineProj P W line f) (1 : Op (PauliRegister P)))
      else 0 := by
  have h : DistanceCalculus.stateQForm (eprState (PauliRegister P))
      (heteroKron (ProjectiveSetting.tauPointProj W u b)
        (tauLineProj P W line f)) =
      DistanceCalculus.stateQForm (eprState (PauliRegister P))
        (heteroKron (tauLineProj P W line f *
          ProjectiveSetting.tauPointProj W u b) (1 : Op (PauliRegister P))) := by
    unfold DistanceCalculus.stateQForm
    congr 2
    ext p
    simpa [applyOperatorToState] using
      congrFun (tauPointProj_tauLineProj_mulVec_eprState P W line u f b) p
  rw [h, tauLineProj_mul_tauPointProj P W line u hu f b]
  split_ifs
  · rfl
  · simp [DistanceCalculus.stateQForm, applyOperatorToState, heteroKron]

/-! ## Perfect consistency on an EPR pair -/

/-- Acting with the same Pauli line projector on both halves of the EPR state
equals acting on one half. Symmetry transports the right action to the left,
where idempotence absorbs the repeated projector. This is the perfect
ancillary consistency used in item 1 of `lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:559-568`. -/
theorem tauLineProj_pair_mulVec_eprState (P : AdmissibleParams)
    (W : PauliKind) (line : LineDesc P.toLdParams)
    (f : DegPoly P.toLdParams (P.m * P.d)) :
    (heteroKron (tauLineProj P W line f) (tauLineProj P W line f)).mulVec
        (eprState (PauliRegister P)) =
      (heteroKron (tauLineProj P W line f) 1).mulVec
        (eprState (PauliRegister P)) := by
  let T := tauLineProj P W line f
  have hfactor : heteroKron T T = heteroKron T 1 * heteroKron 1 T := by
    rw [heteroKron_mul, Matrix.mul_one, Matrix.one_mul]
  rw [hfactor, ← Matrix.mulVec_mulVec,
    ← epr_action_eq_of_transpose T (tauLineProj_transpose P W line f),
    Matrix.mulVec_mulVec, heteroKron_mul, Matrix.mul_one,
    tauLineProj_mul_tauLineProj, if_pos rfl]

/-- The EPR quadratic forms of the Pauli line projectors on one half sum to
one. Formalization-only auxiliary for the ancillary overlaps in
`lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:559-679`. -/
theorem sum_stateQForm_eprState_tauLineProj_one (P : AdmissibleParams)
    (W : PauliKind) (line : LineDesc P.toLdParams) :
    ∑ f : DegPoly P.toLdParams (P.m * P.d),
        DistanceCalculus.stateQForm (eprState (PauliRegister P))
          (heteroKron (tauLineProj P W line f) (1 : Op (PauliRegister P))) = 1 := by
  have hsumop :
      (∑ f : DegPoly P.toLdParams (P.m * P.d),
          heteroKron (tauLineProj P W line f) (1 : Op (PauliRegister P))) =
        heteroKron (∑ f : DegPoly P.toLdParams (P.m * P.d), tauLineProj P W line f)
          (1 : Op (PauliRegister P)) := by
    ext i j
    rcases i with ⟨i₁, i₂⟩
    rcases j with ⟨j₁, j₂⟩
    unfold heteroKron Matrix.kronecker Matrix.kroneckerMap
    simp only [Matrix.of_apply, Matrix.sum_apply]
    rw [Finset.sum_mul]
  rw [← show DistanceCalculus.stateQForm (eprState (PauliRegister P))
      (∑ f : DegPoly P.toLdParams (P.m * P.d),
        heteroKron (tauLineProj P W line f) (1 : Op (PauliRegister P))) =
        ∑ f : DegPoly P.toLdParams (P.m * P.d),
          DistanceCalculus.stateQForm (eprState (PauliRegister P))
            (heteroKron (tauLineProj P W line f) (1 : Op (PauliRegister P))) by
    simp [DistanceCalculus.stateQForm, applyOperatorToState]]
  rw [hsumop, sum_tauLineProj_eq_one, heteroKron_one_one]
  unfold DistanceCalculus.stateQForm
  rw [WinImplications.applyOperatorToState_one]
  calc
    (inner ℂ (eprState (PauliRegister P))
        (eprState (PauliRegister P))).re =
      ‖eprState (PauliRegister P)‖ ^ 2 := by
        simpa using (inner_self_eq_norm_sq (𝕜 := ℂ)
          (eprState (PauliRegister P)))
    _ = 1 := by rw [eprState_norm]; norm_num

/-- The diagonal overlap of the two Pauli line measurements on an EPR pair is
one. Thus the ancillary measurement contributes no consistency defect. This
is the perfect ancillary consistency in item 1 of `lem:qld-comm-line-cons`,
paper `14_analysis_of_the_pauli_basis_test.tex:559-568`. -/
theorem sum_tauLineProj_pair_stateQForm_eprState (P : AdmissibleParams)
    (W : PauliKind) (line : LineDesc P.toLdParams) :
    ∑ f : DegPoly P.toLdParams (P.m * P.d),
        DistanceCalculus.stateQForm (eprState (PauliRegister P))
          (heteroKron (tauLineProj P W line f) (tauLineProj P W line f)) = 1 := by
  have hterm (f : DegPoly P.toLdParams (P.m * P.d)) :
      DistanceCalculus.stateQForm (eprState (PauliRegister P))
          (heteroKron (tauLineProj P W line f) (tauLineProj P W line f)) =
        DistanceCalculus.stateQForm (eprState (PauliRegister P))
          (heteroKron (tauLineProj P W line f) (1 : Op (PauliRegister P))) := by
    unfold DistanceCalculus.stateQForm
    congr 2
    ext p
    simpa [applyOperatorToState] using
      congrFun (tauLineProj_pair_mulVec_eprState P W line f) p
  simp_rw [hterm]
  exact sum_stateQForm_eprState_tauLineProj_one P W line

end

end MIPStarRE.QPBT
