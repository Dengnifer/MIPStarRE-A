import MIPStarRE.QPBT.Observables.PointConsistency

/-!
# Placement calculus on the expanded state

This module records the algebra of the four register placements used by the
combining argument: a placement is a unital `*`-homomorphism, placements on
opposite register pairs commute, and the crosswise exchange of the two EPR
pairs of the expanded state carries the placement `AA'` to `AB''` and `BA''`
to `BB'` while fixing the expanded state.  The last fact transfers every
state-dependent distance between the two bipartition schemes of
`def:symmetric-equivalents` without assuming a symmetric strategy.

## References

The placements are those of `def:symmetric-equivalents`, blueprint
`blueprint/src/chapter/ch14_qpbt_observables.tex:1003-1030`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:420-450`.  The
EPR-exchange invariance is the element `U_σ U_θ` of
`lem:symmetric-equivalents-transfer`, blueprint
`blueprint/src/chapter/ch14_qpbt_observables.tex:1032-1130`, which needs no
symmetry of the strategy; its use for `lem:qld-4-10` is analyzed in
`docs/paper-gaps/qpbt_linearity-theorem-quotation.tex`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

/-! ## Placements as reindexed tensor factors -/

/-- The `AA'` placement is the reindexed left factor of the
`AA' | BA''(B'B'')` bipartition. -/
theorem place_AA'_eq (S : ProjectiveSetting P ε)
    (O : Op (S.ExpandedLocalSpace Placement.AA'.side)) :
    S.place .AA' O =
      reindexOp (aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
        (heteroKron O
          (1 : Op ((S.toStrategy.ιB × PauliRegister P) ×
            (PauliRegister P × PauliRegister P)))) :=
  (reindexOp_aaBaBipartition_left S O).symm

/-- The `BA''` placement is the reindexed right factor of the
`AA' | BA''(B'B'')` bipartition. -/
theorem place_BA''_eq (S : ProjectiveSetting P ε)
    (O : Op (S.ExpandedLocalSpace Placement.BA''.side)) :
    S.place .BA'' O =
      reindexOp (aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
        (heteroKron (1 : Op (S.toStrategy.ιA × PauliRegister P))
          (heteroKron O (1 : Op (PauliRegister P × PauliRegister P)))) :=
  (reindexOp_aaBaBipartition_right S O).symm

/-- The `AB''` placement is the reindexed left factor of the
`AB'' | BB'(A'A'')` bipartition. -/
theorem place_AB''_eq (S : ProjectiveSetting P ε)
    (O : Op (S.ExpandedLocalSpace Placement.AB''.side)) :
    S.place .AB'' O =
      reindexOp (abBbBipartition P S.toStrategy.ιA S.toStrategy.ιB)
        (heteroKron O
          (1 : Op ((S.toStrategy.ιB × PauliRegister P) ×
            (PauliRegister P × PauliRegister P)))) :=
  (reindexOp_abBbBipartition_left S O).symm

/-- The `BB'` placement is the reindexed right factor of the
`AB'' | BB'(A'A'')` bipartition. -/
theorem place_BB'_eq (S : ProjectiveSetting P ε)
    (O : Op (S.ExpandedLocalSpace Placement.BB'.side)) :
    S.place .BB' O =
      reindexOp (abBbBipartition P S.toStrategy.ιA S.toStrategy.ιB)
        (heteroKron (1 : Op (S.toStrategy.ιA × PauliRegister P))
          (heteroKron O (1 : Op (PauliRegister P × PauliRegister P)))) :=
  (reindexOp_abBbBipartition_right S O).symm

/-- Reindexing an operator commutes with the conjugate transpose. -/
theorem reindexOp_conjTranspose {ι κ : Type*} (e : ι ≃ κ) (M : Op κ) :
    reindexOp e Mᴴ = (reindexOp e M)ᴴ := by
  ext i j
  rfl

/-- Reindexing an operator along an equivalence preserves positivity. -/
theorem reindexOp_nonneg {ι κ : Type*} [Finite ι] [Finite κ]
    (e : ι ≃ κ) {M : Op κ} (hM : 0 ≤ M) :
    0 ≤ reindexOp e M := by
  letI := Fintype.ofFinite ι
  letI := Fintype.ofFinite κ
  rw [Matrix.nonneg_iff_posSemidef] at hM ⊢
  exact hM.submatrix e.symm.symm

/-! ## The placement is a unital `*`-homomorphism -/

set_option synthInstance.maxSize 400 in
/-- A placement is multiplicative. -/
theorem place_mul (S : ProjectiveSetting P ε) :
    ∀ (p : Placement) (A B : Op (S.ExpandedLocalSpace p.side)),
      S.place p (A * B) = S.place p A * S.place p B
  | .AA', A, B => by
      classical
      rw [place_AA'_eq, place_AA'_eq, place_AA'_eq,
        ← WinImplications.reindexOp_mul, heteroKron_mul, mul_one]
      all_goals rfl
  | .BA'', A, B => by
      classical
      rw [place_BA''_eq, place_BA''_eq, place_BA''_eq,
        ← WinImplications.reindexOp_mul, heteroKron_mul, heteroKron_mul,
        mul_one, mul_one]
      all_goals rfl
  | .BB', A, B => by
      classical
      rw [place_BB'_eq, place_BB'_eq, place_BB'_eq,
        ← WinImplications.reindexOp_mul, heteroKron_mul, heteroKron_mul,
        mul_one, mul_one]
      all_goals rfl
  | .AB'', A, B => by
      classical
      rw [place_AB''_eq, place_AB''_eq, place_AB''_eq,
        ← WinImplications.reindexOp_mul, heteroKron_mul, mul_one]
      all_goals rfl

/-- A placement sends the local identity to the identity of the six-register
space. -/
theorem place_one (S : ProjectiveSetting P ε) (p : Placement) :
    S.place p (1 : Op (S.ExpandedLocalSpace p.side)) = 1 := by
  ext i j
  cases p <;>
    · simp only [ProjectiveSetting.place, Matrix.one_apply, Prod.ext_iff]
      split_ifs <;> simp_all

/-- A placement is additive over finite sums of local operators. -/
theorem place_finsetSum (S : ProjectiveSetting P ε) (p : Placement) {γ : Type*}
    (s : Finset γ) (O : γ → Op (S.ExpandedLocalSpace p.side)) :
    S.place p (∑ x ∈ s, O x) = ∑ x ∈ s, S.place p (O x) := by
  ext i j
  cases p <;>
    simp only [ProjectiveSetting.place, Matrix.sum_apply, Finset.sum_mul,
      Finset.mul_sum]

/-- A placement commutes with the conjugate transpose. -/
theorem place_conjTranspose (S : ProjectiveSetting P ε) :
    ∀ (p : Placement) (A : Op (S.ExpandedLocalSpace p.side)),
      S.place p Aᴴ = (S.place p A)ᴴ
  | .AA', A => by
      rw [place_AA'_eq, place_AA'_eq, ← reindexOp_conjTranspose,
        WinImplications.heteroKron_conjTranspose, Matrix.conjTranspose_one]
      all_goals rfl
  | .BA'', A => by
      rw [place_BA''_eq, place_BA''_eq, ← reindexOp_conjTranspose,
        WinImplications.heteroKron_conjTranspose,
        WinImplications.heteroKron_conjTranspose, Matrix.conjTranspose_one,
        Matrix.conjTranspose_one]
      all_goals rfl
  | .BB', A => by
      rw [place_BB'_eq, place_BB'_eq, ← reindexOp_conjTranspose,
        WinImplications.heteroKron_conjTranspose,
        WinImplications.heteroKron_conjTranspose, Matrix.conjTranspose_one,
        Matrix.conjTranspose_one]
      all_goals rfl
  | .AB'', A => by
      rw [place_AB''_eq, place_AB''_eq, ← reindexOp_conjTranspose,
        WinImplications.heteroKron_conjTranspose, Matrix.conjTranspose_one]
      all_goals rfl

set_option synthInstance.maxSize 400 in
/-- A placement preserves positivity. -/
theorem place_nonneg (S : ProjectiveSetting P ε) :
    ∀ (p : Placement) {A : Op (S.ExpandedLocalSpace p.side)}, 0 ≤ A →
      0 ≤ S.place p A
  | .AA', A, hA => by
      classical
      rw [place_AA'_eq]
      exact reindexOp_nonneg _ (MIPStarRE.Quantum.kronecker_nonneg hA
        (Matrix.PosSemidef.one.nonneg))
  | .BA'', A, hA => by
      classical
      rw [place_BA''_eq]
      exact reindexOp_nonneg _ (MIPStarRE.Quantum.kronecker_nonneg
        (Matrix.PosSemidef.one.nonneg)
        (MIPStarRE.Quantum.kronecker_nonneg hA (Matrix.PosSemidef.one.nonneg)))
  | .BB', A, hA => by
      classical
      rw [place_BB'_eq]
      exact reindexOp_nonneg _ (MIPStarRE.Quantum.kronecker_nonneg
        (Matrix.PosSemidef.one.nonneg)
        (MIPStarRE.Quantum.kronecker_nonneg hA (Matrix.PosSemidef.one.nonneg)))
  | .AB'', A, hA => by
      classical
      rw [place_AB''_eq]
      exact reindexOp_nonneg _ (MIPStarRE.Quantum.kronecker_nonneg hA
        (Matrix.PosSemidef.one.nonneg))

/-- The placement of a local operator bounded by the identity is bounded by
the identity. -/
theorem place_le_one (S : ProjectiveSetting P ε) (p : Placement)
    {A : Op (S.ExpandedLocalSpace p.side)} (hA : A ≤ 1) :
    S.place p A ≤ 1 := by
  have h : 0 ≤ S.place p (1 - A) := S.place_nonneg p (sub_nonneg.mpr hA)
  rw [place_sub, place_one] at h
  exact sub_nonneg.mp h

/-- The placement of a projector is a contraction. -/
theorem place_conjTranspose_mul_self_le_one (S : ProjectiveSetting P ε)
    (p : Placement) {E : Op (S.ExpandedLocalSpace p.side)} (hE : IsProj E) :
    (S.place p E)ᴴ * S.place p E ≤ 1 := by
  rw [← place_conjTranspose, ← place_mul, hE.isSelfAdjoint.isHermitian.eq,
    hE.isIdempotentElem.eq]
  exact S.place_le_one p (sub_nonneg.mp hE.one_sub.nonneg)

set_option synthInstance.maxSize 400 in
/-- Operators placed on opposite register pairs commute. -/
theorem place_comm (S : ProjectiveSetting P ε) :
    ∀ (p₁ p₂ : Placement), p₁.IsOpposite p₂ →
      ∀ (A : Op (S.ExpandedLocalSpace p₁.side))
        (B : Op (S.ExpandedLocalSpace p₂.side)),
        S.place p₁ A * S.place p₂ B = S.place p₂ B * S.place p₁ A
  | .AA', .BA'', _, A, B => by
      classical
      rw [place_AA'_eq, place_BA''_eq, ← WinImplications.reindexOp_mul,
        ← WinImplications.reindexOp_mul]
      simp only [heteroKron_mul, one_mul, mul_one]
  | .BA'', .AA', _, A, B => by
      classical
      rw [place_AA'_eq, place_BA''_eq, ← WinImplications.reindexOp_mul,
        ← WinImplications.reindexOp_mul]
      simp only [heteroKron_mul, one_mul, mul_one]
  | .BB', .AB'', _, A, B => by
      classical
      rw [place_AB''_eq, place_BB'_eq, ← WinImplications.reindexOp_mul,
        ← WinImplications.reindexOp_mul]
      simp only [heteroKron_mul, one_mul, mul_one]
  | .AB'', .BB', _, A, B => by
      classical
      rw [place_AB''_eq, place_BB'_eq, ← WinImplications.reindexOp_mul,
        ← WinImplications.reindexOp_mul]
      simp only [heteroKron_mul, one_mul, mul_one]
  | .AA', .AA', h, _, _ => by simp [Placement.IsOpposite] at h
  | .AA', .BB', h, _, _ => by simp [Placement.IsOpposite] at h
  | .AA', .AB'', h, _, _ => by simp [Placement.IsOpposite] at h
  | .BA'', .BA'', h, _, _ => by simp [Placement.IsOpposite] at h
  | .BA'', .BB', h, _, _ => by simp [Placement.IsOpposite] at h
  | .BA'', .AB'', h, _, _ => by simp [Placement.IsOpposite] at h
  | .BB', .AA', h, _, _ => by simp [Placement.IsOpposite] at h
  | .BB', .BA'', h, _, _ => by simp [Placement.IsOpposite] at h
  | .BB', .BB', h, _, _ => by simp [Placement.IsOpposite] at h
  | .AB'', .AA', h, _, _ => by simp [Placement.IsOpposite] at h
  | .AB'', .BA'', h, _, _ => by simp [Placement.IsOpposite] at h
  | .AB'', .AB'', h, _, _ => by simp [Placement.IsOpposite] at h

/-- A complete measurement on a local expanded space, placed on one of the
four register pairs, is a complete measurement on the six-register space. -/
def placedMeasurement (S : ProjectiveSetting P ε) (p : Placement) {α : Type*}
    [Fintype α] (M : Measurement α (S.ExpandedLocalSpace p.side)) :
    Measurement α (SixReg P S.toStrategy.ιA S.toStrategy.ιB) :=
  Measurement.ofSumEqOne (fun a => S.place p (M.effect a))
    (fun a => S.place_nonneg p (M.pos a))
    (by rw [← place_finsetSum, M.sum_eq_one, place_one])

/-- The effects of a placed measurement are the placed effects. -/
@[simp] theorem placedMeasurement_effect (S : ProjectiveSetting P ε)
    (p : Placement) {α : Type*} [Fintype α]
    (M : Measurement α (S.ExpandedLocalSpace p.side)) (a : α) :
    (S.placedMeasurement p M).effect a = S.place p (M.effect a) := rfl

/-- A placed projective measurement is projective. -/
theorem placedMeasurement_isProjective (S : ProjectiveSetting P ε)
    (p : Placement) {α : Type*} [Fintype α]
    (M : Measurement α (S.ExpandedLocalSpace p.side))
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) :
    MIPStarRE.QPBT.Measurement.IsProjective (S.placedMeasurement p M) := by
  intro a
  refine isStarProjection_iff'.2 ⟨?_, ?_⟩
  · change S.place p (M.effect a) * S.place p (M.effect a) =
      S.place p (M.effect a)
    rw [← place_mul, (hM a).isIdempotentElem.eq]
  · change star (S.place p (M.effect a)) = S.place p (M.effect a)
    rw [Matrix.star_eq_conjTranspose, ← place_conjTranspose,
      (hM a).isSelfAdjoint.isHermitian.eq]

/-! ## The crosswise exchange of the two EPR pairs -/

/-- The permutation of the six registers exchanging `A'` with `B''` and `A''`
with `B'`.  It is the element `U_σ U_θ` of
`lem:symmetric-equivalents-transfer`, blueprint
`blueprint/src/chapter/ch14_qpbt_observables.tex:1032-1130`; unlike the
generators there it does not touch the strategy registers. -/
def eprCrossSwap (P : AdmissibleParams) (ιA ιB : Type*) :
    SixReg P ιA ιB ≃ SixReg P ιA ιB where
  toFun := fun ⟨⟨a, a', a''⟩, b, b', b''⟩ => ((a, (b'', b')), (b, (a'', a')))
  invFun := fun ⟨⟨a, a', a''⟩, b, b', b''⟩ => ((a, (b'', b')), (b, (a'', a')))
  left_inv := by rintro ⟨⟨a, a', a''⟩, b, b', b''⟩; rfl
  right_inv := by rintro ⟨⟨a, a', a''⟩, b, b', b''⟩; rfl

/-- The EPR vector is symmetric in its two registers. -/
theorem eprState_ofLp_swap {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (x y : V) :
    (eprState V).ofLp (x, y) = (eprState V).ofLp (y, x) := by
  change (if x = y then (Real.sqrt (Fintype.card V : ℝ) : ℂ)⁻¹ else 0) =
    (if y = x then (Real.sqrt (Fintype.card V : ℝ) : ℂ)⁻¹ else 0)
  by_cases h : x = y
  · simp [h]
  · simp [h, Ne.symm h]

/-- The crosswise EPR exchange fixes the expanded state.  This is item 1 of
`lem:symmetric-equivalents-transfer` for the element `U_σ U_θ`, blueprint
`blueprint/src/chapter/ch14_qpbt_observables.tex:1032-1130`; only the symmetry
of the EPR vector is used. -/
theorem reindexState_eprCrossSwap_psiHat (S : ProjectiveSetting P ε) :
    reindexState (eprCrossSwap P S.toStrategy.ιA S.toStrategy.ιB) S.psiHat =
      S.psiHat := by
  ext i
  obtain ⟨⟨a, a', a''⟩, b, b', b''⟩ := i
  change S.toStrategy.ψ.ofLp (a, b) * (eprState (PauliRegister P)).ofLp (b'', b') *
      (eprState (PauliRegister P)).ofLp (a'', a') =
    S.toStrategy.ψ.ofLp (a, b) * (eprState (PauliRegister P)).ofLp (a', a'') *
      (eprState (PauliRegister P)).ofLp (b', b'')
  rw [eprState_ofLp_swap b'' b', eprState_ofLp_swap a'' a']
  ring

/-- The crosswise EPR exchange carries the `AB''` placement to the `AA'`
placement. -/
theorem reindexOp_eprCrossSwap_place_AB'' (S : ProjectiveSetting P ε)
    (O : Op (S.ExpandedLocalSpace .alice)) :
    reindexOp (eprCrossSwap P S.toStrategy.ιA S.toStrategy.ιB)
      (S.place .AB'' O) = S.place .AA' O := by
  ext i j
  obtain ⟨⟨a, a', a''⟩, b, b', b''⟩ := i
  obtain ⟨⟨c, c', c''⟩, d, d', d''⟩ := j
  simp only [reindexOp, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, place, eprCrossSwap, Equiv.coe_fn_mk, Matrix.one_apply]
  ring!

/-- The crosswise EPR exchange carries the `BB'` placement to the `BA''`
placement. -/
theorem reindexOp_eprCrossSwap_place_BB' (S : ProjectiveSetting P ε)
    (O : Op (S.ExpandedLocalSpace .bob)) :
    reindexOp (eprCrossSwap P S.toStrategy.ιA S.toStrategy.ιB)
      (S.place .BB' O) = S.place .BA'' O := by
  ext i j
  obtain ⟨⟨a, a', a''⟩, b, b', b''⟩ := i
  obtain ⟨⟨c, c', c''⟩, d, d', d''⟩ := j
  simp only [reindexOp, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, place, eprCrossSwap, Equiv.coe_fn_mk, Matrix.one_apply]
  ring!

/-- An operator placed on `AB''` has, on the expanded state, the same norm as
the same operator placed on `AA'`.  This is item 2 of
`lem:symmetric-equivalents-transfer` for `U_σ U_θ`, blueprint
`blueprint/src/chapter/ch14_qpbt_observables.tex:1032-1130`. -/
theorem norm_place_AB''_eq_norm_place_AA' (S : ProjectiveSetting P ε)
    (O : Op (S.ExpandedLocalSpace .alice)) :
    ‖applyOperatorToState (S.place .AB'' O) S.psiHat‖ =
      ‖applyOperatorToState (S.place .AA' O) S.psiHat‖ := by
  conv_lhs => rw [← reindexState_eprCrossSwap_psiHat S]
  rw [WinImplications.norm_applyOperatorToState_reindexState,
    reindexOp_eprCrossSwap_place_AB'']

/-- An operator placed on `BB'` has, on the expanded state, the same norm as
the same operator placed on `BA''`.  This is item 2 of
`lem:symmetric-equivalents-transfer` for `U_σ U_θ`, blueprint
`blueprint/src/chapter/ch14_qpbt_observables.tex:1032-1130`. -/
theorem norm_place_BB'_eq_norm_place_BA'' (S : ProjectiveSetting P ε)
    (O : Op (S.ExpandedLocalSpace .bob)) :
    ‖applyOperatorToState (S.place .BB' O) S.psiHat‖ =
      ‖applyOperatorToState (S.place .BA'' O) S.psiHat‖ := by
  conv_lhs => rw [← reindexState_eprCrossSwap_psiHat S]
  rw [WinImplications.norm_applyOperatorToState_reindexState,
    reindexOp_eprCrossSwap_place_BB']

/-- Transfer of a same-side state-dependent distance between the `AA'` and
`AB''` placements. -/
theorem opFamilyDistSq_place_AB''_eq_AA' {X α : Type*} [Fintype α]
    (S : ProjectiveSetting P ε) (μ : Distribution X)
    (A B : X → α → Op (S.ExpandedLocalSpace .alice)) :
    opFamilyDistSq μ (fun x a => S.place .AB'' (A x a))
        (fun x a => S.place .AB'' (B x a)) S.psiHat =
      opFamilyDistSq μ (fun x a => S.place .AA' (A x a))
        (fun x a => S.place .AA' (B x a)) S.psiHat := by
  unfold opFamilyDistSq
  refine avgOver_congr _ _ _ fun x => Finset.sum_congr rfl fun a _ => ?_
  rw [← place_sub, ← place_sub, norm_place_AB''_eq_norm_place_AA']
  all_goals rfl

/-- Transfer of a same-side state-dependent distance between the `BA''` and
`BB'` placements. -/
theorem opFamilyDistSq_place_BB'_eq_BA'' {X α : Type*} [Fintype α]
    (S : ProjectiveSetting P ε) (μ : Distribution X)
    (A B : X → α → Op (S.ExpandedLocalSpace .bob)) :
    opFamilyDistSq μ (fun x a => S.place .BB' (A x a))
        (fun x a => S.place .BB' (B x a)) S.psiHat =
      opFamilyDistSq μ (fun x a => S.place .BA'' (A x a))
        (fun x a => S.place .BA'' (B x a)) S.psiHat := by
  unfold opFamilyDistSq
  refine avgOver_congr _ _ _ fun x => Finset.sum_congr rfl fun a _ => ?_
  rw [← place_sub, ← place_sub, norm_place_BB'_eq_norm_place_BA'']
  all_goals rfl

end ProjectiveSetting

end

end MIPStarRE.QPBT
