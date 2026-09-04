import MIPStarRE.QPBT.Test.MagicSquareTheorems.PerfectStrategy.Measurements

/-!
# Perfect strategies for the Magic Square game

This file completes the construction of `thm:ms-from-ac`.  It identifies the
question pairs in the support of the Magic Square distribution, shows that the
measurement family commutes there and annihilates rejected answer pairs on the
EPR state, evaluates the Born weights of the accepted answers, and assembles a
symmetric SPCC strategy of value one from an anticommuting consistent pair of
binary measurements.

## References

The source statement is `thm:ms-from-ac` in
`blueprint/src/chapter/ch13_qpbt_test.tex:257-267`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:654-722`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

private theorem msConstraintVars_injective (i : Fin 6) :
    Function.Injective (msConstraintVars i) := by
  intro k l h
  fin_cases i <;> fin_cases k <;> fin_cases l <;>
    simp [msConstraintVars] at h ⊢

private theorem msConstraintVars_exists_iff
    (i : Fin 6) (k : Fin 3) (β : Fin 3 → ZMod 2) (b : ZMod 2) :
    (∃ l : Fin 3, msConstraintVars i l = msConstraintVars i k ∧ β l = b) ↔
      β k = b := by
  constructor
  · rintro ⟨l, hl, hlb⟩
    rwa [msConstraintVars_injective i hl] at hlb
  · intro h
    exact ⟨k, rfl, h⟩

private theorem msStrategyMeasurement_incident_commute
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin 9 → Measurement (ZMod 2) V)
    (hP : ∀ j, MIPStarRE.QPBT.Measurement.IsProjective (P j))
    (hcomm : ∀ i k l a b,
      Commute ((P (msConstraintVars i k)).effect a)
        ((P (msConstraintVars i l)).effect b))
    (i : Fin 6) (k : Fin 3) (a b : MsAnswer) :
    Commute ((msStrategyMeasurement P hP hcomm (.constraint i)).effect a)
      ((msStrategyMeasurement P hP hcomm
        (.var (msConstraintVars i k))).effect b) := by
  by_cases ha : a ∈ Set.range (fun ab => MsAnswer.triple (parityTriple i ab))
  · rcases ha with ⟨ab, rfl⟩
    rw [msStrategyMeasurement_constraint_triple]
    by_cases hb : b ∈ Set.range (MsAnswer.bit : ZMod 2 → MsAnswer)
    · rcases hb with ⟨c, rfl⟩
      rw [msStrategyMeasurement_var_bit]
      change Commute
        ((P (msConstraintVars i 0)).effect ab.1 *
          (P (msConstraintVars i 1)).effect ab.2)
        ((P (msConstraintVars i k)).effect c)
      exact (hcomm i 0 k ab.1 c).mul_left (hcomm i 1 k ab.2 c)
    · rw [msStrategyMeasurement_var_zero _ _ _ _ hb]
      exact Commute.zero_right _
  · rw [msStrategyMeasurement_constraint_zero _ _ _ _ ha]
    exact Commute.zero_left _

private theorem msStrategyMeasurement_rejected_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin 9 → Measurement (ZMod 2) V)
    (hP : ∀ j, MIPStarRE.QPBT.Measurement.IsProjective (P j))
    (hcomm : ∀ i k l a b,
      Commute ((P (msConstraintVars i k)).effect a)
        ((P (msConstraintVars i l)).effect b))
    (hmul : ∀ i k ab b,
      (msConstraintJoint P hP hcomm i).effect ab *
          (P (msConstraintVars i k)).effect b =
        if parityTriple i ab k = b then
          (msConstraintJoint P hP hcomm i).effect ab else 0)
    (i : Fin 6) (k : Fin 3) (a b : MsAnswer)
    (hrej : msWinPredicate (.constraint i) (.var (msConstraintVars i k)) a b = false) :
    ((msStrategyMeasurement P hP hcomm (.constraint i)).effect a) *
      ((msStrategyMeasurement P hP hcomm
        (.var (msConstraintVars i k))).effect b) = 0 := by
  by_cases ha : a ∈ Set.range (fun ab => MsAnswer.triple (parityTriple i ab))
  · rcases ha with ⟨ab, rfl⟩
    rw [msStrategyMeasurement_constraint_triple]
    by_cases hb : b ∈ Set.range (MsAnswer.bit : ZMod 2 → MsAnswer)
    · rcases hb with ⟨c, rfl⟩
      rw [msStrategyMeasurement_var_bit]
      have hne : parityTriple i ab k ≠ c := by
        simpa [msWinPredicate, parityTriple_sum,
          msConstraintVars_exists_iff] using hrej
      rw [hmul i k ab c]
      simp [hne]
    · rw [msStrategyMeasurement_var_zero _ _ _ _ hb]
      simp
  · rw [msStrategyMeasurement_constraint_zero _ _ _ _ ha]
    simp

private theorem msStrategyMeasurement_rejected_mul_reverse
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin 9 → Measurement (ZMod 2) V)
    (hP : ∀ j, MIPStarRE.QPBT.Measurement.IsProjective (P j))
    (hcomm : ∀ i k l a b,
      Commute ((P (msConstraintVars i k)).effect a)
        ((P (msConstraintVars i l)).effect b))
    (hmul : ∀ i k ab b,
      (msConstraintJoint P hP hcomm i).effect ab *
          (P (msConstraintVars i k)).effect b =
        if parityTriple i ab k = b then
          (msConstraintJoint P hP hcomm i).effect ab else 0)
    (i : Fin 6) (k : Fin 3) (a b : MsAnswer)
    (hrej : msWinPredicate (.var (msConstraintVars i k)) (.constraint i) a b = false) :
    ((msStrategyMeasurement P hP hcomm
        (.var (msConstraintVars i k))).effect a) *
      ((msStrategyMeasurement P hP hcomm (.constraint i)).effect b) = 0 := by
  rw [(msStrategyMeasurement_incident_commute P hP hcomm i k b a).symm.eq]
  exact msStrategyMeasurement_rejected_mul P hP hcomm hmul i k b a
    (by simpa [msWinPredicate_symm] using hrej)

private theorem msGame_support_incidence (x y : MsType)
    (hxy : (x, y) ∈ msGameSymm.μ.support) :
    (∃ i : Fin 6, ∃ k : Fin 3,
      x = .constraint i ∧ y = .var (msConstraintVars i k)) ∨
      ∃ i : Fin 6, ∃ k : Fin 3,
        x = .var (msConstraintVars i k) ∧ y = .constraint i := by
  change (x, y) ∈
    Finset.univ.filter (fun ab : MsType × MsType =>
      Sym2.mk ab.1 ab.2 ∈ msEdges) at hxy
  have hedge : Sym2.mk x y ∈ msEdges := (Finset.mem_filter.mp hxy).2
  rw [msEdges] at hedge
  rcases Finset.mem_image.mp hedge with ⟨⟨i, k⟩, _, hik⟩
  rcases Sym2.eq_iff.mp hik with hik | hik
  · left
    exact ⟨i, k, hik.1.symm, hik.2.symm⟩
  · right
    exact ⟨i, k, hik.2.symm, hik.1.symm⟩

private theorem msGame_positive_incidence (x y : MsType)
    (hxy : 0 < msGameSymm.μ.weight (x, y)) :
    (∃ i : Fin 6, ∃ k : Fin 3,
      x = .constraint i ∧ y = .var (msConstraintVars i k)) ∨
      ∃ i : Fin 6, ∃ k : Fin 3,
        x = .var (msConstraintVars i k) ∧ y = .constraint i := by
  apply msGame_support_incidence x y
  by_contra hnot
  rw [msGameSymm.μ.outsideSupport (x, y) hnot] at hxy
  exact (lt_irrefl 0 hxy)

private theorem msStrategyMeasurement_commuting
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin 9 → Measurement (ZMod 2) V)
    (hP : ∀ j, MIPStarRE.QPBT.Measurement.IsProjective (P j))
    (hcomm : ∀ i k l a b,
      Commute ((P (msConstraintVars i k)).effect a)
        ((P (msConstraintVars i l)).effect b)) :
    IsCommutingOn msGameSymm.μ
      (msStrategyMeasurement P hP hcomm)
      (msStrategyMeasurement P hP hcomm) := by
  intro x y hxy a b
  rcases msGame_positive_incidence x y hxy with hxy | hxy
  · rcases hxy with ⟨i, k, rfl, rfl⟩
    exact msStrategyMeasurement_incident_commute P hP hcomm i k a b
  · rcases hxy with ⟨i, k, rfl, rfl⟩
    exact (msStrategyMeasurement_incident_commute P hP hcomm i k b a).symm

private theorem msStrategyMeasurement_rejected_mul_on_support
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin 9 → Measurement (ZMod 2) V)
    (hP : ∀ j, MIPStarRE.QPBT.Measurement.IsProjective (P j))
    (hcomm : ∀ i k l a b,
      Commute ((P (msConstraintVars i k)).effect a)
        ((P (msConstraintVars i l)).effect b))
    (hmul : ∀ i k ab b,
      (msConstraintJoint P hP hcomm i).effect ab *
          (P (msConstraintVars i k)).effect b =
        if parityTriple i ab k = b then
          (msConstraintJoint P hP hcomm i).effect ab else 0)
    (x y : MsType) (hxy : (x, y) ∈ msGameSymm.μ.support)
    (a b : MsAnswer) (hrej : msWinPredicate x y a b = false) :
    ((msStrategyMeasurement P hP hcomm x).effect a) *
      ((msStrategyMeasurement P hP hcomm y).effect b) = 0 := by
  rcases msGame_support_incidence x y hxy with hxy | hxy
  · rcases hxy with ⟨i, k, rfl, rfl⟩
    exact msStrategyMeasurement_rejected_mul P hP hcomm hmul i k a b hrej
  · rcases hxy with ⟨i, k, rfl, rfl⟩
    exact msStrategyMeasurement_rejected_mul_reverse P hP hcomm hmul i k a b hrej

private theorem msStrategyMeasurement_effect_transpose
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin 9 → Measurement (ZMod 2) V)
    (hP : ∀ j, MIPStarRE.QPBT.Measurement.IsProjective (P j))
    (hcomm : ∀ i k l a b,
      Commute ((P (msConstraintVars i k)).effect a)
        ((P (msConstraintVars i l)).effect b))
    (hPt : ∀ j b, ((P j).effect b)ᵀ = (P j).effect b)
    (x : MsType) (a : MsAnswer) :
    ((msStrategyMeasurement P hP hcomm x).effect a)ᵀ =
      (msStrategyMeasurement P hP hcomm x).effect a := by
  cases x with
  | var j =>
      exact postprocess_effect_transpose (P j) MsAnswer.bit (hPt j) a
  | constraint i =>
      exact postprocess_effect_transpose (msConstraintJoint P hP hcomm i)
        (fun ab => .triple (parityTriple i ab))
        (msConstraintJoint_effect_transpose P hP hcomm hPt i) a

private theorem heteroKron_mulVec_epr_eq_zero_of_mul_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (E F : Op V) (hFt : Fᵀ = F) (hEF : E * F = 0) :
    (heteroKron E F).mulVec (eprState V) = 0 := by
  have hfactor : heteroKron E F =
      heteroKron E 1 * heteroKron 1 F := by
    rw [heteroKron_mul]
    simp
  rw [hfactor, ← Matrix.mulVec_mulVec,
    ← epr_action_eq_of_transpose F hFt, Matrix.mulVec_mulVec,
    heteroKron_mul, hEF]
  have hz : heteroKron (0 : Op V) (1 : Op V) = 0 := by
    ext ⟨i, k⟩ ⟨j, l⟩
    simp [heteroKron, Matrix.kronecker, Matrix.kroneckerMap_apply]
  simp only [mul_one]
  rw [hz]
  exact Matrix.zero_mulVec _

private theorem sum_heteroKron_measurement_effects
    {V : Type*} [Fintype V] [DecidableEq V]
    {A B : Type*} [Fintype A] [Fintype B]
    (M : Measurement A V) (N : Measurement B V) :
    ∑ a : A, ∑ b : B, heteroKron (M.effect a) (N.effect b) = 1 := by
  calc
    ∑ a : A, ∑ b : B, heteroKron (M.effect a) (N.effect b) =
        heteroKron (∑ a : A, M.effect a) (∑ b : B, N.effect b) := by
      ext p q
      rcases p with ⟨p₁, p₂⟩
      rcases q with ⟨q₁, q₂⟩
      simp only [heteroKron, Matrix.kronecker, Matrix.kroneckerMap_apply,
        Matrix.sum_apply]
      exact (Finset.sum_mul_sum Finset.univ Finset.univ
        (fun a => M.effect a p₁ q₁) (fun b => N.effect b p₂ q₂)).symm
    _ = heteroKron 1 1 := by rw [M.sum_eq_one, N.sum_eq_one]
    _ = 1 := heteroKron_one_one

private theorem sum_apply_measurement_effects
    {V : Type*} [Fintype V] [DecidableEq V]
    {A B : Type*} [Fintype A] [Fintype B]
    (M : Measurement A V) (N : Measurement B V)
    (psi : EuclideanSpace ℂ (V × V)) :
    ∑ a : A, ∑ b : B,
        applyOperatorToState (heteroKron (M.effect a) (N.effect b)) psi = psi := by
  calc
    ∑ a : A, ∑ b : B,
        applyOperatorToState (heteroKron (M.effect a) (N.effect b)) psi =
      applyOperatorToState
        (∑ a : A, ∑ b : B, heteroKron (M.effect a) (N.effect b)) psi := by
          simp [applyOperatorToState]
    _ = applyOperatorToState 1 psi := by
      rw [sum_heteroKron_measurement_effects M N]
    _ = psi := by simp [applyOperatorToState]

private theorem sum_born_weights_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    {A B : Type*} [Fintype A] [Fintype B]
    (M : Measurement A V) (N : Measurement B V)
    (psi : EuclideanSpace ℂ (V × V)) (hpsi : ‖psi‖ = 1) :
    ∑ a : A, ∑ b : B,
        (inner ℂ psi
          (applyOperatorToState
            (heteroKron (M.effect a) (N.effect b)) psi)).re = 1 := by
  calc
    ∑ a : A, ∑ b : B,
        (inner ℂ psi
          (applyOperatorToState
            (heteroKron (M.effect a) (N.effect b)) psi)).re =
      (inner ℂ psi
        (∑ a : A, ∑ b : B,
          applyOperatorToState
            (heteroKron (M.effect a) (N.effect b)) psi)).re := by
              simp only [inner_sum, Complex.re_sum]
    _ = (inner ℂ psi psi).re := by rw [sum_apply_measurement_effects M N psi]
    _ = 1 := by
      calc
        (inner ℂ psi psi).re = ‖psi‖ ^ 2 :=
          inner_self_eq_norm_sq (𝕜 := ℂ) psi
        _ = 1 := by simp [hpsi]

private theorem rejected_born_weight_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Fin 9 → Measurement (ZMod 2) V)
    (hP : ∀ j, MIPStarRE.QPBT.Measurement.IsProjective (P j))
    (hcomm : ∀ i k l a b,
      Commute ((P (msConstraintVars i k)).effect a)
        ((P (msConstraintVars i l)).effect b))
    (hmul : ∀ i k ab b,
      (msConstraintJoint P hP hcomm i).effect ab *
          (P (msConstraintVars i k)).effect b =
        if parityTriple i ab k = b then
          (msConstraintJoint P hP hcomm i).effect ab else 0)
    (hPt : ∀ j b, ((P j).effect b)ᵀ = (P j).effect b)
    (x y : MsType) (hxy : (x, y) ∈ msGameSymm.μ.support)
    (a b : MsAnswer) (hrej : msWinPredicate x y a b = false) :
    (inner ℂ (eprState V)
      (applyOperatorToState
        (heteroKron
          ((msStrategyMeasurement P hP hcomm x).effect a)
          ((msStrategyMeasurement P hP hcomm y).effect b))
        (eprState V))).re = 0 := by
  have hmul_zero :=
    msStrategyMeasurement_rejected_mul_on_support
      P hP hcomm hmul x y hxy a b hrej
  have hright_transpose :=
    msStrategyMeasurement_effect_transpose P hP hcomm hPt y b
  have hzero := heteroKron_mulVec_epr_eq_zero_of_mul_eq_zero
    ((msStrategyMeasurement P hP hcomm x).effect a)
    ((msStrategyMeasurement P hP hcomm y).effect b)
    hright_transpose hmul_zero
  have hacted :
      applyOperatorToState
        (heteroKron
          ((msStrategyMeasurement P hP hcomm x).effect a)
          ((msStrategyMeasurement P hP hcomm y).effect b))
        (eprState V) = 0 := by
    rw [applyOperatorToState, Matrix.toLpLin_apply, hzero]
    rfl
  rw [hacted]
  simp

private theorem accepted_born_weights_eq_one
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Fin 9 → Measurement (ZMod 2) V)
    (hP : ∀ j, MIPStarRE.QPBT.Measurement.IsProjective (P j))
    (hcomm : ∀ i k l a b,
      Commute ((P (msConstraintVars i k)).effect a)
        ((P (msConstraintVars i l)).effect b))
    (hmul : ∀ i k ab b,
      (msConstraintJoint P hP hcomm i).effect ab *
          (P (msConstraintVars i k)).effect b =
        if parityTriple i ab k = b then
          (msConstraintJoint P hP hcomm i).effect ab else 0)
    (hPt : ∀ j b, ((P j).effect b)ᵀ = (P j).effect b)
    (x y : MsType) (hxy : (x, y) ∈ msGameSymm.μ.support) :
    ∑ a : MsAnswer, ∑ b : MsAnswer,
      (if msWinPredicate x y a b then
        (inner ℂ (eprState V)
          (applyOperatorToState
            (heteroKron
              ((msStrategyMeasurement P hP hcomm x).effect a)
              ((msStrategyMeasurement P hP hcomm y).effect b))
            (eprState V))).re
      else 0) = 1 := by
  calc
    ∑ a : MsAnswer, ∑ b : MsAnswer,
        (if msWinPredicate x y a b then
          (inner ℂ (eprState V)
            (applyOperatorToState
              (heteroKron
                ((msStrategyMeasurement P hP hcomm x).effect a)
                ((msStrategyMeasurement P hP hcomm y).effect b))
              (eprState V))).re
        else 0) =
      ∑ a : MsAnswer, ∑ b : MsAnswer,
        (inner ℂ (eprState V)
          (applyOperatorToState
            (heteroKron
              ((msStrategyMeasurement P hP hcomm x).effect a)
              ((msStrategyMeasurement P hP hcomm y).effect b))
            (eprState V))).re := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      by_cases hab : msWinPredicate x y a b = true
      · simp [hab]
      · have hab_false := Bool.eq_false_of_not_eq_true hab
        rw [rejected_born_weight_eq_zero
          P hP hcomm hmul hPt x y hxy a b hab_false]
        simp [hab_false]
    _ = 1 := sum_born_weights_eq_one
      (msStrategyMeasurement P hP hcomm x)
      (msStrategyMeasurement P hP hcomm y)
      (eprState V) (eprState_norm V)

private theorem reflectionEffect_heteroKron_one
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (O : Op V) (b : ZMod 2) :
    reflectionEffect (heteroKron O (1 : Op W)) b =
      heteroKron (reflectionEffect O b) (1 : Op W) := by
  rcases zmod_two_eq_zero_or_one b with rfl | rfl <;>
    ext ⟨i, k⟩ ⟨j, l⟩ <;>
      by_cases hkl : k = l <;> by_cases hij : i = j <;>
        simp [reflectionEffect, heteroKron, Matrix.kronecker,
          Matrix.kroneckerMap_apply, hkl, hij]
  all_goals ring

/-- `thm:ms-from-ac`: any anticommuting pair of projective binary
measurements, consistent on an EPR state, extends to a value-one SPCC Magic
Square strategy. Blueprint `ch13_qpbt_test.tex:257-267`, paper
`08_classical_and_quantum_low_degree_tests.tex:654-722`.

The local index type is arbitrary, finite, and nonempty; no field model or QPBT
parameter is assumed. The equality `hι` identifies the target local Hilbert
space with the constructed tensor factor. -/
theorem exists_ms_perfect_strategy_of_anticommuting
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A B : Measurement (ZMod 2) ι)
    (hA : MIPStarRE.QPBT.Measurement.IsProjective A)
    (hB : MIPStarRE.QPBT.Measurement.IsProjective B)
    (hcA : MIPStarRE.QPBT.Measurement.IsConsistentOn A (eprState ι))
    (hcB : MIPStarRE.QPBT.Measurement.IsConsistentOn B (eprState ι))
    (hac : obsOf A * obsOf B = -(obsOf B * obsOf A)) :
    ∃ S : SymmetricStrategy msGameSymm, ∃ hι : S.ι = (ι × ZMod 2),
      S.IsSPCC ∧ S.toStrategy.value = 1 ∧
      reindexState (Equiv.prodCongr (Equiv.cast hι) (Equiv.cast hι)) S.ψ =
        msPerfectState ι ∧
      ∀ b : ZMod 2,
        reindexOp (Equiv.cast hι.symm) ((S.M (.var 0)).effect (.bit b)) =
            heteroKron (A.effect b) (1 : Op (ZMod 2)) ∧
          reindexOp (Equiv.cast hι.symm) ((S.M (.var 4)).effect (.bit b)) =
            heteroKron (B.effect b) (1 : Op (ZMod 2)) := by
  have hAt : ∀ b, (A.effect b)ᵀ = A.effect b := fun b =>
    transpose_eq_of_epr_action (A.effect b) (hcA b)
  have hBt : ∀ b, (B.effect b)ᵀ = B.effect b := fun b =>
    transpose_eq_of_epr_action (B.effect b) (hcB b)
  have hOAt : (obsOf A)ᵀ = obsOf A := by
    rw [obsOf, Matrix.transpose_sub, hAt 0, hAt 1]
  have hOBt : (obsOf B)ᵀ = obsOf B := by
    rw [obsOf, Matrix.transpose_sub, hBt 0, hBt 1]
  let P := msCellMeasurement (obsOf A) (obsOf B)
    (obsOf_conjTranspose A hA) (obsOf_conjTranspose B hB)
    (obsOf_sq A hA) (obsOf_sq B hB) hac
  let hP := msCellMeasurement_projective (obsOf A) (obsOf B)
    (obsOf_conjTranspose A hA) (obsOf_conjTranspose B hB)
    (obsOf_sq A hA) (obsOf_sq B hB) hac
  let hcomm : ∀ i k l a b,
      Commute ((P (msConstraintVars i k)).effect a)
        ((P (msConstraintVars i l)).effect b) :=
    fun i k l a b => reflectionEffect_commute
      (msConstraintObservable_commute (obsOf A) (obsOf B)
        (obsOf_sq A hA) (obsOf_sq B hB) hac i k l) a b
  let hPt : ∀ j b, ((P j).effect b)ᵀ = (P j).effect b :=
    msCellMeasurement_transpose (obsOf A) (obsOf B)
      (obsOf_conjTranspose A hA) (obsOf_conjTranspose B hB)
      (obsOf_sq A hA) (obsOf_sq B hB) hOAt hOBt hac
  let hmul : ∀ i k ab b,
      (msConstraintJoint P hP hcomm i).effect ab *
          (P (msConstraintVars i k)).effect b =
        if parityTriple i ab k = b then
          (msConstraintJoint P hP hcomm i).effect ab else 0 :=
    msCellConstraintJoint_mul (obsOf A) (obsOf B)
      (obsOf_conjTranspose A hA) (obsOf_conjTranspose B hB)
      (obsOf_sq A hA) (obsOf_sq B hB) hac
  let M := msStrategyMeasurement P hP hcomm
  let S : SymmetricStrategy msGameSymm :=
    { ι := ι × ZMod 2
      ψ := eprState (ι × ZMod 2)
      ψ_norm := eprState_norm (ι × ZMod 2)
      ψ_swap := reindexState_prodComm_eprState (ι × ZMod 2)
      M := M }
  refine ⟨S, rfl, ?_, ?_, ?_, ?_⟩
  · refine ⟨msStrategyMeasurement_projective P hP hcomm, ?_,
      msStrategyMeasurement_commuting P hP hcomm⟩
    intro x a
    exact epr_action_eq_of_transpose _
      (msStrategyMeasurement_effect_transpose P hP hcomm hPt x a)
  · change avgOver msGameSymm.μ (fun xy =>
      ∑ a : MsAnswer, ∑ b : MsAnswer,
        (if msWinPredicate xy.1 xy.2 a b then
          (inner ℂ (eprState (ι × ZMod 2))
            (applyOperatorToState
              (heteroKron ((M xy.1).effect a) ((M xy.2).effect b))
              (eprState (ι × ZMod 2)))).re
        else 0)) = 1
    calc
      avgOver msGameSymm.μ (fun xy =>
          ∑ a : MsAnswer, ∑ b : MsAnswer,
            (if msWinPredicate xy.1 xy.2 a b then
              (inner ℂ (eprState (ι × ZMod 2))
                (applyOperatorToState
                  (heteroKron ((M xy.1).effect a) ((M xy.2).effect b))
                  (eprState (ι × ZMod 2)))).re
            else 0)) = avgOver msGameSymm.μ (fun _ => 1) := by
        apply avgOver_congr_on_support
        rintro ⟨x, y⟩ hxy
        exact accepted_born_weights_eq_one P hP hcomm hmul hPt x y hxy
      _ = 1 := avgOver_const_of_isProbability _ msGameSymm.μ_prob 1
  · change eprState (ι × ZMod 2) = msPerfectState ι
    exact (msPerfectState_eq_eprState ι).symm
  · intro b
    constructor
    · simp only [S, Equiv.cast_refl, reindexOp]
      rw [msStrategyMeasurement_var_bit P hP hcomm]
      change reflectionEffect
          (heteroKron (obsOf A) (1 : Op (ZMod 2))) b =
        heteroKron (A.effect b) (1 : Op (ZMod 2))
      rw [reflectionEffect_heteroKron_one,
        reflectionEffect_obsOf_measurement]
    · simp only [S, Equiv.cast_refl, reindexOp]
      rw [msStrategyMeasurement_var_bit P hP hcomm]
      change reflectionEffect
          (heteroKron (obsOf B) (1 : Op (ZMod 2))) b =
        heteroKron (B.effect b) (1 : Op (ZMod 2))
      rw [reflectionEffect_heteroKron_one,
        reflectionEffect_obsOf_measurement]

end

end MIPStarRE.QPBT
