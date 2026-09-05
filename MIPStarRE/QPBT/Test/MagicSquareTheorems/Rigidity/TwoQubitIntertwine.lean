import MIPStarRE.QPBT.Test.MagicSquareTheorems.Rigidity.JointState

/-!
# Intertwining the first logical pair with the ideal two-qubit Pauli basis

The bit-measurement conclusions of `thm:ms-rigidity` compare a player's
variable-0 and variable-4 measurements with the marginals of the two-qubit
Pauli basis over the *first* register coordinate.  This file identifies those
marginals with the spectral effects of the two-qubit Pauli observable at the
label `Pi.single 0 1` and proves the two intertwining relations that the
two-qubit controlled swap satisfies: the phase observable is transported
exactly, and the shift observable up to the anticommutator defect of the first
logical pair.

Both relations are proved in the joint form in which the assembly uses them,
that is, after tensoring with the other player's controlled swap: the estimate
for the shift then contracts the second register coordinate and the other
player's register through the completeness of the residual factors.

## References

`thm:ms-rigidity`, blueprint `blueprint/src/chapter/ch13_qpbt_test.tex:224-253`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`;
the generalized Pauli basis is `def:generalized-pauli`, blueprint
`ch11_qpbt_algebra.tex:494-688`, paper `04_preliminaries.tex:908-1161`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-! ## The residual factors of one controlled swap -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The residual factors of a controlled swap absorb the phase reflection with
the sign of the register label. -/
theorem swapFactor_mul_obs {X Z : Op ι} (hZ : IsBinaryObservable Z) (b : ZMod 2) :
    swapFactor X Z b * Z = phaseSign b • swapFactor X Z b := by
  rcases zmod_two_eq_zero_or_one b with rfl | rfl
  · rw [swapFactor_zero, reflectionEffect_zero_mul_reflection Z hZ, phaseSign,
      if_pos rfl, one_smul]
  · rw [swapFactor_one, phaseSign, if_neg one_ne_zero, Matrix.mul_assoc,
      reflectionEffect_one_mul_reflection Z hZ, mul_neg, neg_one_smul]

/-- The residual factors of a controlled swap form a complete family. -/
theorem sum_swapFactor_conjTranspose_mul {X Z : Op ι} (hX : IsBinaryObservable X)
    (hZ : IsBinaryObservable Z) :
    (∑ b : ZMod 2, (swapFactor X Z b)ᴴ * swapFactor X Z b) = 1 := by
  have hP : ∀ b : ZMod 2, (reflectionEffect Z b)ᴴ = reflectionEffect Z b := fun b => by
    have := (isProj_reflectionEffect hZ b).isSelfAdjoint.star_eq
    rwa [Matrix.star_eq_conjTranspose] at this
  have hPP : ∀ b : ZMod 2, reflectionEffect Z b * reflectionEffect Z b =
      reflectionEffect Z b := fun b => (isProj_reflectionEffect hZ b).isIdempotentElem.eq
  have hone : reflectionEffect Z 0 + reflectionEffect Z 1 = 1 := by
    simp only [reflectionEffect, if_pos, if_neg one_ne_zero]
    module
  have h0 : (swapFactor X Z 0)ᴴ * swapFactor X Z 0 = reflectionEffect Z 0 := by
    rw [swapFactor_zero, hP, hPP]
  have h1 : (swapFactor X Z 1)ᴴ * swapFactor X Z 1 = reflectionEffect Z 1 := by
    rw [swapFactor_one, Matrix.conjTranspose_mul, hX.conjTranspose_eq, hP]
    calc reflectionEffect Z 1 * X * (X * reflectionEffect Z 1)
        = reflectionEffect Z 1 * (X * X) * reflectionEffect Z 1 := by noncomm_ring
      _ = reflectionEffect Z 1 := by rw [hX.mul_self_eq_one, Matrix.mul_one, hPP]
  rw [sum_zmod_two, h0, h1, hone]

/-- The residual factors of the swap of the second pair, placed on the left, are
a complete family. -/
theorem sum_leftTensor_swapFactor {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB] {X Z : Op ιA} (hX : IsBinaryObservable X)
    (hZ : IsBinaryObservable Z) :
    (∑ b : ZMod 2, (heteroKron (swapFactor X Z b) (1 : Op ιB))ᴴ *
      heteroKron (swapFactor X Z b) (1 : Op ιB)) = 1 := by
  have hstep : ∀ b : ZMod 2, (heteroKron (swapFactor X Z b) (1 : Op ιB))ᴴ *
      heteroKron (swapFactor X Z b) (1 : Op ιB) =
      heteroKron ((swapFactor X Z b)ᴴ * swapFactor X Z b) (1 : Op ιB) := by
    intro b
    rw [heteroKron_conjTranspose, Matrix.conjTranspose_one, heteroKron_mul, mul_one]
  rw [Finset.sum_congr rfl fun b (_ : b ∈ (Finset.univ : Finset (ZMod 2))) => hstep b,
    ← heteroKron_finset_sum_left, sum_swapFactor_conjTranspose_mul hX hZ,
    heteroKron_one_one]

/-- The residual factors of the swap of the second pair, placed on the right,
are a complete family. -/
theorem sum_rightTensor_swapFactor {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB] {X Z : Op ιB} (hX : IsBinaryObservable X)
    (hZ : IsBinaryObservable Z) :
    (∑ b : ZMod 2, (heteroKron (1 : Op ιA) (swapFactor X Z b))ᴴ *
      heteroKron (1 : Op ιA) (swapFactor X Z b)) = 1 := by
  have hstep : ∀ b : ZMod 2, (heteroKron (1 : Op ιA) (swapFactor X Z b))ᴴ *
      heteroKron (1 : Op ιA) (swapFactor X Z b) =
      heteroKron (1 : Op ιA) ((swapFactor X Z b)ᴴ * swapFactor X Z b) := by
    intro b
    rw [heteroKron_conjTranspose, Matrix.conjTranspose_one, heteroKron_mul, mul_one]
  rw [Finset.sum_congr rfl fun b (_ : b ∈ (Finset.univ : Finset (ZMod 2))) => hstep b,
    ← heteroKron_finset_sum_right, sum_swapFactor_conjTranspose_mul hX hZ,
    heteroKron_one_one]

/-! ## The ideal two-qubit Pauli observable -/

/-- The two-qubit Pauli observable read by the first extracted register
coordinate: the generalized Pauli observable at the label `Pi.single 0 1`. -/
noncomputable def twoQubitPauliObs (W : PauliKind) : Op (Fin 2 → ZMod 2) :=
  tauObservable (K := ZMod 2) W (Pi.single 0 1)

/-- The binary trace of the two-element field is the identity. -/
theorem binTrace_zmod_two (x : ZMod 2) : binTrace (ZMod 2) x = x := by
  simp

/-- The marginal of the two-qubit Pauli basis over the first register coordinate
is the spectral effect of the corresponding Pauli observable.  The left-hand
side is the definition of `idealMagicBitProj` in the rigidity facade. -/
theorem sum_ite_pauliProj_eq_reflectionEffect (W : PauliKind) (b : ZMod 2) :
    (∑ e : Fin 2 → ZMod 2, if e 0 = b then pauliProj (K := ZMod 2) W e else 0) =
      reflectionEffect (twoQubitPauliObs W) b := by
  have hphase : ∀ e : Fin 2 → ZMod 2,
      phaseSign (binTrace (ZMod 2) (dotProduct (Pi.single (0 : Fin 2) (1 : ZMod 2)) e)) =
        phaseSign (e 0) := by
    intro e
    congr 1
    rw [binTrace_zmod_two]
    simp [dotProduct, Pi.single_apply]
  have hexp : twoQubitPauliObs W =
      ∑ e : Fin 2 → ZMod 2, phaseSign (e 0) • pauliProj W e := by
    rw [twoQubitPauliObs, tauObservable_eq_sum_pauliProj]
    exact Finset.sum_congr rfl fun e _ => by rw [hphase]
  have hsum : (∑ e : Fin 2 → ZMod 2, pauliProj (K := ZMod 2) W e) = 1 :=
    sum_pauliProj_eq_one W
  rcases zmod_two_eq_zero_or_one b with rfl | rfl
  · rw [reflectionEffect, if_pos rfl, hexp, ← hsum, ← Finset.sum_add_distrib,
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rcases zmod_two_eq_zero_or_one (e 0) with h | h
    · rw [h, if_pos rfl, phaseSign, if_pos rfl]
      module
    · rw [h, if_neg one_ne_zero, phaseSign, if_neg one_ne_zero]
      module
  · rw [reflectionEffect, if_neg one_ne_zero, hexp, ← hsum, ← Finset.sum_sub_distrib,
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rcases zmod_two_eq_zero_or_one (e 0) with h | h
    · rw [h, if_neg (zero_ne_one : (0 : ZMod 2) ≠ 1), phaseSign, if_pos rfl]
      module
    · rw [h, if_pos rfl, phaseSign, if_neg one_ne_zero]
      module

/-! ## The register action of a placed operator -/

/-- The coordinates of a left-placed operator. -/
theorem applyOperatorToState_leftTensor_coord {κA κB : Type} [Fintype κA] [DecidableEq κA]
    [Fintype κB] [DecidableEq κB] (N : Op κA) (u : EuclideanSpace ℂ (κA × κB))
    (a : κA) (b : κB) :
    applyOperatorToState (heteroKron N (1 : Op κB)) u (a, b) =
      ∑ a' : κA, N a a' * u (a', b) := by
  rw [applyOperatorToState_coord, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a' _ => ?_
  have hentry : ∀ b' : κB, heteroKron N (1 : Op κB) (a, b) (a', b') * u (a', b') =
      if b = b' then N a a' * u (a', b') else 0 := by
    intro b'
    by_cases h : b = b'
    · subst h
      simp [heteroKron, Matrix.kronecker]
    · simp [heteroKron, Matrix.kronecker, h]
  rw [Finset.sum_congr rfl fun b' _ => hentry b', Finset.sum_ite_eq]
  simp

/-- The coordinates of a register operator placed on Alice's extracted
register. -/
theorem applyOperatorToState_register_coord {κ ιA ιB : Type} [Fintype κ] [DecidableEq κ]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] (M : Op κ)
    (u : EuclideanSpace ℂ ((κ × ιA) × (κ × ιB))) (e : κ) (i : ιA) (f : κ) (j : ιB) :
    applyOperatorToState
        (heteroKron (heteroKron M (1 : Op ιA)) (1 : Op (κ × ιB))) u ((e, i), (f, j)) =
      ∑ e' : κ, M e e' * u ((e', i), (f, j)) := by
  rw [applyOperatorToState_leftTensor_coord, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun e' _ => ?_
  have hentry : ∀ i' : ιA,
      heteroKron M (1 : Op ιA) (e, i) (e', i') * u ((e', i'), (f, j)) =
      if i = i' then M e e' * u ((e', i'), (f, j)) else 0 := by
    intro i'
    by_cases h : i = i'
    · subst h
      simp [heteroKron, Matrix.kronecker]
    · simp [heteroKron, Matrix.kronecker, h]
  rw [Finset.sum_congr rfl fun i' _ => hentry i', Finset.sum_ite_eq]
  simp

/-! ## Coordinates of the ideal two-qubit Pauli observables -/

/-- The two-qubit phase observable is diagonal with the sign of the first
register coordinate. -/
theorem twoQubitPauliObs_Z_apply (x y : Fin 2 → ZMod 2) :
    twoQubitPauliObs .Z x y = if x = y then phaseSign (y 0) else 0 := by
  have h0 : (Pi.single (0 : Fin 2) (1 : ZMod 2) : Fin 2 → ZMod 2) 0 = 1 := by simp
  have h1 : (Pi.single (0 : Fin 2) (1 : ZMod 2) : Fin 2 → ZMod 2) 1 = 0 := by simp
  show (∏ i : Fin 2, tauPhase (K := ZMod 2)
    ((Pi.single (0 : Fin 2) (1 : ZMod 2) : Fin 2 → ZMod 2) i) (x i) (y i)) = _
  rw [Fin.prod_univ_two, h0, h1]
  simp only [tauPhase, binTrace_zmod_two, one_mul, zero_mul, phaseSign]
  by_cases hxy : x = y
  · subst hxy
    simp
  · rw [if_neg hxy]
    by_cases h : x 0 = y 0
    · have h' : x 1 ≠ y 1 := fun hc => hxy (pi_fin_two_ext h hc)
      simp [h, h']
    · simp [h]

/-- The two-qubit shift observable is the shift of the first register
coordinate. -/
theorem twoQubitPauliObs_X_apply (x y : Fin 2 → ZMod 2) :
    twoQubitPauliObs .X x y =
      if x = y + Pi.single (0 : Fin 2) (1 : ZMod 2) then 1 else 0 := by
  have h0 : (Pi.single (0 : Fin 2) (1 : ZMod 2) : Fin 2 → ZMod 2) 0 = 1 := by simp
  have h1 : (Pi.single (0 : Fin 2) (1 : ZMod 2) : Fin 2 → ZMod 2) 1 = 0 := by simp
  show (∏ i : Fin 2, tauShift (K := ZMod 2)
    ((Pi.single (0 : Fin 2) (1 : ZMod 2) : Fin 2 → ZMod 2) i) (x i) (y i)) = _
  rw [Fin.prod_univ_two, h0, h1]
  simp only [tauShift]
  by_cases hxy : x = y + Pi.single (0 : Fin 2) (1 : ZMod 2)
  · have e0 : x 0 = y 0 + 1 := by rw [hxy]; simp
    have e1 : x 1 = y 1 + 0 := by rw [hxy]; simp
    rw [if_pos hxy, if_pos e0, if_pos e1, one_mul]
  · rw [if_neg hxy]
    by_cases h : x 0 = y 0 + 1
    · have h' : x 1 ≠ y 1 + 0 := by
        intro hc
        refine hxy (pi_fin_two_ext ?_ ?_)
        · rw [h]; simp
        · rw [hc]; simp
      rw [if_neg h', mul_zero]
    · rw [if_neg h, zero_mul]

/-! ## Completeness of the two-qubit residual factors -/

/-- The residual factors of a two-qubit controlled swap form a complete
family. -/
theorem sum_twoSwapFactor_conjTranspose_mul {X₁ Z₁ X₂ Z₂ : Op ι}
    (hX₁ : IsBinaryObservable X₁) (hZ₁ : IsBinaryObservable Z₁)
    (hX₂ : IsBinaryObservable X₂) (hZ₂ : IsBinaryObservable Z₂) :
    (∑ e : Fin 2 → ZMod 2,
      (swapFactor X₂ Z₂ (e 1) * swapFactor X₁ Z₁ (e 0))ᴴ *
        (swapFactor X₂ Z₂ (e 1) * swapFactor X₁ Z₁ (e 0))) = 1 := by
  rw [sum_pi_fin_two (fun b c => (swapFactor X₂ Z₂ c * swapFactor X₁ Z₁ b)ᴴ *
    (swapFactor X₂ Z₂ c * swapFactor X₁ Z₁ b))]
  have hinner : ∀ b : ZMod 2, (∑ c : ZMod 2,
      (swapFactor X₂ Z₂ c * swapFactor X₁ Z₁ b)ᴴ *
        (swapFactor X₂ Z₂ c * swapFactor X₁ Z₁ b)) =
      (swapFactor X₁ Z₁ b)ᴴ * swapFactor X₁ Z₁ b := by
    intro b
    have hstep : ∀ c : ZMod 2, (swapFactor X₂ Z₂ c * swapFactor X₁ Z₁ b)ᴴ *
        (swapFactor X₂ Z₂ c * swapFactor X₁ Z₁ b) =
        (swapFactor X₁ Z₁ b)ᴴ * ((swapFactor X₂ Z₂ c)ᴴ * swapFactor X₂ Z₂ c) *
          swapFactor X₁ Z₁ b := by
      intro c
      rw [Matrix.conjTranspose_mul]
      noncomm_ring
    rw [Finset.sum_congr rfl fun c _ => hstep c, ← Finset.sum_mul, ← Finset.mul_sum,
      sum_swapFactor_conjTranspose_mul hX₂ hZ₂, Matrix.mul_one]
  rw [Finset.sum_congr rfl fun b _ => hinner b, sum_swapFactor_conjTranspose_mul hX₁ hZ₁]

/-- The right-placed residual factors of a two-qubit controlled swap form a
complete family. -/
theorem sum_rightTensor_twoSwapFactor {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB] {X₁ Z₁ X₂ Z₂ : Op ιB}
    (hX₁ : IsBinaryObservable X₁) (hZ₁ : IsBinaryObservable Z₁)
    (hX₂ : IsBinaryObservable X₂) (hZ₂ : IsBinaryObservable Z₂) :
    (∑ f : Fin 2 → ZMod 2,
      (heteroKron (1 : Op ιA) (swapFactor X₂ Z₂ (f 1) * swapFactor X₁ Z₁ (f 0)))ᴴ *
        heteroKron (1 : Op ιA)
          (swapFactor X₂ Z₂ (f 1) * swapFactor X₁ Z₁ (f 0))) = 1 := by
  have hstep : ∀ f : Fin 2 → ZMod 2,
      (heteroKron (1 : Op ιA) (swapFactor X₂ Z₂ (f 1) * swapFactor X₁ Z₁ (f 0)))ᴴ *
        heteroKron (1 : Op ιA)
          (swapFactor X₂ Z₂ (f 1) * swapFactor X₁ Z₁ (f 0)) =
      heteroKron (1 : Op ιA)
        ((swapFactor X₂ Z₂ (f 1) * swapFactor X₁ Z₁ (f 0))ᴴ *
          (swapFactor X₂ Z₂ (f 1) * swapFactor X₁ Z₁ (f 0))) := by
    intro f
    rw [heteroKron_conjTranspose, Matrix.conjTranspose_one, heteroKron_mul, mul_one]
  rw [Finset.sum_congr rfl
      fun f (_ : f ∈ (Finset.univ : Finset (Fin 2 → ZMod 2))) => hstep f,
    ← heteroKron_finset_sum_right,
    sum_twoSwapFactor_conjTranspose_mul hX₁ hZ₁ hX₂ hZ₂, heteroKron_one_one]

end

end MIPStarRE.QPBT.MagicSquareRigidity
