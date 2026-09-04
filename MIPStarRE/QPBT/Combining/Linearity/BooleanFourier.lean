import MIPStarRE.LDT.Preliminaries.FiniteFields
import MIPStarRE.QPBT.Combining.Linearity

/-!
# Boolean Fourier analysis for the quantum linearity theorem

This file develops the finite Fourier identities used in the proof of the
quantum linearity theorem.  The Boolean characters are the additive characters
of `𝔽_2^t`; their orthogonality gives Fourier inversion and matrix-valued
Parseval for operator families.  The final section records the normalization
relating the state-dependent operator distance to the distance between the
associated binary projective measurements.

## References

The Fourier and Parseval argument is Theorem 10, equations (7)--(8), and its
proof in `references/nv-paper/fullpaper.tex:1074-1112`.  The observable-distance
calculation is in the same source at lines 900--912.  The QPBT paper invokes
this theorem in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:711-725`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.Quantum

noncomputable section

/-! ## Boolean characters -/

/-- The character `a |-> (-1)^(a dot u)` on the Boolean cube `𝔽_2^t`.

This is the scalar character used in the Fourier transform at
`references/nv-paper/fullpaper.tex:1095-1098`. -/
noncomputable def booleanCharacter {t : ℕ}
    (u a : Fin t → ZMod 2) : ℂ :=
  MIPStarRE.LDT.Preliminaries.ffVecChar (p := 2) (F := ZMod 2) u a

/-- Formalization-only auxiliary lemma for the Fourier transform at
`references/nv-paper/fullpaper.tex:1095-1098`: a Boolean character is
multiplicative in its argument. -/
theorem booleanCharacter_add_right {t : ℕ} (u a b : Fin t → ZMod 2) :
    booleanCharacter u (a + b) = booleanCharacter u a * booleanCharacter u b := by
  exact AddChar.map_add_eq_mul
    (MIPStarRE.LDT.Preliminaries.ffVecChar (p := 2) (F := ZMod 2) u) a b

/-- Formalization-only auxiliary lemma for the Fourier transform at
`references/nv-paper/fullpaper.tex:1095-1098`: the Boolean pairing defining
the characters is symmetric. -/
theorem booleanCharacter_comm {t : ℕ} (u a : Fin t → ZMod 2) :
    booleanCharacter u a = booleanCharacter a u := by
  simp only [booleanCharacter, MIPStarRE.LDT.Preliminaries.ffVecChar_apply]
  have hdot : MIPStarRE.LDT.Preliminaries.ffDotProduct a u =
      MIPStarRE.LDT.Preliminaries.ffDotProduct u a := by
    unfold MIPStarRE.LDT.Preliminaries.ffDotProduct
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  rw [hdot]

/-- Formalization-only auxiliary lemma for the Fourier transform at
`references/nv-paper/fullpaper.tex:1095-1098`: a Boolean character is
multiplicative in its frequency. -/
theorem booleanCharacter_add_left {t : ℕ} (u v a : Fin t → ZMod 2) :
    booleanCharacter (u + v) a = booleanCharacter u a * booleanCharacter v a := by
  rw [booleanCharacter_comm, booleanCharacter_add_right]
  rw [booleanCharacter_comm a u, booleanCharacter_comm a v]

/-- Formalization-only auxiliary lemma for the Fourier transform at
`references/nv-paper/fullpaper.tex:1095-1098`: a Boolean character takes
the value one at the zero argument. -/
@[simp]
theorem booleanCharacter_zero_right {t : ℕ} (u : Fin t → ZMod 2) :
    booleanCharacter u 0 = 1 := by
  change MIPStarRE.LDT.Preliminaries.ffVecChar (p := 2) (F := ZMod 2) u 0 = 1
  exact AddChar.map_zero_eq_one _

/-- Formalization-only auxiliary lemma for the Fourier transform at
`references/nv-paper/fullpaper.tex:1095-1098`: a Boolean character takes
the value one at the zero frequency. -/
@[simp]
theorem booleanCharacter_zero_left {t : ℕ} (a : Fin t → ZMod 2) :
    booleanCharacter 0 a = 1 := by
  rw [booleanCharacter_comm]
  exact booleanCharacter_zero_right a

/-- Formalization-only auxiliary lemma for the Fourier transform at
`references/nv-paper/fullpaper.tex:1095-1098`: every Boolean character
takes values whose square is one. -/
theorem booleanCharacter_mul_self {t : ℕ} (u a : Fin t → ZMod 2) :
    booleanCharacter u a * booleanCharacter u a = 1 := by
  rw [← booleanCharacter_add_right]
  have haa : a + a = 0 := by
    ext i
    exact CharTwo.add_self_eq_zero (a i)
  rw [haa, booleanCharacter_zero_right]

/-- Formalization-only auxiliary lemma for the Fourier transform at
`references/nv-paper/fullpaper.tex:1095-1098`: Boolean characters are real,
hence fixed by complex conjugation. -/
theorem star_booleanCharacter {t : ℕ} (u a : Fin t → ZMod 2) :
    star (booleanCharacter u a) = booleanCharacter u a := by
  rcases mul_self_eq_one_iff.mp (booleanCharacter_mul_self u a) with h | h
  · simp [h]
  · simp [h]

/-- Formalization-only auxiliary lemma for the Fourier transform at
`references/nv-paper/fullpaper.tex:1095-1098`: the unnormalized character
sum vanishes away from frequency zero. -/
theorem sum_booleanCharacter {t : ℕ} (u : Fin t → ZMod 2) :
    ∑ a : Fin t → ZMod 2, booleanCharacter u a =
      if u = 0 then (Fintype.card (Fin t → ZMod 2) : ℂ) else 0 := by
  rw [show (∑ a : Fin t → ZMod 2, booleanCharacter u a) =
      (Fintype.card (Fin t → ZMod 2) : ℂ) *
        𝔼 a : Fin t → ZMod 2, booleanCharacter u a by
    rw [Fintype.expect_eq_sum_div_card]
    field_simp]
  rw [show (𝔼 a : Fin t → ZMod 2, booleanCharacter u a) =
      if u = 0 then (1 : ℂ) else 0 by
    simpa [booleanCharacter] using
      (MIPStarRE.LDT.Preliminaries.fourier_fact_vector
        (p := 2) (F := ZMod 2) u)]
  split_ifs <;> simp

/-- Formalization-only auxiliary lemma for the Fourier transform at
`references/nv-paper/fullpaper.tex:1095-1098`: summing a character over
frequencies gives the delta function at zero. -/
theorem sum_booleanCharacter_swap {t : ℕ} (a : Fin t → ZMod 2) :
    ∑ u : Fin t → ZMod 2, booleanCharacter u a =
      if a = 0 then (Fintype.card (Fin t → ZMod 2) : ℂ) else 0 := by
  simpa only [booleanCharacter_comm] using sum_booleanCharacter a

/-- Formalization-only auxiliary lemma for the Fourier transform at
`references/nv-paper/fullpaper.tex:1095-1098`: orthogonality of two Boolean
characters, in the form used by Fourier inversion and Parseval. -/
theorem sum_booleanCharacter_mul {t : ℕ} (a b : Fin t → ZMod 2) :
    ∑ u : Fin t → ZMod 2, booleanCharacter u a * booleanCharacter u b =
      if a = b then (Fintype.card (Fin t → ZMod 2) : ℂ) else 0 := by
  rw [← Finset.sum_congr rfl (fun u _ => booleanCharacter_add_right u a b)]
  rw [sum_booleanCharacter_swap]
  have hab : a + b = 0 ↔ a = b := by
    constructor
    · intro h
      have := congrFun h
      funext i
      have hi := this i
      exact (CharTwo.add_eq_zero.mp hi)
    · intro h
      subst b
      ext i
      exact CharTwo.add_self_eq_zero (a i)
  simp only [hab]

/-! ## Operator-valued Fourier analysis -/

/-- The normalized Fourier coefficient of an operator family on the Boolean
cube.  This is `hat A^u = E_a (-1)^(a dot u) A(a)` from
`references/nv-paper/fullpaper.tex:1095-1098`. -/
noncomputable def operatorFourier {t : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (O : (Fin t → ZMod 2) → Op ι) (u : Fin t → ZMod 2) : Op ι :=
  ((Fintype.card (Fin t → ZMod 2) : ℂ)⁻¹) •
    ∑ a : Fin t → ZMod 2, booleanCharacter u a • O a

/-- Formalization-only auxiliary lemma for the Fourier argument at
`references/nv-paper/fullpaper.tex:1095-1100`: Fourier coefficients of a
Hermitian operator family are Hermitian. -/
theorem operatorFourier_isHermitian {t : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (O : (Fin t → ZMod 2) → Op ι) (hO : ∀ a, (O a).IsHermitian)
    (u : Fin t → ZMod 2) :
    (operatorFourier O u).IsHermitian := by
  rw [Matrix.IsHermitian]
  simp only [operatorFourier, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_sum, star_inv₀, star_natCast]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [star_booleanCharacter, (hO a).eq]

/-- Formalization-only auxiliary lemma for the Fourier argument at
`references/nv-paper/fullpaper.tex:1095-1100`: Fourier inversion for
operator-valued functions on the Boolean cube. -/
theorem operatorFourier_inversion {t : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (O : (Fin t → ZMod 2) → Op ι) (a : Fin t → ZMod 2) :
    ∑ u : Fin t → ZMod 2, booleanCharacter u a • operatorFourier O u = O a := by
  classical
  let N : ℂ := Fintype.card (Fin t → ZMod 2)
  have hN : N ≠ 0 := by
    simp [N]
  calc
    ∑ u : Fin t → ZMod 2, booleanCharacter u a • operatorFourier O u =
        ∑ u : Fin t → ZMod 2, ∑ b : Fin t → ZMod 2,
          (booleanCharacter u a * N⁻¹ * booleanCharacter u b) • O b := by
      apply Finset.sum_congr rfl
      intro u _
      simp only [operatorFourier, N, smul_smul, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [mul_assoc]
    _ = ∑ b : Fin t → ZMod 2, ∑ u : Fin t → ZMod 2,
          (booleanCharacter u a * N⁻¹ * booleanCharacter u b) • O b := by
      rw [Finset.sum_comm]
    _ = N⁻¹ • ∑ b : Fin t → ZMod 2,
          (∑ u : Fin t → ZMod 2,
            booleanCharacter u a * booleanCharacter u b) • O b := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [smul_smul, ← Finset.sum_smul, Finset.mul_sum]
      apply congrArg (fun c : ℂ => c • O b)
      apply Finset.sum_congr rfl
      intro u _
      ring
    _ = N⁻¹ • ∑ b : Fin t → ZMod 2,
          (if a = b then N else 0) • O b := by
      congr 1
      apply Finset.sum_congr rfl
      intro b _
      rw [sum_booleanCharacter_mul]
    _ = O a := by
      simp [hN]

/-- Formalization-only auxiliary lemma for the Fourier argument at
`references/nv-paper/fullpaper.tex:1095-1100`: the matrix-valued Parseval
identity for the Boolean Fourier transform.  The order of the two operator
families is preserved. -/
theorem sum_operatorFourier_mul_operatorFourier {t : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (A B : (Fin t → ZMod 2) → Op ι) :
    ∑ u : Fin t → ZMod 2, operatorFourier A u * operatorFourier B u =
      ((Fintype.card (Fin t → ZMod 2) : ℂ)⁻¹) •
        ∑ a : Fin t → ZMod 2, A a * B a := by
  classical
  let N : ℂ := Fintype.card (Fin t → ZMod 2)
  calc
    ∑ u : Fin t → ZMod 2, operatorFourier A u * operatorFourier B u =
        ∑ u : Fin t → ZMod 2, N⁻¹ •
          ∑ a : Fin t → ZMod 2,
            (booleanCharacter u a • A a) * operatorFourier B u := by
      apply Finset.sum_congr rfl
      intro u _
      change (N⁻¹ • ∑ a : Fin t → ZMod 2, booleanCharacter u a • A a) *
          operatorFourier B u = _
      rw [smul_mul_assoc, Finset.sum_mul]
    _ = N⁻¹ • ∑ u : Fin t → ZMod 2, ∑ a : Fin t → ZMod 2,
          (booleanCharacter u a • A a) * operatorFourier B u := by
      rw [Finset.smul_sum]
    _ = N⁻¹ • ∑ a : Fin t → ZMod 2, ∑ u : Fin t → ZMod 2,
          (booleanCharacter u a • A a) * operatorFourier B u := by
      congr 1
      rw [Finset.sum_comm]
    _ = N⁻¹ • ∑ a : Fin t → ZMod 2,
          A a * (∑ u : Fin t → ZMod 2,
            booleanCharacter u a • operatorFourier B u) := by
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      rw [smul_mul_assoc, mul_smul_comm]
    _ = N⁻¹ • ∑ a : Fin t → ZMod 2, A a * B a := by
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      rw [operatorFourier_inversion]
    _ = ((Fintype.card (Fin t → ZMod 2) : ℂ)⁻¹) •
          ∑ a : Fin t → ZMod 2, A a * B a := by
      rfl

/-- Formalization-only auxiliary lemma for the Fourier argument at
`references/nv-paper/fullpaper.tex:1095-1100`: Parseval specialized to the
square of a single operator family. -/
theorem sum_operatorFourier_sq {t : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (O : (Fin t → ZMod 2) → Op ι) :
    ∑ u : Fin t → ZMod 2, operatorFourier O u * operatorFourier O u =
      ((Fintype.card (Fin t → ZMod 2) : ℂ)⁻¹) •
        ∑ a : Fin t → ZMod 2, O a * O a :=
  sum_operatorFourier_mul_operatorFourier O O

/-- For a family of binary observables, the squares of the Fourier
coefficients sum to the identity.  This is the Parseval step asserting that
`B^u = (hat A^u)^2` is a POVM in
`references/nv-paper/fullpaper.tex:1096-1100`. -/
theorem sum_operatorFourier_sq_eq_one {t : ℕ} {ι : Type}
    [Fintype ι] [DecidableEq ι]
    (O : (Fin t → ZMod 2) → Op ι)
    (hO : ∀ a, IsBinaryObservable (O a)) :
    ∑ u : Fin t → ZMod 2, operatorFourier O u * operatorFourier O u = 1 := by
  rw [sum_operatorFourier_sq]
  simp_rw [(hO _).2]
  rw [Finset.sum_const]
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  rw [smul_smul]
  simp

/-! ## Observable-distance normalization -/

/-- The affine operator `(1 ± S)/2`, which is the effect of a binary projective
measurement when `S` is a binary observable.
The two effects are `(1 + O) / 2` and `(1 - O) / 2`. -/
noncomputable def binaryObservableEffect {ι : Type} [Fintype ι]
    [DecidableEq ι] (outcome : Bool) (O : Op ι) : Op ι :=
  if outcome then ((2 : ℂ)⁻¹) • (1 - O) else ((2 : ℂ)⁻¹) • (1 + O)

/-- The squared binary-measurement distance of two operators, summed over the two
effects `(1 ± O)/2`; when both operators are binary observables this is the
squared distance between the associated binary projective measurements.  This is the measurement
distance calculated in `references/nv-paper/fullpaper.tex:900-912`; its relation
to `stateDepDistSq` is recorded in
`docs/paper-gaps/qpbt_linearity-distance-normalization.tex`. -/
noncomputable def binaryObservableDistSq {ι : Type} [Fintype ι]
    [DecidableEq ι] (S T ρ : Op ι) : ℝ :=
  ∑ outcome : Bool,
    stateDepDistSq (binaryObservableEffect outcome S)
      (binaryObservableEffect outcome T) ρ

/-- The squared binary-measurement distance is half the squared
state-dependent operator distance.

**Local fix:** Source equation (3) at
`references/nv-paper/fullpaper.tex:903-911` ends by identifying the squared
binary-measurement distance with the squared state-dependent operator distance
of the two observables; the correct relation carries the factor `1 / 2` proved
here.
Documented in
`docs/paper-gaps/qpbt_linearity-distance-normalization.tex`. -/
theorem binaryObservableDistSq_eq_stateDepDistSq_div_two
    {ι : Type} [Fintype ι] [DecidableEq ι] (S T ρ : Op ι) :
    binaryObservableDistSq S T ρ = stateDepDistSq S T ρ / 2 := by
  simp only [binaryObservableDistSq, Fintype.univ_bool, stateDepDistSq,
    binaryObservableEffect, smul_add, Matrix.conjTranspose_sub,
    Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
    Finset.sum_insert, reduceIte, Matrix.conjTranspose_smul, star_inv₀,
    star_ofNat, Matrix.conjTranspose_one, Finset.sum_singleton,
    Bool.false_eq_true, Matrix.conjTranspose_add, add_sub_add_left_eq_sub]
  have hminusStar :
      (2 : ℂ)⁻¹ • (1 - Sᴴ) - (2 : ℂ)⁻¹ • (1 - Tᴴ) =
        -((2 : ℂ)⁻¹ • (Sᴴ - Tᴴ)) := by
    module
  have hminus :
      (2 : ℂ)⁻¹ • (1 - S) - (2 : ℂ)⁻¹ • (1 - T) =
        -((2 : ℂ)⁻¹ • (S - T)) := by
    module
  have hplusStar :
      (2 : ℂ)⁻¹ • Sᴴ - (2 : ℂ)⁻¹ • Tᴴ =
        (2 : ℂ)⁻¹ • (Sᴴ - Tᴴ) := by
    module
  have hplus :
      (2 : ℂ)⁻¹ • S - (2 : ℂ)⁻¹ • T =
        (2 : ℂ)⁻¹ • (S - T) := by
    module
  rw [hminusStar, hminus, hplusStar, hplus]
  simp only [neg_mul, mul_neg, neg_neg, smul_mul_assoc, Matrix.trace_smul]
  norm_num [Complex.mul_re]
  ring

/-- The state-dependent squared distance between binary observables in terms
of their correlation. -/
theorem stateDepDistSq_eq_two_sub_two_mul_correlation
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S T ρ : Op ι) (hS : IsBinaryObservable S)
    (hT : IsBinaryObservable T) (hρ : ρ.PosSemidef)
    (htrace : Matrix.trace ρ = 1) :
    stateDepDistSq S T ρ =
      2 - 2 * (Matrix.trace (S * T * ρ)).re := by
  have hstar :
      star (Matrix.trace (S * T * ρ)) = Matrix.trace (T * S * ρ) := by
    calc
      star (Matrix.trace (S * T * ρ)) = Matrix.trace ((S * T * ρ)ᴴ) := by
        rw [Matrix.trace_conjTranspose]
      _ = Matrix.trace (ρ * T * S) := by
        simp [Matrix.conjTranspose_mul, hS.1.eq, hT.1.eq, hρ.isHermitian.eq,
          Matrix.mul_assoc]
      _ = Matrix.trace (T * S * ρ) := by
        exact (Matrix.trace_mul_cycle T S ρ).symm
  have hcross :
      (Matrix.trace (S * T * ρ)).re = (Matrix.trace (T * S * ρ)).re := by
    have := congrArg Complex.re hstar
    simpa [Complex.star_def, Complex.conj_re] using this
  have hdiff :
      (S - T)ᴴ * (S - T) =
        (2 : ℂ) • (1 : Op ι) - S * T - T * S := by
    rw [Matrix.conjTranspose_sub, hS.1.eq, hT.1.eq]
    calc
      (S - T) * (S - T) = S * S - S * T - T * S + T * T := by
        noncomm_ring
      _ = (2 : ℂ) • (1 : Op ι) - S * T - T * S := by
        rw [hS.2, hT.2]
        module
  unfold stateDepDistSq
  rw [hdiff]
  simp only [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]
  rw [smul_mul_assoc, one_mul, Matrix.trace_smul, htrace]
  norm_num [Complex.mul_re]
  rw [hcross]
  ring

/-- The squared binary-measurement distance is one minus the real
state-dependent correlation. -/
theorem binaryObservableDistSq_eq_one_sub_correlation
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S T ρ : Op ι) (hS : IsBinaryObservable S)
    (hT : IsBinaryObservable T) (hρ : ρ.PosSemidef)
    (htrace : Matrix.trace ρ = 1) :
    binaryObservableDistSq S T ρ =
      1 - (Matrix.trace (S * T * ρ)).re := by
  rw [binaryObservableDistSq_eq_stateDepDistSq_div_two,
    stateDepDistSq_eq_two_sub_two_mul_correlation S T ρ hS hT hρ htrace]
  ring

end

end MIPStarRE.QPBT
