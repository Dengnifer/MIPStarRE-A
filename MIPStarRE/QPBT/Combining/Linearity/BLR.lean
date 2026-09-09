import MIPStarRE.LDT.Basic.DistributionAvg
import MIPStarRE.QPBT.Combining.Linearity.BooleanFourier

/-!
# The operator-valued BLR bound

This file carries out the Fourier-analytic part of the proof of the quantum
linearity theorem of Natarajan and Vidick.  Given binary observables `O^u`
indexed by the Boolean cube `𝔽_2^t` and a positive semidefinite trace-one
operator `ρ`, it expresses the state-dependent multiplicative defect of the
family through the two-query correlation of the linearity test, identifies the
sum of the cubic Fourier coefficients with that correlation, and records the
overlap certificate for the Fourier-square POVM `B^u = (hat O^u)^2` used in the
Naimark-dilation argument.  Pairwise commutation of the observables is never
assumed, and every complex trace is handled through its real part.

## Main results

* `multiplicativeDefect`: the state-dependent squared defect of `O^u O^v`
  from `O^{u+v}`.
* `avg_multiplicativeDefect_eq_two_sub_two_mul_correlation` and
  `avg_multiplicativeDefect_le_two_mul_error`: the average defect equals
  `2 - 2 * (correlation)`, hence is at most `2 * δ` under the correlation
  hypothesis of `exists_exactly_linear_observables`.
* `operatorFourier_cube_trace_eq_correlation`: the identity
  `∑_u Tr_ρ((hat O^u)^3) = E_{a,b} Tr_ρ(O^a O^b O^{a+b})`.
* `fourierSquareMeasurement` and `one_sub_error_le_avg_overlap_fourierSquare`:
  the Fourier-square POVM together with its overlap certificate.

## References

Natarajan--Vidick, arXiv:1610.03574, Theorem 10 with displays (7)--(8) and
its proof, `references/nv-paper/fullpaper.tex:1074-1113`; the state-dependent
distance is defined at lines 866--900 of the same file.  The QPBT paper quotes
the theorem at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:711-725` and
invokes it at lines 787--832.  The blueprint statement is blueprint
`thm:linearity`.  The normalization of
the error constant is analyzed in
`docs/paper-gaps/qpbt_linearity-distance-normalization.tex`: the exact defect
bound is `2 * δ` for the squared state-dependent operator distance
`stateDepDistSq`, equivalently `δ` for the squared binary-observable distance.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.Quantum

noncomputable section

/-! ## The two-query correlation and the multiplicative defect -/

/-- The two-query correlation of the linearity test: the average, over a
uniformly random pair `(u, u')` in `𝔽_2^t`, of the real part of
`Tr(O^u O^{u'} O^{u+u'} ρ)`.  This is the left-hand side of display (7) in
Natarajan--Vidick, `references/nv-paper/fullpaper.tex:1078-1080`, and the
quantity bounded below in the hypothesis of
`exists_exactly_linear_observables`; the order of the two uniform variables is
the one used there. -/
def blrCorrelation {t : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (O : (Fin t → ZMod 2) → Op ι) (ρ : Op ι) : ℝ :=
  avgOver (uniformDistribution ((Fin t → ZMod 2) × (Fin t → ZMod 2)))
    (fun pair =>
      (Matrix.trace (O pair.1 * O pair.2 * O (pair.1 + pair.2) * ρ)).re)

/-- The state-dependent squared defect of the product `O^u O^v` from `O^{u+v}`,
namely `d_ρ(O^u O^v, O^{u+v})^2` for the state-dependent distance of
`references/nv-paper/fullpaper.tex:873-875`.  Its average over uniformly random
`u, v` is the approximate-linearity error of the family in the sense of the QPBT
quotation `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:713-718`,
measured with the squared state-dependent operator distance
`stateDepDistSq`. -/
def multiplicativeDefect {t : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (O : (Fin t → ZMod 2) → Op ι) (ρ : Op ι) (u v : Fin t → ZMod 2) : ℝ :=
  stateDepDistSq (O u * O v) (O (u + v)) ρ

/-- Pointwise form of the defect identity: for binary observables the squared
defect of `O^u O^v` from `O^{u+v}` is `2 - 2 Re Tr(O^v O^u O^{v+u} ρ)`.  The
expansion of `(O^u O^v - O^{u+v})^† (O^u O^v - O^{u+v})` produces the two
triple products `O^v O^u O^{u+v}` and `O^{u+v} O^u O^v`; the second is the
adjoint of the first, so their traces against `ρ` are complex conjugates with
equal real parts.  This is the calculation behind display (3) of
`references/nv-paper/fullpaper.tex:900-912`, applied to the products of the
family. -/
theorem multiplicativeDefect_eq_two_sub_two_mul_correlation {t : ℕ}
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (O : (Fin t → ZMod 2) → Op ι) (hO : ∀ a, IsBinaryObservable (O a))
    (ρ : Op ι) (hρ : ρ.PosSemidef) (htrace : ρ.trace = 1)
    (u v : Fin t → ZMod 2) :
    multiplicativeDefect O ρ u v =
      2 - 2 * (Matrix.trace (O v * O u * O (v + u) * ρ)).re := by
  have hu := hO u
  have hv := hO v
  have huv := hO (u + v)
  have hdiff :
      (O u * O v - O (u + v))ᴴ * (O u * O v - O (u + v)) =
        (2 : ℂ) • (1 : Op ι) - O v * O u * O (u + v) - O (u + v) * O u * O v := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hu.1.eq, hv.1.eq,
      huv.1.eq]
    calc
      (O v * O u - O (u + v)) * (O u * O v - O (u + v)) =
          O v * (O u * O u) * O v - O v * O u * O (u + v) -
            O (u + v) * O u * O v + O (u + v) * O (u + v) := by
        noncomm_ring
      _ = (2 : ℂ) • (1 : Op ι) - O v * O u * O (u + v) -
            O (u + v) * O u * O v := by
        rw [hu.2, Matrix.mul_one, hv.2, huv.2]
        module
  have hstar :
      star (Matrix.trace (O (u + v) * O u * O v * ρ)) =
        Matrix.trace (O v * O u * O (u + v) * ρ) := by
    calc
      star (Matrix.trace (O (u + v) * O u * O v * ρ)) =
          Matrix.trace ((O (u + v) * O u * O v * ρ)ᴴ) := by
        rw [Matrix.trace_conjTranspose]
      _ = Matrix.trace (ρ * (O v * O u * O (u + v))) := by
        simp [Matrix.conjTranspose_mul, hu.1.eq, hv.1.eq, huv.1.eq,
          hρ.isHermitian.eq, Matrix.mul_assoc]
      _ = Matrix.trace (O v * O u * O (u + v) * ρ) := by
        exact Matrix.trace_mul_comm _ _
  have hcross :
      (Matrix.trace (O (u + v) * O u * O v * ρ)).re =
        (Matrix.trace (O v * O u * O (u + v) * ρ)).re := by
    have := congrArg Complex.re hstar
    simpa [Complex.star_def, Complex.conj_re] using this
  unfold multiplicativeDefect stateDepDistSq
  rw [hdiff]
  simp only [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]
  rw [smul_mul_assoc, one_mul, Matrix.trace_smul, htrace]
  norm_num [Complex.mul_re]
  rw [hcross, add_comm v u]
  ring

/-- The average multiplicative defect over a uniformly random pair equals
`2 - 2 * (two-query correlation)`.  The pointwise identity
`multiplicativeDefect_eq_two_sub_two_mul_correlation` produces the correlation
summand with the two variables in reversed order; since the pair is uniform,
exchanging the two coordinates leaves the average unchanged.  This is the
relation between the approximate-linearity hypothesis of the QPBT quotation
(`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:713-718`) and
display (7) of Natarajan--Vidick (`references/nv-paper/fullpaper.tex:1078-1080`),
in the operator-distance normalization of
`docs/paper-gaps/qpbt_linearity-distance-normalization.tex`. -/
theorem avg_multiplicativeDefect_eq_two_sub_two_mul_correlation {t : ℕ}
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (O : (Fin t → ZMod 2) → Op ι) (hO : ∀ a, IsBinaryObservable (O a))
    (ρ : Op ι) (hρ : ρ.PosSemidef) (htrace : ρ.trace = 1) :
    avgOver (uniformDistribution ((Fin t → ZMod 2) × (Fin t → ZMod 2)))
        (fun pair => multiplicativeDefect O ρ pair.1 pair.2) =
      2 - 2 * blrCorrelation O ρ := by
  have hswap :
      avgOver (uniformDistribution ((Fin t → ZMod 2) × (Fin t → ZMod 2)))
        (fun pair =>
          (Matrix.trace (O pair.2 * O pair.1 * O (pair.2 + pair.1) * ρ)).re) =
        blrCorrelation O ρ := by
    unfold blrCorrelation
    refine (avgOver_uniform_equiv (Equiv.prodComm _ _) _).trans ?_
    exact avgOver_congr _ _ _ (fun pair => rfl)
  calc
    avgOver (uniformDistribution ((Fin t → ZMod 2) × (Fin t → ZMod 2)))
        (fun pair => multiplicativeDefect O ρ pair.1 pair.2) =
        avgOver (uniformDistribution ((Fin t → ZMod 2) × (Fin t → ZMod 2)))
          (fun pair => 2 - 2 *
            (Matrix.trace (O pair.2 * O pair.1 * O (pair.2 + pair.1) * ρ)).re) :=
      avgOver_congr _ _ _ (fun pair =>
        multiplicativeDefect_eq_two_sub_two_mul_correlation O hO ρ hρ htrace
          pair.1 pair.2)
    _ = 2 - 2 * blrCorrelation O ρ := by
      rw [avgOver_sub, avgOver_const_mul, avgOver_uniform_const, hswap]

/-- The operator-valued BLR bound: under the correlation hypothesis of
`exists_exactly_linear_observables`, the average squared defect of `O^u O^v`
from `O^{u+v}` is at most `2 * δ`.  This is the passage from display (7) of
Natarajan--Vidick (`references/nv-paper/fullpaper.tex:1078-1080`) to the
approximate-linearity relation of the QPBT quotation
(`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:713-718`); the
constant `2` is the operator-distance normalization recorded in
`docs/paper-gaps/qpbt_linearity-distance-normalization.tex`. -/
theorem avg_multiplicativeDefect_le_two_mul_error {t : ℕ}
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (O : (Fin t → ZMod 2) → Op ι) (hO : ∀ a, IsBinaryObservable (O a))
    (ρ : Op ι) (hρ : ρ.PosSemidef) (htrace : ρ.trace = 1)
    (δ : ℝ) (hcorrelation : 1 - δ ≤ blrCorrelation O ρ) :
    avgOver (uniformDistribution ((Fin t → ZMod 2) × (Fin t → ZMod 2)))
        (fun pair => multiplicativeDefect O ρ pair.1 pair.2) ≤ 2 * δ := by
  rw [avg_multiplicativeDefect_eq_two_sub_two_mul_correlation O hO ρ hρ htrace]
  linarith

/-! ## The cubic Fourier identity -/

/-- Formalization-only auxiliary lemma for the Fourier computations in the
proof of Theorem 10 of Natarajan--Vidick
(`references/nv-paper/fullpaper.tex:1096-1112`): a twisted form of the
matrix-valued Parseval identity in which only the first factor is expanded
through its Fourier coefficients.  Taking `a = 0` recovers Parseval. -/
private theorem sum_booleanCharacter_smul_operatorFourier_mul {t : ℕ}
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (A X : (Fin t → ZMod 2) → Op ι) (a : Fin t → ZMod 2) :
    ∑ u : Fin t → ZMod 2,
        booleanCharacter u a • (operatorFourier A u * X u) =
      ((Fintype.card (Fin t → ZMod 2) : ℂ)⁻¹) •
        ∑ b : Fin t → ZMod 2,
          A b * ∑ u : Fin t → ZMod 2, booleanCharacter u (a + b) • X u := by
  classical
  let N : ℂ := Fintype.card (Fin t → ZMod 2)
  calc
    ∑ u : Fin t → ZMod 2,
        booleanCharacter u a • (operatorFourier A u * X u) =
        ∑ u : Fin t → ZMod 2, N⁻¹ • ∑ b : Fin t → ZMod 2,
          booleanCharacter u (a + b) • (A b * X u) := by
      apply Finset.sum_congr rfl
      intro u _
      simp only [operatorFourier, N, smul_mul_assoc, Finset.sum_mul,
        Finset.smul_sum, smul_smul, booleanCharacter_add_right]
      apply Finset.sum_congr rfl
      intro b _
      congr 1
      ring
    _ = N⁻¹ • ∑ b : Fin t → ZMod 2, ∑ u : Fin t → ZMod 2,
          booleanCharacter u (a + b) • (A b * X u) := by
      rw [← Finset.smul_sum]
      congr 1
      exact Finset.sum_comm
    _ = N⁻¹ • ∑ b : Fin t → ZMod 2,
          A b * ∑ u : Fin t → ZMod 2, booleanCharacter u (a + b) • X u := by
      congr 1
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      rw [mul_smul_comm]

/-- The sum of the cubes of the Fourier coefficients of an operator family is
the average of `O^a O^b O^{a+b}` over a uniformly random pair `(a, b)`.  This
is the operator form of the identity
`∑_u (hat A^u)^3 = E_{a,b} A(a) A(b) A(a+b)` invoked at
`references/nv-paper/fullpaper.tex:1111-1112`; the order of the three factors
is preserved throughout. -/
theorem sum_operatorFourier_cube {t : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (O : (Fin t → ZMod 2) → Op ι) :
    ∑ u : Fin t → ZMod 2,
        operatorFourier O u * operatorFourier O u * operatorFourier O u =
      ((Fintype.card ((Fin t → ZMod 2) × (Fin t → ZMod 2)) : ℂ)⁻¹) •
        ∑ p : (Fin t → ZMod 2) × (Fin t → ZMod 2),
          O p.1 * O p.2 * O (p.1 + p.2) := by
  classical
  let N : ℂ := Fintype.card (Fin t → ZMod 2)
  have hinner : ∀ b : Fin t → ZMod 2,
      ∑ u : Fin t → ZMod 2,
          booleanCharacter u b • (operatorFourier O u * operatorFourier O u) =
        N⁻¹ • ∑ c : Fin t → ZMod 2, O c * O (b + c) := by
    intro b
    rw [sum_booleanCharacter_smul_operatorFourier_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro c _
    rw [operatorFourier_inversion]
  calc
    ∑ u : Fin t → ZMod 2,
        operatorFourier O u * operatorFourier O u * operatorFourier O u =
        ∑ u : Fin t → ZMod 2, booleanCharacter u 0 •
          (operatorFourier O u * (operatorFourier O u * operatorFourier O u)) := by
      apply Finset.sum_congr rfl
      intro u _
      rw [booleanCharacter_zero_right, one_smul, Matrix.mul_assoc]
    _ = N⁻¹ • ∑ b : Fin t → ZMod 2, O b * ∑ u : Fin t → ZMod 2,
          booleanCharacter u (0 + b) •
            (operatorFourier O u * operatorFourier O u) := by
      rw [sum_booleanCharacter_smul_operatorFourier_mul]
    _ = N⁻¹ • ∑ b : Fin t → ZMod 2,
          O b * (N⁻¹ • ∑ c : Fin t → ZMod 2, O c * O (b + c)) := by
      simp only [zero_add, hinner]
    _ = (N⁻¹ * N⁻¹) • ∑ b : Fin t → ZMod 2, ∑ c : Fin t → ZMod 2,
          O b * O c * O (b + c) := by
      simp only [mul_smul_comm, Finset.mul_sum, ← Finset.smul_sum, smul_smul,
        Matrix.mul_assoc]
    _ = ((Fintype.card ((Fin t → ZMod 2) × (Fin t → ZMod 2)) : ℂ)⁻¹) •
          ∑ p : (Fin t → ZMod 2) × (Fin t → ZMod 2),
            O p.1 * O p.2 * O (p.1 + p.2) := by
      rw [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul, mul_inv]

/-- Formalization-only auxiliary lemma for the averages in this file: a uniform
average over a nonempty finite type is the sum divided by the cardinality. -/
private theorem avgOver_uniform_eq_inv_card_mul_sum {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α] (f : α → ℝ) :
    avgOver (uniformDistribution α) f = (Fintype.card α : ℝ)⁻¹ * ∑ a, f a := by
  simp [avgOver, uniformDistribution, Distribution.uniformOnFinset_weight,
    Finset.mul_sum]

/-- The sum of the cubic Fourier coefficients evaluated in `ρ` equals the
two-query correlation:
`∑_u Re Tr((hat O^u)^3 ρ) = E_{a,b} Re Tr(O^a O^b O^{a+b} ρ)`.  This is the
identity stated at `references/nv-paper/fullpaper.tex:1111-1112`, with the
complex traces compared through their real parts. -/
theorem operatorFourier_cube_trace_eq_correlation {t : ℕ}
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (O : (Fin t → ZMod 2) → Op ι) (ρ : Op ι) :
    ∑ u : Fin t → ZMod 2,
        (Matrix.trace (operatorFourier O u * operatorFourier O u *
          operatorFourier O u * ρ)).re =
      blrCorrelation O ρ := by
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul,
    sum_operatorFourier_cube, smul_mul_assoc, Matrix.trace_smul, Finset.sum_mul,
    Matrix.trace_sum]
  unfold blrCorrelation
  rw [avgOver_uniform_eq_inv_card_mul_sum, smul_eq_mul, ← Complex.ofReal_natCast,
    ← Complex.ofReal_inv, Complex.re_ofReal_mul, Complex.re_sum]

/-! ## The Fourier-square POVM and its overlap certificate -/

/-- Each Fourier square `B^u = (hat O^u)^2` of a Hermitian operator family is
positive semidefinite, being the product of a Hermitian matrix with its
adjoint.  This is the positivity half of the assertion that the `B^u` form a
POVM at `references/nv-paper/fullpaper.tex:1098-1099`. -/
theorem operatorFourier_mul_self_posSemidef {t : ℕ}
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (O : (Fin t → ZMod 2) → Op ι) (hO : ∀ a, (O a).IsHermitian)
    (u : Fin t → ZMod 2) :
    (operatorFourier O u * operatorFourier O u).PosSemidef := by
  have h := operatorFourier_isHermitian O hO u
  simpa [h.eq] using
    Matrix.posSemidef_conjTranspose_mul_self (operatorFourier O u)

/-- The Fourier-square POVM `{B^u = (hat O^u)^2}` of a family of binary
observables, with outcomes in `𝔽_2^t`.  Positivity is
`operatorFourier_mul_self_posSemidef` and completeness is the Parseval
identity `sum_operatorFourier_sq_eq_one`.  This is the POVM to which Naimark's
theorem is applied at `references/nv-paper/fullpaper.tex:1097-1100`. -/
def fourierSquareMeasurement {t : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (O : (Fin t → ZMod 2) → Op ι) (hO : ∀ a, IsBinaryObservable (O a)) :
    Measurement (Fin t → ZMod 2) ι :=
  Measurement.ofSumEqOne
    (fun u => operatorFourier O u * operatorFourier O u)
    (fun u => (operatorFourier_mul_self_posSemidef O (fun a => (hO a).1) u).nonneg)
    (sum_operatorFourier_sq_eq_one O hO)

/-- The effects of the Fourier-square POVM are the squares of the Fourier
coefficients. -/
@[simp]
theorem fourierSquareMeasurement_effect {t : ℕ}
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (O : (Fin t → ZMod 2) → Op ι) (hO : ∀ a, IsBinaryObservable (O a))
    (u : Fin t → ZMod 2) :
    (fourierSquareMeasurement O hO).effect u =
      operatorFourier O u * operatorFourier O u :=
  rfl

/-- The average state-dependent overlap between `O^a` and the character sum
`∑_u (-1)^{u·a} B^u` of the Fourier-square operators `B^u = (hat O^u)^2` equals
the sum of the cubic Fourier coefficients evaluated in `ρ`.  The family `O` is
arbitrary here, so the `B^u` need not be positive or sum to the identity; they
are the effects of a POVM only under the binary-observable hypothesis of
`fourierSquareMeasurement`.  This is the computation of
`E_a Re Tr_{ρ'}(A(a) 𝒜(a))` at `references/nv-paper/fullpaper.tex:1104-1110`,
carried out before the Naimark dilation: the character sum is the compression
of the exactly linear observable `𝒜(a) = ∑_u (-1)^{u·a} C^u` to the original
space. -/
theorem avg_overlap_fourierSquare_eq_sum_cube {t : ℕ}
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (O : (Fin t → ZMod 2) → Op ι) (ρ : Op ι) :
    avgOver (uniformDistribution (Fin t → ZMod 2))
        (fun a => (Matrix.trace (O a *
          (∑ u : Fin t → ZMod 2, booleanCharacter u a •
            (operatorFourier O u * operatorFourier O u)) * ρ)).re) =
      ∑ u : Fin t → ZMod 2,
        (Matrix.trace (operatorFourier O u * operatorFourier O u *
          operatorFourier O u * ρ)).re := by
  classical
  have hop :
      ∑ u : Fin t → ZMod 2,
          operatorFourier O u * (operatorFourier O u * operatorFourier O u) =
        ((Fintype.card (Fin t → ZMod 2) : ℂ)⁻¹) •
          ∑ b : Fin t → ZMod 2, O b * ∑ u : Fin t → ZMod 2,
            booleanCharacter u b • (operatorFourier O u * operatorFourier O u) := by
    have := sum_booleanCharacter_smul_operatorFourier_mul O
      (fun u => operatorFourier O u * operatorFourier O u) 0
    simpa only [booleanCharacter_zero_right, one_smul, zero_add] using this
  symm
  calc
    ∑ u : Fin t → ZMod 2,
        (Matrix.trace (operatorFourier O u * operatorFourier O u *
          operatorFourier O u * ρ)).re =
        (Matrix.trace ((∑ u : Fin t → ZMod 2,
          operatorFourier O u * (operatorFourier O u * operatorFourier O u)) *
            ρ)).re := by
      rw [Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
      simp only [Matrix.mul_assoc]
    _ = (Matrix.trace ((((Fintype.card (Fin t → ZMod 2) : ℂ)⁻¹) •
          ∑ b : Fin t → ZMod 2, O b * ∑ u : Fin t → ZMod 2,
            booleanCharacter u b • (operatorFourier O u * operatorFourier O u)) *
              ρ)).re := by
      rw [hop]
    _ = (Fintype.card (Fin t → ZMod 2) : ℝ)⁻¹ *
          ∑ b : Fin t → ZMod 2, (Matrix.trace (O b *
            (∑ u : Fin t → ZMod 2, booleanCharacter u b •
              (operatorFourier O u * operatorFourier O u)) * ρ)).re := by
      rw [smul_mul_assoc, Matrix.trace_smul, Finset.sum_mul, Matrix.trace_sum,
        smul_eq_mul, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
        Complex.re_ofReal_mul, Complex.re_sum]
    _ = avgOver (uniformDistribution (Fin t → ZMod 2))
          (fun a => (Matrix.trace (O a *
            (∑ u : Fin t → ZMod 2, booleanCharacter u a •
              (operatorFourier O u * operatorFourier O u)) * ρ)).re) := by
      rw [avgOver_uniform_eq_inv_card_mul_sum]

/-- The overlap certificate for the Fourier-square operators `B^u = (hat O^u)^2`:
under the correlation hypothesis of `exists_exactly_linear_observables`, the
average state-dependent overlap between `O^a` and the character sum
`∑_u (-1)^{u·a} B^u` is at least `1 - δ`.  The family `O` is arbitrary here, so
the `B^u` are the effects of a POVM only under the binary-observable hypothesis
of `fourierSquareMeasurement`.  This is the conclusion of the computation at
`references/nv-paper/fullpaper.tex:1104-1112` in the form used after the
Naimark dilation: the same overlap, evaluated in `ρ ⊗ |anc⟩⟨anc|` against the
exactly linear observables, is what bounds the average distance in display (8).
No commutation among the observables is used. -/
theorem one_sub_error_le_avg_overlap_fourierSquare {t : ℕ}
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (O : (Fin t → ZMod 2) → Op ι) (ρ : Op ι)
    (δ : ℝ) (hcorrelation : 1 - δ ≤ blrCorrelation O ρ) :
    1 - δ ≤ avgOver (uniformDistribution (Fin t → ZMod 2))
        (fun a => (Matrix.trace (O a *
          (∑ u : Fin t → ZMod 2, booleanCharacter u a •
            (operatorFourier O u * operatorFourier O u)) * ρ)).re) := by
  rw [avg_overlap_fourierSquare_eq_sum_cube,
    operatorFourier_cube_trace_eq_correlation]
  exact hcorrelation

end

end MIPStarRE.QPBT
