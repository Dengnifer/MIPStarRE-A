import MIPStarRE.QPBT.Algebra.PauliTheorems
import MIPStarRE.QPBT.Games.DistanceTheorems.TensorSupport
import MIPStarRE.QPBT.Observables.LineMeasurement.Restriction
import MIPStarRE.QPBT.Test.MagicSquareTheorems
import MIPStarRE.QPBT.Test.PauliBasisTest

/-!
# The honest Pauli basis measurements of the completeness proof

This module builds the measurements used by the honest strategy of
`lem:pauli-completeness`: the generalized Pauli basis measurement in a fixed
basis `W`, and its coarse-graining by the binary trace
`h ↦ tr(g_h(u_W) r_W)` which the source calls `A` (for `W = X`) and `B`
(for `W = Z`).  The main results are the observable identity

  `A_0 - A_1 = τ^W(ind_m(u_W) r_W)`

of `eq:finally-got-an-observable`, and the resulting commutation law

  `𝒪_A 𝒪_B = (-1)^γ 𝒪_B 𝒪_A`

with `γ` the phase bit `eq:gamma-value`.  When `γ ≠ 0` the two observables
anticommute, so `thm:ms-from-ac` produces the Magic Square part of the honest
strategy.

## References

The construction is the strategy displayed in the proof of
`lem:pauli-completeness`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1290-1360`;
blueprint `blueprint/src/chapter/ch13_qpbt_test.tex:390-395`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

variable {K ι : Type*} [Field K] [Fintype K] [DecidableEq K] [Algebra (ZMod 2) K]
  [Fintype ι] [DecidableEq ι]

/-! ### The generalized Pauli basis measurement -/

/-- The generalized Pauli observable at the zero label is the identity.  This is
the normalization implicit in `def:generalized-pauli`, blueprint
`blueprint/src/chapter/ch11_qpbt_algebra.tex:529-571`, paper origin
`references/qpbt-paper/04_preliminaries.tex:1052-1096`. -/
theorem tauObservable_zero (W : PauliKind) :
    tauObservable W (0 : ι → K) = 1 := by
  have hmul := tauObservable_mul W (0 : ι → K) 0
  rw [add_zero, tauObservable_sq] at hmul
  exact hmul.symm

/-- Every generalized Pauli projector is positive semidefinite: it is the
rank-one projector onto the corresponding basis vector of
`def:generalized-pauli`, blueprint `ch11_qpbt_algebra.tex:529-571`, paper origin
`references/qpbt-paper/04_preliminaries.tex:1101-1122`. -/
theorem pauliProj_posSemidef (W : PauliKind) (e : ι → K) :
    (pauliProj W e).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star (pauliVec W e)

/-- Every generalized Pauli projector is a nonnegative operator. -/
theorem pauliProj_nonneg (W : PauliKind) (e : ι → K) : 0 ≤ pauliProj W e :=
  Matrix.nonneg_iff_posSemidef.mpr (pauliProj_posSemidef W e)

/-- Every generalized Pauli projector is Hermitian. -/
theorem pauliProj_conjTranspose (W : PauliKind) (e : ι → K) :
    (pauliProj W e)ᴴ = pauliProj W e :=
  (pauliProj_posSemidef W e).isHermitian.eq

/-- The generalized Pauli projectors in a fixed basis form a resolution of the
identity.  This is the completeness half of `def:generalized-pauli`, blueprint
`ch11_qpbt_algebra.tex:529-571`, paper origin
`references/qpbt-paper/04_preliminaries.tex:1101-1122`. -/
theorem sum_pauliProj (W : PauliKind) :
    ∑ e : ι → K, pauliProj W e = 1 := by
  have h := tauObservable_eq_sum_pauliProj (K := K) (ι := ι) W 0
  rw [tauObservable_zero] at h
  refine Eq.trans (Finset.sum_congr rfl fun e _ => ?_) h.symm
  have hzero : dotProduct (0 : ι → K) e = 0 := by simp
  simp [hzero, phaseSign]

/-- The generalized Pauli basis measurement in basis `W`: the projective
measurement whose outcomes are the labels of `def:generalized-pauli`, blueprint
`blueprint/src/chapter/ch11_qpbt_algebra.tex:529-571`, paper origin
`references/qpbt-paper/04_preliminaries.tex:1101-1122`. -/
noncomputable def pauliBasisMeasurement (W : PauliKind) :
    Measurement (ι → K) (ι → K) :=
  Measurement.ofSumEqOne (pauliProj W) (pauliProj_nonneg W) (sum_pauliProj W)

@[simp] theorem pauliBasisMeasurement_effect (W : PauliKind) (e : ι → K) :
    (pauliBasisMeasurement W).effect e = pauliProj W e := rfl

/-! ### Symmetry and Hermiticity of the generalized Pauli observables -/

/-- Formalization-only auxiliary: the binary sign character is real. -/
private theorem star_phaseSign' (t : ZMod 2) : star (phaseSign t) = phaseSign t := by
  by_cases ht : t = 0 <;> simp [phaseSign, ht]

omit [Fintype K] in
/-- Generalized Pauli observables are symmetric matrices in the computational
basis.  Symmetry is what makes the honest measurements consistent on the EPR
state used by `lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1290-1360`. -/
theorem tauObservable_transpose (W : PauliKind) (a : ι → K) :
    (tauObservable W a)ᵀ = tauObservable W a := by
  haveI : CharP K 2 := (Algebra.charP_iff (ZMod 2) K 2).mp (ZMod.charP 2)
  have hswap : ∀ x y c : K, (x = y + c) ↔ (y = x + c) := by
    intro x y c
    constructor
    · rintro rfl
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    · rintro rfl
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  ext x y
  rw [Matrix.transpose_apply]
  cases W with
  | X =>
      refine Finset.prod_congr rfl fun i _ => ?_
      change (if y i = x i + a i then (1 : ℂ) else 0) = if x i = y i + a i then 1 else 0
      by_cases h : x i = y i + a i
      · rw [if_pos h, if_pos ((hswap _ _ _).mp h)]
      · rw [if_neg h, if_neg (fun hc => h ((hswap _ _ _).mp hc))]
  | Z =>
      refine Finset.prod_congr rfl fun i _ => ?_
      change (if y i = x i then phaseSign (binTrace K (a i * x i)) else 0) =
        if x i = y i then phaseSign (binTrace K (a i * y i)) else 0
      by_cases h : x i = y i
      · rw [h]
      · rw [if_neg h, if_neg (fun hc => h hc.symm)]

/-- Generalized Pauli observables are Hermitian.  This is the self-adjointness
of the observables `𝒪_A` and `𝒪_B` used in the proof of
`lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1290-1360`. -/
theorem tauObservable_conjTranspose (W : PauliKind) (a : ι → K) :
    (tauObservable W a)ᴴ = tauObservable W a := by
  rw [tauObservable_eq_sum_pauliProj, Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Matrix.conjTranspose_smul, star_phaseSign', pauliProj_conjTranspose]

/-! ### Orthogonality of the generalized Pauli projectors

The generalized Pauli projectors in a fixed basis are pairwise orthogonal, so
every coarse-graining of a Pauli basis measurement is again projective.  This is
the projectivity used throughout the honest strategy of `lem:pauli-completeness`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1364-1370`.
-/


/-- Every generalized Pauli projector is a projector. -/
theorem pauliProj_isProj (W : PauliKind) (e : ι → K) : IsProj (pauliProj W e) := by
  refine isStarProjection_iff'.2 ⟨?_, ?_⟩
  · simpa using pauliProj_mul_pauliProj W e e
  · rw [Matrix.star_eq_conjTranspose, pauliProj_conjTranspose]

/-- Every coarse-graining of a generalized Pauli basis measurement is
projective.  This is the projectivity of the honest Point, Line and Pauli
measurements in the proof of `lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1364-1370`. -/
theorem pauliBasisMeasurement_postprocess_projective {β : Type*} [Fintype β]
    [DecidableEq β] (W : PauliKind) (g : (ι → K) → β) :
    MIPStarRE.QPBT.Measurement.IsProjective ((pauliBasisMeasurement W).postprocess g) := by
  classical
  intro b
  rw [Measurement.postprocess_effect]
  refine isStarProjection_iff'.2 ⟨?_, ?_⟩
  · rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    have hterm : ∀ f ∈ Finset.univ.filter (fun a : ι → K => g a = b),
        (pauliBasisMeasurement W).effect e * (pauliBasisMeasurement W).effect f =
          if e = f then pauliProj W e else 0 :=
      fun f _ => pauliProj_mul_pauliProj W e f
    rw [Finset.sum_congr rfl hterm,
      Finset.sum_ite_eq_of_mem _ e (fun _ => pauliProj W e) he]
    rfl
  · rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    exact pauliProj_conjTranspose W e

/-- Every coarse-graining of a generalized Pauli basis measurement has symmetric
effects, hence is consistent on the EPR state.  This is the consistency of the
honest Point, Line and Pauli measurements in the proof of
`lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1368-1372`. -/
theorem pauliBasisMeasurement_postprocess_isConsistentOn {β : Type*} [Fintype β]
    [DecidableEq β] [Nonempty ι] (W : PauliKind) (g : (ι → K) → β) :
    MIPStarRE.QPBT.Measurement.IsConsistentOn ((pauliBasisMeasurement W).postprocess g)
      (eprState (ι → K)) := by
  classical
  intro b
  refine epr_action_eq_of_transpose _ ?_
  rw [Measurement.postprocess_effect, Matrix.transpose_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  exact pauliProj_transpose W e

/-! ### The honest Pair/W measurements

For an ambient question `ω = (u_X, u_Z, r_X, r_Z)` the honest player measures
the Pauli register in basis `W` and reports the binary trace
`tr(g_h(u_W) r_W)` of the resulting label.  These are the measurements `A` and
`B` of the proof of `lem:pauli-completeness`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1290-1330`.
-/

/-- The binary trace bit `tr(g_h(u) r)` reported by the honest Pair/W
measurement on the Pauli label `h`.  Paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1290-1330`. -/
noncomputable def pauliTraceBit (P : AdmissibleParams)
    (u : Fin P.m → PauliScalar P) (r : PauliScalar P) (h : PauliRegister P) : ZMod 2 :=
  fixedBinTrace P.model (lowDegreeEnc h u * r)

/-- The honest Pair/W measurement `τ^W_{[tr(g_·(u) r) = β]}` of the proof of
`lem:pauli-completeness`: the generalized Pauli basis measurement coarse-grained
by the trace bit.  Paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1290-1330`,
blueprint `blueprint/src/chapter/ch13_qpbt_test.tex:390-395`. -/
noncomputable def pauliTraceMeasurement (P : AdmissibleParams) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) (r : PauliScalar P) :
    Measurement (ZMod 2) (PauliRegister P) :=
  (pauliBasisMeasurement W).postprocess (pauliTraceBit P u r)

theorem pauliTraceMeasurement_effect (P : AdmissibleParams) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) (r : PauliScalar P) (b : ZMod 2) :
    (pauliTraceMeasurement P W u r).effect b =
      ∑ h ∈ Finset.univ.filter (fun h : PauliRegister P => pauliTraceBit P u r h = b),
        pauliProj W h := rfl

/-- Equation `eq:finally-got-an-observable`: the observable of the honest
Pair/W measurement is the generalized Pauli observable at the label
`ind_m(u) r`.  Paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1300-1315`. -/
theorem obsOf_pauliTraceMeasurement (P : AdmissibleParams) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) (r : PauliScalar P) :
    obsOf (pauliTraceMeasurement P W u r) =
      tauObservable W (r • indicatorVec u) := by
  classical
  have hdot : ∀ e : PauliRegister P,
      dotProduct (r • indicatorVec u) e = lowDegreeEnc e u * r := by
    intro e
    rw [lowDegreeEnc_eq_dotProduct]
    simp only [dotProduct, Finset.sum_mul, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun y _ => by ring
  have hp : ∀ e : PauliRegister P,
      phaseSign (binTrace (PauliScalar P) (dotProduct (r • indicatorVec u) e)) =
        phaseSign (pauliTraceBit P u r e) := by
    intro e
    rw [hdot e]
    rfl
  rw [tauObservable_eq_sum_pauliProj,
    Finset.sum_congr rfl (fun e (_ : e ∈ Finset.univ) => by rw [hp e]),
    ← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (PauliRegister P))
      (fun e => pauliTraceBit P u r e = 0)]
  have hfilter :
      (Finset.univ.filter fun e : PauliRegister P => ¬ pauliTraceBit P u r e = 0) =
        Finset.univ.filter fun e : PauliRegister P => pauliTraceBit P u r e = 1 := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases zmod_two_eq_zero_or_one (pauliTraceBit P u r e) with h | h <;> simp [h]
  have h0 : ∑ e ∈ Finset.univ.filter (fun e : PauliRegister P => pauliTraceBit P u r e = 0),
      phaseSign (pauliTraceBit P u r e) • pauliProj W e =
      (pauliTraceMeasurement P W u r).effect 0 := by
    rw [pauliTraceMeasurement_effect]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [(Finset.mem_filter.mp he).2]
    simp [phaseSign]
  have h1 : ∑ e ∈ Finset.univ.filter (fun e : PauliRegister P => ¬ pauliTraceBit P u r e = 0),
      phaseSign (pauliTraceBit P u r e) • pauliProj W e =
      -(pauliTraceMeasurement P W u r).effect 1 := by
    rw [hfilter, pauliTraceMeasurement_effect]
    calc ∑ e ∈ Finset.univ.filter (fun e : PauliRegister P => pauliTraceBit P u r e = 1),
          phaseSign (pauliTraceBit P u r e) • pauliProj W e
        = ∑ e ∈ Finset.univ.filter (fun e : PauliRegister P => pauliTraceBit P u r e = 1),
            (-1 : ℂ) • pauliProj W e :=
          Finset.sum_congr rfl fun e he => by
            rw [(Finset.mem_filter.mp he).2]
            norm_num [phaseSign]
      _ = (-1 : ℂ) • ∑ e ∈ Finset.univ.filter
            (fun e : PauliRegister P => pauliTraceBit P u r e = 1), pauliProj W e :=
          Finset.smul_sum.symm
      _ = _ := neg_one_smul ℂ _
  rw [h0, h1, ← sub_eq_add_neg]
  rfl

/-- Each effect of the honest Pair/W measurement is the spectral projector of
its observable, so the measurement is projective; part of the projectivity
assertion of the honest strategy in the proof of `lem:pauli-completeness`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1364-1370`. -/
theorem pauliTraceMeasurement_effect_eq_reflectionEffect (P : AdmissibleParams)
    (W : PauliKind) (u : Fin P.m → PauliScalar P) (r : PauliScalar P) (b : ZMod 2) :
    (pauliTraceMeasurement P W u r).effect b =
      reflectionEffect (tauObservable W (r • indicatorVec u)) b := by
  rw [← obsOf_pauliTraceMeasurement, reflectionEffect_obsOf_measurement]

/-- The honest Pair/W measurement is projective, as asserted for the honest
strategy in the proof of `lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1364-1370`. -/
theorem pauliTraceMeasurement_projective (P : AdmissibleParams) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) (r : PauliScalar P) :
    MIPStarRE.QPBT.Measurement.IsProjective (pauliTraceMeasurement P W u r) := by
  intro b
  rw [pauliTraceMeasurement_effect_eq_reflectionEffect]
  exact reflectionMeasurement_projective (tauObservable W (r • indicatorVec u))
    (tauObservable_conjTranspose W _) (tauObservable_sq W _) b

/-- The effects of the honest Pair/W measurement are symmetric matrices. -/
theorem pauliTraceMeasurement_effect_transpose (P : AdmissibleParams) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) (r : PauliScalar P) (b : ZMod 2) :
    ((pauliTraceMeasurement P W u r).effect b)ᵀ =
      (pauliTraceMeasurement P W u r).effect b := by
  rw [pauliTraceMeasurement_effect_eq_reflectionEffect]
  rcases zmod_two_eq_zero_or_one b with rfl | rfl
  · simp only [reflectionEffect, if_pos]
    rw [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_one,
      tauObservable_transpose]
  · simp only [reflectionEffect, if_neg one_ne_zero]
    rw [Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_one,
      tauObservable_transpose]

/-- The honest Pair/W measurement is consistent on the EPR state, because its
effects are symmetric matrices.  This is the consistency assertion for the
Pauli basis measurements in the proof of `lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1364-1372`. -/
theorem pauliTraceMeasurement_isConsistentOn (P : AdmissibleParams) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) (r : PauliScalar P) :
    MIPStarRE.QPBT.Measurement.IsConsistentOn (pauliTraceMeasurement P W u r)
      (eprState (PauliRegister P)) := fun b =>
  epr_action_eq_of_transpose _ (pauliTraceMeasurement_effect_transpose P W u r b)

/-! ### The honest Point/W measurements -/

/-- The honest Point/W measurement: the generalized Pauli basis measurement
coarse-grained by the value `g_h(u)` of the low-degree encoding at the point
`u`.  Paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1290-1300`. -/
noncomputable def pauliPointMeasurement (P : AdmissibleParams) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) : Measurement (PauliScalar P) (PauliRegister P) :=
  (pauliBasisMeasurement W).postprocess (fun h => lowDegreeEnc h u)

/-- The honest Point/W measurement is projective. -/
theorem pauliPointMeasurement_projective (P : AdmissibleParams) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) :
    MIPStarRE.QPBT.Measurement.IsProjective (pauliPointMeasurement P W u) :=
  pauliBasisMeasurement_postprocess_projective W _

/-- The honest Point/W measurement is consistent on the EPR state. -/
theorem pauliPointMeasurement_isConsistentOn (P : AdmissibleParams) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) :
    MIPStarRE.QPBT.Measurement.IsConsistentOn (pauliPointMeasurement P W u)
      (eprState (PauliRegister P)) :=
  pauliBasisMeasurement_postprocess_isConsistentOn W _

/-! ### Honest line measurements -/

/-- Restrict a multivariate polynomial to an axis-parallel line, retaining the
coefficients through degree `d`.  This is the degree-`d` answer used for the
axis-line clause of `lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1290-1305`. -/
noncomputable def restrictToAxisLine (L : LdParams) (line : LineDesc L)
    (g : MvPolynomial (Fin L.m) (ScalarQ L)) : DegPoly L L.d :=
  fun i => (polynomialOnLine L line g).coeff i.val

/-- The coefficient-list restriction to an axis line evaluates to the original
low-degree encoding at every point of that line. -/
theorem evalCoefficient_restrictToAxisLine_lowDegreeEncoding
    (L : LdParams) (line : LineDesc L) (hline : line.kind = .axis)
    (h : Cube L.m → ScalarQ L) (t : ScalarQ L) :
    evalCoefficient (restrictToAxisLine L line (lowDegreeEncoding h)) t =
      MvPolynomial.eval (line.base + t • line.direction) (lowDegreeEncoding h) := by
  calc
    evalCoefficient (restrictToAxisLine L line (lowDegreeEncoding h)) t =
        Polynomial.eval t (polynomialOnLine L line (lowDegreeEncoding h)) := by
      unfold evalCoefficient restrictToAxisLine
      rw [Polynomial.eval_eq_sum_range'
        (Nat.lt_succ_of_le
          ((polynomialOnLine_lowDegreeEncoding_natDegree_le_one_of_axis
            L line hline h).trans L.hd)) t]
      exact Fin.sum_univ_eq_sum_range
        (fun i => (polynomialOnLine L line (lowDegreeEncoding h)).coeff i * t ^ i)
        (L.d + 1)
    _ = _ := eval_polynomialOnLine L line (lowDegreeEncoding h) t

/-- The honest axis-line measurement is the generalized Pauli basis
measurement coarse-grained by the degree-`d` restriction of `g_h` to the
canonical line carried by the question. -/
noncomputable def pauliALineMeasurement (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) :
    Measurement (Fin (P.d + 1) → PauliScalar P) (PauliRegister P) :=
    (pauliBasisMeasurement W).postprocess fun h =>
    restrictToAxisLine P.toLdParams
      (aLineDescOf P.toLdParams
        (ldALineCL P.toLdParams (pauliToLd P W z))) (lowDegreeEncoding h)

/-- The honest axis-line measurement is projective. -/
theorem pauliALineMeasurement_projective (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) :
    MIPStarRE.QPBT.Measurement.IsProjective (pauliALineMeasurement P W z) :=
  pauliBasisMeasurement_postprocess_projective W _

/-- The honest axis-line measurement is consistent on the EPR state. -/
theorem pauliALineMeasurement_isConsistentOn (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) :
    MIPStarRE.QPBT.Measurement.IsConsistentOn (pauliALineMeasurement P W z)
      (eprState (PauliRegister P)) :=
  pauliBasisMeasurement_postprocess_isConsistentOn W _

/-- The honest diagonal-line measurement is the generalized Pauli basis
measurement coarse-grained by the degree-`m d` restriction of `g_h` to the
canonical line carried by the question. -/
noncomputable def pauliDLineMeasurement (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) :
    Measurement (Fin (P.m * P.d + 1) → PauliScalar P) (PauliRegister P) :=
    (pauliBasisMeasurement W).postprocess fun h =>
    restrictToLine P.toLdParams
      (dLineDescOf P.toLdParams
        (ldDLineCL P.toLdParams (pauliToLd P W z))) (lowDegreeEncoding h)

/-- The honest diagonal-line measurement is projective. -/
theorem pauliDLineMeasurement_projective (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) :
    MIPStarRE.QPBT.Measurement.IsProjective (pauliDLineMeasurement P W z) :=
  pauliBasisMeasurement_postprocess_projective W _

/-- The honest diagonal-line measurement is consistent on the EPR state. -/
theorem pauliDLineMeasurement_isConsistentOn (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) :
    MIPStarRE.QPBT.Measurement.IsConsistentOn (pauliDLineMeasurement P W z)
      (eprState (PauliRegister P)) :=
  pauliBasisMeasurement_postprocess_isConsistentOn W _

/-- The Point/W measurement coarse-grained by the trace against `r` is the
Pair/W measurement.  This is the displayed identity
`E^{(Point,W),y}_{[tr(· r_W) = a]} = E^{(Pair,W),ω}_a` used twice in the
value-one argument of `lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1396-1420`. -/
theorem pauliPointMeasurement_postprocess_trace_effect (P : AdmissibleParams)
    (W : PauliKind) (u : Fin P.m → PauliScalar P) (r : PauliScalar P) (b : ZMod 2) :
    ((pauliPointMeasurement P W u).postprocess
        (fun a => fixedBinTrace P.model (a * r))).effect b =
      (pauliTraceMeasurement P W u r).effect b := by
  have hmaps : ∀ h ∈ Finset.univ.filter
      (fun h : PauliRegister P => pauliTraceBit P u r h = b),
      lowDegreeEnc h u ∈ Finset.univ.filter
        (fun a : PauliScalar P => fixedBinTrace P.model (a * r) = b) := fun h hh =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hh).2⟩
  have hinner : ∀ a ∈ Finset.univ.filter
      (fun a : PauliScalar P => fixedBinTrace P.model (a * r) = b),
      (Finset.univ.filter fun h : PauliRegister P => lowDegreeEnc h u = a) =
        (Finset.univ.filter fun h : PauliRegister P =>
          pauliTraceBit P u r h = b).filter fun h => lowDegreeEnc h u = a := by
    intro a ha
    ext h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hh
      refine ⟨?_, hh⟩
      change fixedBinTrace P.model (lowDegreeEnc h u * r) = b
      rw [hh]
      exact (Finset.mem_filter.mp ha).2
    · exact fun hh => hh.2
  calc ((pauliPointMeasurement P W u).postprocess
        (fun a => fixedBinTrace P.model (a * r))).effect b
      = ∑ a ∈ Finset.univ.filter
          (fun a : PauliScalar P => fixedBinTrace P.model (a * r) = b),
          ∑ h ∈ Finset.univ.filter (fun h : PauliRegister P => lowDegreeEnc h u = a),
            pauliProj W h := rfl
    _ = ∑ a ∈ Finset.univ.filter
          (fun a : PauliScalar P => fixedBinTrace P.model (a * r) = b),
          ∑ h ∈ (Finset.univ.filter fun h : PauliRegister P =>
              pauliTraceBit P u r h = b).filter (fun h => lowDegreeEnc h u = a),
            pauliProj W h :=
        Finset.sum_congr rfl fun a ha => by rw [hinner a ha]
    _ = ∑ h ∈ Finset.univ.filter (fun h : PauliRegister P => pauliTraceBit P u r h = b),
          pauliProj W h := Finset.sum_fiberwise_of_maps_to hmaps _
    _ = (pauliTraceMeasurement P W u r).effect b := rfl

/-! ### The commutation law of the honest pair -/

/-- The commutation law `𝒪_A 𝒪_B = (-1)^γ 𝒪_B 𝒪_A` of the proof of
`lem:pauli-completeness`, with `γ` the phase bit `eq:gamma-value`.  Paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1316-1330`. -/
theorem obsOf_pauliTraceMeasurement_mul_comm (P : AdmissibleParams) (z : PauliSpace P) :
    obsOf (pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z)) *
        obsOf (pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z)) =
      phaseSign (pauliPairGamma P z) •
        (obsOf (pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z)) *
          obsOf (pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z))) := by
  rw [obsOf_pauliTraceMeasurement, obsOf_pauliTraceMeasurement, tauObservable_X_mul_Z]
  rfl

/-- If the phase bit `γ` of `eq:gamma-value` is nonzero, the two honest Pair/W
observables anticommute.  Paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1316-1330`. -/
theorem obsOf_pauliTraceMeasurement_anticommute (P : AdmissibleParams)
    (z : PauliSpace P) (hgamma : pauliPairGamma P z ≠ 0) :
    obsOf (pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z)) *
        obsOf (pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z)) =
      -(obsOf (pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z)) *
        obsOf (pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z))) := by
  rw [obsOf_pauliTraceMeasurement_mul_comm]
  rcases zmod_two_eq_zero_or_one (pauliPairGamma P z) with h | h
  · exact absurd h hgamma
  · rw [h]
    simp [phaseSign]

/-- The Magic Square part of the honest strategy in the case `γ ≠ 0`: the two
honest Pair/W measurements anticommute, so `thm:ms-from-ac` supplies a
value-one SPCC Magic Square strategy whose first and fifth variable
measurements are the honest Pair/X and Pair/Z measurements.  Paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1345-1355`,
blueprint `blueprint/src/chapter/ch13_qpbt_test.tex:390-395`. -/
theorem exists_ms_perfect_strategy_of_pauliPairGamma_ne_zero (P : AdmissibleParams)
    (z : PauliSpace P) (hgamma : pauliPairGamma P z ≠ 0) :
    ∃ S : SymmetricStrategy msGameSymm, ∃ hι : S.ι = (PauliRegister P × ZMod 2),
      S.IsSPCC ∧ S.toStrategy.value = 1 ∧
      reindexState (Equiv.prodCongr (Equiv.cast hι) (Equiv.cast hι)) S.ψ =
        msPerfectState (PauliRegister P) ∧
      ∀ b : ZMod 2,
        reindexOp (Equiv.cast hι.symm) ((S.M (.var 0)).effect (.bit b)) =
            heteroKron
              ((pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z)).effect b)
              (1 : Op (ZMod 2)) ∧
          reindexOp (Equiv.cast hι.symm) ((S.M (.var 4)).effect (.bit b)) =
            heteroKron
              ((pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z)).effect b)
              (1 : Op (ZMod 2)) := by
  haveI : Nonempty (PauliRegister P) := ⟨0⟩
  exact exists_ms_perfect_strategy_of_anticommuting
    (pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z))
    (pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z))
    (pauliTraceMeasurement_projective P .X _ _)
    (pauliTraceMeasurement_projective P .Z _ _)
    (pauliTraceMeasurement_isConsistentOn P .X _ _)
    (pauliTraceMeasurement_isConsistentOn P .Z _ _)
    (obsOf_pauliTraceMeasurement_anticommute P z hgamma)

/-! ### The pointwise Magic Square measurement -/

/-- The nine cell measurements obtained from the anticommuting Pair/X and
Pair/Z observables at a question with nonzero phase bit. -/
noncomputable def pauliMagicCellMeasurement (P : AdmissibleParams)
    (z : PauliSpace P) (hgamma : pauliPairGamma P z ≠ 0) :
    Fin 9 → Measurement (ZMod 2) (PauliRegister P × ZMod 2) :=
  let A := pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z)
  let B := pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z)
  msCellMeasurement (obsOf A) (obsOf B)
    (obsOf_conjTranspose A (pauliTraceMeasurement_projective P .X _ _))
    (obsOf_conjTranspose B (pauliTraceMeasurement_projective P .Z _ _))
    (obsOf_sq A (pauliTraceMeasurement_projective P .X _ _))
    (obsOf_sq B (pauliTraceMeasurement_projective P .Z _ _))
    (obsOf_pauliTraceMeasurement_anticommute P z hgamma)

/-- Every Pauli-induced Magic Square cell measurement is projective. -/
theorem pauliMagicCellMeasurement_projective (P : AdmissibleParams)
    (z : PauliSpace P) (hgamma : pauliPairGamma P z ≠ 0) (j : Fin 9) :
    MIPStarRE.QPBT.Measurement.IsProjective
      (pauliMagicCellMeasurement P z hgamma j) := by
  simp only [pauliMagicCellMeasurement]
  exact msCellMeasurement_projective _ _
    (obsOf_conjTranspose _ (pauliTraceMeasurement_projective P .X _ _))
    (obsOf_conjTranspose _ (pauliTraceMeasurement_projective P .Z _ _))
    (obsOf_sq _ (pauliTraceMeasurement_projective P .X _ _))
    (obsOf_sq _ (pauliTraceMeasurement_projective P .Z _ _))
    (obsOf_pauliTraceMeasurement_anticommute P z hgamma) j

/-- Cell effects belonging to one Magic Square constraint commute. -/
theorem pauliMagicCellMeasurement_commute (P : AdmissibleParams)
    (z : PauliSpace P) (hgamma : pauliPairGamma P z ≠ 0)
    (i : Fin 6) (k l : Fin 3) (a b : ZMod 2) :
    Commute
      ((pauliMagicCellMeasurement P z hgamma (msConstraintVars i k)).effect a)
      ((pauliMagicCellMeasurement P z hgamma (msConstraintVars i l)).effect b) := by
  simp only [pauliMagicCellMeasurement]
  exact reflectionEffect_commute
    (msConstraintObservable_commute _ _
      (obsOf_sq _ (pauliTraceMeasurement_projective P .X _ _))
      (obsOf_sq _ (pauliTraceMeasurement_projective P .Z _ _))
      (obsOf_pauliTraceMeasurement_anticommute P z hgamma) i k l) a b

/-- The Magic Square measurement family used at a Pauli question with nonzero
phase bit. -/
noncomputable def pauliMagicMeasurement (P : AdmissibleParams)
    (z : PauliSpace P) (hgamma : pauliPairGamma P z ≠ 0) :
    MsType → Measurement MsAnswer (PauliRegister P × ZMod 2) :=
  msStrategyMeasurement (pauliMagicCellMeasurement P z hgamma)
    (pauliMagicCellMeasurement_projective P z hgamma)
    (pauliMagicCellMeasurement_commute P z hgamma)

/-- The Pauli-induced Magic Square measurement is projective. -/
theorem pauliMagicMeasurement_projective (P : AdmissibleParams)
    (z : PauliSpace P) (hgamma : pauliPairGamma P z ≠ 0) (x : MsType) :
    MIPStarRE.QPBT.Measurement.IsProjective
      (pauliMagicMeasurement P z hgamma x) := by
  exact msStrategyMeasurement_projective _ _ _ x

/-- Every effect of the Pauli-induced Magic Square measurement is symmetric. -/
theorem pauliMagicMeasurement_effect_transpose (P : AdmissibleParams)
    (z : PauliSpace P) (hgamma : pauliPairGamma P z ≠ 0)
    (x : MsType) (a : MsAnswer) :
    ((pauliMagicMeasurement P z hgamma x).effect a)ᵀ =
      (pauliMagicMeasurement P z hgamma x).effect a := by
  apply msStrategyMeasurement_effect_transpose
  intro j b
  simp only [pauliMagicCellMeasurement]
  apply msCellMeasurement_transpose
  · rw [obsOf_pauliTraceMeasurement]
    exact tauObservable_transpose _ _
  · rw [obsOf_pauliTraceMeasurement]
    exact tauObservable_transpose _ _

/-- The Pauli-induced Magic Square measurements commute on an incident
constraint-variable pair. -/
theorem pauliMagicMeasurement_incident_commute (P : AdmissibleParams)
    (z : PauliSpace P) (hgamma : pauliPairGamma P z ≠ 0)
    (i : Fin 6) (k : Fin 3) (a b : MsAnswer) :
    Commute ((pauliMagicMeasurement P z hgamma (.constraint i)).effect a)
      ((pauliMagicMeasurement P z hgamma
        (.var (msConstraintVars i k))).effect b) := by
  exact msStrategyMeasurement_incident_commute _ _ _ i k a b

/-- The distinguished variable effects of the Pauli-induced Magic Square
measurement are the tensor placements of the Pair/X and Pair/Z effects. -/
theorem pauliMagicMeasurement_var_effect (P : AdmissibleParams)
    (z : PauliSpace P) (hgamma : pauliPairGamma P z ≠ 0) (b : ZMod 2) :
    (pauliMagicMeasurement P z hgamma (.var 0)).effect (.bit b) =
        heteroKron
          ((pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z)).effect b)
          (1 : Op (ZMod 2)) ∧
      (pauliMagicMeasurement P z hgamma (.var 4)).effect (.bit b) =
        heteroKron
          ((pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z)).effect b)
          (1 : Op (ZMod 2)) := by
  constructor
  · unfold pauliMagicMeasurement
    rw [msStrategyMeasurement_var_bit]
    change reflectionEffect
        (heteroKron
          (obsOf (pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z)))
          (1 : Op (ZMod 2))) b = _
    rw [reflectionEffect_heteroKron_one, reflectionEffect_obsOf_measurement]
  · unfold pauliMagicMeasurement
    rw [msStrategyMeasurement_var_bit]
    change reflectionEffect
        (heteroKron
          (obsOf (pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z)))
          (1 : Op (ZMod 2))) b = _
    rw [reflectionEffect_heteroKron_one, reflectionEffect_obsOf_measurement]

/-! ### The Pair measurement in the case `γ = 0`

If the phase bit vanishes, the two honest Pair/W measurements commute and their
product is the Pair measurement `E^{Pair,ω}_{β_X, β_Z} = A_{β_X} B_{β_Z}` of
Equation `eq:pair-definition` in the proof of `lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1331-1344`.
-/

/-- If the phase bit `γ` of `eq:gamma-value` vanishes, the two honest Pair/W
observables commute.  Paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1316-1330`. -/
theorem obsOf_pauliTraceMeasurement_commute (P : AdmissibleParams)
    (z : PauliSpace P) (hgamma : pauliPairGamma P z = 0) :
    Commute (obsOf (pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z)))
      (obsOf (pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z))) := by
  rw [commute_iff_eq, obsOf_pauliTraceMeasurement_mul_comm, hgamma]
  simp [phaseSign]

/-- If the phase bit `γ` vanishes, the effects of the two honest Pair/W
measurements commute; this is the commutation assertion of the honest strategy
in the case `γ = 0`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1374-1382`. -/
theorem pauliTraceMeasurement_effect_commute (P : AdmissibleParams)
    (z : PauliSpace P) (hgamma : pauliPairGamma P z = 0) (a b : ZMod 2) :
    Commute ((pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z)).effect a)
      ((pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z)).effect b) := by
  have hOO :
      Commute (tauObservable PauliKind.X (pauliRXBlock z • indicatorVec (pauliXBlock z)))
        (tauObservable PauliKind.Z (pauliRZBlock z • indicatorVec (pauliZBlock z))) := by
    rw [← obsOf_pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z),
      ← obsOf_pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z)]
    exact obsOf_pauliTraceMeasurement_commute P z hgamma
  rw [pauliTraceMeasurement_effect_eq_reflectionEffect,
    pauliTraceMeasurement_effect_eq_reflectionEffect]
  exact reflectionEffect_commute hOO a b

/-- The Pair effect `E^{Pair,ω}_{β_X, β_Z} = A_{β_X} B_{β_Z}` of Equation
`eq:pair-definition`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1331-1339`. -/
noncomputable def pauliPairEffect (P : AdmissibleParams) (z : PauliSpace P)
    (β : ZMod 2 × ZMod 2) : Op (PauliRegister P) :=
  (pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z)).effect β.1 *
    (pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z)).effect β.2

/-- For `γ = 0` the Pair effects are projectors, being products of commuting
projectors.  Paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1331-1344`. -/
theorem pauliPairEffect_isProj (P : AdmissibleParams) (z : PauliSpace P)
    (hgamma : pauliPairGamma P z = 0) (β : ZMod 2 × ZMod 2) :
    IsProj (pauliPairEffect P z β) :=
  IsStarProjection.mul (pauliTraceMeasurement_projective P .X _ _ β.1)
    (pauliTraceMeasurement_projective P .Z _ _ β.2)
    (pauliTraceMeasurement_effect_commute P z hgamma β.1 β.2)

/-- The Pair effects sum to the identity. -/
theorem sum_pauliPairEffect (P : AdmissibleParams) (z : PauliSpace P) :
    ∑ β : ZMod 2 × ZMod 2, pauliPairEffect P z β = 1 := by
  calc ∑ β : ZMod 2 × ZMod 2, pauliPairEffect P z β
      = ∑ a : ZMod 2, ∑ b : ZMod 2,
          (pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z)).effect a *
            (pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z)).effect b :=
        Fintype.sum_prod_type _
    _ = ∑ a : ZMod 2,
          (pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z)).effect a *
            ∑ b : ZMod 2,
              (pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z)).effect b :=
        Finset.sum_congr rfl fun a _ => by rw [Finset.mul_sum]
    _ = 1 := by
        rw [(pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z)).sum_eq_one]
        simp [(pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z)).sum_eq_one]

/-- The Pair measurement of Equation `eq:pair-definition` in the case `γ = 0`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1331-1344`,
blueprint `blueprint/src/chapter/ch13_qpbt_test.tex:390-395`. -/
noncomputable def pauliPairMeasurement (P : AdmissibleParams) (z : PauliSpace P)
    (hgamma : pauliPairGamma P z = 0) : Measurement (ZMod 2 × ZMod 2) (PauliRegister P) :=
  Measurement.ofSumEqOne (pauliPairEffect P z)
    (fun β => (pauliPairEffect_isProj P z hgamma β).nonneg) (sum_pauliPairEffect P z)

/-- The Pair measurement is projective. -/
theorem pauliPairMeasurement_projective (P : AdmissibleParams) (z : PauliSpace P)
    (hgamma : pauliPairGamma P z = 0) :
    MIPStarRE.QPBT.Measurement.IsProjective (pauliPairMeasurement P z hgamma) :=
  pauliPairEffect_isProj P z hgamma

/-- The Pair measurement is consistent on the EPR state.  This is the
consistency assertion for the Pair measurement in the case `γ = 0`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1368-1372`. -/
theorem pauliPairMeasurement_isConsistentOn (P : AdmissibleParams) (z : PauliSpace P)
    (hgamma : pauliPairGamma P z = 0) :
    MIPStarRE.QPBT.Measurement.IsConsistentOn (pauliPairMeasurement P z hgamma)
      (eprState (PauliRegister P)) := by
  intro β
  refine epr_action_eq_of_transpose _ ?_
  change (pauliPairEffect P z β)ᵀ = pauliPairEffect P z β
  rw [pauliPairEffect, Matrix.transpose_mul, pauliTraceMeasurement_effect_transpose,
    pauliTraceMeasurement_effect_transpose]
  exact (pauliTraceMeasurement_effect_commute P z hgamma β.1 β.2).eq.symm

end

end MIPStarRE.QPBT
