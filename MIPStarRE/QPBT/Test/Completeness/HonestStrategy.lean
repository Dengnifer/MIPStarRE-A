import MIPStarRE.QPBT.Algebra.PauliTheorems
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

open MIPStarRE.LDT MIPStarRE.Quantum

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
      show (if y i = x i + a i then (1 : ℂ) else 0) = if x i = y i + a i then 1 else 0
      by_cases h : x i = y i + a i
      · rw [if_pos h, if_pos ((hswap _ _ _).mp h)]
      · rw [if_neg h, if_neg (fun hc => h ((hswap _ _ _).mp hc))]
  | Z =>
      refine Finset.prod_congr rfl fun i _ => ?_
      show (if y i = x i then phaseSign (binTrace K (a i * x i)) else 0) =
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

/-- The honest Pair/W measurement is consistent on the EPR state, because its
effects are symmetric matrices.  This is the consistency assertion for the
Pauli basis measurements in the proof of `lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1364-1372`. -/
theorem pauliTraceMeasurement_isConsistentOn (P : AdmissibleParams) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) (r : PauliScalar P) :
    MIPStarRE.QPBT.Measurement.IsConsistentOn (pauliTraceMeasurement P W u r)
      (eprState (PauliRegister P)) := by
  intro b
  refine epr_action_eq_of_transpose _ ?_
  rw [pauliTraceMeasurement_effect_eq_reflectionEffect]
  rcases zmod_two_eq_zero_or_one b with rfl | rfl
  · simp only [reflectionEffect, if_pos]
    rw [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_one,
      tauObservable_transpose]
  · simp only [reflectionEffect, if_neg one_ne_zero]
    rw [Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_one,
      tauObservable_transpose]

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

end

end MIPStarRE.QPBT
