import MIPStarRE.QPBT.Combining.ExtendedLineGame.StateTransport
import MIPStarRE.QPBT.Combining.Points.Placement
import MIPStarRE.QPBT.Extraction.Observables

/-!
# Consistency of the pulled-apart Pauli measurements

This module records the two estimates by which the polynomial marginals absorb
the expanded point measurements, with all heterogeneous placements written
explicitly. It also defines the mass of non-encoding marginal outcomes and
states the support estimate needed by the corrected decoder calculation.

The marginal agreement estimates and reverse-placement correlation transports
are developed from a supplied global polynomial-pair witness.

## References

The marginal estimates formalize blueprint
`lem:qld-constructing-the-paulis-helper`, from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1609-1664`.
The non-encoding support obligation contributes to blueprint
`lem:qld-construct-the-paulis`, from paper lines 1458-1608; see
`docs/paper-gaps/qpbt_decoding-identity.tex`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus
open ProjectiveSetting

noncomputable section

/-! ## Absorption of expanded point measurements -/

/-- A placed measurement effect is Hermitian. -/
private theorem placedMeasurement_effect_hermitian
    {P : AdmissibleParams} {epsilon : ℝ}
    {Outcome : Type*} [Fintype Outcome] (S : ProjectiveSetting P epsilon)
    (placement : Placement) (measurement : Measurement Outcome
      (S.ExpandedLocalSpace placement.side)) (answer : Outcome) :
    (S.place placement (measurement.effect answer))ᴴ =
      S.place placement (measurement.effect answer) := by
  simpa only [placedMeasurement_effect] using
    (measurement_effect_hermitian (placedMeasurement S placement measurement) answer)

/-- Reversing two Hermitian factors does not change the real quadratic form. -/
private theorem stateQForm_mul_comm_of_hermitian
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (psi : EuclideanSpace ℂ ι) (A B : Op ι)
    (hA : Aᴴ = A) (hB : Bᴴ = B) :
    stateQForm psi (A * B) = stateQForm psi (B * A) := by
  unfold stateQForm applyOperatorToState
  rw [show A * B = (B * A)ᴴ by
    rw [Matrix.conjTranspose_mul, hA, hB]]
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    LinearMap.adjoint_inner_right]
  simpa using (inner_re_symm (𝕜 := ℂ)
    ((Matrix.toEuclideanLin (B * A)) psi) psi)

namespace GlobalPairWitness

/-- Evaluating a single-basis marginal is the same finite postprocessing as
evaluating the corresponding component of the joint polynomial outcome. This
is the coarse-graining in the proof of blueprint
`lem:qld-constructing-the-paulis-helper`, paper
`14_analysis_of_the_pauli_basis_test.tex:1626-1637`. -/
theorem marginalPoly_postprocess_eval {P : AdmissibleParams} {epsilon deltaG : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S deltaG)
    (side : PlayerSide) (W : PauliKind) (point : Fin P.m → PauliScalar P) :
    (w.marginalPoly side W).postprocess (fun poly => MvPolynomial.eval point poly.1) =
      (w.Smeas side).postprocess (evalAt W point) := by
  rw [marginalPoly, MIPStarRE.Quantum.Measurement.postprocess_comp]
  cases W <;> rfl

end GlobalPairWitness

/-- Regrouping polynomial outcomes by their value at a point preserves the
agreement operator. This is the finite-sum identity behind paper
`14_analysis_of_the_pauli_basis_test.tex:1626-1637`, blueprint
`lem:qld-constructing-the-paulis-helper`. -/
theorem sum_marginalPoly_eval_mul {P : AdmissibleParams} {epsilon deltaG : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S deltaG)
    (placement : Placement) (W : PauliKind) (point : Fin P.m → PauliScalar P)
    (family : PauliScalar P → Op (SixReg P S.toStrategy.ιA S.toStrategy.ιB)) :
    (∑ answer : PauliScalar P, S.place placement
      (((w.marginalPoly placement.side W).postprocess
        (fun poly => MvPolynomial.eval point poly.1)).effect answer) * family answer) =
      ∑ poly : Poly P, S.place placement ((w.marginalPoly placement.side W).effect poly) *
        family (MvPolynomial.eval point poly.1) := by
  classical
  simp only [MIPStarRE.Quantum.Measurement.postprocess_effect, place_finsetSum,
    Finset.sum_mul]
  calc
    _ = ∑ answer : PauliScalar P,
        ∑ poly ∈ Finset.univ.filter (fun poly : Poly P =>
          MvPolynomial.eval point poly.1 = answer),
          S.place placement ((w.marginalPoly placement.side W).effect poly) *
            family (MvPolynomial.eval point poly.1) := by
      apply Finset.sum_congr rfl
      intro answer _
      apply Finset.sum_congr rfl
      intro poly hpoly
      rw [(Finset.mem_filter.mp hpoly).2]
    _ = _ := Finset.sum_fiberwise _ _ _

/-- Alice's evaluated marginal on `AA'` retains the witness consistency with
Bob's expanded point measurement on `BA''`. This is the direct placement in
paper `14_analysis_of_the_pauli_basis_test.tex:1626-1637`, supporting blueprint
`lem:qld-constructing-the-paulis-helper`; no register transfer is used. -/
theorem marginalPoly_pointMeas_consistent_alice {P : AdmissibleParams}
    {epsilon deltaG : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S deltaG) (W : PauliKind) :
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
      (fun point answer => S.place .AA'
        (((w.marginalPoly .alice W).postprocess
          (fun poly => MvPolynomial.eval point poly.1)).effect answer))
      (fun point answer => S.place .BA''
        ((S.pointMeasExp .bob W point).effect answer)) S.psiHat ≤ deltaG := by
  simpa only [w.marginalPoly_postprocess_eval] using w.point_consistent_alice W

/-- Bob's evaluated marginal on `BB'` retains the witness consistency with
Alice's expanded point measurement on `AB''`. This is the reverse-player
direct placement of paper `14_analysis_of_the_pauli_basis_test.tex:1626-1637`,
supporting blueprint `lem:qld-constructing-the-paulis-helper`; no register
transfer is used. -/
theorem marginalPoly_pointMeas_consistent_bob {P : AdmissibleParams}
    {epsilon deltaG : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S deltaG) (W : PauliKind) :
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
      (fun point answer => S.place .BB'
        (((w.marginalPoly .bob W).postprocess
          (fun poly => MvPolynomial.eval point poly.1)).effect answer))
      (fun point answer => S.place .AB''
        ((S.pointMeasExp .alice W point).effect answer)) S.psiHat ≤ deltaG := by
  simpa only [w.marginalPoly_postprocess_eval] using w.point_consistent_bob W

/-- The Alice marginal consistency estimate is unchanged when both active
operators are moved from the first EPR pair to the second one. -/
private theorem marginalPoly_pointMeas_consistent_alice_reversed
    {P : AdmissibleParams} {epsilon deltaG : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S deltaG)
    (W : PauliKind) :
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
      (fun point answer => S.place .AB''
        (((w.marginalPoly .alice W).postprocess
          (fun poly => MvPolynomial.eval point poly.1)).effect answer))
      (fun point answer => S.place .BB'
        ((S.pointMeasExp .bob W point).effect answer)) S.psiHat ≤ deltaG := by
  calc
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
        (fun point answer => S.place .AB''
          (((w.marginalPoly .alice W).postprocess
            (fun poly => MvPolynomial.eval point poly.1)).effect answer))
        (fun point answer => S.place .BB'
          ((S.pointMeasExp .bob W point).effect answer)) S.psiHat =
      consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
        (fun point answer => S.place .AA'
          (((w.marginalPoly .alice W).postprocess
            (fun poly => MvPolynomial.eval point poly.1)).effect answer))
        (fun point answer => S.place .BA''
          ((S.pointMeasExp .bob W point).effect answer)) S.psiHat := by
      unfold consistencyDefect
      apply avgOver_congr
      intro point
      apply Finset.sum_congr rfl
      intro answer _
      apply Finset.sum_congr rfl
      intro other _
      by_cases hanswer : answer = other
      · simp [hanswer]
      · simp only [hanswer, if_false, consistency_term_eq_stateQForm]
        let A := ((w.marginalPoly .alice W).postprocess
          (fun poly => MvPolynomial.eval point poly.1)).effect answer
        let B := (S.pointMeasExp .bob W point).effect other
        have hA : A.IsHermitian :=
          (Matrix.nonneg_iff_posSemidef.mp
            (((w.marginalPoly .alice W).postprocess
              (fun poly => MvPolynomial.eval point poly.1)).pos answer)).isHermitian
        have hB : B.IsHermitian :=
          (Matrix.nonneg_iff_posSemidef.mp
            ((S.pointMeasExp .bob W point).pos other)).isHermitian
        exact
          (ExtendedLineGame.stateQForm_pairState_eq_AB''_BB' S A B hA hB).symm.trans
            (ExtendedLineGame.stateQForm_pairState_eq_AA'_BA'' S A B hA hB)
    _ ≤ deltaG := marginalPoly_pointMeas_consistent_alice w W

/-- The Bob marginal consistency estimate is unchanged when both active
operators are moved from the second EPR pair to the first one. -/
private theorem marginalPoly_pointMeas_consistent_bob_reversed
    {P : AdmissibleParams} {epsilon deltaG : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S deltaG)
    (W : PauliKind) :
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
      (fun point answer => S.place .BA''
        (((w.marginalPoly .bob W).postprocess
          (fun poly => MvPolynomial.eval point poly.1)).effect answer))
      (fun point answer => S.place .AA'
        ((S.pointMeasExp .alice W point).effect answer)) S.psiHat ≤ deltaG := by
  calc
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
        (fun point answer => S.place .BA''
          (((w.marginalPoly .bob W).postprocess
            (fun poly => MvPolynomial.eval point poly.1)).effect answer))
        (fun point answer => S.place .AA'
          ((S.pointMeasExp .alice W point).effect answer)) S.psiHat =
      consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
        (fun point answer => S.place .BB'
          (((w.marginalPoly .bob W).postprocess
            (fun poly => MvPolynomial.eval point poly.1)).effect answer))
        (fun point answer => S.place .AB''
          ((S.pointMeasExp .alice W point).effect answer)) S.psiHat := by
      unfold consistencyDefect
      apply avgOver_congr
      intro point
      apply Finset.sum_congr rfl
      intro answer _
      apply Finset.sum_congr rfl
      intro other _
      by_cases hanswer : answer = other
      · simp [hanswer]
      · simp only [hanswer, if_false, consistency_term_eq_stateQForm]
        let A := (S.pointMeasExp .alice W point).effect other
        let B := ((w.marginalPoly .bob W).postprocess
          (fun poly => MvPolynomial.eval point poly.1)).effect answer
        have hA : A.IsHermitian :=
          (Matrix.nonneg_iff_posSemidef.mp
            ((S.pointMeasExp .alice W point).pos other)).isHermitian
        have hB : B.IsHermitian :=
          (Matrix.nonneg_iff_posSemidef.mp
            (((w.marginalPoly .bob W).postprocess
              (fun poly => MvPolynomial.eval point poly.1)).pos answer)).isHermitian
        have hBA : (S.place .BA'' B)ᴴ = S.place .BA'' B :=
          placedMeasurement_effect_hermitian S .BA''
            ((w.marginalPoly .bob W).postprocess
              (fun poly => MvPolynomial.eval point poly.1)) answer
        have hAA : (S.place .AA' A)ᴴ = S.place .AA' A :=
          placedMeasurement_effect_hermitian S .AA'
            (S.pointMeasExp .alice W point) other
        have hBB : (S.place .BB' B)ᴴ = S.place .BB' B :=
          placedMeasurement_effect_hermitian S .BB'
            ((w.marginalPoly .bob W).postprocess
              (fun poly => MvPolynomial.eval point poly.1)) answer
        have hAB : (S.place .AB'' A)ᴴ = S.place .AB'' A :=
          placedMeasurement_effect_hermitian S .AB''
            (S.pointMeasExp .alice W point) other
        calc
          stateQForm S.psiHat (S.place .BA'' B * S.place .AA' A) =
              stateQForm S.psiHat (S.place .AA' A * S.place .BA'' B) :=
            stateQForm_mul_comm_of_hermitian S.psiHat _ _ hBA hAA
          _ = stateQForm (ExtendedLineGame.pairState S) (heteroKron A B) :=
            (ExtendedLineGame.stateQForm_pairState_eq_AA'_BA'' S A B hA hB).symm
          _ = stateQForm S.psiHat (S.place .AB'' A * S.place .BB' B) :=
            ExtendedLineGame.stateQForm_pairState_eq_AB''_BB' S A B hA hB
          _ = stateQForm S.psiHat (S.place .BB' B * S.place .AB'' A) :=
            stateQForm_mul_comm_of_hermitian S.psiHat _ _ hAB hBB
    _ ≤ deltaG := marginalPoly_pointMeas_consistent_bob w W

/-- Alice's evaluated marginal on `AA'` is within squared distance `2 * deltaG`
of Bob's expanded point measurement on `BA''`, with the answer sum over the
field. This is the direct-placement agreement estimate used for both displays
of blueprint `lem:qld-constructing-the-paulis-helper`, paper
`14_analysis_of_the_pauli_basis_test.tex:1626-1637`. The factor two makes
`fact:agreement` explicit; no placement transfer is assumed. -/
theorem marginalPoly_pointMeas_approx_alice {P : AdmissibleParams}
    {epsilon deltaG : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S deltaG) (W : PauliKind) :
    opFamilyDistSq (uniformDistribution (Fin P.m → PauliScalar P))
      (fun point answer => S.place .AA'
        (((w.marginalPoly .alice W).postprocess
          (fun poly => MvPolynomial.eval point poly.1)).effect answer))
      (fun point answer => S.place .BA''
        ((S.pointMeasExp .bob W point).effect answer)) S.psiHat ≤ 2 * deltaG := by
  have hAgreement := opFamilyDistSq_le_two_mul_consistencyDefect
    (uniformDistribution (Fin P.m → PauliScalar P))
    (fun point => placedMeasurement S .AA'
      ((w.marginalPoly .alice W).postprocess
        (fun poly => MvPolynomial.eval point poly.1)))
    (fun point => placedMeasurement S .BA'' (S.pointMeasExp .bob W point)) S.psiHat
  simp only [placedMeasurement_effect] at hAgreement
  exact hAgreement.trans (mul_le_mul_of_nonneg_left
    (marginalPoly_pointMeas_consistent_alice w W) (by norm_num))

/-- Bob's evaluated marginal on `BB'` is within squared distance `2 * deltaG`
of Alice's expanded point measurement on `AB''`. This is the reverse-player
direct-placement estimate in paper
`14_analysis_of_the_pauli_basis_test.tex:1626-1637`, supporting blueprint
`lem:qld-constructing-the-paulis-helper`. It does not assert either of the
two placements that require transfer between primed and double-primed registers. -/
theorem marginalPoly_pointMeas_approx_bob {P : AdmissibleParams}
    {epsilon deltaG : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S deltaG) (W : PauliKind) :
    opFamilyDistSq (uniformDistribution (Fin P.m → PauliScalar P))
      (fun point answer => S.place .BB'
        (((w.marginalPoly .bob W).postprocess
          (fun poly => MvPolynomial.eval point poly.1)).effect answer))
      (fun point answer => S.place .AB''
        ((S.pointMeasExp .alice W point).effect answer)) S.psiHat ≤ 2 * deltaG := by
  have hAgreement := opFamilyDistSq_le_two_mul_consistencyDefect
    (uniformDistribution (Fin P.m → PauliScalar P))
    (fun point => placedMeasurement S .BB'
      ((w.marginalPoly .bob W).postprocess
        (fun poly => MvPolynomial.eval point poly.1)))
    (fun point => placedMeasurement S .AB'' (S.pointMeasExp .alice W point)) S.psiHat
  simp only [placedMeasurement_effect] at hAgreement
  exact hAgreement.trans (mul_le_mul_of_nonneg_left
    (marginalPoly_pointMeas_consistent_bob w W) (by norm_num))

/-- The agreement sum for Alice's marginal on `AA'` and Bob's expanded point
measurement on `BA''` is within squared distance `2 * deltaG` of the identity.
This proves the direct placement of Equation `eq:qld-sg-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:1626-1634`, blueprint
`lem:qld-constructing-the-paulis-helper`. Projectivity is obtained by applying
finite postprocessing directly to `w.Smeas`, without using the open marginal
projectivity theorem or any register-transfer theorem. -/
theorem sum_marginalPoly_pointMeas_approx_id_alice {P : AdmissibleParams}
    {epsilon deltaG : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S deltaG) (W : PauliKind) :
    opDistSq (uniformDistribution (Fin P.m → PauliScalar P))
      (fun point => ∑ poly : Poly P,
        S.place .AA' ((w.marginalPoly .alice W).effect poly) *
          S.place .BA'' ((S.pointMeasExp .bob W point).effect
            (MvPolynomial.eval point poly.1)))
      (fun _ => 1) S.psiHat ≤ 2 * deltaG := by
  let evaluated := fun point : Fin P.m → PauliScalar P =>
    placedMeasurement S .AA' ((w.marginalPoly .alice W).postprocess
      (fun poly => MvPolynomial.eval point poly.1))
  have hProjective (point : Fin P.m → PauliScalar P) :
      Measurement.IsProjective (evaluated point) := by
    apply placedMeasurement_isProjective
    rw [w.marginalPoly_postprocess_eval]
    exact SandwichProduct.postprocess_isProjective
      (w.Smeas .alice) (w.projective .alice) (evalAt W point)
  have hDistance : opFamilyDistSq (uniformDistribution (Fin P.m → PauliScalar P))
      (fun point answer => (evaluated point).effect answer)
      (fun point answer => S.place .BA''
        ((S.pointMeasExp .bob W point).effect answer)) S.psiHat ≤ 2 * deltaG := by
    simpa only [evaluated, placedMeasurement_effect] using
      marginalPoly_pointMeas_approx_alice w W
  have hSum := opDistSq_sum_sub_mul_le_of_projective
    (uniformDistribution (Fin P.m → PauliScalar P)) evaluated
    (fun point answer => S.place .BA''
      ((S.pointMeasExp .bob W point).effect answer)) S.psiHat (2 * deltaG)
    hProjective hDistance Finset.univ
  simp only [MIPStarRE.Quantum.Measurement.sum_eq_one] at hSum
  simp only [evaluated, placedMeasurement_effect] at hSum
  have hRegroup (point : Fin P.m → PauliScalar P) :
      (∑ answer : PauliScalar P, S.place .AA'
        (((w.marginalPoly .alice W).postprocess
          (fun poly => MvPolynomial.eval point poly.1)).effect answer) *
          S.place .BA'' ((S.pointMeasExp .bob W point).effect answer)) =
        ∑ poly : Poly P, S.place .AA' ((w.marginalPoly .alice W).effect poly) *
          S.place .BA'' ((S.pointMeasExp .bob W point).effect
            (MvPolynomial.eval point poly.1)) :=
    sum_marginalPoly_eval_mul w .AA' W point
      (fun answer => S.place .BA'' ((S.pointMeasExp .bob W point).effect answer))
  simp only [hRegroup] at hSum
  rw [opDistSq, opFamilyDistSq_symm] at hSum
  exact hSum

/-- The agreement sum for Bob's marginal on `BB'` and Alice's expanded point
measurement on `AB''` is within squared distance `2 * deltaG` of the identity.
This proves the reverse-player direct placement of Equation `eq:qld-sg-cons`,
paper `14_analysis_of_the_pauli_basis_test.tex:1626-1634`, blueprint
`lem:qld-constructing-the-paulis-helper`. The other two directed placements
remain outside this conclusion. -/
theorem sum_marginalPoly_pointMeas_approx_id_bob {P : AdmissibleParams}
    {epsilon deltaG : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S deltaG) (W : PauliKind) :
    opDistSq (uniformDistribution (Fin P.m → PauliScalar P))
      (fun point => ∑ poly : Poly P,
        S.place .BB' ((w.marginalPoly .bob W).effect poly) *
          S.place .AB'' ((S.pointMeasExp .alice W point).effect
            (MvPolynomial.eval point poly.1)))
      (fun _ => 1) S.psiHat ≤ 2 * deltaG := by
  let evaluated := fun point : Fin P.m → PauliScalar P =>
    placedMeasurement S .BB' ((w.marginalPoly .bob W).postprocess
      (fun poly => MvPolynomial.eval point poly.1))
  have hProjective (point : Fin P.m → PauliScalar P) :
      Measurement.IsProjective (evaluated point) := by
    apply placedMeasurement_isProjective
    rw [w.marginalPoly_postprocess_eval]
    exact SandwichProduct.postprocess_isProjective
      (w.Smeas .bob) (w.projective .bob) (evalAt W point)
  have hDistance : opFamilyDistSq (uniformDistribution (Fin P.m → PauliScalar P))
      (fun point answer => (evaluated point).effect answer)
      (fun point answer => S.place .AB''
        ((S.pointMeasExp .alice W point).effect answer)) S.psiHat ≤ 2 * deltaG := by
    simpa only [evaluated, placedMeasurement_effect] using
      marginalPoly_pointMeas_approx_bob w W
  have hSum := opDistSq_sum_sub_mul_le_of_projective
    (uniformDistribution (Fin P.m → PauliScalar P)) evaluated
    (fun point answer => S.place .AB''
      ((S.pointMeasExp .alice W point).effect answer)) S.psiHat (2 * deltaG)
    hProjective hDistance Finset.univ
  simp only [MIPStarRE.Quantum.Measurement.sum_eq_one] at hSum
  simp only [evaluated, placedMeasurement_effect] at hSum
  have hRegroup (point : Fin P.m → PauliScalar P) :
      (∑ answer : PauliScalar P, S.place .BB'
        (((w.marginalPoly .bob W).postprocess
          (fun poly => MvPolynomial.eval point poly.1)).effect answer) *
          S.place .AB'' ((S.pointMeasExp .alice W point).effect answer)) =
        ∑ poly : Poly P, S.place .BB' ((w.marginalPoly .bob W).effect poly) *
          S.place .AB'' ((S.pointMeasExp .alice W point).effect
            (MvPolynomial.eval point poly.1)) :=
    sum_marginalPoly_eval_mul w .BB' W point
      (fun answer => S.place .AB'' ((S.pointMeasExp .alice W point).effect answer))
  simp only [hRegroup] at hSum
  rw [opDistSq, opFamilyDistSq_symm] at hSum
  exact hSum

set_option maxHeartbeats 800000 in
-- The explicit measurement aliases keep the six-register instance search local.
/-- The Alice-first agreement sum has the same identity-absorption bound on
the `AB''`--`BB'` EPR pair. -/
private theorem sum_marginalPoly_pointMeas_approx_id_alice_reversed
    {P : AdmissibleParams} {epsilon deltaG : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S deltaG)
    (W : PauliKind) :
    opDistSq (uniformDistribution (Fin P.m → PauliScalar P))
      (fun point => ∑ poly : Poly P,
        S.place .AB'' ((w.marginalPoly .alice W).effect poly) *
          S.place .BB' ((S.pointMeasExp .bob W point).effect
            (MvPolynomial.eval point poly.1)))
      (fun _ => 1) S.psiHat ≤ 2 * deltaG := by
  let evaluated : (Fin P.m → PauliScalar P) →
      MIPStarRE.Quantum.Measurement (PauliScalar P)
        (SixReg P S.toStrategy.ιA S.toStrategy.ιB) := fun point =>
    placedMeasurement S .AB'' ((w.marginalPoly .alice W).postprocess
      (fun poly => MvPolynomial.eval point poly.1))
  let comparison : (Fin P.m → PauliScalar P) →
      MIPStarRE.Quantum.Measurement (PauliScalar P)
        (SixReg P S.toStrategy.ιA S.toStrategy.ιB) := fun point =>
    placedMeasurement S .BB' (S.pointMeasExp .bob W point)
  have hProjective (point : Fin P.m → PauliScalar P) :
      Measurement.IsProjective (evaluated point) := by
    apply placedMeasurement_isProjective
    rw [w.marginalPoly_postprocess_eval]
    exact SandwichProduct.postprocess_isProjective
      (w.Smeas .alice) (w.projective .alice) (evalAt W point)
  have hAgreement :
      opFamilyDistSq (uniformDistribution (Fin P.m → PauliScalar P))
          (fun point answer => (evaluated point).effect answer)
          (fun point answer => (comparison point).effect answer) S.psiHat ≤
        2 * consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
          (fun point answer => (evaluated point).effect answer)
          (fun point answer => (comparison point).effect answer) S.psiHat :=
    opFamilyDistSq_le_two_mul_consistencyDefect
      (X := Fin P.m → PauliScalar P) (α := PauliScalar P)
      (ι := SixReg P S.toStrategy.ιA S.toStrategy.ιB)
      (uniformDistribution (Fin P.m → PauliScalar P)) evaluated comparison S.psiHat
  have hConsistency :
      consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
          (fun point answer => (evaluated point).effect answer)
          (fun point answer => (comparison point).effect answer) S.psiHat ≤ deltaG := by
    simpa only [evaluated, comparison, placedMeasurement_effect] using
      marginalPoly_pointMeas_consistent_alice_reversed w W
  have hDistance : opFamilyDistSq
      (uniformDistribution (Fin P.m → PauliScalar P))
      (fun point answer => (evaluated point).effect answer)
      (fun point answer => S.place .BB'
        ((S.pointMeasExp .bob W point).effect answer)) S.psiHat ≤ 2 * deltaG := by
    simpa only [comparison, placedMeasurement_effect] using
      hAgreement.trans (mul_le_mul_of_nonneg_left hConsistency (by norm_num))
  have hSum := opDistSq_sum_sub_mul_le_of_projective
    (uniformDistribution (Fin P.m → PauliScalar P)) evaluated
    (fun point answer => S.place .BB'
      ((S.pointMeasExp .bob W point).effect answer)) S.psiHat (2 * deltaG)
    hProjective hDistance Finset.univ
  simp only [MIPStarRE.Quantum.Measurement.sum_eq_one] at hSum
  simp only [evaluated, placedMeasurement_effect] at hSum
  have hRegroup (point : Fin P.m → PauliScalar P) :
      (∑ answer : PauliScalar P, S.place .AB''
        (((w.marginalPoly .alice W).postprocess
          (fun poly => MvPolynomial.eval point poly.1)).effect answer) *
          S.place .BB' ((S.pointMeasExp .bob W point).effect answer)) =
        ∑ poly : Poly P, S.place .AB''
          ((w.marginalPoly .alice W).effect poly) *
            S.place .BB' ((S.pointMeasExp .bob W point).effect
              (MvPolynomial.eval point poly.1)) :=
    sum_marginalPoly_eval_mul w .AB'' W point
      (fun answer => S.place .BB' ((S.pointMeasExp .bob W point).effect answer))
  simp only [hRegroup] at hSum
  rw [opDistSq, opFamilyDistSq_symm] at hSum
  exact hSum

set_option maxHeartbeats 800000 in
-- The explicit measurement aliases keep the six-register instance search local.
/-- The Bob-first agreement sum has the same identity-absorption bound on
the `BA''`--`AA'` EPR pair. -/
private theorem sum_marginalPoly_pointMeas_approx_id_bob_reversed
    {P : AdmissibleParams} {epsilon deltaG : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S deltaG)
    (W : PauliKind) :
    opDistSq (uniformDistribution (Fin P.m → PauliScalar P))
      (fun point => ∑ poly : Poly P,
        S.place .BA'' ((w.marginalPoly .bob W).effect poly) *
          S.place .AA' ((S.pointMeasExp .alice W point).effect
            (MvPolynomial.eval point poly.1)))
      (fun _ => 1) S.psiHat ≤ 2 * deltaG := by
  let evaluated : (Fin P.m → PauliScalar P) →
      MIPStarRE.Quantum.Measurement (PauliScalar P)
        (SixReg P S.toStrategy.ιA S.toStrategy.ιB) := fun point =>
    placedMeasurement S .BA'' ((w.marginalPoly .bob W).postprocess
      (fun poly => MvPolynomial.eval point poly.1))
  let comparison : (Fin P.m → PauliScalar P) →
      MIPStarRE.Quantum.Measurement (PauliScalar P)
        (SixReg P S.toStrategy.ιA S.toStrategy.ιB) := fun point =>
    placedMeasurement S .AA' (S.pointMeasExp .alice W point)
  have hProjective (point : Fin P.m → PauliScalar P) :
      Measurement.IsProjective (evaluated point) := by
    apply placedMeasurement_isProjective
    rw [w.marginalPoly_postprocess_eval]
    exact SandwichProduct.postprocess_isProjective
      (w.Smeas .bob) (w.projective .bob) (evalAt W point)
  have hAgreement :
      opFamilyDistSq (uniformDistribution (Fin P.m → PauliScalar P))
          (fun point answer => (evaluated point).effect answer)
          (fun point answer => (comparison point).effect answer) S.psiHat ≤
        2 * consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
          (fun point answer => (evaluated point).effect answer)
          (fun point answer => (comparison point).effect answer) S.psiHat :=
    opFamilyDistSq_le_two_mul_consistencyDefect
      (X := Fin P.m → PauliScalar P) (α := PauliScalar P)
      (ι := SixReg P S.toStrategy.ιA S.toStrategy.ιB)
      (uniformDistribution (Fin P.m → PauliScalar P)) evaluated comparison S.psiHat
  have hConsistency :
      consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
          (fun point answer => (evaluated point).effect answer)
          (fun point answer => (comparison point).effect answer) S.psiHat ≤ deltaG := by
    simpa only [evaluated, comparison, placedMeasurement_effect] using
      marginalPoly_pointMeas_consistent_bob_reversed w W
  have hDistance : opFamilyDistSq
      (uniformDistribution (Fin P.m → PauliScalar P))
      (fun point answer => (evaluated point).effect answer)
      (fun point answer => S.place .AA'
        ((S.pointMeasExp .alice W point).effect answer)) S.psiHat ≤ 2 * deltaG := by
    simpa only [comparison, placedMeasurement_effect] using
      hAgreement.trans (mul_le_mul_of_nonneg_left hConsistency (by norm_num))
  have hSum := opDistSq_sum_sub_mul_le_of_projective
    (uniformDistribution (Fin P.m → PauliScalar P)) evaluated
    (fun point answer => S.place .AA'
      ((S.pointMeasExp .alice W point).effect answer)) S.psiHat (2 * deltaG)
    hProjective hDistance Finset.univ
  simp only [MIPStarRE.Quantum.Measurement.sum_eq_one] at hSum
  simp only [evaluated, placedMeasurement_effect] at hSum
  have hRegroup (point : Fin P.m → PauliScalar P) :
      (∑ answer : PauliScalar P, S.place .BA''
        (((w.marginalPoly .bob W).postprocess
          (fun poly => MvPolynomial.eval point poly.1)).effect answer) *
          S.place .AA' ((S.pointMeasExp .alice W point).effect answer)) =
        ∑ poly : Poly P, S.place .BA''
          ((w.marginalPoly .bob W).effect poly) *
            S.place .AA' ((S.pointMeasExp .alice W point).effect
              (MvPolynomial.eval point poly.1)) :=
    sum_marginalPoly_eval_mul w .BA'' W point
      (fun answer => S.place .AA' ((S.pointMeasExp .alice W point).effect answer))
  simp only [hRegroup] at hSum
  rw [opDistSq, opFamilyDistSq_symm] at hSum
  exact hSum

/-- The polynomial marginal and the opposite player's expanded point
measurement resolve the identity on average. Quantification over the directed
opposite-placement relation gives all four instances of the source's
symmetric-equivalents clause.

This is Equation `eq:qld-sg-cons` of
blueprint
`lem:qld-constructing-the-paulis-helper`, paper
`14_analysis_of_the_pauli_basis_test.tex:1609-1635`.

The source absorbs constant factors and the game error into `deltaS`. Here
`deltaG` is the global polynomial-pair witness error, and
`deltaConstructPaulis` records that enlargement explicitly.

The direct placements use the witness fields themselves. The two remaining
directions follow by transporting the same correlations between the two EPR
pairs and, for the Bob-first ordering, reversing two Hermitian factors inside
the real quadratic form. -/
theorem sum_marginalPoly_pointMeas_approx_id :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (epsilon deltaG : ℝ),
        0 ≤ epsilon → epsilon ≤ 1 → 0 ≤ deltaG →
          ∀ (S : ProjectiveSetting P epsilon)
            (w : GlobalPairWitness S deltaG) (W : PauliKind)
            (p₁ p₂ : Placement), p₁.IsOpposite p₂ →
              opDistSq (uniformDistribution (Fin P.m → PauliScalar P))
                (fun u => ∑ g : Poly P,
                  S.place p₁ ((w.marginalPoly p₁.side W).effect g) *
                    S.place p₂ ((S.pointMeasExp p₂.side W u).effect
                      (MvPolynomial.eval u g.1)))
                (fun _ => 1) S.psiHat ≤
                  deltaConstructPaulis C epsilon deltaG P.m P.d P.q := by
  refine ⟨2, by norm_num, ?_⟩
  intro P epsilon deltaG _ _ _ S w W p₁ p₂ hopp
  have hbase :
      opDistSq (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u => ∑ g : Poly P,
          S.place p₁ ((w.marginalPoly p₁.side W).effect g) *
            S.place p₂ ((S.pointMeasExp p₂.side W u).effect
              (MvPolynomial.eval u g.1)))
        (fun _ => 1) S.psiHat ≤ 2 * deltaG := by
    cases p₁ <;> cases p₂ <;> simp only [Placement.IsOpposite] at hopp
    · simpa only [Placement.side] using
        sum_marginalPoly_pointMeas_approx_id_alice w W
    · simpa only [Placement.side] using
        sum_marginalPoly_pointMeas_approx_id_bob_reversed w W
    · simpa only [Placement.side] using
        sum_marginalPoly_pointMeas_approx_id_bob w W
    · simpa only [Placement.side] using
        sum_marginalPoly_pointMeas_approx_id_alice_reversed w W
  refine hbase.trans ?_
  unfold deltaConstructPaulis
  have hsqrt : 0 ≤ Real.sqrt epsilon := Real.sqrt_nonneg epsilon
  have hratio : 0 ≤ ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ) := by positivity
  nlinarith

/-- Each polynomial marginal effect absorbs the fiber of its own coarse
graining at the evaluated answer. Projectivity of the placed marginal reduces
the fiber sum to the single matching polynomial outcome. This is the
coarse-graining step in the proof of blueprint
`lem:qld-constructing-the-paulis-helper`, paper
`14_analysis_of_the_pauli_basis_test.tex:1637-1646`. -/
private theorem place_marginalPoly_mul_postprocess_effect
    {P : AdmissibleParams} {epsilon deltaG : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S deltaG)
    (p : Placement) (W : PauliKind) (u : Fin P.m → PauliScalar P)
    (g : Poly P) :
    S.place p ((w.marginalPoly p.side W).effect g) *
        S.place p (((w.marginalPoly p.side W).postprocess
          (fun poly => MvPolynomial.eval u poly.1)).effect
            (MvPolynomial.eval u g.1)) =
      S.place p ((w.marginalPoly p.side W).effect g) := by
  classical
  have hproj : Measurement.IsProjective
      (placedMeasurement S p (w.marginalPoly p.side W)) :=
    placedMeasurement_isProjective S p _ (w.marginalPoly_isProjective p.side W)
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect, place_finsetSum,
    Finset.mul_sum]
  rw [Finset.sum_eq_single g]
  · simpa only [placedMeasurement_effect] using (hproj g).isIdempotentElem.eq
  · intro other _ hother
    simpa only [placedMeasurement_effect] using
      projective_effect_mul_effect_eq_zero _ hproj hother.symm
  · intro hg
    exact (hg (Finset.mem_filter.mpr ⟨Finset.mem_univ g, rfl⟩)).elim

/-- The coarse-grained polynomial marginal at one placement stays consistent
with the expanded point measurement at the opposite placement. Quantification
over the directed opposite-placement relation gives all four instances of the
source's symmetric-equivalents clause.

This is the coarse-grained point-consistency input of blueprint
`lem:qld-constructing-the-paulis-helper`, paper
`14_analysis_of_the_pauli_basis_test.tex:1626-1637`. -/
private theorem marginalPoly_pointMeas_consistent_opposite
    {P : AdmissibleParams} {epsilon deltaG : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S deltaG)
    (W : PauliKind) (p q : Placement) (hopp : p.IsOpposite q) :
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
      (fun point answer => S.place p
        (((w.marginalPoly p.side W).postprocess
          (fun poly => MvPolynomial.eval point poly.1)).effect answer))
      (fun point answer => S.place q
        ((S.pointMeasExp q.side W point).effect answer)) S.psiHat ≤ deltaG := by
  cases p <;> cases q <;> simp only [Placement.IsOpposite] at hopp
  · exact marginalPoly_pointMeas_consistent_alice w W
  · exact marginalPoly_pointMeas_consistent_bob_reversed w W
  · exact marginalPoly_pointMeas_consistent_bob w W
  · exact marginalPoly_pointMeas_consistent_alice_reversed w W

/-- The agreement estimate between the coarse-grained polynomial marginal and
the opposite placement's expanded point measurement, on every directed
opposite-placement pair. The factor two makes blueprint `fact:agreement`
explicit; paper `14_analysis_of_the_pauli_basis_test.tex:1626-1637`. -/
private theorem marginalPoly_pointMeas_approx_opposite
    {P : AdmissibleParams} {epsilon deltaG : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S deltaG)
    (W : PauliKind) (p q : Placement) (hopp : p.IsOpposite q) :
    opFamilyDistSq (uniformDistribution (Fin P.m → PauliScalar P))
      (fun point answer => S.place p
        (((w.marginalPoly p.side W).postprocess
          (fun poly => MvPolynomial.eval point poly.1)).effect answer))
      (fun point answer => S.place q
        ((S.pointMeasExp q.side W point).effect answer)) S.psiHat ≤
        2 * deltaG := by
  have hAgreement := opFamilyDistSq_le_two_mul_consistencyDefect
    (uniformDistribution (Fin P.m → PauliScalar P))
    (fun point => placedMeasurement S p
      ((w.marginalPoly p.side W).postprocess
        (fun poly => MvPolynomial.eval point poly.1)))
    (fun point => placedMeasurement S q (S.pointMeasExp q.side W point))
    S.psiHat
  simp only [placedMeasurement_effect] at hAgreement
  exact hAgreement.trans (mul_le_mul_of_nonneg_left
    (marginalPoly_pointMeas_consistent_opposite w W p q hopp) (by norm_num))

/-- Each polynomial marginal annihilates the complement of the corresponding
same-side expanded point effect on average. The answer summation is over the
polynomial outcome, and quantification over `Placement` gives all four
single-party symmetric equivalents.

This is Equation `eq:qld-sg-cons2` of
blueprint
`lem:qld-constructing-the-paulis-helper`, paper
`14_analysis_of_the_pauli_basis_test.tex:1617-1662`.

The explicit `deltaConstructPaulis` bound retains the point-measurement error
which the source absorbs into its adjusted `deltaS`.

The source's three steps are followed exactly. The coarse-grained marginal
agrees with the opposite placement's expanded point measurement at scale
`2 * deltaG`; moving that point measurement onto the marginal's own registers
costs the self-consistency error of `lem:qld-comm-cons`; and the left
projective marginal factor is absorbed by blueprint `fact:add-a-proj2`, using
that a marginal effect is fixed by the fiber of its own coarse graining. -/
theorem marginalPoly_sub_pointMeas_approx_zero :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (epsilon deltaG : ℝ),
        0 ≤ epsilon → epsilon ≤ 1 → 0 ≤ deltaG →
          ∀ (S : ProjectiveSetting P epsilon)
            (w : GlobalPairWitness S deltaG) (W : PauliKind) (p : Placement),
            opFamilyDistSq (uniformDistribution (Fin P.m → PauliScalar P))
              (fun u g =>
                S.place p ((w.marginalPoly p.side W).effect g) *
                  (1 - S.place p ((S.pointMeasExp p.side W u).effect
                    (MvPolynomial.eval u g.1))))
              (fun _ _ => 0) S.psiHat ≤
                deltaConstructPaulis C epsilon deltaG P.m P.d P.q := by
  classical
  obtain ⟨C₀, hC₀one, hC₀⟩ := expPoint_self_cons
  refine ⟨4 + 2 * C₀, by linarith, ?_⟩
  intro P epsilon deltaG hepsilon0 hepsilon1 hdeltaG S w W p
  obtain ⟨q, hopp⟩ : ∃ q : Placement, p.IsOpposite q := by
    cases p
    · exact ⟨.BA'', trivial⟩
    · exact ⟨.AA', trivial⟩
    · exact ⟨.AB'', trivial⟩
    · exact ⟨.BB', trivial⟩
  have hpoint : opFamilyDistSq (uniformDistribution (Fin P.m → PauliScalar P))
      (fun u a => S.place q ((S.pointMeasExp q.side W u).effect a))
      (fun u a => S.place p ((S.pointMeasExp p.side W u).effect a))
      S.psiHat ≤ C₀ * epsilon := by
    rw [opFamilyDistSq_symm]
    exact hC₀ P epsilon S p q hopp W
  have hsame : opFamilyDistSq (uniformDistribution (Fin P.m → PauliScalar P))
      (fun point answer => S.place p
        (((w.marginalPoly p.side W).postprocess
          (fun poly => MvPolynomial.eval point poly.1)).effect answer))
      (fun u a => S.place p ((S.pointMeasExp p.side W u).effect a))
      S.psiHat ≤ 2 * (2 * deltaG) + 2 * (C₀ * epsilon) :=
    opFamilyDistSq_le_of_le_of_le _ _ _ _ _ _ _
      (marginalPoly_pointMeas_approx_opposite w W p q hopp) hpoint
  have hproj : Measurement.IsProjective
      (placedMeasurement S p (w.marginalPoly p.side W)) :=
    placedMeasurement_isProjective S p _ (w.marginalPoly_isProjective p.side W)
  have hterm : ∀ g : Poly P,
      (S.place p ((w.marginalPoly p.side W).effect g))ᴴ *
          S.place p ((w.marginalPoly p.side W).effect g) =
        S.place p ((w.marginalPoly p.side W).effect g) := by
    intro g
    have hhermitian : (S.place p ((w.marginalPoly p.side W).effect g))ᴴ =
        S.place p ((w.marginalPoly p.side W).effect g) := by
      simpa only [placedMeasurement_effect] using
        (hproj g).isSelfAdjoint.isHermitian.eq
    rw [hhermitian]
    simpa only [placedMeasurement_effect] using (hproj g).isIdempotentElem.eq
  have hcontract : ∀ _u : Fin P.m → PauliScalar P,
      (1 - ∑ g : Poly P,
        (S.place p ((w.marginalPoly p.side W).effect g))ᴴ *
          S.place p ((w.marginalPoly p.side W).effect g)).PosSemidef := by
    intro _u
    have hsum : ∑ g : Poly P,
        S.place p ((w.marginalPoly p.side W).effect g) = 1 := by
      simpa only [placedMeasurement_effect] using
        (placedMeasurement S p (w.marginalPoly p.side W)).sum_eq_one
    simp only [hterm, hsum, sub_self]
    exact Matrix.PosSemidef.zero
  have habsorb := opFamilyDistSq_mul_funIndexed_le
    (uniformDistribution (Fin P.m → PauliScalar P))
    (fun u => placedMeasurement S p ((w.marginalPoly p.side W).postprocess
      (fun poly => MvPolynomial.eval u poly.1)))
    (fun u => placedMeasurement S p (S.pointMeasExp p.side W u))
    (fun (g : Poly P) (u : Fin P.m → PauliScalar P) => MvPolynomial.eval u g.1)
    (fun (_u : Fin P.m → PauliScalar P) (g : Poly P) =>
      S.place p ((w.marginalPoly p.side W).effect g))
    S.psiHat (2 * (2 * deltaG) + 2 * (C₀ * epsilon)) hcontract
    (by simpa only [placedMeasurement_effect] using hsame)
  simp only [placedMeasurement_effect,
    place_marginalPoly_mul_postprocess_effect w p W] at habsorb
  refine le_trans (le_of_eq ?_) (habsorb.trans ?_)
  · unfold opFamilyDistSq
    apply avgOver_congr
    intro u
    apply Finset.sum_congr rfl
    intro g _
    simp only [sub_zero, mul_sub, mul_one]
  · unfold deltaConstructPaulis
    have hsqrtnonneg : 0 ≤ Real.sqrt epsilon := Real.sqrt_nonneg epsilon
    have hsqrtle : Real.sqrt epsilon ≤ 1 := by
      simpa using Real.sqrt_le_sqrt hepsilon1
    have hsquare : Real.sqrt epsilon * Real.sqrt epsilon = epsilon :=
      Real.mul_self_sqrt hepsilon0
    have hepsle : epsilon ≤ Real.sqrt epsilon := by
      nlinarith [mul_nonneg hsqrtnonneg (sub_nonneg.2 hsqrtle)]
    have hratio : 0 ≤ ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ) := by positivity
    have hC₀pos : (0 : ℝ) < C₀ := lt_of_lt_of_le zero_lt_one hC₀one
    nlinarith [mul_nonneg hC₀pos.le hdeltaG,
      mul_nonneg hC₀pos.le (sub_nonneg.2 hepsle),
      mul_nonneg hC₀pos.le hratio]

/-! ## Non-encoding support -/

/-- The state-dependent mass assigned by a side's polynomial marginal to
outcomes outside the low-degree encoding image.  The finite support filter is
written explicitly so the restricted decoder identity is never applied to an
arbitrary polynomial representative.

This is the left-hand side of blueprint
`eq:qld-nonencoding-mass`, from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1458-1602`.
The bound remains a proposition-valued proof obligation, as required by
`docs/paper-gaps/qpbt_decoding-identity.tex:87-123`. -/
noncomputable def nonencodingMarginalMass {P : AdmissibleParams}
    {epsilon deltaS : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S deltaS) (side : PlayerSide) (W : PauliKind) : ℝ := by
  classical
  exact ∑ g ∈ Finset.univ.filter (fun g : Poly P => ¬ IsEncoding g),
    (inner ℂ S.psiHat
      (applyOperatorToState
        (S.placeSide side
          (heteroKron ((w.marginalPoly side W).effect g)
            (1 : Op (PauliRegister P))))
        S.psiHat)).re

/-- The non-encoding support estimate required by the Chapter 16 extraction
argument. For either player side and either Pauli basis, the marginal mass on
polynomial representatives outside the encoding image is bounded by the
common construction error.

This is the named obligation for blueprint
`eq:qld-nonencoding-mass`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1458-1602`.
The estimate is intentionally not folded into a decoder identity; its proof
must use the point-consistency hypotheses and Schwartz--Zippel. See
`docs/paper-gaps/qpbt_decoding-identity.tex:87-123`.

**Proof obligation:** issue #47 tracks this support estimate. -/
theorem nonencodingMarginalMass_le :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (epsilon deltaG : ℝ),
        0 ≤ epsilon → epsilon ≤ 1 → 0 ≤ deltaG →
          ∀ (S : ProjectiveSetting P epsilon)
            (w : GlobalPairWitness S deltaG)
            (side : PlayerSide) (W : PauliKind),
            nonencodingMarginalMass w side W ≤
              deltaConstructPaulis C epsilon deltaG P.m P.d P.q := by
  sorry

end

end MIPStarRE.QPBT
