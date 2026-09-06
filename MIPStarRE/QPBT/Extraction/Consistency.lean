import MIPStarRE.QPBT.Extraction.Observables

/-!
# Consistency of the pulled-apart Pauli measurements

This module records the two estimates by which the polynomial marginals absorb
the expanded point measurements, with all heterogeneous placements written
explicitly. It also states the consistency of the pulled-apart
measurements with the original point measurements and the self-consistency of
the corresponding observables.

The direct `AA'`--`BA''` and `BB'`--`AB''` marginal agreement estimates are
proved from the given global polynomial-pair witness. The conclusions
quantified over all placements remain separate proof obligations.

## References

The marginal estimates formalize blueprint
`lem:qld-constructing-the-paulis-helper`, from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1609-1664`.
The remaining declarations formalize blueprint `lem:qld-construct-the-paulis`,
from paper lines 1458-1608.
-/

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

/-! ## Absorption of expanded point measurements -/

section PlacementMeasurements

open scoped Classical

/-- The original-player register not acted on by a placement. This only
indexes the identity factors in the definition of `ProjectiveSetting.place`. -/
private def complementSide : Placement → PlayerSide
  | .AA' | .AB'' => .bob
  | .BA'' | .BB' => .alice

/-- Separate the two acted-on registers from the four identity registers.
This is a coordinate decomposition of the placements in paper
`14_analysis_of_the_pauli_basis_test.tex:420-450`, not a transfer of operators
between registers in the expanded state. -/
private def placementEquiv {P : AdmissibleParams} {epsilon : ℝ}
    (S : ProjectiveSetting P epsilon) (placement : Placement) :
    SixReg P S.toStrategy.ιA S.toStrategy.ιB ≃
      (S.ExpandedLocalSpace placement.side ×
        (S.LocalSpace (complementSide placement) ×
          (PauliRegister P × (PauliRegister P × PauliRegister P)))) := by
  cases placement
  · exact
      { toFun := fun index => ((index.1.1, index.1.2.1),
          (index.2.1, (index.1.2.2, (index.2.2.1, index.2.2.2))))
        invFun := fun index => ((index.1.1, (index.1.2, index.2.2.1)),
          (index.2.1, (index.2.2.2.1, index.2.2.2.2)))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  · exact
      { toFun := fun index => ((index.2.1, index.1.2.2),
          (index.1.1, (index.1.2.1, (index.2.2.1, index.2.2.2))))
        invFun := fun index => ((index.2.1, (index.2.2.1, index.1.2)),
          (index.1.1, (index.2.2.2.1, index.2.2.2.2)))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  · exact
      { toFun := fun index => ((index.2.1, index.2.2.1),
          (index.1.1, (index.1.2.1, (index.1.2.2, index.2.2.2))))
        invFun := fun index => ((index.2.1, (index.2.2.1, index.2.2.2.1)),
          (index.1.1, (index.1.2, index.2.2.2.2)))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  · exact
      { toFun := fun index => ((index.1.1, index.2.2.2),
          (index.2.1, (index.1.2.1, (index.1.2.2, index.2.2.1))))
        invFun := fun index => ((index.1.1, (index.2.2.1, index.2.2.2.1)),
          (index.2.1, (index.2.2.2.2, index.1.2)))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }

/-- The entrywise placement agrees with tensoring by the identity and changing
coordinates. No invariance property of the expanded state enters this equality. -/
private theorem place_eq_reindex {P : AdmissibleParams} {epsilon : ℝ}
    (S : ProjectiveSetting P epsilon) (placement : Placement)
    (operator : Op (S.ExpandedLocalSpace placement.side)) :
    S.place placement operator =
      reindexOp (placementEquiv S placement) (heteroKron operator 1) := by
  cases placement <;> ext row col <;>
    simp [ProjectiveSetting.place, placementEquiv, reindexOp, heteroKron,
      Matrix.kronecker, Matrix.one_apply, Prod.ext_iff, ite_and, mul_ite, ite_mul] <;>
    split_ifs <;> simp_all

/-- Tensoring a measurement with the identity and reindexing gives its
six-register placement, with completeness and positivity retained. This is
finite-dimensional support for blueprint `lem:qld-constructing-the-paulis-helper`. -/
private noncomputable def placedMeasurement {P : AdmissibleParams} {epsilon : ℝ}
    {Outcome : Type*} [Fintype Outcome] (S : ProjectiveSetting P epsilon)
    (placement : Placement) (measurement : Measurement Outcome
      (S.ExpandedLocalSpace placement.side)) :
    Measurement Outcome (SixReg P S.toStrategy.ιA S.toStrategy.ιB) :=
  reindexMeasurement (placementEquiv S placement) (leftPlacedMeasurement measurement)

/-- The transported POVM has exactly the effects in the entrywise placement. -/
private theorem placedMeasurement_effect {P : AdmissibleParams} {epsilon : ℝ}
    {Outcome : Type*} [Fintype Outcome] (S : ProjectiveSetting P epsilon)
    (placement : Placement) (measurement : Measurement Outcome
      (S.ExpandedLocalSpace placement.side)) (answer : Outcome) :
    (placedMeasurement S placement measurement).effect answer =
      S.place placement (measurement.effect answer) :=
  (place_eq_reindex S placement (measurement.effect answer)).symm

/-- Tensoring with an identity and changing finite coordinates preserve
projectivity, as needed to apply `lem:cool-closeness-fact` to a placed POVM. -/
private theorem placedMeasurement_isProjective {P : AdmissibleParams} {epsilon : ℝ}
    {Outcome : Type*} [Fintype Outcome] (S : ProjectiveSetting P epsilon)
    (placement : Placement) (measurement : Measurement Outcome
      (S.ExpandedLocalSpace placement.side))
    (projective : MIPStarRE.QPBT.Measurement.IsProjective measurement) :
    MIPStarRE.QPBT.Measurement.IsProjective (placedMeasurement S placement measurement) := by
  letI : Fintype (S.LocalSpace (complementSide placement) ×
      (PauliRegister P × (PauliRegister P × PauliRegister P))) := inferInstance
  apply reindexMeasurement_isProjective
  intro answer
  have hOne : IsProj (1 : Op (S.LocalSpace (complementSide placement) ×
      (PauliRegister P × (PauliRegister P × PauliRegister P)))) :=
    IsStarProjection.one (Op (S.LocalSpace (complementSide placement) ×
      (PauliRegister P × (PauliRegister P × PauliRegister P))))
  exact MIPStarRE.LDT.MakingMeasurementsProjective.isProj_kronecker
    (projective answer) hOne

end PlacementMeasurements

/-- The entrywise register placement commutes with a finite sum of effects. -/
private theorem place_finset_sum {P : AdmissibleParams} {epsilon : ℝ}
    {Index : Type*} (S : ProjectiveSetting P epsilon) (placement : Placement)
    (indices : Finset Index) (family : Index → Op (S.ExpandedLocalSpace placement.side)) :
    S.place placement (∑ index ∈ indices, family index) =
      ∑ index ∈ indices, S.place placement (family index) := by
  cases placement <;> ext row col <;>
    simp [ProjectiveSetting.place, Matrix.sum_apply, Finset.sum_mul, Finset.mul_sum]

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
  simp only [MIPStarRE.Quantum.Measurement.postprocess_effect, place_finset_sum,
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

The two direct placements are proved in
`sum_marginalPoly_pointMeas_approx_id_alice` and
`sum_marginalPoly_pointMeas_approx_id_bob`.

**Proof obligation:** issue #47 and the register-transfer work in issue #115
track the remaining two directed placements and the common error enlargement.
The independent direct-placement argument is recorded in the audit for issue #243. -/
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
  sorry

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

**Proof obligation:** issue #47 tracks the projection-contraction and expanded
point self-consistency calculation on every placement at paper lines
1637-1662. -/
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
  sorry

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

/-! ## Consistency of the pulled-apart measurements -/

/-- Alice's original point measurement is consistent with Bob's pulled-apart
measurement on average over uniformly random points. This is the first display
of Item 1 in blueprint
`lem:qld-construct-the-paulis`, paper
`14_analysis_of_the_pauli_basis_test.tex:1463-1492`.

The source reuses `deltaS` after absorbing the non-encoding and game-error
terms. The bound keeps the global polynomial-pair witness error `deltaG`
separate in `deltaConstructPaulis`.

**Proof obligation:** issue #47 tracks the non-encoding-mass estimate required
by the restricted decoder identity; see
`docs/paper-gaps/qpbt_decoding-identity.tex`. -/
theorem tildeM_consistent_pointMeas :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (epsilon deltaG : ℝ),
        0 ≤ epsilon → epsilon ≤ 1 → 0 ≤ deltaG →
          ∀ (S : ProjectiveSetting P epsilon)
            (w : GlobalPairWitness S deltaG) (W : PauliKind),
            consistencyDefect
              (uniformDistribution (Fin P.m → PauliScalar P))
              (fun u a =>
                S.placePlayer .alice ((S.pointMeas .alice W u).effect a))
              (fun u a => S.placeSide .bob
                (tildeM w .bob W (indicatorVec u) a))
              S.psiHat ≤
                deltaConstructPaulis C epsilon deltaG P.m P.d P.q := by
  sorry

/-- Alice's pulled-apart measurement is consistent with Bob's original point
measurement on average over uniformly random points. This is the
register-interchanged display of Item 1 in blueprint
`lem:qld-construct-the-paulis`, paper
`14_analysis_of_the_pauli_basis_test.tex:1463-1492`.

The conclusion uses the same explicit construction scale as the first player
ordering.

**Proof obligation:** issue #47 tracks the player-interchanged
non-encoding-mass argument. -/
theorem tildeM_consistent_pointMeas' :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (epsilon deltaG : ℝ),
        0 ≤ epsilon → epsilon ≤ 1 → 0 ≤ deltaG →
          ∀ (S : ProjectiveSetting P epsilon)
            (w : GlobalPairWitness S deltaG) (W : PauliKind),
            consistencyDefect
              (uniformDistribution (Fin P.m → PauliScalar P))
              (fun u a => S.placeSide .alice
                (tildeM w .alice W (indicatorVec u) a))
              (fun u a =>
                S.placePlayer .bob ((S.pointMeas .bob W u).effect a))
              S.psiHat ≤
                deltaConstructPaulis C epsilon deltaG P.m P.d P.q := by
  sorry

/-- The pulled-apart observables on Alice's and Bob's extraction blocks are
self-consistent on average over the uniformly random Pauli register. This is
Item 2 of blueprint
`lem:qld-construct-the-paulis`, paper
`14_analysis_of_the_pauli_basis_test.tex:1476-1605`.

The construction scale exposes the square-root game error and
Schwartz--Zippel loss that the source absorbs into `deltaS`.

**Proof obligation:** issue #47 tracks the pulling-consistency calculation and
the final trace postprocessing from measurements to observables. -/
theorem tildeObs_selfConsistent :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (epsilon deltaG : ℝ),
        0 ≤ epsilon → epsilon ≤ 1 → 0 ≤ deltaG →
          ∀ (S : ProjectiveSetting P epsilon)
            (w : GlobalPairWitness S deltaG) (W : PauliKind)
            (j : Fin P.model.basisDim),
            opDistSq (uniformDistribution (PauliRegister P))
              (fun u => S.placeSide .alice (tildeObs w .alice W u j))
              (fun u => S.placeSide .bob (tildeObs w .bob W u j))
              S.psiHat ≤
                deltaConstructPaulis C epsilon deltaG P.m P.d P.q := by
  sorry

end

end MIPStarRE.QPBT
