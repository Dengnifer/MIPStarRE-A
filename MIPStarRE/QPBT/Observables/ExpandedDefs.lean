import MIPStarRE.QPBT.Algebra.PauliTheorems
import MIPStarRE.QPBT.Observables.Defs

/-!
# Expanded registers and point measurements

This module adjoins two EPR pairs to a heterogeneous Pauli-basis-test strategy,
records the four register placements used in the analysis, and defines the
expanded point observables and measurements.

## References

The constructions formalize `def:expanded-state`, `def:expanded-observables`,
`def:expanded-point-measurement`, and `def:expanded-point-trace-projection` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:760-874`. Their paper source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:367-418`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-- The six registers `AA'A''BB'B''`, retaining distinct Alice and Bob local
spaces. This is the register index type of `def:expanded-state`, paper
`14_analysis_of_the_pauli_basis_test.tex:367-372`, blueprint
`ch14_qpbt_observables.tex:760-781`. -/
abbrev SixReg (P : AdmissibleParams) (ιA ιB : Type*) :=
  (ιA × (PauliRegister P × PauliRegister P)) ×
    (ιB × (PauliRegister P × PauliRegister P))

/-- Equality of six-register indices is decidable because the index set is
finite. This is the index set of `def:expanded-state`; blueprint
`ch14_qpbt_observables.tex:760-781`. -/
noncomputable instance sixRegDecidableEq (P : AdmissibleParams)
    (ιA ιB : Type*) : DecidableEq (SixReg P ιA ιB) :=
  Classical.decEq _

/-- Reassociate the tensor product of the strategy state and two EPR states
directly into register order `AA'A''BB'B''` for
`eq:def-psihat`, paper `14_analysis_of_the_pauli_basis_test.tex:367-372`. -/
def sixRegShuffle (P : AdmissibleParams) (ιA ιB : Type*) :
    (((ιA × ιB) × (PauliRegister P × PauliRegister P)) ×
        (PauliRegister P × PauliRegister P)) ≃ SixReg P ιA ιB where
  toFun p := ((p.1.1.1, (p.1.2.1, p.1.2.2)),
    (p.1.1.2, (p.2.1, p.2.2)))
  invFun p := (((p.1.1, p.2.1), (p.1.2.1, p.1.2.2)),
    (p.2.2.1, p.2.2.2))
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

/-- The four placements `AA'`, `BA''`, `BB'`, and `AB''` used explicitly in
the chapter-14 consistency statements. Paper
`14_analysis_of_the_pauli_basis_test.tex:420-450`; blueprint
`ch14_qpbt_observables.tex:876-922`. -/
inductive Placement where
  | AA'
  | BA''
  | BB'
  | AB''
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The strategy-player side supplying the local Hilbert space in each of the
four register placements at paper
`14_analysis_of_the_pauli_basis_test.tex:420-450`. -/
def Placement.side : Placement → PlayerSide
  | .AA' => .alice
  | .BA'' => .bob
  | .BB' => .bob
  | .AB'' => .alice

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

/-- A strategy-local register paired with one generalized-Pauli register. This
is the operator space in `def:expanded-observables`, paper
`14_analysis_of_the_pauli_basis_test.tex:374-382`. -/
abbrev ExpandedLocalSpace (S : ProjectiveSetting P ε) (side : PlayerSide) :=
  S.LocalSpace side × PauliRegister P

/-- The strategy state tensored with EPR states on `A'A''` and `B'B''`, in the
six-register order. This is `eq:def-psihat`, paper
`14_analysis_of_the_pauli_basis_test.tex:367-372`, blueprint
`ch14_qpbt_observables.tex:760-781`. -/
noncomputable def psiHat (S : ProjectiveSetting P ε) :
    EuclideanSpace ℂ (SixReg P S.toStrategy.ιA S.toStrategy.ιB) := by
  classical
  exact
    reindexState (sixRegShuffle P S.toStrategy.ιA S.toStrategy.ιB)
      (vecTensor
        (vecTensor S.toStrategy.ψ (eprState (PauliRegister P)))
        (eprState (PauliRegister P)))

/-- Place an operator on one of `AA'`, `BA''`, `BB'`, or `AB''`, with the
identity on all remaining registers. The input local space is determined by
the placement, so no equality between the player spaces is assumed. Paper
`14_analysis_of_the_pauli_basis_test.tex:420-450`; blueprint
`ch14_qpbt_observables.tex:876-922`. -/
noncomputable def place (S : ProjectiveSetting P ε) (p : Placement)
    (O : Op (S.ExpandedLocalSpace p.side)) :
    Op (SixReg P S.toStrategy.ιA S.toStrategy.ιB) :=
  fun i j =>
    match p with
    | .AA' =>
        O (i.1.1, i.1.2.1) (j.1.1, j.1.2.1) *
          (1 : Op (PauliRegister P)) i.1.2.2 j.1.2.2 *
          (1 : Op S.toStrategy.ιB) i.2.1 j.2.1 *
          (1 : Op (PauliRegister P)) i.2.2.1 j.2.2.1 *
          (1 : Op (PauliRegister P)) i.2.2.2 j.2.2.2
    | .BA'' =>
        (1 : Op S.toStrategy.ιA) i.1.1 j.1.1 *
          (1 : Op (PauliRegister P)) i.1.2.1 j.1.2.1 *
          O (i.2.1, i.1.2.2) (j.2.1, j.1.2.2) *
          (1 : Op (PauliRegister P)) i.2.2.1 j.2.2.1 *
          (1 : Op (PauliRegister P)) i.2.2.2 j.2.2.2
    | .BB' =>
        (1 : Op S.toStrategy.ιA) i.1.1 j.1.1 *
          (1 : Op (PauliRegister P)) i.1.2.1 j.1.2.1 *
          (1 : Op (PauliRegister P)) i.1.2.2 j.1.2.2 *
          O (i.2.1, i.2.2.1) (j.2.1, j.2.2.1) *
          (1 : Op (PauliRegister P)) i.2.2.2 j.2.2.2
    | .AB'' =>
        O (i.1.1, i.2.2.2) (j.1.1, j.2.2.2) *
          (1 : Op (PauliRegister P)) i.1.2.1 j.1.2.1 *
          (1 : Op (PauliRegister P)) i.1.2.2 j.1.2.2 *
          (1 : Op S.toStrategy.ιB) i.2.1 j.2.1 *
          (1 : Op (PauliRegister P)) i.2.2.1 j.2.2.1

/-- The expanded observable
`W^r(u) tensor tau^W(r * ind_m(u))` on a selected player side. This is
Equation `eq:lc-23`, paper `14_analysis_of_the_pauli_basis_test.tex:374-382`,
blueprint `ch14_qpbt_observables.tex:783-807`. -/
noncomputable def expObs (S : ProjectiveSetting P ε) (side : PlayerSide)
    (W : PauliKind) (r : PauliScalar P) (u : Fin P.m → PauliScalar P) :
    Op (S.ExpandedLocalSpace side) :=
  heteroKron (S.pointObs side W r u)
    (tauObservable W (fun h => r * indicatorVec u h))

/-- The Fourier average defining the expanded point effect. This is the first
display of `def:expanded-point-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:384-418`, blueprint
`ch14_qpbt_observables.tex:809-844`. -/
noncomputable def expPointOp (S : ProjectiveSetting P ε) (side : PlayerSide)
    (W : PauliKind) (u : Fin P.m → PauliScalar P) (a : PauliScalar P) :
    Op (S.ExpandedLocalSpace side) :=
  averageOperatorOverDistribution (uniformDistribution (PauliScalar P)) fun r =>
    phaseSign (fixedBinTrace P.model (a * r)) • S.expObs side W r u

/-- The Pauli-register projector onto labels whose low-degree encoding has
value `a` at `u`. This is Equation `eq:qld-point-obs-def`, paper
`14_analysis_of_the_pauli_basis_test.tex:389-394`, blueprint
`ch14_qpbt_observables.tex:809-844`. -/
noncomputable def tauPointProj (W : PauliKind)
    (u : Fin P.m → PauliScalar P) (a : PauliScalar P) : Op (PauliRegister P) :=
  ∑ h ∈ Finset.univ.filter (fun h : PauliRegister P =>
      dotProduct h (indicatorVec u) = a),
    pauliProj W h

/-- Expanded point effects are positive semidefinite. This is the positivity
obligation in `def:expanded-point-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:384-418`. -/
theorem expPointOp_nonneg (S : ProjectiveSetting P ε) (side : PlayerSide)
    (W : PauliKind) (u : Fin P.m → PauliScalar P) (a : PauliScalar P) :
    0 ≤ S.expPointOp side W u a := by
  sorry

/-- Expanded point effects sum to the identity. This is the completeness
obligation in `def:expanded-point-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:384-418`. -/
theorem expPointOp_sum_eq_one (S : ProjectiveSetting P ε) (side : PlayerSide)
    (W : PauliKind) (u : Fin P.m → PauliScalar P) :
    ∑ a, S.expPointOp side W u a = 1 := by
  sorry

/-- The complete expanded point measurement on the chosen player and Pauli
register. Its effects are those of `def:expanded-point-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:384-418`, blueprint
`ch14_qpbt_observables.tex:809-844`. -/
noncomputable def pointMeasExp (S : ProjectiveSetting P ε) (side : PlayerSide)
    (W : PauliKind) (u : Fin P.m → PauliScalar P) :
    Measurement (PauliScalar P) (S.ExpandedLocalSpace side) :=
  Measurement.ofSumEqOne (S.expPointOp side W u)
    (S.expPointOp_nonneg side W u) (S.expPointOp_sum_eq_one side W u)

/-- The expanded point effect is the convolution of the strategy point
measurement and the Pauli-register point projection. This is the final display
of `def:expanded-point-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:395-418`. -/
theorem expPointOp_eq_convolution (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (u : Fin P.m → PauliScalar P)
    (a : PauliScalar P) :
    S.expPointOp side W u a =
      ∑ p ∈ Finset.univ.filter (fun p : PauliScalar P × PauliScalar P =>
          p.1 + p.2 = a),
        heteroKron ((S.pointMeas side W u).effect p.1)
          (tauPointProj W u p.2) := by
  sorry

/-- The expanded point measurement is projective, as asserted after the
convolution formula in `def:expanded-point-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:395-418`. -/
theorem pointMeasExp_isProjective (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (u : Fin P.m → PauliScalar P) :
    MIPStarRE.QPBT.Measurement.IsProjective (S.pointMeasExp side W u) := by
  sorry

/-- Trace-coarse-graining of the expanded point measurement. This is Equation
`eq:qld-def-mptur`, paper `14_analysis_of_the_pauli_basis_test.tex:411-418`,
blueprint `ch14_qpbt_observables.tex:846-874`. -/
noncomputable def expPointTrace (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (u : Fin P.m → PauliScalar P)
    (r : PauliScalar P) : Measurement (ZMod 2) (S.ExpandedLocalSpace side) :=
  (S.pointMeasExp side W u).postprocess fun a => fixedBinTrace P.model (a * r)

/-- Fourier inversion writes a trace-coarse-grained point effect as one half
of the identity plus its signed expanded observable. This is Equation
`eq:lc-22`, paper `14_analysis_of_the_pauli_basis_test.tex:411-418`, blueprint
`ch14_qpbt_observables.tex:846-874`. -/
theorem expPointTrace_eq_half_add (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (u : Fin P.m → PauliScalar P)
    (r : PauliScalar P) (b : ZMod 2) :
    (S.expPointTrace side W u r).effect b =
      (2 : ℂ)⁻¹ •
        (1 + phaseSign b • S.expObs side W r u) := by
  sorry

end ProjectiveSetting

end

end MIPStarRE.QPBT
