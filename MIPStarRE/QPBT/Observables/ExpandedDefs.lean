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

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum
open MIPStarRE.LDT.Preliminaries

noncomputable section

/-- The six registers `AA'A''BB'B''`, retaining distinct Alice and Bob local
spaces. This is the register index type of `def:expanded-state`, paper
`14_analysis_of_the_pauli_basis_test.tex:367-372`, blueprint
`ch14_qpbt_observables.tex:760-781`. -/
abbrev SixReg (P : AdmissibleParams) (ιA ιB : Type*) :=
  (ιA × (PauliRegister P × PauliRegister P)) ×
    (ιB × (PauliRegister P × PauliRegister P))

/-- Equality of six-register indices is supplied by classical decidability for
the register type. This is the index set of `def:expanded-state`; blueprint
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

/-- The point coarse-graining of the generalized Pauli projectors is symmetric.
This is the EPR-transport identity used for the perfect ancilla consistency in
item 1 of `lem:qld-comm-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:455-465`. -/
theorem tauPointProj_transpose (W : PauliKind)
    (u : Fin P.m → PauliScalar P) (a : PauliScalar P) :
    (tauPointProj W u a)ᵀ = tauPointProj W u a := by
  classical
  simp only [tauPointProj, Matrix.transpose_sum, pauliProj_transpose]

/-- Pauli point projectors belonging to distinct values are orthogonal, while
each projector is idempotent. This is the ancillary product calculation in
item 1 of `lem:qld-comm-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:455-465`. -/
theorem tauPointProj_mul_tauPointProj (W : PauliKind)
    (u : Fin P.m → PauliScalar P) (a b : PauliScalar P) :
    tauPointProj W u a * tauPointProj W u b =
      if a = b then tauPointProj W u a else 0 := by
  classical
  unfold tauPointProj
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  by_cases hab : a = b
  · subst b
    rw [if_pos rfl]
    apply Finset.sum_congr rfl
    intro e he
    rw [Finset.sum_eq_single e]
    · rw [pauliProj_mul_pauliProj, if_pos rfl]
    · intro f hf hfe
      rw [pauliProj_mul_pauliProj, if_neg hfe.symm]
    · exact fun h => (h he).elim
  · rw [if_neg hab]
    apply Finset.sum_eq_zero
    intro e he
    apply Finset.sum_eq_zero
    intro f hf
    rw [pauliProj_mul_pauliProj, if_neg]
    intro hef
    apply hab
    rw [← (Finset.mem_filter.mp he).2, ← (Finset.mem_filter.mp hf).2, hef]

/-- The phase induced by the fixed binary trace is an additive character. -/
private theorem fixedCharacter_add (x y : PauliScalar P) :
    phaseSign (fixedBinTrace P.model x) * phaseSign (fixedBinTrace P.model y) =
      phaseSign (fixedBinTrace P.model (x + y)) := by
  rw [fixedBinTrace, map_add, phaseSign_eq_ffChar,
    phaseSign_eq_ffChar, phaseSign_eq_ffChar]
  exact ((ZMod.stdAddChar (N := 2)).map_add_eq_mul _ _).symm

private theorem fixedCharacter_mul_add (x y r : PauliScalar P) :
    phaseSign (fixedBinTrace P.model (x * r)) *
        phaseSign (fixedBinTrace P.model (y * r)) =
      phaseSign (fixedBinTrace P.model ((x + y) * r)) := by
  rw [add_mul]
  exact fixedCharacter_add (x * r) (y * r)

/-- Orthogonality of the fixed trace character over the Pauli scalar field. -/
private theorem fixedCharacter_expect (c : PauliScalar P) :
    (𝔼 r : PauliScalar P, phaseSign (fixedBinTrace P.model (c * r))) =
      if c = 0 then (1 : ℂ) else 0 := by
  simpa only [fixedBinTrace, phaseSign_eq_ffChar,
    MIPStarRE.LDT.Preliminaries.ffChar_apply, mul_comm c] using
    (fourier_fact_scalar (p := 2) (F := PauliScalar P) c)

private theorem average_fixedCharacter_smul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : PauliScalar P) (A : Op ι) :
    averageOperatorOverDistribution (uniformDistribution (PauliScalar P))
        (fun r => phaseSign (fixedBinTrace P.model (c * r)) • A) =
      if c = 0 then A else 0 := by
  classical
  ext i j
  simp only [averageOperatorOverDistribution, uniformDistribution,
    Distribution.uniformOnFinset, Finset.mem_univ, if_true, Matrix.sum_apply,
    Matrix.smul_apply, Complex.real_smul]
  simp_rw [smul_eq_mul]
  rw [← Finset.mul_sum, ← Finset.sum_mul]
  have havg := fixedCharacter_expect (P := P) c
  rw [Fintype.expect_eq_sum_div_card] at havg
  have hcoeff :
      ((1 / (Fintype.card (PauliScalar P) : ℝ) : ℝ) : ℂ) *
          (∑ r : PauliScalar P,
            phaseSign (fixedBinTrace P.model (c * r))) =
        if c = 0 then (1 : ℂ) else 0 := by
    convert havg using 1
    all_goals (push_cast; ring)
  rw [Finset.card_univ, ← mul_assoc, hcoeff]
  by_cases hc : c = 0 <;> simp [hc]

/-- Averaging three fixed trace characters imposes the convolution constraint. -/
private theorem average_three_fixedCharacters_smul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a x y : PauliScalar P) (A : Op ι) :
    averageOperatorOverDistribution (uniformDistribution (PauliScalar P))
        (fun r => phaseSign (fixedBinTrace P.model (a * r)) •
          (phaseSign (fixedBinTrace P.model (x * r)) •
            (phaseSign (fixedBinTrace P.model (y * r)) • A))) =
      if x + y = a then A else 0 := by
  haveI : CharP (PauliScalar P) 2 :=
    (Algebra.charP_iff (ZMod 2) (PauliScalar P) 2).mp (ZMod.charP 2)
  have hzero : a + x + y = 0 ↔ x + y = a := by
    constructor
    · intro h
      exact (CharTwo.add_eq_zero.mp (by simpa only [add_assoc] using h)).symm
    · intro h
      rw [add_assoc]
      exact CharTwo.add_eq_zero.mpr h.symm
  calc
    averageOperatorOverDistribution (uniformDistribution (PauliScalar P))
        (fun r => phaseSign (fixedBinTrace P.model (a * r)) •
          (phaseSign (fixedBinTrace P.model (x * r)) •
            (phaseSign (fixedBinTrace P.model (y * r)) • A))) =
      averageOperatorOverDistribution (uniformDistribution (PauliScalar P))
        (fun r => phaseSign (fixedBinTrace P.model ((a + x + y) * r)) • A) := by
          apply averageOperatorOverDistribution_congr
          intro r
          rw [smul_smul, fixedCharacter_mul_add a x r, smul_smul,
            fixedCharacter_mul_add (a + x) y r]
    _ = if a + x + y = 0 then A else 0 :=
      average_fixedCharacter_smul (a + x + y) A
    _ = if x + y = a then A else 0 := if_congr hzero rfl rfl

private theorem dot_smul_indicator (r : PauliScalar P)
    (u : Fin P.m → PauliScalar P) (e : PauliRegister P) :
    dotProduct (fun h => r * indicatorVec u h) e =
      dotProduct e (indicatorVec u) * r := by
  simp only [dotProduct, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem heteroKron_sum_sum {α β ι κ : Type*}
    [Fintype α] [Fintype β] (A : α → Op ι) (B : β → Op κ) :
    heteroKron (∑ x, A x) (∑ y, B y) =
      ∑ x, ∑ y, heteroKron (A x) (B y) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  unfold heteroKron Matrix.kronecker Matrix.kroneckerMap
  simp only [Matrix.of_apply, Matrix.sum_apply]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mul_sum]

private theorem heteroKron_finset_sum_right {α ι κ : Type*}
    (A : Op ι) (s : Finset α) (B : α → Op κ) :
    heteroKron A (∑ y ∈ s, B y) = ∑ y ∈ s, heteroKron A (B y) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  unfold heteroKron Matrix.kronecker Matrix.kroneckerMap
  simp only [Matrix.of_apply, Matrix.sum_apply]
  rw [Finset.mul_sum]

private theorem heteroKron_smul_smul {ι κ : Type*}
    (c d : ℂ) (A : Op ι) (B : Op κ) :
    heteroKron (c • A) (d • B) = c • (d • heteroKron A B) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  change (c * A i j) * (d * B k l) = c * (d * (A i j * B k l))
  ring

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
  classical
  rw [expPointOp]
  simp only [expObs, pointObs, tauObservable_eq_sum_pauliProj]
  simp_rw [dot_smul_indicator]
  calc
    averageOperatorOverDistribution (uniformDistribution (PauliScalar P))
        (fun r => phaseSign (fixedBinTrace P.model (a * r)) •
          heteroKron
            (∑ x, phaseSign (fixedBinTrace P.model (x * r)) •
              (S.pointMeas side W u).effect x)
            (∑ e, phaseSign (fixedBinTrace P.model
              (dotProduct e (indicatorVec u) * r)) • pauliProj W e)) =
      averageOperatorOverDistribution (uniformDistribution (PauliScalar P))
        (fun r => ∑ x, ∑ e,
          phaseSign (fixedBinTrace P.model (a * r)) •
            (phaseSign (fixedBinTrace P.model (x * r)) •
              (phaseSign (fixedBinTrace P.model
                (dotProduct e (indicatorVec u) * r)) •
                  heteroKron ((S.pointMeas side W u).effect x)
                    (pauliProj W e)))) := by
          apply averageOperatorOverDistribution_congr
          intro r
          rw [heteroKron_sum_sum]
          simp_rw [heteroKron_smul_smul, Finset.smul_sum]
    _ = ∑ x, ∑ e,
          if x + dotProduct e (indicatorVec u) = a then
            heteroKron ((S.pointMeas side W u).effect x) (pauliProj W e)
          else 0 := by
      rw [averageOperatorOverDistribution_sum]
      simp_rw [averageOperatorOverDistribution_sum]
      simp_rw [average_three_fixedCharacters_smul]
    _ = ∑ p ∈ Finset.univ.filter (fun p : PauliScalar P × PauliScalar P =>
          p.1 + p.2 = a),
        heteroKron ((S.pointMeas side W u).effect p.1)
          (tauPointProj W u p.2) := by
      simp only [tauPointProj]
      rw [Finset.sum_filter, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x hx
      calc
        (∑ e, if x + dotProduct e (indicatorVec u) = a then
              heteroKron ((S.pointMeas side W u).effect x) (pauliProj W e)
            else 0) =
          ∑ y, ∑ e ∈ Finset.univ.filter
              (fun e : PauliRegister P => dotProduct e (indicatorVec u) = y),
            if x + dotProduct e (indicatorVec u) = a then
              heteroKron ((S.pointMeas side W u).effect x) (pauliProj W e)
            else 0 :=
          (Finset.sum_fiberwise Finset.univ
            (fun e : PauliRegister P => dotProduct e (indicatorVec u))
            (fun e => if x + dotProduct e (indicatorVec u) = a then
              heteroKron ((S.pointMeas side W u).effect x) (pauliProj W e)
            else 0)).symm
        _ = ∑ y, if x + y = a then
              heteroKron ((S.pointMeas side W u).effect x)
                (∑ e ∈ Finset.univ.filter
                  (fun e : PauliRegister P =>
                    dotProduct e (indicatorVec u) = y),
                  pauliProj W e)
            else 0 := by
          apply Finset.sum_congr rfl
          intro y hy
          by_cases hxy : x + y = a
          · rw [if_pos hxy, heteroKron_finset_sum_right]
            apply Finset.sum_congr rfl
            intro e he
            rw [if_pos]
            rw [(Finset.mem_filter.mp he).2]
            exact hxy
          · rw [if_neg hxy]
            apply Finset.sum_eq_zero
            intro e he
            rw [if_neg]
            intro heq
            apply hxy
            rw [← (Finset.mem_filter.mp he).2]
            exact heq

/-- Each generalized Pauli eigenspace projector is positive semidefinite. -/
private theorem pauliProj_nonneg {K ι : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Algebra (ZMod 2) K] [Fintype ι] [DecidableEq ι]
    (W : PauliKind) (e : ι → K) : 0 ≤ pauliProj W e :=
  Matrix.nonneg_iff_posSemidef.mpr
    (Matrix.posSemidef_vecMulVec_self_star (pauliVec W e))

private theorem tauPointProj_nonneg (W : PauliKind)
    (u : Fin P.m → PauliScalar P) (a : PauliScalar P) :
    0 ≤ tauPointProj W u a := by
  classical
  unfold tauPointProj
  exact Finset.sum_nonneg fun e he => pauliProj_nonneg W e

private theorem tauObservable_zero {K ι : Type*} [Field K] [Finite K]
    [DecidableEq K] [Algebra (ZMod 2) K] [Fintype ι] [DecidableEq ι]
    (W : PauliKind) : tauObservable W (0 : ι → K) = 1 := by
  letI : Fintype K := Fintype.ofFinite K
  have hmul := tauObservable_mul W (0 : ι → K) 0
  rw [add_zero, tauObservable_sq] at hmul
  exact hmul.symm

private theorem sum_pauliProj_eq_one {K ι : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Algebra (ZMod 2) K] [Fintype ι] [DecidableEq ι]
    (W : PauliKind) : ∑ e : ι → K, pauliProj W e = 1 := by
  have h := tauObservable_eq_sum_pauliProj W (0 : ι → K)
  rw [tauObservable_zero] at h
  simpa [dotProduct, phaseSign] using h.symm

/-- The point fibers partition the complete family of Pauli eigenspace projectors. -/
private theorem sum_tauPointProj_eq_one (W : PauliKind)
    (u : Fin P.m → PauliScalar P) :
    ∑ a, tauPointProj W u a = 1 := by
  classical
  rw [show (∑ a, tauPointProj W u a) =
      ∑ e : PauliRegister P, pauliProj W e by
    simp only [tauPointProj]
    exact Finset.sum_fiberwise Finset.univ
      (fun e : PauliRegister P => dotProduct e (indicatorVec u))
      (fun e => pauliProj W e)]
  exact sum_pauliProj_eq_one W

/-- The projective point measurement on one Pauli register obtained by
coarse-graining the generalized Pauli basis according to its value at `u`.
This is the ancillary measurement used in item 1 of `lem:qld-comm-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:455-465`. -/
noncomputable def tauPointMeas (W : PauliKind)
    (u : Fin P.m → PauliScalar P) :
    Measurement (PauliScalar P) (PauliRegister P) :=
  Measurement.ofSumEqOne (tauPointProj W u) (tauPointProj_nonneg W u)
    (sum_tauPointProj_eq_one W u)

/-- The effects of the Pauli point measurement are the point projectors. -/
@[simp] theorem tauPointMeas_effect (W : PauliKind)
    (u : Fin P.m → PauliScalar P) (a : PauliScalar P) :
    (tauPointMeas W u).effect a = tauPointProj W u a := rfl

/-- The fine product measurement underlying the convolution definition of an
expanded point measurement. Its outcome records the strategy and Pauli point
values separately. Paper `14_analysis_of_the_pauli_basis_test.tex:455-465`. -/
noncomputable def pointTauMeas (S : ProjectiveSetting P ε) (side : PlayerSide)
    (W : PauliKind) (u : Fin P.m → PauliScalar P) :
    Measurement (PauliScalar P × PauliScalar P) (S.ExpandedLocalSpace side) :=
  Measurement.ofSumEqOne
    (fun p => heteroKron ((S.pointMeas side W u).effect p.1)
      ((tauPointMeas W u).effect p.2))
    (fun p => Quantum.kronecker_nonneg
      ((S.pointMeas side W u).pos p.1) ((tauPointMeas W u).pos p.2))
    (by
      change ∑ p : PauliScalar P × PauliScalar P,
          heteroKron ((S.pointMeas side W u).effect p.1)
            (tauPointProj W u p.2) = 1
      rw [Fintype.sum_prod_type]
      calc
        (∑ x, ∑ y, heteroKron ((S.pointMeas side W u).effect x)
            (tauPointProj W u y)) =
            heteroKron (∑ x, (S.pointMeas side W u).effect x)
              (∑ y, tauPointProj W u y) := (heteroKron_sum_sum _ _).symm
        _ = 1 := by
          rw [(S.pointMeas side W u).sum_eq_one, sum_tauPointProj_eq_one]
          exact Matrix.one_kronecker_one)

/-- Effects of the fine product measurement are the corresponding Kronecker
products of strategy and Pauli point effects. -/
@[simp] theorem pointTauMeas_effect (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (u : Fin P.m → PauliScalar P)
    (p : PauliScalar P × PauliScalar P) :
    (S.pointTauMeas side W u).effect p =
      heteroKron ((S.pointMeas side W u).effect p.1)
        (tauPointProj W u p.2) := rfl

/-- Expanded point effects are positive semidefinite. This is the positivity
obligation in `def:expanded-point-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:384-418`. -/
theorem expPointOp_nonneg (S : ProjectiveSetting P ε) (side : PlayerSide)
    (W : PauliKind) (u : Fin P.m → PauliScalar P) (a : PauliScalar P) :
    0 ≤ S.expPointOp side W u a := by
  rw [expPointOp_eq_convolution]
  exact Finset.sum_nonneg fun p hp => Quantum.kronecker_nonneg
    ((S.pointMeas side W u).pos p.1) (tauPointProj_nonneg W u p.2)

/-- Expanded point effects sum to the identity. This is the completeness
obligation in `def:expanded-point-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:384-418`. -/
theorem expPointOp_sum_eq_one (S : ProjectiveSetting P ε) (side : PlayerSide)
    (W : PauliKind) (u : Fin P.m → PauliScalar P) :
    ∑ a, S.expPointOp side W u a = 1 := by
  simp_rw [expPointOp_eq_convolution]
  calc
    (∑ a, ∑ p ∈ Finset.univ.filter
        (fun p : PauliScalar P × PauliScalar P => p.1 + p.2 = a),
      heteroKron ((S.pointMeas side W u).effect p.1)
        (tauPointProj W u p.2)) =
      ∑ p : PauliScalar P × PauliScalar P,
        heteroKron ((S.pointMeas side W u).effect p.1)
          (tauPointProj W u p.2) := by
      let f : PauliScalar P × PauliScalar P → PauliScalar P :=
        fun p => p.1 + p.2
      let A : PauliScalar P × PauliScalar P →
          Op (S.ExpandedLocalSpace side) := fun p =>
        heteroKron ((S.pointMeas side W u).effect p.1)
          (tauPointProj W u p.2)
      change (∑ a, ∑ p ∈ Finset.univ.filter (fun p => f p = a), A p) =
        ∑ p, A p
      exact Finset.sum_fiberwise Finset.univ f A
    _ = heteroKron (∑ x, (S.pointMeas side W u).effect x)
        (∑ y, tauPointProj W u y) := by
      rw [Fintype.sum_prod_type]
      exact (heteroKron_sum_sum _ _).symm
    _ = 1 := by
      rw [(S.pointMeas side W u).sum_eq_one,
        sum_tauPointProj_eq_one (P := P)]
      exact Matrix.one_kronecker_one

/-- The complete expanded point measurement on the chosen player and Pauli
register. Its effects are those of `def:expanded-point-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:384-418`, blueprint
`ch14_qpbt_observables.tex:809-844`. -/
noncomputable def pointMeasExp (S : ProjectiveSetting P ε) (side : PlayerSide)
    (W : PauliKind) (u : Fin P.m → PauliScalar P) :
    Measurement (PauliScalar P) (S.ExpandedLocalSpace side) :=
  Measurement.ofSumEqOne (S.expPointOp side W u)
    (S.expPointOp_nonneg side W u) (S.expPointOp_sum_eq_one side W u)

/-- The expanded point measurement is the addition postprocessing of its fine
strategy--Pauli product measurement. This is the data-processing presentation
used in item 1 of `lem:qld-comm-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:455-465`. -/
theorem pointMeasExp_effect_eq_pointTauMeas_postprocess
    (S : ProjectiveSetting P ε) (side : PlayerSide) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) (a : PauliScalar P) :
    (S.pointMeasExp side W u).effect a =
      ((S.pointTauMeas side W u).postprocess (fun p => p.1 + p.2)).effect a := by
  change S.expPointOp side W u a = _
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
  exact expPointOp_eq_convolution S side W u a

/-- Folding malformed point answers into zero preserves the strategy projectors. -/
private theorem pointMeas_isProjective (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (u : Fin P.m → PauliScalar P) :
    Measurement.IsProjective (S.pointMeas side W u) := by
  classical
  let M := S.strategyMeasurement side (pointQuestion P W u)
  have hM : Measurement.IsProjective M := by
    cases side with
    | alice => exact S.isProjective.1 _
    | bob => exact S.isProjective.2 _
  change Measurement.IsProjective (M.postprocess pointAnswerOrZero)
  intro b
  refine ⟨?_, ?_⟩
  · change (M.postprocess pointAnswerOrZero).effect b *
      (M.postprocess pointAnswerOrZero).effect b =
        (M.postprocess pointAnswerOrZero).effect b
    let fiber : Finset (PauliAnswer P) :=
      Finset.univ.filter fun a => pointAnswerOrZero a = b
    calc
      (M.postprocess pointAnswerOrZero).effect b *
          (M.postprocess pointAnswerOrZero).effect b =
        (∑ a ∈ fiber, M.effect a) * (∑ a' ∈ fiber, M.effect a') := by
          rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
      _ = ∑ a ∈ fiber, ∑ a' ∈ fiber, M.effect a * M.effect a' := by
          rw [Finset.sum_mul]
          simp_rw [Finset.mul_sum]
      _ = ∑ a ∈ fiber, ∑ a' ∈ fiber,
          if a' = a then M.effect a else 0 := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          refine Finset.sum_congr rfl ?_
          intro a' ha'
          by_cases haa' : a' = a
          · subst a'
            simp [(hM a).isIdempotentElem.eq]
          · have hne : a ≠ a' := fun h => haa' h.symm
            simp [DistanceCalculus.projective_effect_mul_effect_eq_zero M hM hne,
              haa']
      _ = ∑ a ∈ fiber, M.effect a := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          simp [fiber, ha]
      _ = (M.postprocess pointAnswerOrZero).effect b := by
          rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
  · change ((M.postprocess pointAnswerOrZero).effect b)ᴴ =
      (M.postprocess pointAnswerOrZero).effect b
    exact (Matrix.nonneg_iff_posSemidef.mp
      ((M.postprocess pointAnswerOrZero).pos b)).isHermitian.eq

/-- Point observables form a representation of the additive Pauli scalar group. -/
private theorem pointObs_mul (S : ProjectiveSetting P ε) (side : PlayerSide)
    (W : PauliKind) (r s : PauliScalar P)
    (u : Fin P.m → PauliScalar P) :
    S.pointObs side W r u * S.pointObs side W s u =
      S.pointObs side W (r + s) u := by
  classical
  let M := S.pointMeas side W u
  have hM : Measurement.IsProjective M := pointMeas_isProjective S side W u
  change (∑ a : PauliScalar P,
      phaseSign (fixedBinTrace P.model (a * r)) • M.effect a) *
      (∑ a : PauliScalar P,
        phaseSign (fixedBinTrace P.model (a * s)) • M.effect a) =
    ∑ a : PauliScalar P,
      phaseSign (fixedBinTrace P.model (a * (r + s))) • M.effect a
  calc
    _ = ∑ a : PauliScalar P, ∑ b : PauliScalar P,
        (phaseSign (fixedBinTrace P.model (a * r)) *
          phaseSign (fixedBinTrace P.model (b * s))) •
            (M.effect a * M.effect b) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    _ = ∑ a : PauliScalar P,
        phaseSign (fixedBinTrace P.model (a * (r + s))) • M.effect a := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_eq_single a]
      · rw [(hM a).isIdempotentElem.eq]
        congr 1
        simpa only [mul_add] using fixedCharacter_add (P := P) (a * r) (a * s)
      · intro b hb hba
        have hab : a ≠ b := fun h => hba h.symm
        rw [DistanceCalculus.projective_effect_mul_effect_eq_zero M hM hab]
        simp
      · intro ha'
        exact (ha' (Finset.mem_univ a)).elim

/-- Expanded observables inherit the additive representation law. -/
private theorem expObs_mul (S : ProjectiveSetting P ε) (side : PlayerSide)
    (W : PauliKind) (r s : PauliScalar P)
    (u : Fin P.m → PauliScalar P) :
    S.expObs side W r u * S.expObs side W s u =
      S.expObs side W (r + s) u := by
  calc
    S.expObs side W r u * S.expObs side W s u =
        heteroKron
          (S.pointObs side W r u * S.pointObs side W s u)
          (tauObservable W (fun h => r * indicatorVec u h) *
            tauObservable W (fun h => s * indicatorVec u h)) := by
      exact (Matrix.mul_kronecker_mul
        (S.pointObs side W r u) (S.pointObs side W s u)
        (tauObservable W (fun h => r * indicatorVec u h))
        (tauObservable W (fun h => s * indicatorVec u h))).symm
    _ = heteroKron (S.pointObs side W (r + s) u)
        (tauObservable W ((fun h => r * indicatorVec u h) +
          (fun h => s * indicatorVec u h))) := by
      rw [pointObs_mul, tauObservable_mul]
    _ = S.expObs side W (r + s) u := by
      congr 2
      funext h
      simp only [Pi.add_apply]
      ring

private theorem star_phaseSign (t : ZMod 2) :
    star (phaseSign t) = phaseSign t := by
  by_cases ht : t = 0 <;> simp [phaseSign, ht]

private theorem tauObservable_isHermitian {K ι : Type*} [Field K]
    [Finite K] [DecidableEq K] [Algebra (ZMod 2) K]
    [Fintype ι] [DecidableEq ι]
    (W : PauliKind) (v : ι → K) : (tauObservable W v).IsHermitian := by
  letI : Fintype K := Fintype.ofFinite K
  rw [tauObservable_eq_sum_pauliProj, Matrix.IsHermitian,
    Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [Matrix.conjTranspose_smul, star_phaseSign]
  exact congrArg (fun A : Op (ι → K) =>
    phaseSign (binTrace K (dotProduct v e)) • A)
      (Matrix.nonneg_iff_posSemidef.mp (pauliProj_nonneg W e)).isHermitian.eq

private theorem expObs_isHermitian (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (r : PauliScalar P)
    (u : Fin P.m → PauliScalar P) :
    (S.expObs side W r u).IsHermitian := by
  rw [Matrix.IsHermitian]
  calc
    (S.expObs side W r u)ᴴ = heteroKron
        (S.pointObs side W r u)ᴴ
        (tauObservable W (fun h => r * indicatorVec u h))ᴴ := by
      exact Matrix.conjTranspose_kronecker _ _
    _ = S.expObs side W r u := by
      rw [(S.pointObs_isHermitian side W r u).eq,
        (tauObservable_isHermitian W (fun h => r * indicatorVec u h)).eq]
      rfl

private theorem expPointOp_isHermitian (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (u : Fin P.m → PauliScalar P)
    (a : PauliScalar P) : (S.expPointOp side W u a).IsHermitian := by
  classical
  rw [expPointOp, averageOperatorOverDistribution, Matrix.IsHermitian,
    Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, star_phaseSign,
    (expObs_isHermitian S side W r u).eq]
  simp

private theorem expPointOp_mul_self (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (u : Fin P.m → PauliScalar P)
    (a : PauliScalar P) :
    S.expPointOp side W u a * S.expPointOp side W u a =
      S.expPointOp side W u a := by
  classical
  let D := uniformDistribution (PauliScalar P)
  let F : PauliScalar P → Op (S.ExpandedLocalSpace side) := fun r =>
    phaseSign (fixedBinTrace P.model (a * r)) • S.expObs side W r u
  change averageOperatorOverDistribution D F *
      averageOperatorOverDistribution D F = averageOperatorOverDistribution D F
  calc
    averageOperatorOverDistribution D F * averageOperatorOverDistribution D F =
        averageOperatorOverDistribution D
          (fun r => F r * averageOperatorOverDistribution D F) := by
      simpa using (averageOperatorOverDistribution_mul_left_right D
        1 (averageOperatorOverDistribution D F) F).symm
    _ = averageOperatorOverDistribution D
          (fun r => averageOperatorOverDistribution D (fun s => F r * F s)) := by
      apply averageOperatorOverDistribution_congr
      intro r
      simpa using
        (averageOperatorOverDistribution_mul_left_right D (F r) 1 F).symm
    _ = averageOperatorOverDistribution D
          (fun r => averageOperatorOverDistribution D (fun s => F (r + s))) := by
      apply averageOperatorOverDistribution_congr
      intro r
      apply averageOperatorOverDistribution_congr
      intro s
      dsimp only [F]
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, expObs_mul]
      congr 1
      simpa only [mul_add] using
        fixedCharacter_add (P := P) (a * r) (a * s)
    _ = averageOperatorOverDistribution D
          (fun _ => averageOperatorOverDistribution D F) := by
      apply averageOperatorOverDistribution_congr
      intro r
      exact (averageOperatorOverDistribution_uniform_equiv
        ((Equiv.addLeft r).symm) F).symm
    _ = averageOperatorOverDistribution D F := by
      exact averageOperatorOverDistribution_const_of_isProbability D
        (uniformDistribution_isProbability (PauliScalar P)) _

/-- A Fourier coefficient of the expanded representation is a projection. -/
private theorem expPointOp_isProj (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (u : Fin P.m → PauliScalar P)
    (a : PauliScalar P) : IsProj (S.expPointOp side W u a) := by
  refine isStarProjection_iff'.2 ⟨expPointOp_mul_self S side W u a, ?_⟩
  rw [Matrix.star_eq_conjTranspose]
  exact (expPointOp_isHermitian S side W u a).eq

/-- The expanded point measurement is projective, as asserted after the
convolution formula in `def:expanded-point-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:395-418`. -/
theorem pointMeasExp_isProjective (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (u : Fin P.m → PauliScalar P) :
    MIPStarRE.QPBT.Measurement.IsProjective (S.pointMeasExp side W u) := by
  intro a
  change IsProj (S.expPointOp side W u a)
  exact expPointOp_isProj S side W u a

/-- Trace-coarse-graining of the expanded point measurement. This is Equation
`eq:qld-def-mptur`, paper `14_analysis_of_the_pauli_basis_test.tex:411-418`,
blueprint `ch14_qpbt_observables.tex:846-874`. -/
noncomputable def expPointTrace (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (u : Fin P.m → PauliScalar P)
    (r : PauliScalar P) : Measurement (ZMod 2) (S.ExpandedLocalSpace side) :=
  (S.pointMeasExp side W u).postprocess fun a => fixedBinTrace P.model (a * r)

/-- Fourier expansion of a Pauli observable after grouping labels by point value. -/
private theorem tauObservable_eq_sum_tauPointProj (W : PauliKind)
    (u : Fin P.m → PauliScalar P) (r : PauliScalar P) :
    tauObservable W (fun h => r * indicatorVec u h) =
      ∑ y, phaseSign (fixedBinTrace P.model (y * r)) • tauPointProj W u y := by
  classical
  symm
  calc
    (∑ y, phaseSign (fixedBinTrace P.model (y * r)) • tauPointProj W u y) =
        ∑ y, ∑ e ∈ Finset.univ.filter
            (fun e : PauliRegister P => dotProduct e (indicatorVec u) = y),
          phaseSign (fixedBinTrace P.model (y * r)) • pauliProj W e := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [tauPointProj, Finset.smul_sum]
    _ = ∑ y, ∑ e ∈ Finset.univ.filter
            (fun e : PauliRegister P => dotProduct e (indicatorVec u) = y),
          phaseSign (fixedBinTrace P.model
            (dotProduct e (indicatorVec u) * r)) • pauliProj W e := by
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro e he
      rw [(Finset.mem_filter.mp he).2]
    _ = ∑ e : PauliRegister P,
          phaseSign (fixedBinTrace P.model
            (dotProduct e (indicatorVec u) * r)) • pauliProj W e := by
      exact Finset.sum_fiberwise Finset.univ
        (fun e : PauliRegister P => dotProduct e (indicatorVec u))
        (fun e => phaseSign (fixedBinTrace P.model
          (dotProduct e (indicatorVec u) * r)) • pauliProj W e)
    _ = tauObservable W (fun h => r * indicatorVec u h) := by
      rw [tauObservable_eq_sum_pauliProj]
      apply Finset.sum_congr rfl
      intro e he
      rw [dot_smul_indicator, fixedBinTrace]

/-- Fourier inversion recovers an expanded observable from its point effects. -/
private theorem expObs_eq_sum_expPointOp (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (u : Fin P.m → PauliScalar P)
    (r : PauliScalar P) :
    S.expObs side W r u =
      ∑ a, phaseSign (fixedBinTrace P.model (a * r)) •
        S.expPointOp side W u a := by
  classical
  rw [expObs, pointObs, tauObservable_eq_sum_tauPointProj]
  calc
    heteroKron
        (∑ x, phaseSign (fixedBinTrace P.model (x * r)) •
          (S.pointMeas side W u).effect x)
        (∑ y, phaseSign (fixedBinTrace P.model (y * r)) •
          tauPointProj W u y) =
      ∑ x, ∑ y,
        phaseSign (fixedBinTrace P.model (x * r)) •
          (phaseSign (fixedBinTrace P.model (y * r)) •
            heteroKron ((S.pointMeas side W u).effect x)
              (tauPointProj W u y)) := by
        rw [heteroKron_sum_sum]
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        rw [heteroKron_smul_smul]
    _ = ∑ p : PauliScalar P × PauliScalar P,
        phaseSign (fixedBinTrace P.model ((p.1 + p.2) * r)) •
          heteroKron ((S.pointMeas side W u).effect p.1)
            (tauPointProj W u p.2) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      rw [smul_smul, fixedCharacter_mul_add]
    _ = ∑ a, ∑ p ∈ Finset.univ.filter
          (fun p : PauliScalar P × PauliScalar P => p.1 + p.2 = a),
        phaseSign (fixedBinTrace P.model ((p.1 + p.2) * r)) •
          heteroKron ((S.pointMeas side W u).effect p.1)
            (tauPointProj W u p.2) := by
      exact (Finset.sum_fiberwise Finset.univ
        (fun p : PauliScalar P × PauliScalar P => p.1 + p.2)
        (fun p => phaseSign (fixedBinTrace P.model ((p.1 + p.2) * r)) •
          heteroKron ((S.pointMeas side W u).effect p.1)
            (tauPointProj W u p.2))).symm
    _ = ∑ a, phaseSign (fixedBinTrace P.model (a * r)) •
        ∑ p ∈ Finset.univ.filter
          (fun p : PauliScalar P × PauliScalar P => p.1 + p.2 = a),
          heteroKron ((S.pointMeas side W u).effect p.1)
            (tauPointProj W u p.2) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]
    _ = ∑ a, phaseSign (fixedBinTrace P.model (a * r)) •
        S.expPointOp side W u a := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [expPointOp_eq_convolution]

private theorem zmod_two_eq_zero_or_one (b : ZMod 2) : b = 0 ∨ b = 1 := by
  fin_cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- A binary coarse-graining is the spectral effect of its signed observable. -/
private theorem postprocess_binary_effect_eq_half_add
    {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (M : MIPStarRE.Quantum.Measurement α ι) (f : α → ZMod 2) (b : ZMod 2) :
    (M.postprocess f).effect b =
      (2 : ℂ)⁻¹ •
        (1 + phaseSign b • ∑ a, phaseSign (f a) • M.effect a) := by
  classical
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect, Finset.sum_filter]
  calc
    (∑ a, if f a = b then M.effect a else 0) =
        ∑ a, (2 : ℂ)⁻¹ •
          (M.effect a + phaseSign b • (phaseSign (f a) • M.effect a)) := by
      apply Finset.sum_congr rfl
      intro a ha
      rcases zmod_two_eq_zero_or_one b with hb | hb <;>
        rcases zmod_two_eq_zero_or_one (f a) with hfa | hfa
      all_goals simp [hb, hfa, phaseSign]
      all_goals module
    _ = (2 : ℂ)⁻¹ • ∑ a,
          (M.effect a + phaseSign b • (phaseSign (f a) • M.effect a)) := by
      rw [Finset.smul_sum]
    _ = (2 : ℂ)⁻¹ •
        ((∑ a, M.effect a) +
          ∑ a, phaseSign b • (phaseSign (f a) • M.effect a)) := by
      rw [Finset.sum_add_distrib]
    _ = (2 : ℂ)⁻¹ •
        ((∑ a, M.effect a) +
          phaseSign b • ∑ a, phaseSign (f a) • M.effect a) := by
      rw [Finset.smul_sum]
    _ = (2 : ℂ)⁻¹ •
        (1 + phaseSign b • ∑ a, phaseSign (f a) • M.effect a) := by
      rw [M.sum_eq_one]

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
  change ((S.pointMeasExp side W u).postprocess
    (fun a => fixedBinTrace P.model (a * r))).effect b = _
  calc
    _ = (2 : ℂ)⁻¹ •
        (1 + phaseSign b • ∑ a,
          phaseSign (fixedBinTrace P.model (a * r)) •
            (S.pointMeasExp side W u).effect a) :=
      postprocess_binary_effect_eq_half_add _ _ _
    _ = (2 : ℂ)⁻¹ •
        (1 + phaseSign b • S.expObs side W r u) := by
      change (2 : ℂ)⁻¹ •
        (1 + phaseSign b • ∑ a,
          phaseSign (fixedBinTrace P.model (a * r)) •
            S.expPointOp side W u a) = _
      rw [← expObs_eq_sum_expPointOp]

end ProjectiveSetting

end

end MIPStarRE.QPBT
