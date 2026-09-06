import MIPStarRE.QPBT.Observables.ExpandedPlacement

/-!
# Approximate commutation of the expanded point projections

The trace-coarse-grained expanded point projections approximately commute on
each of the four register placements.  The commutator of the two projections is
a scalar multiple of a factorized operator whose strategy factor is the twisted
commutator of the two point observables and whose Pauli factor is a product of
generalized Pauli observables; the latter is an isometry, so the placement
bookkeeping of `ExpandedPlacement` reduces the estimate to the twisted
commutation relation of `lem:qld-win-implications-obs` on the corresponding
player side.  Both player sides are treated explicitly.

## References

The declarations prove item 2 of `lem:qld-comm-cons` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:1139-1178`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:466-505`.
-/

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-! ## Algebraic preliminaries -/

/-- The generalized Pauli observables are self-adjoint. A private copy of this
statement, phrased through `Matrix.IsHermitian`, lives at
`MIPStarRE/QPBT/Observables/ExpandedDefs.lean:692` and is unreachable from
here; this form is the one used by `lem:qld-comm-cons`, and promoting the
private original is issue #204. Blueprint `ch11_qpbt_algebra.tex:587-634`,
paper `references/qpbt-paper/04_preliminaries.tex:1052-1096`. -/
theorem tauObservable_conjTranspose {K ι : Type*} [Field K] [Finite K]
    [DecidableEq K] [Algebra (ZMod 2) K] [Fintype ι] [DecidableEq ι]
    (W : PauliKind) (v : ι → K) :
    (tauObservable W v)ᴴ = tauObservable W v := by
  cases nonempty_fintype K
  rw [tauObservable_eq_sum_pauliProj, Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [Matrix.conjTranspose_smul, star_phaseSign]
  congr 1
  exact (Matrix.posSemidef_vecMulVec_self_star (pauliVec W e)).isHermitian.eq

/-- The generalized Pauli observables are reflections. Blueprint
`ch11_qpbt_algebra.tex:587-634`, paper
`references/qpbt-paper/04_preliminaries.tex:1088-1089`. -/
theorem tauObservable_conjTranspose_mul_self {K ι : Type*} [Field K]
    [Fintype K] [DecidableEq K] [Algebra (ZMod 2) K] [Fintype ι]
    [DecidableEq ι] (W : PauliKind) (v : ι → K) :
    (tauObservable W v)ᴴ * tauObservable W v = 1 := by
  rw [tauObservable_conjTranspose, tauObservable_sq]

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

/-! ## The commutator of two expanded point projections -/

/-- The Pauli-register factor of the expanded `X` observable at a tuple. -/
noncomputable def tauX (P : AdmissibleParams) (ω : PauliTuple P) :
    Op (PauliRegister P) :=
  tauObservable .X (fun h => ω.2.2.1 * indicatorVec ω.1 h)

/-- The Pauli-register factor of the expanded `Z` observable at a tuple. -/
noncomputable def tauZ (P : AdmissibleParams) (ω : PauliTuple P) :
    Op (PauliRegister P) :=
  tauObservable .Z (fun h => ω.2.2.2 * indicatorVec ω.2.1 h)

/-- The product of the two Pauli-register factors is an isometry. Blueprint
`ch11_qpbt_algebra.tex:587-634`, paper
`references/qpbt-paper/04_preliminaries.tex:1088-1095`. -/
theorem tauX_mul_tauZ_isometry (P : AdmissibleParams) (ω : PauliTuple P) :
    (tauX P ω * tauZ P ω)ᴴ * (tauX P ω * tauZ P ω) = 1 :=
  WinImplications.mul_conjTranspose_mul_self
    (tauObservable_conjTranspose_mul_self _ _)
    (tauObservable_conjTranspose_mul_self _ _)

/-- The two Pauli-register factors commute up to the tuple's commutation sign.
This is the exact half of the argument of `lem:qld-comm-cons`; blueprint
`ch11_qpbt_algebra.tex:587-634`, paper
`14_analysis_of_the_pauli_basis_test.tex:495-505`. -/
theorem tauZ_mul_tauX (P : AdmissibleParams) (ω : PauliTuple P) :
    tauZ P ω * tauX P ω =
      phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
        (tauX P ω * tauZ P ω) := by
  have h := tauObservable_X_mul_Z (K := PauliScalar P)
    (fun h => ω.2.2.1 * indicatorVec ω.1 h)
    (fun h => ω.2.2.2 * indicatorVec ω.2.1 h)
  have hg : binTrace (PauliScalar P)
      (dotProduct (fun h => ω.2.2.1 * indicatorVec ω.1 h)
        (fun h => ω.2.2.2 * indicatorVec ω.2.1 h)) =
      gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2 := rfl
  rw [hg, show (tauObservable .X fun k => ω.2.2.1 * indicatorVec ω.1 k) =
      tauX P ω from rfl,
    show (tauObservable .Z fun k => ω.2.2.2 * indicatorVec ω.2.1 k) =
      tauZ P ω from rfl] at h
  have hsq := phaseSign_mul_self (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
  calc tauZ P ω * tauX P ω
      = (phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) *
          phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)) •
            (tauZ P ω * tauX P ω) := by rw [hsq, one_smul]
    _ = phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
          (phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
            (tauZ P ω * tauX P ω)) := by rw [smul_smul]
    _ = phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
          (tauX P ω * tauZ P ω) := by rw [← h]

/-- The twisted commutator of the two point observables at a tuple. -/
noncomputable def twistedCommutator (S : ProjectiveSetting P ε)
    (side : PlayerSide) (ω : PauliTuple P) : Op (S.LocalSpace side) :=
  S.pointObs side .X ω.2.2.1 ω.1 * S.pointObs side .Z ω.2.2.2 ω.2.1 -
    phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
      (S.pointObs side .Z ω.2.2.2 ω.2.1 * S.pointObs side .X ω.2.2.1 ω.1)

/-- The commutator of the two expanded observables factorizes with the twisted
commutator of the point observables on the strategy register. This is the
display following `eq:lc-23` in the proof of `lem:qld-comm-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:487-505`, blueprint
`ch14_qpbt_observables.tex:1164-1175`. -/
theorem expObs_commutator (S : ProjectiveSetting P ε) (side : PlayerSide)
    (ω : PauliTuple P) :
    S.expObs side .X ω.2.2.1 ω.1 * S.expObs side .Z ω.2.2.2 ω.2.1 -
        S.expObs side .Z ω.2.2.2 ω.2.1 * S.expObs side .X ω.2.2.1 ω.1 =
      heteroKron (S.twistedCommutator side ω) (tauX P ω * tauZ P ω) := by
  rw [expObs, expObs, heteroKron_mul, heteroKron_mul]
  rw [show tauObservable .X (fun h => ω.2.2.1 * indicatorVec ω.1 h) =
    tauX P ω from rfl,
    show tauObservable .Z (fun h => ω.2.2.2 * indicatorVec ω.2.1 h) =
      tauZ P ω from rfl]
  rw [tauZ_mul_tauX, MagicSquareRigidity.heteroKron_smul_right,
    ← WinImplications.heteroKron_smul_left,
    WinImplications.heteroKron_sub_left, twistedCommutator]

/-- The commutator of two trace-coarse-grained expanded point projections is a
unit-modulus multiple of one quarter of the factorized commutator. This is the
first display in the proof of item 2 of `lem:qld-comm-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:487-495`, blueprint
`ch14_qpbt_observables.tex:1164-1175`. -/
theorem expPointTrace_commutator (S : ProjectiveSetting P ε)
    (side : PlayerSide) (ω : PauliTuple P) (b b' : ZMod 2) :
    (S.expPointTrace side .X ω.1 ω.2.2.1).effect b *
          (S.expPointTrace side .Z ω.2.1 ω.2.2.2).effect b' -
        (S.expPointTrace side .Z ω.2.1 ω.2.2.2).effect b' *
          (S.expPointTrace side .X ω.1 ω.2.2.1).effect b =
      ((4 : ℂ)⁻¹ * (phaseSign b * phaseSign b')) •
        heteroKron (S.twistedCommutator side ω) (tauX P ω * tauZ P ω) := by
  set A := S.expObs side .X ω.2.2.1 ω.1 with hA
  set B := S.expObs side .Z ω.2.2.2 ω.2.1 with hB
  rw [expPointTrace_eq_half_add, expPointTrace_eq_half_add, ← expObs_commutator]
  have hexp : (1 + phaseSign b • A) * (1 + phaseSign b' • B) -
      (1 + phaseSign b' • B) * (1 + phaseSign b • A) =
      (phaseSign b * phaseSign b') • (A * B - B * A) := by
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc,
      mul_smul_comm, smul_add, smul_smul, smul_sub,
      mul_comm (phaseSign b') (phaseSign b)]
    abel
  calc (2 : ℂ)⁻¹ • (1 + phaseSign b • A) *
        ((2 : ℂ)⁻¹ • (1 + phaseSign b' • B)) -
        (2 : ℂ)⁻¹ • (1 + phaseSign b' • B) *
          ((2 : ℂ)⁻¹ • (1 + phaseSign b • A))
      = (4 : ℂ)⁻¹ • ((1 + phaseSign b • A) * (1 + phaseSign b' • B) -
          (1 + phaseSign b' • B) * (1 + phaseSign b • A)) := by
        rw [smul_mul_assoc, mul_smul_comm, smul_smul, smul_mul_assoc,
          mul_smul_comm, smul_smul, ← smul_sub]
        norm_num
    _ = ((4 : ℂ)⁻¹ * (phaseSign b * phaseSign b')) • (A * B - B * A) := by
        rw [hexp, smul_smul]

/-! ## The approximate commutation on each placement -/

/-- The placement of a scalar multiple is the scalar multiple of the
placement. Paper `14_analysis_of_the_pauli_basis_test.tex:420-450`,
blueprint `ch14_qpbt_observables.tex:1002-1031`. -/
theorem place_smul (S : ProjectiveSetting P ε) (p : Placement) (c : ℂ)
    (O : Op (S.ExpandedLocalSpace p.side)) :
    S.place p (c • O) = c • S.place p O := by
  ext i j
  cases p <;> simp only [place, Matrix.smul_apply, smul_eq_mul] <;> ring

/-- The twisted commutator of the point observables is small on average, on
either player side. This packages both orientations of
`eq:pts-obs-commutation`; paper
`14_analysis_of_the_pauli_basis_test.tex:309-354`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem exists_twistedCommutator_avg_le :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
        (side : PlayerSide), 0 ≤ ε →
      avgOver (uniformDistribution (PauliTuple P)) (fun ω =>
        ‖applyOperatorToState (S.placeStrategySide side (S.twistedCommutator side ω))
          S.toStrategy.ψ‖ ^ 2) ≤ C * Real.sqrt ε := by
  obtain ⟨C₁, hC₁, h₁⟩ := pointObs_twisted_commutation
  obtain ⟨C₂, hC₂, h₂⟩ := pointObs_twisted_commutation_interchanged
  refine ⟨C₁ + C₂, by linarith, ?_⟩
  intro P ε S side hε
  have hs : (0 : ℝ) ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  cases side with
  | alice =>
      have h := h₁ P ε S hε
      rw [WinImplications.opDistSq_eq_avgOver] at h
      refine le_trans (le_of_eq ?_) (le_trans h ?_)
      · refine avgOver_congr _ _ _ (fun ω => ?_)
        have hop : S.placeStrategySide .alice (S.twistedCommutator .alice ω) =
            heteroKron (S.pointObs .alice .X ω.2.2.1 ω.1 *
                S.pointObs .alice .Z ω.2.2.2 ω.2.1)
                (1 : Op S.toStrategy.ιB) -
              phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
                heteroKron (S.pointObs .alice .Z ω.2.2.2 ω.2.1 *
                  S.pointObs .alice .X ω.2.2.1 ω.1) 1 := by
          have h1 : heteroKron (S.twistedCommutator .alice ω)
              (1 : Op S.toStrategy.ιB) =
              heteroKron (S.pointObs .alice .X ω.2.2.1 ω.1 *
                S.pointObs .alice .Z ω.2.2.2 ω.2.1) 1 -
                heteroKron
                  (phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
                    (S.pointObs .alice .Z ω.2.2.2 ω.2.1 *
                      S.pointObs .alice .X ω.2.2.1 ω.1)) 1 :=
            (WinImplications.heteroKron_sub_left _ _ _).symm
          rw [← WinImplications.heteroKron_smul_left]
          exact h1
        rw [hop]
        rfl
      · nlinarith
  | bob =>
      have h := h₂ P ε S hε
      rw [WinImplications.opDistSq_eq_avgOver] at h
      refine le_trans (le_of_eq ?_) (le_trans h ?_)
      · refine avgOver_congr _ _ _ (fun ω => ?_)
        have hop : S.placeStrategySide .bob (S.twistedCommutator .bob ω) =
            heteroKron (1 : Op S.toStrategy.ιA)
                (S.pointObs .bob .X ω.2.2.1 ω.1 *
                  S.pointObs .bob .Z ω.2.2.2 ω.2.1) -
              phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
                heteroKron 1 (S.pointObs .bob .Z ω.2.2.2 ω.2.1 *
                  S.pointObs .bob .X ω.2.2.1 ω.1) := by
          have h1 : heteroKron (1 : Op S.toStrategy.ιA)
              (S.twistedCommutator .bob ω) =
              heteroKron 1 (S.pointObs .bob .X ω.2.2.1 ω.1 *
                S.pointObs .bob .Z ω.2.2.2 ω.2.1) -
                heteroKron 1
                  (phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
                    (S.pointObs .bob .Z ω.2.2.2 ω.2.1 *
                      S.pointObs .bob .X ω.2.2.1 ω.1)) :=
            heteroKron_sub_right _ _ _
          rw [← MagicSquareRigidity.heteroKron_smul_right]
          exact h1
        rw [hop]
        rfl
      · nlinarith

/-- Trace-coarse-grained expanded point projections approximately commute on
each of the four register placements. This is item 2 of `lem:qld-comm-cons`,
paper `14_analysis_of_the_pauli_basis_test.tex:466-505`, blueprint
`ch14_qpbt_observables.tex:1164-1175`. -/
theorem expPointTrace_comm_proof :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
        (p : Placement),
        opFamilyDistSq (uniformDistribution (PauliTuple P))
          (fun ω (bits : ZMod 2 × ZMod 2) => S.place p
            ((S.expPointTrace p.side .X ω.1 ω.2.2.1).effect bits.1 *
              (S.expPointTrace p.side .Z ω.2.1 ω.2.2.2).effect bits.2))
          (fun ω (bits : ZMod 2 × ZMod 2) => S.place p
            ((S.expPointTrace p.side .Z ω.2.1 ω.2.2.2).effect bits.2 *
              (S.expPointTrace p.side .X ω.1 ω.2.2.1).effect bits.1))
          S.psiHat ≤ C * Real.sqrt ε := by
  classical
  obtain ⟨C, hC, h⟩ := exists_twistedCommutator_avg_le
  refine ⟨C, hC, ?_⟩
  intro P ε S p
  have hε : (0 : ℝ) ≤ ε := by
    have hv := WinImplications.strategy_value_le_one S.toStrategy
    have hw := S.win
    linarith
  have hpt : ∀ (ω : PauliTuple P) (bits : ZMod 2 × ZMod 2),
      ‖applyOperatorToState
          (S.place p ((S.expPointTrace p.side .X ω.1 ω.2.2.1).effect bits.1 *
              (S.expPointTrace p.side .Z ω.2.1 ω.2.2.2).effect bits.2) -
            S.place p
              ((S.expPointTrace p.side .Z ω.2.1 ω.2.2.2).effect bits.2 *
                (S.expPointTrace p.side .X ω.1 ω.2.2.1).effect bits.1))
          S.psiHat‖ ^ 2 =
        (16 : ℝ)⁻¹ * ‖applyOperatorToState
          (S.placeStrategySide p.side (S.twistedCommutator p.side ω))
          S.toStrategy.ψ‖ ^ 2 := by
    intro ω bits
    rw [← place_sub, expPointTrace_commutator, place_smul,
      WinImplications.applyOperatorToState_smul_op, norm_smul,
      norm_place_heteroKron_psiHat S p (S.twistedCommutator p.side ω)
        (tauX P ω * tauZ P ω) (tauX_mul_tauZ_isometry P ω)]
    have hc : ‖(4 : ℂ)⁻¹ * (phaseSign bits.1 * phaseSign bits.2)‖ =
        (4 : ℝ)⁻¹ := by
      rw [norm_mul, norm_mul, WinImplications.norm_phaseSign,
        WinImplications.norm_phaseSign]
      norm_num
    rw [hc]
    ring
  have hcard : (Finset.univ : Finset (ZMod 2 × ZMod 2)).card = 4 := by decide
  have hrw : opFamilyDistSq (uniformDistribution (PauliTuple P))
      (fun ω (bits : ZMod 2 × ZMod 2) => S.place p
        ((S.expPointTrace p.side .X ω.1 ω.2.2.1).effect bits.1 *
          (S.expPointTrace p.side .Z ω.2.1 ω.2.2.2).effect bits.2))
      (fun ω (bits : ZMod 2 × ZMod 2) => S.place p
        ((S.expPointTrace p.side .Z ω.2.1 ω.2.2.2).effect bits.2 *
          (S.expPointTrace p.side .X ω.1 ω.2.2.1).effect bits.1))
      S.psiHat =
      (4 : ℝ)⁻¹ * avgOver (uniformDistribution (PauliTuple P)) (fun ω =>
        ‖applyOperatorToState
          (S.placeStrategySide p.side (S.twistedCommutator p.side ω))
          S.toStrategy.ψ‖ ^ 2) := by
    rw [← avgOver_const_mul]
    unfold opFamilyDistSq
    refine avgOver_congr _ _ _ (fun ω => ?_)
    rw [Finset.sum_congr rfl (fun bits _ => hpt ω bits), Finset.sum_const,
      hcard, nsmul_eq_mul]
    push_cast
    ring
  rw [hrw]
  have hbound := h P ε S p.side hε
  have hs : (0 : ℝ) ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  have hnn : (0 : ℝ) ≤ avgOver (uniformDistribution (PauliTuple P)) (fun ω =>
      ‖applyOperatorToState
        (S.placeStrategySide p.side (S.twistedCommutator p.side ω))
        S.toStrategy.ψ‖ ^ 2) :=
    avgOver_nonneg _ _ (fun _ => by positivity)
  nlinarith

end ProjectiveSetting

end

end MIPStarRE.QPBT
