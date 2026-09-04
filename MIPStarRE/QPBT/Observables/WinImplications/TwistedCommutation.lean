import MIPStarRE.QPBT.Observables.WinImplications.AnticommutingObs

/-!
# The phase-signed commutation relation of the point observables

This module assembles the commuting and anticommuting halves into Equation
`eq:pts-obs-commutation` of `lem:qld-win-implications-obs`: on average over a
uniformly random tuple the two point observables commute up to the sign
`(-1)^gamma(omega)`, with error the square root of the test error.

## References

The declarations formalize the first assertion of
`lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:683-733`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:309-362`.
-/

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace WinImplications

/-! ## The unconditional bound on a difference of reflections -/

/-- The identity operator acts trivially on a state. Formalization-only support
for `def:strategy-observables`, blueprint
`ch14_qpbt_observables.tex:480-503`. -/
theorem applyOperatorToState_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) : applyOperatorToState (1 : Op ι) ψ = ψ := by
  ext i
  simp [applyOperatorToState]

/-- An isometry preserves the state-dependent norm. Formalization-only support
for `def:strategy-observables`, blueprint
`ch14_qpbt_observables.tex:480-503`. -/
theorem norm_applyOperatorToState_of_isometry {ι : Type} [Fintype ι]
    [DecidableEq ι] {U : Op ι} (hU : Uᴴ * U = 1) (ψ : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState U ψ‖ = ‖ψ‖ := by
  have h : ‖applyOperatorToState (U * 1) ψ‖ = ‖applyOperatorToState 1 ψ‖ :=
    MagicSquareRigidity.norm_applyOperatorToState_isometry_mul hU 1 ψ
  rwa [mul_one, applyOperatorToState_one] at h

/-- The product of two reflections is an isometry. Formalization-only support
for `eq:pts-obs-commutation`, paper
`14_analysis_of_the_pauli_basis_test.tex:309-354`. -/
theorem mul_conjTranspose_mul_self {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Op ι} (hA : Aᴴ * A = 1) (hB : Bᴴ * B = 1) :
    (A * B)ᴴ * (A * B) = 1 := by
  rw [Matrix.conjTranspose_mul]
  calc
    Bᴴ * Aᴴ * (A * B) = Bᴴ * (Aᴴ * A) * B := by noncomm_ring
    _ = Bᴴ * B := by rw [hA, mul_one]
    _ = 1 := hB

/-- Both sides of the twisted commutation relation are unit vectors, so their
distance is bounded by two for every tuple. This is the unconditional bound
used when the error parameter exceeds one; paper
`14_analysis_of_the_pauli_basis_test.tex:309-362`, blueprint
`ch14_qpbt_observables.tex:683-733`. -/
theorem norm_twistedCommutator_sq_le_four {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (ω : PauliTuple P) :
    ‖applyOperatorToState
        (heteroKron (S.pointObs .alice .X ω.2.2.1 ω.1 *
            S.pointObs .alice .Z ω.2.2.2 ω.2.1) (1 : Op S.toStrategy.ιB) -
          phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
            heteroKron (S.pointObs .alice .Z ω.2.2.2 ω.2.1 *
              S.pointObs .alice .X ω.2.2.1 ω.1) (1 : Op S.toStrategy.ιB))
        S.toStrategy.ψ‖ ^ 2 ≤ 4 := by
  set X : Op S.toStrategy.ιA := S.pointObs .alice .X ω.2.2.1 ω.1 with hX
  set Z : Op S.toStrategy.ιA := S.pointObs .alice .Z ω.2.2.2 ω.2.1 with hZ
  have hXh : Xᴴ = X := (S.pointObs_isHermitian .alice .X ω.2.2.1 ω.1).eq
  have hZh : Zᴴ = Z := (S.pointObs_isHermitian .alice .Z ω.2.2.2 ω.2.1).eq
  have hXref : Xᴴ * X = 1 := by
    rw [hXh]
    exact S.pointObs_sq_eq_one .alice .X ω.2.2.1 ω.1
  have hZref : Zᴴ * Z = 1 := by
    rw [hZh]
    exact S.pointObs_sq_eq_one .alice .Z ω.2.2.2 ω.2.1
  have hXZ := heteroKron_left_isometry (ιB := S.toStrategy.ιB) (X * Z)
    (mul_conjTranspose_mul_self hXref hZref)
  have hZX := heteroKron_left_isometry (ιB := S.toStrategy.ιB) (Z * X)
    (mul_conjTranspose_mul_self hZref hXref)
  have h1 : ‖applyOperatorToState
      (heteroKron (X * Z) (1 : Op S.toStrategy.ιB)) S.toStrategy.ψ‖ = 1 := by
    rw [norm_applyOperatorToState_of_isometry hXZ]
    exact S.toStrategy.ψ_norm
  have h2 : ‖applyOperatorToState
      (phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
        heteroKron (Z * X) (1 : Op S.toStrategy.ιB)) S.toStrategy.ψ‖ = 1 := by
    rw [applyOperatorToState_smul_op, norm_smul, norm_phaseSign,
      norm_applyOperatorToState_of_isometry hZX, S.toStrategy.ψ_norm, one_mul]
  have hsub : ‖applyOperatorToState
      (heteroKron (X * Z) (1 : Op S.toStrategy.ιB) -
        phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
          heteroKron (Z * X) (1 : Op S.toStrategy.ιB)) S.toStrategy.ψ‖ ≤ 2 := by
    rw [MagicSquareRigidity.applyOperatorToState_sub_op]
    calc
      _ ≤ ‖applyOperatorToState (heteroKron (X * Z)
            (1 : Op S.toStrategy.ιB)) S.toStrategy.ψ‖ +
          ‖applyOperatorToState
            (phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
              heteroKron (Z * X) (1 : Op S.toStrategy.ιB))
            S.toStrategy.ψ‖ := norm_sub_le _ _
      _ = 2 := by rw [h1, h2]; norm_num
  have key : ‖applyOperatorToState
      (heteroKron (X * Z) (1 : Op S.toStrategy.ιB) -
        phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
          heteroKron (Z * X) (1 : Op S.toStrategy.ιB))
      S.toStrategy.ψ‖ ^ 2 ≤ 4 := by
    nlinarith [hsub, norm_nonneg (applyOperatorToState
      (heteroKron (X * Z) (1 : Op S.toStrategy.ιB) -
        phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
          heteroKron (Z * X) (1 : Op S.toStrategy.ιB)) S.toStrategy.ψ)]
  exact key

/-! ## Splitting the uniform average -/

/-- A gated uniform average is bounded by the corresponding conditional
average. Formalization-only support for the case split of
`eq:pts-obs-commutation`, paper
`14_analysis_of_the_pauli_basis_test.tex:309-362`. -/
theorem avgOver_gated_le {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (p : X → Prop) [DecidablePred p] (hp : (Finset.univ.filter p).Nonempty)
    (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) {K : ℝ}
    (hK : avgOver (Distribution.uniformOnFinset (Finset.univ.filter p)) f ≤ K) :
    avgOver (uniformDistribution X) (fun x => if p x then f x else 0) ≤ K := by
  rw [← cardRatio_mul_avgOver_filter p hp f]
  have hA : 0 ≤ avgOver
      (Distribution.uniformOnFinset (Finset.univ.filter p)) f :=
    avgOver_nonneg _ _ hf
  have hratio : ((Finset.univ.filter p).card : ℝ) / Fintype.card X ≤ 1 := by
    rw [div_le_one (by exact_mod_cast Fintype.card_pos)]
    exact_mod_cast Finset.card_le_univ _
  have hratio0 : 0 ≤ ((Finset.univ.filter p).card : ℝ) / Fintype.card X := by
    positivity
  nlinarith

/-- The commuting event is nonempty. Paper
`14_analysis_of_the_pauli_basis_test.tex:70-77`, blueprint
`ch14_qpbt_observables.tex:151-178`. -/
theorem commuting_filter_nonempty (P : AdmissibleParams) :
    (Finset.univ.filter (@IsCommuting P)).Nonempty := by
  refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  simp [IsCommuting, gammaValue, fixedBinTrace, binTrace, dotProduct]

/-- The anticommuting event is nonempty. Paper
`14_analysis_of_the_pauli_basis_test.tex:70-77`, blueprint
`ch14_qpbt_observables.tex:151-178`. -/
theorem anticommuting_filter_nonempty (P : AdmissibleParams) :
    (Finset.univ.filter (@IsAnticommuting P)).Nonempty := by
  by_contra h
  have hempty : Finset.univ.filter (@IsAnticommuting P) = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp h
  have hprob := anticommTupleDist_isProbability P
  unfold anticommTupleDist Distribution.IsProbability
    Distribution.totalWeight at hprob
  rw [hempty] at hprob
  simp at hprob

/-- Splitting a uniform average over the commuting and anticommuting events.
Formalization-only support for `eq:pts-obs-commutation`, paper
`14_analysis_of_the_pauli_basis_test.tex:309-362`. -/
theorem avgOver_uniform_split_le (P : AdmissibleParams)
    (f : PauliTuple P → ℝ) (hf : ∀ ω, 0 ≤ f ω) {Kc Ka : ℝ}
    (hc : avgOver (commTupleDist P) f ≤ Kc)
    (ha : avgOver (anticommTupleDist P) f ≤ Ka) :
    avgOver (uniformDistribution (PauliTuple P)) f ≤ Kc + Ka := by
  classical
  have hsplit : avgOver (uniformDistribution (PauliTuple P)) f =
      avgOver (uniformDistribution (PauliTuple P))
          (fun ω => if IsCommuting ω then f ω else 0) +
        avgOver (uniformDistribution (PauliTuple P))
          (fun ω => if IsAnticommuting ω then f ω else 0) := by
    rw [← avgOver_add]
    refine avgOver_congr _ _ _ ?_
    intro ω
    by_cases h : IsCommuting ω
    · have hna : ¬ IsAnticommuting ω := by
        simp only [IsAnticommuting, not_not]
        exact h
      simp [h, hna]
    · have hna : IsAnticommuting ω := by
        simpa [IsAnticommuting, IsCommuting] using h
      simp [h, hna]
  rw [hsplit]
  exact add_le_add
    (avgOver_gated_le (@IsCommuting P) (commuting_filter_nonempty P) f hf hc)
    (avgOver_gated_le (@IsAnticommuting P) (anticommuting_filter_nonempty P) f
      hf ha)

/-! ## The twisted commutation relation -/

/-- The strategy observables satisfy the phase-signed commutation relation on
Alice's factor. This is Equation `eq:pts-obs-commutation`, paper
`14_analysis_of_the_pauli_basis_test.tex:309-354`, blueprint
`ch14_qpbt_observables.tex:683-733`. -/
theorem pointObs_twisted_commutation_proof :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε →
      opDistSq (uniformDistribution (PauliTuple P))
        (fun ω => heteroKron
          (S.pointObs .alice .X ω.2.2.1 ω.1 *
            S.pointObs .alice .Z ω.2.2.2 ω.2.1) 1)
        (fun ω => phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
          heteroKron
            (S.pointObs .alice .Z ω.2.2.2 ω.2.1 *
              S.pointObs .alice .X ω.2.2.1 ω.1) 1)
        S.toStrategy.ψ ≤ C * Real.sqrt ε := by
  classical
  obtain ⟨Cc, hCc, hcomm⟩ := exists_pointObs_commutator_comm_le
  obtain ⟨Ca, hCa, hanti⟩ := exists_pointObs_anticommutator_anticomm_le
  refine ⟨2 * Cc + Ca + 4, by linarith, ?_⟩
  intro P ε S hε
  rw [opDistSq_eq_avgOver]
  set f : PauliTuple P → ℝ := fun ω =>
    ‖applyOperatorToState
      (heteroKron (S.pointObs .alice .X ω.2.2.1 ω.1 *
          S.pointObs .alice .Z ω.2.2.2 ω.2.1) (1 : Op S.toStrategy.ιB) -
        phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
          heteroKron (S.pointObs .alice .Z ω.2.2.2 ω.2.1 *
            S.pointObs .alice .X ω.2.2.1 ω.1) (1 : Op S.toStrategy.ιB))
      S.toStrategy.ψ‖ ^ 2 with hfdef
  have hfnn : ∀ ω, 0 ≤ f ω := by
    intro ω
    rw [hfdef]
    positivity
  have hsq : (0 : ℝ) ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  -- the commuting conditional average
  have hcbound : avgOver (commTupleDist P) f ≤ Cc * (ε + Real.sqrt ε) := by
    have hcongr : avgOver (commTupleDist P) f =
        avgOver (commTupleDist P) (fun ω =>
          ‖applyOperatorToState
            (heteroKron (S.pointObs .alice .X ω.2.2.1 ω.1 *
                S.pointObs .alice .Z ω.2.2.2 ω.2.1)
                (1 : Op S.toStrategy.ιB) -
              heteroKron (S.pointObs .alice .Z ω.2.2.2 ω.2.1 *
                S.pointObs .alice .X ω.2.2.1 ω.1)
                (1 : Op S.toStrategy.ιB)) S.toStrategy.ψ‖ ^ 2) := by
      refine avgOver_congr_on_support _ _ _ ?_
      intro ω hω
      have hIs : IsCommuting ω := by
        rw [commTupleDist, Distribution.uniformOnFinset_support,
          Finset.mem_filter] at hω
        exact hω.2
      have hph : phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) = 1 := by
        rw [show gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2 = 0 from hIs]
        simp [phaseSign]
      simp only [hfdef]
      rw [hph, one_smul]
    rw [hcongr]
    exact hcomm P ε S hε
  -- the anticommuting conditional average
  have habound : avgOver (anticommTupleDist P) f ≤ Ca * ε := by
    have hcongr : avgOver (anticommTupleDist P) f =
        avgOver (anticommTupleDist P) (fun ω =>
          ‖applyOperatorToState
            (heteroKron (S.pointObs .alice .X ω.2.2.1 ω.1 *
                S.pointObs .alice .Z ω.2.2.2 ω.2.1)
                (1 : Op S.toStrategy.ιB) +
              heteroKron (S.pointObs .alice .Z ω.2.2.2 ω.2.1 *
                S.pointObs .alice .X ω.2.2.1 ω.1)
                (1 : Op S.toStrategy.ιB)) S.toStrategy.ψ‖ ^ 2) := by
      refine avgOver_congr_on_support _ _ _ ?_
      intro ω hω
      have hIs : IsAnticommuting ω := by
        rw [anticommTupleDist, Distribution.uniformOnFinset_support,
          Finset.mem_filter] at hω
        exact hω.2
      have hone : gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2 = 1 := by
        have h := hIs
        rw [IsAnticommuting] at h
        revert h
        generalize gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2 = t
        revert t
        decide
      have hph : phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) = -1 := by
        rw [hone]
        simp [phaseSign, show (1 : ZMod 2) ≠ 0 from by decide]
      simp only [hfdef]
      rw [hph, neg_one_smul, sub_neg_eq_add]
    rw [hcongr]
    exact hanti P ε S hε
  have hmain : avgOver (uniformDistribution (PauliTuple P)) f ≤
      Cc * (ε + Real.sqrt ε) + Ca * ε :=
    avgOver_uniform_split_le P f hfnn hcbound habound
  have htriv : avgOver (uniformDistribution (PauliTuple P)) f ≤ 4 := by
    refine le_trans (avgOver_mono _ _ (fun _ => (4 : ℝ)) ?_) ?_
    · intro ω
      rw [hfdef]
      exact norm_twistedCommutator_sq_le_four S ω
    · exact le_of_eq (avgOver_const_of_isProbability _
        (uniformDistribution_isProbability (PauliTuple P)) 4)
  have hs2 : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε
  have hCc0 : (0 : ℝ) ≤ Cc := by linarith
  have hCa0 : (0 : ℝ) ≤ Ca := by linarith
  by_cases hle : ε ≤ 1
  · have hsle : Real.sqrt ε ≤ 1 := by nlinarith
    have hεsq : ε ≤ Real.sqrt ε := by nlinarith
    have h1 : Cc * (ε + Real.sqrt ε) + Ca * ε ≤
        (2 * Cc + Ca) * Real.sqrt ε := by
      nlinarith [mul_le_mul_of_nonneg_left hεsq hCc0,
        mul_le_mul_of_nonneg_left hεsq hCa0]
    have h2 : (2 * Cc + Ca) * Real.sqrt ε ≤
        (2 * Cc + Ca + 4) * Real.sqrt ε := by nlinarith [hsq]
    linarith
  · have hgt : (1 : ℝ) < ε := not_le.mp hle
    have hone : (1 : ℝ) ≤ Real.sqrt ε := by nlinarith
    have h3 : (4 : ℝ) ≤ (2 * Cc + Ca + 4) * Real.sqrt ε := by
      nlinarith [hone, hCc0, hCa0]
    linarith

end WinImplications

end

end MIPStarRE.QPBT
