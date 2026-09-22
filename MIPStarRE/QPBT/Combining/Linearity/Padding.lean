import MIPStarRE.QPBT.Combining.Linearity
import MIPStarRE.QPBT.Observables.ExpandedDefs
import MIPStarRE.QPBT.Test.Completeness

/-!
# Obstructions to absorbing the linearity ancilla

The common Fourier--Naimark ancilla has dimension `2 ^ t + 1`. Its uniformity
does not identify the enlarged space with an already fixed finite local space.
The results below record necessary distinctions for the zero-state padding
construction; they do not assert that the source's padding has been supplied.

## References

The zero-state convention and its use are in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:160-172,367-372,825-832`.
See blueprint `rem:linearity-import` and
`docs/paper-gaps/qpbt_linearity-theorem-quotation.tex`, issue #697.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum
open scoped BigOperators Matrix ComplexOrder

/-- Formalization-only obstruction to absorbing the entire common-ancilla
extension into its original finite space. Such an absorption would multiply
the dimension by `2 ^ t + 1` and then inject it into the original dimension.
This does not rule out using a smaller space with an independently reserved
zero-state register, as assumed at paper
`14_analysis_of_the_pauli_basis_test.tex:825-832`; see
`docs/paper-gaps/qpbt_linearity-theorem-quotation.tex`, issue #697. -/
theorem not_nonempty_linearity_ancilla_isometry (t : ℕ) (ι : Type*)
    [Fintype ι] [Nonempty ι] :
    ¬ Nonempty (EuclideanSpace ℂ (ι × Option (Fin t → ZMod 2)) →ₗᵢ[ℂ]
      EuclideanSpace ℂ ι) := by
  rintro ⟨V⟩
  have hdim := V.toLinearMap.finrank_le_finrank_of_injective V.injective
  simp only [finrank_euclideanSpace, Fintype.card_prod, Fintype.card_option] at hdim
  have hι := Fintype.card_pos (α := ι)
  have hcube := Fintype.card_pos (α := Fin t → ZMod 2)
  nlinarith

/-- A positive definite local state cannot acquire the canonical pure
linearity ancilla by an invertible change of coordinates on the same space.
The right-hand side has zero diagonal on every `some u` coordinate, whereas
positive definiteness is preserved by invertible conjugation. In particular,
the maximally mixed reduced state of an EPR pair has no such reserved factor.

This is a formalization-only obstruction, not a refutation of the source's
permission to pad the strategy in advance at paper
`14_analysis_of_the_pauli_basis_test.tex:160-172,367-372`. The distinction is
recorded in `docs/paper-gaps/qpbt_linearity-theorem-quotation.tex`, issue #697. -/
theorem posDef_ne_linearity_ancilla_conjugate (t : ℕ) (ι : Type*)
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ρ : Op (ι × Option (Fin t → ZMod 2))) (hρ : ρ.PosDef)
    (σ : Op ι) (U : Op (ι × Option (Fin t → ZMod 2))) (hU : IsUnit U) :
    U * ρ * Uᴴ ≠ heteroKron σ (ancProj (naimarkAncilla t)) := by
  intro heq
  have hpos : (U * ρ * Uᴴ).PosDef :=
    (Matrix.IsUnit.posDef_star_right_conjugate_iff hU).mpr hρ
  rw [heq] at hpos
  have hdiag := hpos.diag_pos (i := (Classical.arbitrary ι, some 0))
  simp [heteroKron, ancProj, naimarkAncilla, Matrix.vecMulVec_apply] at hdiag

/-- Every admissible parameter tuple admits a projective setting whose expanded
Alice state has full support: any local operator fixing the expanded state is
the identity. In particular, no proper projection onto a reserved zero-state
sector can fix this state. The witness uses the honest strategy's EPR state
and its actual rejection probability as `ε`; only `ε ≥ 0` is asserted here.

This formalization-only counterexample shows that `ProjectiveSetting` alone
does not encode the padding convention of paper
`14_analysis_of_the_pauli_basis_test.tex:160-172,367-372,825-832`. It does not
refute that convention or the combined-point conclusion; see
`docs/paper-gaps/qpbt_linearity-theorem-quotation.tex`, issue #697. -/
theorem exists_projectiveSetting_no_proper_alice_support (P : AdmissibleParams) :
    ∃ ε : ℝ, 0 ≤ ε ∧ ∃ S : ProjectiveSetting P ε,
      ∀ R : Op (S.ExpandedLocalSpace .alice),
        applyOperatorToState (S.place .AA' R) S.psiHat = S.psiHat → R = 1 := by
  classical
  let T : Strategy (pauliBasisTest P) := (honestStrategy P).toStrategy
  let S : ProjectiveSetting P (1 - T.value) :=
    ⟨T, ⟨honestStrategy_projective P, honestStrategy_projective P⟩, by linarith⟩
  refine ⟨1 - T.value, sub_nonneg.mpr T.value_le_one, S, ?_⟩
  change ∀ R : Op (HonestIndex P × PauliRegister P),
    applyOperatorToState (S.place .AA' R) S.psiHat = S.psiHat →
      R = (1 : Op (HonestIndex P × PauliRegister P))
  intro R hR
  let c : ℂ := (Real.sqrt (Fintype.card (HonestIndex P) : ℝ) : ℂ)⁻¹
  let d : ℂ := (Real.sqrt (Fintype.card (PauliRegister P) : ℝ) : ℂ)⁻¹
  have hψ (p : SixReg P T.ιA T.ιB) : S.psiHat p =
      (if p.1.1 = p.2.1 then c else 0) *
      (if p.1.2.1 = p.1.2.2 then d else 0) *
      (if p.2.2.1 = p.2.2.2 then d else 0) := rfl
  ext ⟨i, a⟩ ⟨j, b⟩
  have h := congrArg (fun v => v ((i, (a, b)), (j, (0, 0)))) hR
  change (S.place .AA' R).mulVec S.psiHat ((i, (a, b)), (j, (0, 0))) =
    S.psiHat ((i, (a, b)), (j, (0, 0))) at h
  change (∑ x : SixReg P T.ιA T.ιB,
    S.place .AA' R ((i, (a, b)), (j, (0, 0))) x * S.psiHat x) = _ at h
  simp only [hψ, ProjectiveSetting.place, SixReg, Fintype.sum_prod_type,
    Matrix.one_apply, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, if_true] at h
  dsimp only [S, T, honestStrategy, SymmetricStrategy.toStrategy,
    ProjectiveSetting.LocalSpace] at h
  simp at h
  have hc : c ≠ 0 := by dsimp [c]; positivity
  have hd : d ≠ 0 := by dsimp [d]; positivity
  apply mul_right_cancel₀ (mul_ne_zero (mul_ne_zero hc hd) hd)
  by_cases hij : i = j <;> by_cases hab : a = b
  all_goals
    simp [Matrix.one_apply, hij, hab] at h ⊢
    convert h using 1
    rfl

end MIPStarRE.QPBT
