import MIPStarRE.QPBT.Combining.ExtendedLineGame.StateTransport

/-!
# Removing the unused EPR registers from the expanded state

The opposite placements `AA'`, `BA''` use the ancillary pair `A'A''`, whereas
`AB''`, `BB'` use `B'B''`. The other EPR pair contributes its squared norm,
which is one. The identities below retain the full complex expectation of
arbitrary operators, strengthening the Hermitian `stateQForm` transport of
`ExtendedLineGame.StateTransport`, which they share the two-player state
`ExtendedLineGame.pairState` and the two regroupings with.

These are Lean-only coordinate identities supporting the expanded-state
construction, not consistency estimates.

## References

- Paper `eq:def-psihat`,
  `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:367-372`.
- The two register partitions at the same source, lines 433-450.
- Blueprint `def:expanded-state` and `def:symmetric-equivalents`.
- Issue #273.
-/

-- The six-register products require the same instance-search size as ExpandedPlacement.
set_option synthInstance.maxSize 400

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum
open ProjectiveSetting

/-- The unused normalized EPR pair contributes one to the complex expectation.
This coordinate calculation is specialized to an identity operator on the
spectator, as required by `eq:def-psihat`. -/
private theorem inner_reindex_tensor_epr_one {ι κ V : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype V] [DecidableEq V] [Nonempty V]
    (e : (ι × (V × V)) ≃ κ) (ψ : EuclideanSpace ℂ ι) (M : Op ι) :
    inner ℂ (reindexState e (vecTensor ψ (eprState V)))
      (applyOperatorToState (reindexOp e.symm (heteroKron M (1 : Op (V × V))))
        (reindexState e (vecTensor ψ (eprState V)))) =
      inner ℂ ψ (applyOperatorToState M ψ) := by
  let η := eprState V
  let v : ι × (V × V) → ℂ := fun p => ψ p.1 * η p.2
  have hη : (∑ r : V × V, η r * star (η r)) = (1 : ℂ) := by
    change inner ℂ η η = 1
    simp [η, inner_self_eq_norm_sq_to_K, eprState_norm]
  have hact (p : ι × (V × V)) :
      ((heteroKron M (1 : Op (V × V))) *ᵥ v) p =
        (M *ᵥ ψ.ofLp) p.1 * η p.2 := by
    simp [heteroKron, Matrix.mulVec, dotProduct, v, Fintype.sum_prod_type,
      Matrix.one_apply, mul_ite, ite_mul, mul_assoc, Finset.sum_mul]
  simp only [EuclideanSpace.inner_eq_star_dotProduct]
  change (((heteroKron M (1 : Op (V × V))).submatrix e.symm e.symm) *ᵥ
      (v ∘ e.symm)) ⬝ᵥ (star v ∘ e.symm) = (M *ᵥ ψ.ofLp) ⬝ᵥ star ψ.ofLp
  rw [Matrix.submatrix_mulVec_equiv]
  simp only [Function.comp_def, Equiv.symm_symm, Equiv.symm_apply_apply]
  change (((heteroKron M (1 : Op (V × V))) *ᵥ v) ∘ e.symm) ⬝ᵥ
      (star v ∘ e.symm) = (M *ᵥ ψ.ofLp) ⬝ᵥ star ψ.ofLp
  rw [comp_equiv_dotProduct_comp_equiv]
  simp only [dotProduct, hact, Pi.star_apply]
  calc
    (∑ p : ι × (V × V), (M *ᵥ ψ.ofLp) p.1 * η p.2 * star (v p)) =
        ∑ i : ι, ∑ r : V × V,
          ((M *ᵥ ψ.ofLp) i * star (ψ i)) * (η r * star (η r)) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro r _
      simp only [v, star_mul]
      ring
    _ = ∑ i : ι, (M *ᵥ ψ.ofLp) i * star (ψ i) := by
      simp_rw [← Finset.mul_sum, hη, mul_one]

namespace ExtendedLineGame

variable {P : AdmissibleParams} {epsilon : Real}

/-- The inverse reading of `reindexState_aaBaRegrouping_psiHat`: the expanded
state of `eq:def-psihat` is the two-player state `pairState` together with the
unused pair `B'B''`, put back into the six-register order. -/
theorem psiHat_eq_reindexState_aaBaRegrouping_symm
    (setting : ProjectiveSetting P epsilon) :
    setting.psiHat = reindexState (aaBaRegrouping setting).symm
      (vecTensor (pairState setting) (eprState (PauliRegister P))) := by
  rw [← reindexState_aaBaRegrouping_psiHat setting]
  ext p
  rfl

/-- The inverse reading of `reindexState_abBbRegrouping_psiHat`. The two-player
state is the same `pairState`; the unused pair is `A'A''`. -/
theorem psiHat_eq_reindexState_abBbRegrouping_symm
    (setting : ProjectiveSetting P epsilon) :
    setting.psiHat = reindexState (abBbRegrouping setting).symm
      (vecTensor (pairState setting) (eprState (PauliRegister P))) := by
  rw [← reindexState_abBbRegrouping_psiHat setting]
  ext p
  rfl

/-- Arbitrary operators on `AA'` and `BA''` multiply to their tensor product,
with the identity on the unused pair `B'B''`, in the coordinates of
`eq:def-psihat`. This is the operator half of the `AA'`--`BA''` transport, here
without the Hermiticity used by `stateQForm_pairState_eq_AA'_BA''`. -/
theorem reindexOp_aaBaRegrouping_heteroKron (setting : ProjectiveSetting P epsilon)
    (A : Op (setting.ExpandedLocalSpace .alice))
    (B : Op (setting.ExpandedLocalSpace .bob)) :
    reindexOp (aaBaRegrouping setting)
        (heteroKron (heteroKron A B)
          (1 : Op (PauliRegister P × PauliRegister P))) =
      setting.place .AA' A * setting.place .BA'' B := by
  let I : Op (PauliRegister P × PauliRegister P) := 1
  change Op (setting.toStrategy.ιA × PauliRegister P) at A
  change Op (setting.toStrategy.ιB × PauliRegister P) at B
  change reindexOp (aaBaBipartition P setting.toStrategy.ιA setting.toStrategy.ιB)
    (reindexOp (Equiv.prodAssoc _ _ _).symm (heteroKron (heteroKron A B) I)) = _
  rw [show reindexOp (Equiv.prodAssoc _ _ _).symm
      (heteroKron (heteroKron A B) I) = heteroKron A (heteroKron B I) from
    Matrix.kronecker_assoc A B I]
  rw [show heteroKron A (heteroKron B I) =
      heteroKron A 1 * heteroKron 1 (heteroKron B I) by
    rw [heteroKron_mul, Matrix.mul_one, Matrix.one_mul]]
  exact (WinImplications.reindexOp_mul _ _ _).trans
    (congrArg₂ (fun X Y => X * Y)
      (reindexOp_aaBaBipartition_left setting A)
      (reindexOp_aaBaBipartition_right setting B))

/-- Arbitrary operators on `AB''` and `BB'` multiply to their tensor product,
with the identity on the unused pair `A'A''`. This is the second orientation of
the operator half, matching `stateQForm_pairState_eq_AB''_BB'`. -/
theorem reindexOp_abBbRegrouping_heteroKron (setting : ProjectiveSetting P epsilon)
    (A : Op (setting.ExpandedLocalSpace .alice))
    (B : Op (setting.ExpandedLocalSpace .bob)) :
    reindexOp (abBbRegrouping setting)
        (heteroKron (heteroKron A B)
          (1 : Op (PauliRegister P × PauliRegister P))) =
      setting.place .AB'' A * setting.place .BB' B := by
  let I : Op (PauliRegister P × PauliRegister P) := 1
  change Op (setting.toStrategy.ιA × PauliRegister P) at A
  change Op (setting.toStrategy.ιB × PauliRegister P) at B
  change reindexOp (abBbBipartition P setting.toStrategy.ιA setting.toStrategy.ιB)
    (reindexOp (Equiv.prodAssoc _ _ _).symm (heteroKron (heteroKron A B) I)) = _
  rw [show reindexOp (Equiv.prodAssoc _ _ _).symm
      (heteroKron (heteroKron A B) I) = heteroKron A (heteroKron B I) from
    Matrix.kronecker_assoc A B I]
  rw [show heteroKron A (heteroKron B I) =
      heteroKron A 1 * heteroKron 1 (heteroKron B I) by
    rw [heteroKron_mul, Matrix.mul_one, Matrix.one_mul]]
  exact (WinImplications.reindexOp_mul _ _ _).trans
    (congrArg₂ (fun X Y => X * Y)
      (reindexOp_abBbBipartition_left setting A)
      (reindexOp_abBbBipartition_right setting B))

/-- Removing the unused pair `B'B''` preserves the complex expectation of an
arbitrary product on `AA'`, `BA''`. This is a Lean-only exact identity for
`eq:def-psihat`; unlike `stateQForm_pairState_eq_AA'_BA''` it requires neither
Hermiticity nor positivity of the operators, and no symmetry of the strategy. -/
theorem psiHat_expectation_AA'_BA'' (setting : ProjectiveSetting P epsilon)
    (A : Op (setting.ExpandedLocalSpace .alice))
    (B : Op (setting.ExpandedLocalSpace .bob)) :
    inner ℂ setting.psiHat
        (applyOperatorToState (setting.place .AA' A * setting.place .BA'' B)
          setting.psiHat) =
      inner ℂ (pairState setting)
        (applyOperatorToState (heteroKron A B) (pairState setting)) := by
  rw [← reindexOp_aaBaRegrouping_heteroKron setting A B,
    psiHat_eq_reindexState_aaBaRegrouping_symm setting]
  exact inner_reindex_tensor_epr_one (aaBaRegrouping setting).symm
    (pairState setting) (heteroKron A B)

/-- Removing the unused pair `A'A''` preserves the complex expectation of an
arbitrary product on `AB''`, `BB'`. The remaining state is the same `pairState`,
because an EPR pair is invariant under exchanging its registers. This is the
second Lean-only spectator identity for `eq:def-psihat`. -/
theorem psiHat_expectation_AB''_BB' (setting : ProjectiveSetting P epsilon)
    (A : Op (setting.ExpandedLocalSpace .alice))
    (B : Op (setting.ExpandedLocalSpace .bob)) :
    inner ℂ setting.psiHat
        (applyOperatorToState (setting.place .AB'' A * setting.place .BB' B)
          setting.psiHat) =
      inner ℂ (pairState setting)
        (applyOperatorToState (heteroKron A B) (pairState setting)) := by
  rw [← reindexOp_abBbRegrouping_heteroKron setting A B,
    psiHat_eq_reindexState_abBbRegrouping_symm setting]
  exact inner_reindex_tensor_epr_one (abBbRegrouping setting).symm
    (pairState setting) (heteroKron A B)

end ExtendedLineGame

end MIPStarRE.QPBT
