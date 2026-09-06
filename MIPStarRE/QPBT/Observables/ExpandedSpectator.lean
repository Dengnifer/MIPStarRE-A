import MIPStarRE.QPBT.Observables.ExpandedDefs

/-!
# Removing the unused EPR registers from the expanded state

The opposite placements `AA'`, `BA''` use the ancillary pair `A'A''`, whereas
`BB'`, `AB''` use `B'B''`. The other EPR pair contributes its squared norm, which
is one. The identities below retain the full complex expectation of arbitrary
operators. In the Bob-first order the original strategy state is explicitly
reindexed from `AB` to `BA`; the two player spaces may be different.

These are Lean-only coordinate identities supporting the expanded-state
construction, not consistency estimates.

## References

- Paper `eq:def-psihat`,
  `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:367-372`.
- The two register partitions at the same source, lines 433-450.
- Blueprint `def:expanded-state` and `def:symmetric-equivalents`.
- Issue #273.
-/

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum
open Classical

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

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

/-- The four-register state on `AA'BA''`, obtained from the original state and
the EPR pair on `A'A''` by the explicit four-factor shuffle. This is a Lean-only
restriction of `eq:def-psihat` to its first register partition. -/
noncomputable def psiHatAlicePair (S : ProjectiveSetting P ε) :
    EuclideanSpace ℂ (S.ExpandedLocalSpace .alice × S.ExpandedLocalSpace .bob) :=
  reindexState prodShuffle (vecTensor S.toStrategy.ψ (eprState (PauliRegister P)))

/-- The four-register state on `BB'AB''`. The original state is explicitly
reversed from `AB` to `BA` before adjoining the EPR pair on `B'B''`; no symmetry
of the strategy is used. This is a Lean-only restriction of `eq:def-psihat` to
its second register partition. -/
noncomputable def psiHatBobPair (S : ProjectiveSetting P ε) :
    EuclideanSpace ℂ (S.ExpandedLocalSpace .bob × S.ExpandedLocalSpace .alice) :=
  reindexState prodShuffle
    (vecTensor (reindexState (Equiv.prodComm _ _) S.toStrategy.ψ)
      (eprState (PauliRegister P)))

/-- Put `AA'BA''` and the unused pair `B'B''` into the six-register order of
`eq:def-psihat`. This is an explicit coordinate permutation. -/
def aliceSpectatorShuffle (S : ProjectiveSetting P ε) :
    ((S.ExpandedLocalSpace .alice × S.ExpandedLocalSpace .bob) ×
        (PauliRegister P × PauliRegister P)) ≃
      SixReg P S.toStrategy.ιA S.toStrategy.ιB where
  toFun p := ((p.1.1.1, (p.1.1.2, p.1.2.2)), (p.1.2.1, p.2))
  invFun p := (((p.1.1, p.1.2.1), (p.2.1, p.1.2.2)), p.2.2)
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

/-- Put `BB'AB''` and the unused pair `A'A''` into the six-register order of
`eq:def-psihat`. The permutation retains distinct original player spaces. -/
def bobSpectatorShuffle (S : ProjectiveSetting P ε) :
    ((S.ExpandedLocalSpace .bob × S.ExpandedLocalSpace .alice) ×
        (PauliRegister P × PauliRegister P)) ≃
      SixReg P S.toStrategy.ιA S.toStrategy.ιB where
  toFun p := ((p.1.2.1, p.2), (p.1.1.1, (p.1.1.2, p.1.2.2)))
  invFun p := (((p.2.1, p.2.2.1), (p.1.1, p.2.2.2)), p.1.2)
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

/-- Coordinate factorization of `eq:def-psihat` with the unused pair `B'B''`
last. The remaining pair is exactly the one used by `AA'`, `BA''`. -/
theorem psiHat_eq_alicePair_tensor_epr (S : ProjectiveSetting P ε) :
    S.psiHat = reindexState S.aliceSpectatorShuffle
      (vecTensor S.psiHatAlicePair (eprState (PauliRegister P))) := by
  ext p
  rfl

/-- Coordinate factorization of `eq:def-psihat` with the unused pair `A'A''`
last. The remaining pair is exactly the one used by `BB'`, `AB''`. -/
theorem psiHat_eq_bobPair_tensor_epr (S : ProjectiveSetting P ε) :
    S.psiHat = reindexState S.bobSpectatorShuffle
      (vecTensor S.psiHatBobPair (eprState (PauliRegister P))) := by
  ext p
  change (S.toStrategy.ψ (p.1.1, p.2.1) *
      eprState (PauliRegister P) p.1.2) * eprState (PauliRegister P) p.2.2 =
    (S.toStrategy.ψ (p.1.1, p.2.1) *
      eprState (PauliRegister P) p.2.2) * eprState (PauliRegister P) p.1.2
  exact mul_right_comm _ _ _

/-- Arbitrary operators on `AA'` and `BA''` multiply to their tensor product,
with the identity on `B'B''`, in the coordinates of `eq:def-psihat`. -/
theorem place_AA'_mul_BA'' (S : ProjectiveSetting P ε)
    (A : Op (S.ExpandedLocalSpace .alice)) (B : Op (S.ExpandedLocalSpace .bob)) :
    S.place .AA' A * S.place .BA'' B =
      reindexOp S.aliceSpectatorShuffle.symm
        (heteroKron (heteroKron A B) (1 : Op (PauliRegister P × PauliRegister P))) := by
  classical
  ext i j
  simp [Matrix.mul_apply, Fintype.sum_prod_type, place, reindexOp, heteroKron,
    aliceSpectatorShuffle, Matrix.one_apply, mul_ite, ite_mul, Prod.ext_iff,
    ite_and]
  split_ifs <;> rfl

/-- Arbitrary operators on `BB'` and `AB''` multiply to their tensor product,
with the identity on `A'A''`, in the coordinates of `eq:def-psihat`. -/
theorem place_BB'_mul_AB'' (S : ProjectiveSetting P ε)
    (B : Op (S.ExpandedLocalSpace .bob)) (A : Op (S.ExpandedLocalSpace .alice)) :
    S.place .BB' B * S.place .AB'' A =
      reindexOp S.bobSpectatorShuffle.symm
        (heteroKron (heteroKron B A) (1 : Op (PauliRegister P × PauliRegister P))) := by
  classical
  ext i j
  simp [Matrix.mul_apply, Fintype.sum_prod_type, place, reindexOp, heteroKron,
    bobSpectatorShuffle, Matrix.one_apply, mul_ite, ite_mul, mul_comm, Prod.ext_iff,
    ite_and]
  rfl

/-- Removing the unused pair `B'B''` preserves the complex expectation of an
arbitrary product on `AA'`, `BA''`. The four-register state retains the EPR pair
on `A'A''`. This is a Lean-only exact identity for `eq:def-psihat`, requiring
neither positivity of the operators nor symmetry of the strategy. -/
theorem psiHat_expectation_AA'_BA'' (S : ProjectiveSetting P ε)
    (A : Op (S.ExpandedLocalSpace .alice)) (B : Op (S.ExpandedLocalSpace .bob)) :
    inner ℂ S.psiHat (applyOperatorToState (S.place .AA' A * S.place .BA'' B) S.psiHat) =
      inner ℂ S.psiHatAlicePair
        (applyOperatorToState (heteroKron A B) S.psiHatAlicePair) := by
  rw [place_AA'_mul_BA'', psiHat_eq_alicePair_tensor_epr]
  exact inner_reindex_tensor_epr_one S.aliceSpectatorShuffle S.psiHatAlicePair (heteroKron A B)

/-- Removing the unused pair `A'A''` preserves the complex expectation of an
arbitrary product on `BB'`, `AB''`. The remaining state uses the original
strategy with explicitly reversed coordinates and the EPR pair on `B'B''`.
This is the second Lean-only spectator identity for `eq:def-psihat`. -/
theorem psiHat_expectation_BB'_AB'' (S : ProjectiveSetting P ε)
    (B : Op (S.ExpandedLocalSpace .bob)) (A : Op (S.ExpandedLocalSpace .alice)) :
    inner ℂ S.psiHat (applyOperatorToState (S.place .BB' B * S.place .AB'' A) S.psiHat) =
      inner ℂ S.psiHatBobPair
        (applyOperatorToState (heteroKron B A) S.psiHatBobPair) := by
  rw [place_BB'_mul_AB'', psiHat_eq_bobPair_tensor_epr]
  exact inner_reindex_tensor_epr_one S.bobSpectatorShuffle S.psiHatBobPair (heteroKron B A)

end ProjectiveSetting

end MIPStarRE.QPBT
