import MIPStarRE.QPBT.Observables.PointConsistency
import MIPStarRE.QPBT.Combining.Points.PlacementSupport

/-!
# Placement calculus on the expanded state

This module records the algebra of the four register placements used by the
combining argument: a placement is a unital `*`-homomorphism, placements on
opposite register pairs commute, and the crosswise exchange of the two EPR
pairs of the expanded state carries the placement `AA'` to `AB''` and `BA''`
to `BB'` while fixing the expanded state.  The last fact transfers every
state-dependent distance between the two bipartition schemes of
`def:symmetric-equivalents` without assuming a symmetric strategy.

## References

The placements are those of blueprint `def:symmetric-equivalents`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:420-450`.
The ancillary permutation exchanging the two EPR pairs crosswise gives the
same-side distance transfers needed here without symmetry of the strategy.
It is not `U_σ U_θ` and does not formalize the full blueprint lemma
`lem:symmetric-equivalents-transfer`. Its use for `lem:qld-4-10` is analyzed in
`docs/paper-gaps/qpbt_combined-points-direct.tex`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

/-! ## The crosswise exchange of the two EPR pairs -/

/-- The ancillary permutation exchanging the two EPR pairs crosswise:
`A'` with `B''` and `A''` with `B'`, leaving the strategy registers fixed.
This involution is distinct from `U_σ U_θ` in blueprint
`lem:symmetric-equivalents-transfer`. -/
def eprCrossSwap (P : AdmissibleParams) (ιA ιB : Type*) :
    SixReg P ιA ιB ≃ SixReg P ιA ιB where
  toFun := fun ⟨⟨a, a', a''⟩, b, b', b''⟩ => ((a, (b'', b')), (b, (a'', a')))
  invFun := fun ⟨⟨a, a', a''⟩, b, b', b''⟩ => ((a, (b'', b')), (b, (a'', a')))
  left_inv := by rintro ⟨⟨a, a', a''⟩, b, b', b''⟩; rfl
  right_inv := by rintro ⟨⟨a, a', a''⟩, b, b', b''⟩; rfl

/-- The EPR vector is symmetric in its two registers. -/
theorem eprState_ofLp_swap {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (x y : V) :
    (eprState V).ofLp (x, y) = (eprState V).ofLp (y, x) := by
  change (if x = y then (Real.sqrt (Fintype.card V : ℝ) : ℂ)⁻¹ else 0) =
    (if y = x then (Real.sqrt (Fintype.card V : ℝ) : ℂ)⁻¹ else 0)
  by_cases h : x = y
  · simp [h]
  · simp [h, Ne.symm h]

/-- The ancillary permutation exchanging the two EPR pairs crosswise fixes
the expanded state of blueprint `def:expanded-state`; only the symmetry of
the EPR vector is used, with no symmetry assumption on the strategy. -/
theorem reindexState_eprCrossSwap_psiHat (S : ProjectiveSetting P ε) :
    reindexState (eprCrossSwap P S.toStrategy.ιA S.toStrategy.ιB) S.psiHat =
      S.psiHat := by
  ext i
  obtain ⟨⟨a, a', a''⟩, b, b', b''⟩ := i
  change S.toStrategy.ψ.ofLp (a, b) * (eprState (PauliRegister P)).ofLp (b'', b') *
      (eprState (PauliRegister P)).ofLp (a'', a') =
    S.toStrategy.ψ.ofLp (a, b) * (eprState (PauliRegister P)).ofLp (a', a'') *
      (eprState (PauliRegister P)).ofLp (b', b'')
  rw [eprState_ofLp_swap b'' b', eprState_ofLp_swap a'' a']
  ring

/-- The crosswise EPR exchange carries the `AB''` placement to the `AA'`
placement. -/
theorem reindexOp_eprCrossSwap_place_AB'' (S : ProjectiveSetting P ε)
    (O : Op (S.ExpandedLocalSpace .alice)) :
    reindexOp (eprCrossSwap P S.toStrategy.ιA S.toStrategy.ιB)
      (S.place .AB'' O) = S.place .AA' O := by
  ext i j
  obtain ⟨⟨a, a', a''⟩, b, b', b''⟩ := i
  obtain ⟨⟨c, c', c''⟩, d, d', d''⟩ := j
  simp only [reindexOp, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, place, eprCrossSwap, Equiv.coe_fn_mk, Matrix.one_apply]
  ring!

/-- The crosswise EPR exchange carries the `BB'` placement to the `BA''`
placement. -/
theorem reindexOp_eprCrossSwap_place_BB' (S : ProjectiveSetting P ε)
    (O : Op (S.ExpandedLocalSpace .bob)) :
    reindexOp (eprCrossSwap P S.toStrategy.ιA S.toStrategy.ιB)
      (S.place .BB' O) = S.place .BA'' O := by
  ext i j
  obtain ⟨⟨a, a', a''⟩, b, b', b''⟩ := i
  obtain ⟨⟨c, c', c''⟩, d, d', d''⟩ := j
  simp only [reindexOp, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, place, eprCrossSwap, Equiv.coe_fn_mk, Matrix.one_apply]
  ring!

/-- An operator placed on `AB''` has, on the expanded state, the same norm as
the same operator placed on `AA'`, by the ancillary permutation exchanging
the two EPR pairs crosswise. This is a same-side transfer for the placements
of blueprint `def:symmetric-equivalents`. -/
theorem norm_place_AB''_eq_norm_place_AA' (S : ProjectiveSetting P ε)
    (O : Op (S.ExpandedLocalSpace .alice)) :
    ‖applyOperatorToState (S.place .AB'' O) S.psiHat‖ =
      ‖applyOperatorToState (S.place .AA' O) S.psiHat‖ := by
  conv_lhs => rw [← reindexState_eprCrossSwap_psiHat S]
  rw [WinImplications.norm_applyOperatorToState_reindexState,
    reindexOp_eprCrossSwap_place_AB'']

/-- An operator placed on `BB'` has, on the expanded state, the same norm as
the same operator placed on `BA''`, by the ancillary permutation exchanging
the two EPR pairs crosswise. This is a same-side transfer for the placements
of blueprint `def:symmetric-equivalents`. -/
theorem norm_place_BB'_eq_norm_place_BA'' (S : ProjectiveSetting P ε)
    (O : Op (S.ExpandedLocalSpace .bob)) :
    ‖applyOperatorToState (S.place .BB' O) S.psiHat‖ =
      ‖applyOperatorToState (S.place .BA'' O) S.psiHat‖ := by
  conv_lhs => rw [← reindexState_eprCrossSwap_psiHat S]
  rw [WinImplications.norm_applyOperatorToState_reindexState,
    reindexOp_eprCrossSwap_place_BB']

/-- Transfer of a same-side state-dependent distance between the `AA'` and
`AB''` placements. -/
theorem opFamilyDistSq_place_AB''_eq_AA' {X α : Type*} [Fintype α]
    (S : ProjectiveSetting P ε) (μ : Distribution X)
    (A B : X → α → Op (S.ExpandedLocalSpace .alice)) :
    opFamilyDistSq μ (fun x a => S.place .AB'' (A x a))
        (fun x a => S.place .AB'' (B x a)) S.psiHat =
      opFamilyDistSq μ (fun x a => S.place .AA' (A x a))
        (fun x a => S.place .AA' (B x a)) S.psiHat := by
  unfold opFamilyDistSq
  refine avgOver_congr _ _ _ fun x => Finset.sum_congr rfl fun a _ => ?_
  rw [← place_sub, ← place_sub, norm_place_AB''_eq_norm_place_AA']
  all_goals rfl

/-- Transfer of a same-side state-dependent distance between the `BA''` and
`BB'` placements. -/
theorem opFamilyDistSq_place_BB'_eq_BA'' {X α : Type*} [Fintype α]
    (S : ProjectiveSetting P ε) (μ : Distribution X)
    (A B : X → α → Op (S.ExpandedLocalSpace .bob)) :
    opFamilyDistSq μ (fun x a => S.place .BB' (A x a))
        (fun x a => S.place .BB' (B x a)) S.psiHat =
      opFamilyDistSq μ (fun x a => S.place .BA'' (A x a))
        (fun x a => S.place .BA'' (B x a)) S.psiHat := by
  unfold opFamilyDistSq
  refine avgOver_congr _ _ _ fun x => Finset.sum_congr rfl fun a _ => ?_
  rw [← place_sub, ← place_sub, norm_place_BB'_eq_norm_place_BA'']
  all_goals rfl

end ProjectiveSetting

end

end MIPStarRE.QPBT
