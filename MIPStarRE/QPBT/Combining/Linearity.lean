import MIPStarRE.QPBT.Combining.Linearity.Stability

/-!
# The quantum linearity theorem

This file proves the quantum linearity theorem of Natarajan and Vidick in the
form used to combine the binary observables produced in the point analysis.
A family of binary observables indexed by the Boolean cube `F_2^t`, whose
two-query linearity correlation weighted by a positive semidefinite trace-one
operator `ρ` is at least `1 - δ`, is close on average, in the state-dependent
distance weighted by `ρ ⊗ |anc⟩⟨anc|`, to an exactly linear family of binary
observables on a finite ancillary extension.

The proof assembles two results of the linearity route: the operator BLR bound
`avg_multiplicativeDefect_le_two_mul_error`, which converts the correlation
hypothesis into the bound `2δ` on the average multiplicative defect
`E_{u,u'} d_ρ(O^u O^{u'}, O^{u+u'})^2`, and Boolean representation stability
`exists_exact_boolean_representation`, which converts that defect bound into
the exactly linear family with the same average distance bound.  The notions
in which the theorem is stated are in
`MIPStarRE/QPBT/Combining/Linearity/Defs.lean`.

## Main results

* `exists_exactly_linear_observables`: the theorem, with the closeness measured
  by the squared state-dependent operator distance `stateDepDistSq` and the
  bound `2 * δ`.
* `exists_exactly_linear_observables_binaryObservableDistSq`: the same
  conclusion measured by the binary-measurement distance
  `binaryObservableDistSq`, with the bound `δ` intended by the source.

## References

The declaration is blueprint
`thm:linearity`.  The QPBT paper quotes
the theorem at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:713-725`; the
provider is Theorem 10 of Natarajan--Vidick, arXiv:1610.03574,
`references/nv-paper/fullpaper.tex:1074-1113`.  The normalization of the
distance bound is analyzed in
`docs/paper-gaps/qpbt_linearity-distance-normalization.tex`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.Quantum

noncomputable section

/-- The quantum linearity theorem of Natarajan--Vidick.  Let `t` be positive,
`δ ≥ 0`, `ρ` a positive semidefinite trace-one operator on a finite-dimensional
Hilbert space, and `O^u`, for `u ∈ F_2^t`, binary observables whose two-query
correlation satisfies `E_{u,u'} Re Tr(O^u O^{u'} O^{u+u'} ρ) ≥ 1 - δ`.  Then
there are a finite-dimensional ancillary Hilbert space, a unit vector `anc` in
it, and binary observables `L^u` on the tensor-product Hilbert space such that
`L^u L^{u'} = L^{u+u'}` for all `u, u'` and
`E_u d_{ρ'}(L^u, O^u ⊗ 1)^2 ≤ 2δ`, where `ρ' = ρ ⊗ |anc⟩⟨anc|`.

This is Theorem 10 of Natarajan--Vidick,
`references/nv-paper/fullpaper.tex:1074-1088`, hypothesis as in its display
(7) and conclusion as in its display (8), stated as blueprint
`thm:linearity`; the QPBT paper quotes
it at `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:713-725`.
As recorded in blueprint `rem:linearity-import`, this form
imposes no upper bound on `δ`, asserts exact linearity for every pair, and
averages closeness only over `u`.  The quotation instead adds `δ ≤ 1`, phrases
closeness pointwise under a pair quantifier, and appends `L 0 = 1`; those three
deviations are not reproduced.  The identity at zero follows from exact
linearity and the binary-observable condition.

**Local fix:** The source prints the closeness bound as `δ` for the squared
state-dependent operator distance.  Its calculation at
`references/nv-paper/fullpaper.tex:900-912` bounds the squared distance between
the binary projective measurements of the observables, which is half the
squared operator distance, and then identifies the two quantities; the operator
bound `δ` is refuted by a four-point counterexample, and the bound established
by the Fourier--Naimark argument is `2 * δ` for `stateDepDistSq`, equivalently
`δ` for `binaryObservableDistSq`
(`exists_exactly_linear_observables_binaryObservableDistSq`).  Documented in
`docs/paper-gaps/qpbt_linearity-distance-normalization.tex` and blueprint
`rem:linearity-distance-normalization`.

The proof passes the correlation hypothesis through the operator BLR bound
`avg_multiplicativeDefect_le_two_mul_error`, obtaining
`E_{u,u'} d_ρ(O^u O^{u'}, O^{u+u'})^2 ≤ 2δ`, and applies Boolean representation
stability `exists_exact_boolean_representation` with `η = 2δ`. -/
theorem exists_exactly_linear_observables {ι : Type}
    [Fintype ι] [DecidableEq ι]
    (t : ℕ) (ht : 0 < t) (δ : ℝ) (hδ : 0 ≤ δ)
    (ρ : Op ι) (hρ : ρ.PosSemidef) (htrace : ρ.trace = 1)
    (O : (Fin t → ZMod 2) → Op ι)
    (hO : ∀ u, IsBinaryObservable (O u))
    (hcorrelation :
      1 - δ ≤ avgOver
        (uniformDistribution
          ((Fin t → ZMod 2) × (Fin t → ZMod 2)))
        (fun pair =>
          (Matrix.trace
            (O pair.1 * O pair.2 * O (pair.1 + pair.2) * ρ)).re)) :
    ∃ (ι' : Type) (_ : Fintype ι') (_ : DecidableEq ι')
        (anc : EuclideanSpace ℂ ι'),
      ‖anc‖ = 1 ∧
        ∃ L : (Fin t → ZMod 2) → Op (ι × ι'),
          (∀ u, IsBinaryObservable (L u)) ∧
          (∀ u u', L u * L u' = L (u + u')) ∧
          avgOver (uniformDistribution (Fin t → ZMod 2))
              (fun u => stateDepDistSq (L u)
                (heteroKron (O u) (1 : Op ι'))
                (heteroKron ρ (ancProj anc))) ≤ 2 * δ :=
  exists_exact_boolean_representation t ht (2 * δ) (by linarith) ρ hρ htrace O hO
    (avg_multiplicativeDefect_le_two_mul_error O hO ρ hρ htrace δ hcorrelation)

/-- The quantum linearity theorem with the closeness measured by the distance
between the binary projective measurements associated with the observables:
under the hypotheses of `exists_exactly_linear_observables`, the exactly linear
family satisfies `E_u d^{bin}_{ρ'}(L^u, O^u ⊗ 1)^2 ≤ δ`.  This is the bound of
display (8) of Theorem 10 of Natarajan--Vidick,
`references/nv-paper/fullpaper.tex:1083-1086`, in the measurement-distance
convention of `references/nv-paper/fullpaper.tex:876-900`, the convention in
which the source's calculation is correct; see
blueprint `rem:linearity-distance-normalization` and
`docs/paper-gaps/qpbt_linearity-distance-normalization.tex`.  It follows from
`exists_exactly_linear_observables` by halving, through
`binaryObservableDistSq_eq_stateDepDistSq_div_two`. -/
theorem exists_exactly_linear_observables_binaryObservableDistSq {ι : Type}
    [Fintype ι] [DecidableEq ι]
    (t : ℕ) (ht : 0 < t) (δ : ℝ) (hδ : 0 ≤ δ)
    (ρ : Op ι) (hρ : ρ.PosSemidef) (htrace : ρ.trace = 1)
    (O : (Fin t → ZMod 2) → Op ι)
    (hO : ∀ u, IsBinaryObservable (O u))
    (hcorrelation :
      1 - δ ≤ avgOver
        (uniformDistribution
          ((Fin t → ZMod 2) × (Fin t → ZMod 2)))
        (fun pair =>
          (Matrix.trace
            (O pair.1 * O pair.2 * O (pair.1 + pair.2) * ρ)).re)) :
    ∃ (ι' : Type) (_ : Fintype ι') (_ : DecidableEq ι')
        (anc : EuclideanSpace ℂ ι'),
      ‖anc‖ = 1 ∧
        ∃ L : (Fin t → ZMod 2) → Op (ι × ι'),
          (∀ u, IsBinaryObservable (L u)) ∧
          (∀ u u', L u * L u' = L (u + u')) ∧
          avgOver (uniformDistribution (Fin t → ZMod 2))
              (fun u => binaryObservableDistSq (L u)
                (heteroKron (O u) (1 : Op ι'))
                (heteroKron ρ (ancProj anc))) ≤ δ := by
  obtain ⟨ι', hF, hD, anc, hanc, L, hL, hlin, hdist⟩ :=
    exists_exactly_linear_observables t ht δ hδ ρ hρ htrace O hO hcorrelation
  refine ⟨ι', hF, hD, anc, hanc, L, hL, hlin, ?_⟩
  calc
    avgOver (uniformDistribution (Fin t → ZMod 2))
        (fun u => binaryObservableDistSq (L u) (heteroKron (O u) (1 : Op ι'))
          (heteroKron ρ (ancProj anc))) =
        avgOver (uniformDistribution (Fin t → ZMod 2))
          (fun u => stateDepDistSq (L u) (heteroKron (O u) (1 : Op ι'))
            (heteroKron ρ (ancProj anc)) / 2) :=
      avgOver_congr _ _ _
        (fun u => binaryObservableDistSq_eq_stateDepDistSq_div_two _ _ _)
    _ = avgOver (uniformDistribution (Fin t → ZMod 2))
          (fun u => stateDepDistSq (L u) (heteroKron (O u) (1 : Op ι'))
            (heteroKron ρ (ancProj anc))) / 2 := by
      simp only [div_eq_mul_inv]
      exact avgOver_mul_const _ _ _
    _ ≤ 2 * δ / 2 := by gcongr
    _ = δ := by ring

end

end MIPStarRE.QPBT
