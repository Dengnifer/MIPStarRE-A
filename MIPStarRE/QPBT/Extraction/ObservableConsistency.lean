import MIPStarRE.QPBT.Extraction.Consistency
import MIPStarRE.QPBT.Extraction.PullingDefect

/-!
# Self-consistency of the pulled-apart observables

The difference-polynomial measurements reduce observable self-consistency to
point self-consistency and polynomial collision. The global witness remains
an explicit premise.

## References

- Blueprint `lem:qld-construct-the-paulis-given-global-pair`, Item 2.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1476-1662`.
- Issues #520 and #519; `docs/paper-gaps/qpbt_decoding-identity.tex`.
- The joint source obligation for `lem:qld-construct-the-paulis` is stated in
  `Extraction.Construction`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

/-- Conditional self-consistency of the pulled-apart observables on Alice's and
Bob's extraction blocks, averaged over the uniformly random Pauli register.
This is the supplied-witness form of Item 2 in blueprint
`lem:qld-construct-the-paulis-given-global-pair`, paper
`14_analysis_of_the_pauli_basis_test.tex:1476-1605`.

The construction scale exposes the square-root game error and
Schwartz--Zippel loss that the source absorbs into `deltaS`. The proof combines
the evaluated difference-polynomial comparison, the collision bound, and the
fixed-coordinate character conversion. It does not use the non-encoding mass
or complement-absorption obligations.

**Unfaithful:** The premise `w : GlobalPairWitness S deltaG` is not constructed
here from `lem:qld-4-7`. Issue #519 and
`docs/paper-gaps/qpbt_decoding-identity.tex` record this distinction.
Elimination: discharge the construction required by `exists_pulled_apart_consistency`
using `exists_globalPairWitness`, including its missing zero-error case.
The joint source obligation is stated separately in `Extraction.Construction`;
this proof establishes only the supplied-witness estimate. -/
theorem tildeObs_selfConsistent_ofGlobalPairWitness :
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
  have hcard : 0 ≤ (Fintype.card PauliEdge : ℝ) := Nat.cast_nonneg _
  refine ⟨48 + 32 * (Fintype.card PauliEdge : ℝ), by linarith, ?_⟩
  intro P epsilon deltaG hepsilon hepsilon_one hdeltaG S w W j
  have hbound := (tildeObs_opDistSq_le_pulling_eval_add w W j).trans
    (mul_le_mul_of_nonneg_left
      (add_le_add (pullingMeas_eval_consistencyDefect_le w W) (le_refl _))
      (by norm_num : (0 : ℝ) ≤ 4))
  have heps : epsilon ≤ Real.sqrt epsilon := Real.le_sqrt_self_iff.mpr hepsilon_one
  have hsqrt := Real.sqrt_nonneg epsilon
  have hratio : 0 ≤ (P.m * P.d : ℝ) / P.q :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hscaled := mul_le_mul_of_nonneg_left heps
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 32) hcard)
  refine hbound.trans ?_
  unfold deltaConstructPaulis
  rw [Nat.cast_mul]
  nlinarith [mul_nonneg hcard hdeltaG, mul_nonneg hcard hratio]

end

end MIPStarRE.QPBT
