import MIPStarRE.QPBT.Observables.Setup
import MIPStarRE.QPBT.Test.PauliBasisTest
import Mathlib.Logic.Equiv.Fintype

/-!
# Reserving the common linearity ancilla in Boolean padding

The active Naimark summand and the common linearity ancilla fit in the Boolean
cube already allocated by the initial projective strategy construction. The
reservation is chosen from the parameter tuple, before any observable family.

## References

The initial padding and its later use occur in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:160-172,825-832`.
These are construction lemmas for blueprint `rem:linearity-import`, tracked in
`docs/paper-gaps/qpbt_linearity-theorem-quotation.tex` and issue #697.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

/-- The existing Boolean allocation contains the active Naimark summand times
the common ancilla for the group of field pairs. The estimate follows from the
actual Pauli-answer alphabet and admissibility, without a capacity hypothesis.
This is a formalization-only construction lemma for the padding at paper
`14_analysis_of_the_pauli_basis_test.tex:160-172,825-832`. -/
theorem linearity_padding_capacity (P : AdmissibleParams) :
    Fintype.card (Option (PauliAnswer P) ×
      Option (Fin (2 * P.model.basisDim) → ZMod 2)) ≤
      Fintype.card (Fin (Fintype.card (PauliAnswer P) + 1) → Bool) := by
  have hfield : Fintype.card (PauliScalar P) = P.q :=
    @FieldModel.card P.q P.model.toFieldModel
  have hregister : P.q ^ (2 ^ P.m) ≤ Fintype.card (PauliAnswer P) := by
    have h := Fintype.card_le_of_injective
      (PauliAnswer.pauliOutcome (P := P)) (fun _ _ h => PauliAnswer.pauliOutcome.inj h)
    simpa [PauliRegister, Cube, Fintype.card_fun, hfield] using h
  have hm : 2 ≤ 2 ^ P.m := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2) P.one_le_m
  have hqpos : 0 < P.q := lt_of_lt_of_le (by decide) P.hq.two_le
  have hq : P.q ^ 2 ≤ Fintype.card (PauliAnswer P) :=
    (Nat.pow_le_pow_right hqpos hm).trans hregister
  have hN : 4 ≤ Fintype.card (PauliAnswer P) := by
    have := P.hq.two_le
    nlinarith
  have hsquare : ∀ n : ℕ, 5 ≤ n → n ^ 2 ≤ 2 ^ n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
        calc
          (n + 1) ^ 2 ≤ 2 * n ^ 2 := by nlinarith
          _ ≤ 2 * 2 ^ n := by omega
          _ = 2 ^ (n + 1) := by rw [pow_succ]; omega
  have hanc : 2 ^ (2 * P.model.basisDim) = P.q ^ 2 := by
    rw [Nat.mul_comm 2, pow_mul]
    exact congrArg (fun n : ℕ => n ^ 2) P.model.basisCard.symm
  simp only [Fintype.card_prod, Fintype.card_option, Fintype.card_fun,
    Fintype.card_fin, ZMod.card, Fintype.card_bool, hanc]
  calc
    (Fintype.card (PauliAnswer P) + 1) * (P.q ^ 2 + 1) ≤
        (Fintype.card (PauliAnswer P) + 1) ^ 2 := by nlinarith
    _ ≤ _ := hsquare _ (by omega)

end MIPStarRE.QPBT
