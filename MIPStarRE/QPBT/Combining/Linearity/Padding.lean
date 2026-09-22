import MIPStarRE.QPBT.Combining.Linearity

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

end MIPStarRE.QPBT
