import MIPStarRE.QPBT.Extraction.Observables

/-! # Unasserted printed claims in Pauli extraction

This module retains the false cross-basis dichotomy and the two false decoder
identities as propositions, not theorems. They are not assumptions or inputs to
any construction. The corrected results remain in `Observables` and `Decoding`.

## References

* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1451-1456,1483-1492,1805-1822`.
* `docs/paper-gaps/qpbt_cross-basis-phase.tex`.
* `docs/paper-gaps/qpbt_decoding-identity.tex`.
* Issue #667, retention of printed claims under completion criterion C3.
-/

namespace MIPStarRE.QPBT

/-- **Source statement, unasserted:** The full commutation dichotomy printed at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1451-1456`.

The source has already fixed the global polynomial-pair measurement of
`lem:qld-4-7`; `w` supplies that ambient object on either player side. The
register vectors range over the entire field, and the basis indices are
zero-based. In particular, no prime-field restriction is imposed on their dot
product. Both branches are retained, including the false distinct-index branch.

This definition asserts nothing. The corrected full-phase relation is
`tildeObs_twisted_commutation`, linked from blueprint `lem:tildew-product-form`.
The source-domain counterexample and consumer analysis are in
`docs/paper-gaps/qpbt_cross-basis-phase.tex`, issue #667. -/
def PrintedCrossBasisCommutationClaim {P : AdmissibleParams}
    {epsilon delta : Real} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S delta) : Prop :=
  ∀ (side : PlayerSide) (u v : PauliRegister P) (j j' : Fin P.model.basisDim),
    tildeObs w side .X u j * tildeObs w side .Z v j' =
      if j = j' then
        phaseSign (fixedBinTrace P.model
          (dotProduct (P.model.basis j • u) (P.model.basis j • v))) •
          (tildeObs w side .Z v j * tildeObs w side .X u j)
      else tildeObs w side .Z v j' * tildeObs w side .X u j

/-- **Source statement, unasserted:** The unrestricted evaluation identity used
at `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1483-1492`.

The decoder retains every Boolean-cube evaluation, as specified at lines
1419-1420. The polynomial ranges over all bounded representatives, without an
`IsEncoding` hypothesis, and the evaluation point ranges over the whole field.
This is not the stronger equality of polynomial representatives used later.

This definition asserts nothing. The corrected identity is
`decodeFq_dotProduct_indicatorVec`, blueprint `lem:qld-decoder-evaluation`.
The counterexample and the separate treatment of non-encoding outcomes are in
`docs/paper-gaps/qpbt_decoding-identity.tex`, issue #667. -/
def PrintedDecoderEvaluationClaim (P : AdmissibleParams) : Prop :=
  ∀ (g : Poly P) (u : Fin P.m → PauliScalar P),
    dotProduct (decodeFq g) (indicatorVec u) = evalPoly g u

/-- **Source statement, unasserted:** The polynomial reindexing identity used at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1805-1822`:
after setting `h' = h + Dec(g)`, the source writes `g_h' = g_h + g`.

Both sides are polynomial representatives, not their evaluation functions.
Every bounded polynomial and every field-valued word are quantified, with no
encoding hypothesis. This distinction matters when the degree is at least the
field size: pointwise equality alone does not imply this printed identity.

This definition asserts nothing. The proved `swapUnitary_conj_tildeM`, blueprint
`lem:v-swap-conjugation`, instead cancels the decoded label in the projector
constraint. See `docs/paper-gaps/qpbt_decoding-identity.tex`, issue #667. -/
def PrintedDecoderReindexingClaim (P : AdmissibleParams) : Prop :=
  ∀ (g : Poly P) (h : PauliRegister P),
    lowDegreeEncoding (h + decodeFq g) = lowDegreeEncoding h + g.1

end MIPStarRE.QPBT
