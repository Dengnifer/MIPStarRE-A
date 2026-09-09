# Heterogeneous Pasting: Statement Integrity

This audit concerns issue #495 and paper `lem:pasting`,
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`.
Its intended application is `lem:qld-xz-lines`,
`14_analysis_of_the_pauli_basis_test.tex:882-963`.

## Source Theorem

The paper assumes a probability distribution on triples `(x,y1,y2)`, two
codeword evaluation maps, measurement families `G1,G2`, and a joint projective
measurement family `A`. The family `G2` is projective. Distinct second
codewords collide with conditional probability at most `eta`, conditioned on
each pair `(x,y1)` of positive marginal probability. Both marginals of `A`
are consistent with the corresponding evaluated codeword family to error
`delta`; the joint family `A` also satisfies the printed self-consistency
comparison. The state is normalized and the error parameters are nonnegative.

The conclusion compares `A` with the evaluated sandwich `G2 G1 G2`, with one
universal polynomial error function of `(eta,delta)`. The existing additive
interpretation of this polynomial error is unchanged; its justification is
`docs/paper-gaps/qpbt_pasting-product-error.tex`, issue #201.

The public Lean statement `exists_pasting_error` is unchanged. All paper
hypotheses, including the third comparison, and the conclusion are retained.
Its proof is now a corollary of an extracted two-comparison proof.
The declaration `pastedMeasurement_isMeasurement` is moved without any change
to its statement or proof. Verdict: exact preservation of both existing
statements, with their previously documented finite-dimensional encoding and
additive-error correction.

## Stronger Auxiliary Statements

The extracted `exists_pasting_error_of_marginal_consistency` has the original
homogeneous conclusion and all hypotheses except the third comparison. This
is justified because the existing Schmidt-mirror argument does not use that
comparison. The mathematical proof is retained once, rather than duplicated.

The new `exists_pasting_error_heterogeneous` also assumes only the two forward
marginal comparisons. Alice and Bob have independent finite carriers. The
distribution, evaluation maps, projectivity conditions, conditional collision
bound, normalized state, nonnegative errors, universal error quantifier, and
pasted conclusion agree with the extracted homogeneous statement. There is
no dimension equality, carrier equivalence, register-exchange assumption, or
unproved intermediate hypothesis. Verdict: stronger auxiliary theorem, with
weaker assumptions and an unchanged conclusion; it is recorded in its own
blueprint entry, not as a replacement for the source-labelled theorem.

The literal third homogeneous comparison cannot be placed on independent
carriers using a single Alice measurement. No artificial Bob measurement is
introduced. The original paper-facing statement continues to display that
comparison in its well-typed homogeneous setting.

## Common-Space Realization

Let the original spaces be `HA` and `HB`. Choose unit coordinate vectors
`a0` and `b0` and use the common space `K = HA tensor HB` on each side.
Alice's operators become `A tensor I`, and Bob's become `I tensor B`.
The new bipartite state has coefficients
`Psi((i,b),(a,j)) = [b=b0] [a=a0] psi(i,j)`.

Direct finite-sum calculations prove equality of norms and of all bipartite
quadratic forms. Consequently the input consistency defects and the pasted
output defect are equal before and after this realization. Existing tensor
placement theorems preserve POVMs, projectivity, and postprocessing; tensor
multiplicativity preserves the sandwich. The distribution and collision
condition are untouched. A unit state rules out an empty product carrier,
so local nonemptiness is derived internally. No outcome nonemptiness is used.

These constructions are closed Lean proofs and introduce no proof holes or
additional axioms. They do not assert an isomorphism between the original
matrix algebras of unequal dimensions.
