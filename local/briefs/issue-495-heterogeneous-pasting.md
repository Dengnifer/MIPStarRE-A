# Issue 495: Pasting on Independent Local Spaces

Paper sources: `lem:pasting` in `06_nonlocal_games_and_mipstar.tex:504-525`,
and `lem:qld-xz-lines` in `14_analysis_of_the_pauli_basis_test.tex:882-963`.

The line-pasting application keeps Alice's and Bob's carriers distinct.
Realize both in their tensor product by adjoining fixed unit basis vectors.
Reuse the existing measurement placements and prove exact state and defect
preservation. Apply the stronger two-forward-comparison form of the existing
Schmidt-mirror argument, extracted once from its present proof.

Preserve the public three-comparison statement `exists_pasting_error` as a
corollary. Record the two stronger auxiliary statements separately in the
blueprint. The source-labelled theorem and its certification remain unchanged.
The statement audit is `audits/2026-09-09-qpbt-heterogeneous-pasting.md`.

The implementation owns only the new pasting leaf, the minimal changes to
`Sandwich.lean`, and corresponding documentation. It does not modify the
line-game transport or other active repair files.
