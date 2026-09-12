# Issue 378: swap conjugation

## Scope

Close `swapUnitary_conj_tildeObs` and `swapUnitary_conj_tildeM` in
`MIPStarRE/QPBT/Extraction/Observables.lean`, with only the private algebraic
support needed for their proofs.

## Sources

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1687-1713`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1805-1822`
- Blueprint `lem:v-swap-conjugation`, Equations
  `eq:v-swap-obs-conjugation` and `eq:qld-unitary-6`

## Dependency

This packet is stacked on #370 / PR #375 at
`302a27d6d83db70246fd9951382521de3c8c2395`. It preserves that packet's proofs
of `tildeM_isProj`, `sum_tildeM_eq_one`, `swapUnitary_mul_conjTranspose`, and
`conjTranspose_mul_swapUnitary`.

## Integrity

Both public theorem statements remain unchanged. The proof uses the supplied
`GlobalPairWitness`, projectivity of `w.Smeas`, Pauli Fourier inversion, and
`lowDegreeEnc_eq_dotProduct` at `indicatorVec`; it adds no witness construction,
decoder interpolation assumption, axiom, or proof bypass.
