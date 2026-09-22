# Linearity Padding: Statement Integrity and Remaining Construction

Issue #697, based on `a159185acc52b82fd2ab377eb8dbdef03c0fc2da`.
The source padding construction remains unproved. The new results certify
three obstructions to inferring a reserved pure register from an arbitrary
fixed projective setting. They do not refute the paper's advance choice of
padding, a different proof of linearity on the same space, or the combined-point
conclusion.

## Source and Quantifiers

The primary source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`:

- Lines 160--172 choose a zero-padded projective dilation of the input strategy.
- Lines 367--372 define the expanded state using two EPR pairs and recall the
  zero-padding convention. The Pauli-register size remains `M = 2^m`.
- Lines 713--725 quote quantum linearity; lines 825--832 apply it separately to
  every `(x,z)` and assume enough zero ancillas to avoid another extension.

The provider is `references/nv-paper/fullpaper.tex:1074-1113`. Its corrected
averaged operator bound is `2 delta`, with equivalent binary-measurement bound
`delta`; normalization is owned separately by #694 and was not changed.

The existing `exists_exactly_linear_observables_commonAncilla` has the order
`forall t > 0, exists K, anc, forall H, delta, rho, O, ...`.
The chosen `K` has basis `Option (Fin t -> ZMod 2)` and `anc` is its `none`
basis vector. This theorem and its proof are unchanged. A caller search found
no Lean call sites beyond its declaration and documentation; the concrete
point construction follows the independent field-valued argument.

`ProjectiveSetting P epsilon` stores a strategy, projectivity, and the winning
inequality. It does not identify a smaller invariant local space or a reserved
pure register. `exists_projective_padded_strategy` is an existential setup
theorem, not a characterization of every `ProjectiveSetting`; its public
conclusion supplies zero-padding isometries and equal value but no unused
subspace for later measurements.

## Checked Obstructions

All new declarations are in
`MIPStarRE/QPBT/Combining/Linearity/Padding.lean`.

| Declaration | Assumptions | Conclusion | Integrity verdict |
| --- | --- | --- | --- |
| `not_nonempty_linearity_ancilla_isometry` | Finite nonzero `H`; arbitrary natural `t` | No linear isometry from `H tensor K_t` into `H` | Exact auxiliary; finite-dimensional injectivity bound |
| `posDef_ne_linearity_ancilla_conjugate` | Positive definite `rho` on `H tensor K_t`; invertible `U`; arbitrary `sigma` on nonzero finite `H` | `U rho U*` is not `sigma tensor |none><none|` | Exact auxiliary; positive definiteness contradicts the zero diagonal |
| `exists_projectiveSetting_no_proper_alice_support` | An admissible parameter tuple `P` | Some nonnegative error and projective setting satisfy: every local `R` fixing `psiHat` on `AA'` equals identity | Exact auxiliary; coordinate calculation on the honest EPR state |

The third witness uses the actual rejection probability `1 - T.value`, whose
nonnegativity follows from `T.value <= 1`. Its Lean statement does not assert
that this error equals zero. It needs no new winning-probability assumption.
The original state is EPR on `HonestIndex P`; after expansion the reduced state
on `AA'` is maximally mixed of dimension `card(HonestIndex P) * q^M`. Thus even
a change of local basis cannot expose a proper zero-state sector: the conjugate
of its support projection would be a nonidentity operator fixing `psiHat`.

The blueprint gives these results three separately labelled auxiliary entries.
No source-labelled theorem statement, existing proof, error constant, or
formalization mark was weakened or replaced. No proof hole was introduced.
The verdict for the requested source absorption is **unproved**, not a changed
source statement with extra hypotheses.

## Closest Sufficient Construction

Keep the existing general `ProjectiveSetting` domain. A reservation should be
constructed in the conclusion of the initial strategy reduction, before the
fiber observables, rather than assumed by a paper-facing theorem. For
`q = 2^t`, use the common `K_(2t)`, of dimension `q^2 + 1`. A Boolean register
of `2t + 1` qubits can hold it, with no change to `M = 2^m`.

The actual Boolean-padding implementation in `Observables/Setup.lean` offers
a more economical candidate than another enlargement: it preserves the active
Naimark summand `I x Option Answer` inside `I x Bool^(N+1)`, where
`N = card Answer`, and puts a fixed-outcome measurement on the complement.
For `PauliAnswer P`, the `pauliOutcome` constructor and `P.m >= 1` imply
`N >= q^(2^m) >= q^2 >= 4`. Therefore
`(N+1)(q^2+1) <= (N+1)^2 <= 2^(N+1)`.
Tensoring this comparison with the unchanged Pauli register preserves it.

This dimension calculation is a mathematical proposal, not a formal embedding
or a proved absorption. It leaves the following named construction targets:

1. `linearity_padding_ground_embedding`: construct an embedding of the active
   summand times `K_(2t)` into the prescribed Boolean-padded space, agreeing on
   the `none` slice with the existing one-hot embedding. It must be chosen
   before all observable families and for both players.
2. `linearity_padding_state_transport`: prove the bipartite state identity,
   its six-register expansion, and its four relevant placements.
3. `linearity_padding_measurement_transport`: retain the active subspace in
   all earlier binary rounding choices and extend the rounded PVM by assigning
   the complementary projection to outcome zero. An arbitrary family acting
   on the whole padded space cannot be presumed to preserve this subspace.
4. `linearity_padding_error_transport`: prove each squared-distance identity
   and then both finite averages, keeping the common embedding independent of
   `(x,z)`, `rho`, `delta`, and the eligible observable family on the core.
5. `linearity_padding_absorption`: assemble these constructions for the actual
   source binary families. The existing fixed-space point theorem must not be
   restricted to selected padded strategies or credited as proving this step.

These are documentation targets, not Lean axioms, hypotheses, or admitted
theorems. Their common gap note is
`docs/paper-gaps/qpbt_linearity-theorem-quotation.tex`. Main must decide how the
explicit initial reservation is exposed before changing the setup interface;
no such interface or game change was made here.

## Consumers

| Source or blueprint use | Lean surface | Effect of this session |
| --- | --- | --- |
| Projective reduction and expanded state | `exists_projective_padded_strategy`, `ProjectiveSetting`, `psiHat`, `ExpandedLocalSpace` | Inspected, unchanged; no reserved-space contract added |
| `thm:linearity`, `lem:linearity-common-ancilla` | The three existing `exists_exactly_linear_observables*` declarations | Unchanged, including ancilla quantifier order and normalization |
| `lem:qld-4-10`, `lem:qld-4-12` | `exists_combinedPointsWitness`, `exists_extendedQ` | Independent field-valued construction unchanged; not counted as absorption |
| `lem:qld-xz-lines` | `exists_combinedLinesWitness`, supplied-point companion | Unchanged; consumes the existing point witness |
| `lem:qld-4-13`, `lem:qld-4-7` | `exists_extendedLinesWitness_established`, `exists_globalPairWitness` | Unchanged; separate source-law and error gaps remain |
| Pauli construction and extraction | `exists_pulled_apart_consistency`, `exists_extractionWitness` | Unchanged; consume the existing global pair |
| `thm:pauli`, `cor:pauli-binary` | `pauli_soundness`, `pauli_soundness_qubit` | Unchanged |
| Arbitrary-strategy reduction | `pauliNaimarkSetting`, `exists_arbitrary_strategy_isometry_bounds` | Uses a separate Option-indexed dilation, not the Boolean-padding setup theorem; future source-route integration must account for this |

Focused checks passed for the new module, `Linearity.lean`, `QPBT.lean`,
`Points.lean`, `Apply.lean`, `Extraction/SourceUnitary.lean`, `Test/Soundness.lean`,
and `Test/QubitForm.lean`. The new declarations and the common-ancilla, point,
global-pair, extraction, and headline soundness declarations have transitive
axiom sets contained in `propext`, `Classical.choice`, and `Quot.sound`.
Full CI and independent review remain Main's responsibility.
