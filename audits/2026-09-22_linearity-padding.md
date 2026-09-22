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

## Initial Proposal (First Session)

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

## Admitted Continuation

The continuation began from `45039ea9bf8058b2b40fc8eb2aafbf57e3b3ce5c`.
Main authorized constructing the reserve in the initial padded strategy. The
four predecessor commits, all three obstructions, the predecessor's 2094
dispatcher seconds, and every historical/shared charge remain retained. The
continuation has one 3600-second admission, starting 2026-09-22T21:14:10+09:00;
it does not authorize a further session or change any earlier budget.

The proposed capacity estimate is correct. `linearity_padding_capacity`
derives it from `PauliAnswer.pauliOutcome`, `P.one_le_m`, and the actual field
cardinality. `linearity_padding_ground_embedding` uses Mathlib's extension of
a finite partial bijection to construct an injection whose entire ground
slice agrees with `optionBoolEmbedding`. Its choice precedes the player,
state, density, errors, and observable families.

The continuation proves the following additional construction results:

| Declaration | Exact content | Remaining limitation |
| --- | --- | --- |
| `linearity_padding_state_transport` | Reservation of an appended pure ancilla equals the active Boolean embedding for every bipartite vector | Six-register identity not asserted |
| `linearity_padding_naimark_comparison` | The actual Option strategy state maps to the Boolean state; both original question/answer families intertwine | The consumer is compared, not replaced |
| `linearity_padding_measurement_transport` | Extend any PVM across an isometry, assigning the complement to its distinguished outcome; prove projectivity and intertwining | Instantiation with the earlier source binary rounding remains |
| `linearity_padding_error_transport` | Exact pointwise squared vector errors | Operators are the stated isometric extensions |
| `LinearityPadding.extendObservable_stateDepDistSq` | Exact pointwise density-weighted squared errors | Density is explicitly conjugated by the isometry |
| `linearity_padding_average_error_transport` | Both finite averages retain the exact identity | No replacement of the state or comparator is implicit |
| `linearity_padding_ground_error_transport` | Compare an operator on an extension to the original operator on its ground slice | Six-register placement not asserted |
| `linearity_padding_rounding_transport` | One actual expanded reservation serves every fiber; exact linearity, identity at zero, and the corrected averaged bound are preserved | Transported density and comparator still need source identification |

All extensions use `J L J* + (I - J J*)`; PVM completion assigns the
complement to a specified outcome, with zero intended for linearity. The
expanded reservation leaves every `PauliRegister P` coordinate unchanged.
It changes neither `M = 2^m` nor any game, answer, error, or unrestricted
`ProjectiveSetting` definition. Setup changes expose the existing embedding
and construction functions and prove their active-coordinate formula; their
definitions and source-facing setup theorem are unchanged.

### Statement Integrity of the Continuation

Paper assumptions: an admissible parameter tuple, an initial projective
strategy chosen with zero padding, and the density/binary-observable averaged
linearity premises at the later application. Lean assumptions: the capacity
and embedding theorems take only the admissible tuple; the initial comparison
takes only the input strategy; the general extension lemmas take finite
isometries and actual operators/PVMs, and prove rather than assume transport.
The rounding auxiliary uses the same density and correlation premises as the
provider, on the explicitly displayed active expanded space.

Paper conclusion: exactly linear observables and their PVM on the prescribed
expanded spaces, compared with the actual source binary families. Lean
conclusion: the constructed reservation, exact initial and algebraic
transports, and rounding with an explicitly transported comparator and
density. Verdict: exact for these separately stated auxiliaries; the full
paper application is still unproved. No source theorem gains an assumption
or loses a conclusion, and no auxiliary is advertised as full absorption.

### Remaining Construction

1. Extend the bipartite state comparison to `psiHat` and prove operator
   intertwining for `AA'`, `BA''`, `BB'`, and `AB''` with the same reservation.
2. Choose the binary sandwich orthonormalizations on the active expanded
   spaces, and prove that their extensions satisfy the comparisons required
   by paper lines 731--824. The construction must derive its estimates from
   the actual projective setting, not take a transport or rounding package.
3. Identify the density and comparator of `linearity_padding_rounding_transport`
   with that construction and assemble `linearity_padding_absorption` for all
   point pairs and placements. This declaration has not been introduced.

The quotation gap remains open. There are no new or retained `sorry` sites
in these modules. The source pipeline and independent field-valued point
proof listed above are unchanged; none is counted as the missing absorption.

### Continuation Validation

Focused Lean checks pass without diagnostics for all four new modules,
`Observables/Setup.lean`, the root `QPBT.lean`, `Points.lean`, `Apply.lean`,
`Extraction/SourceUnitary.lean`, `Test/Soundness.lean`, and `Test/QubitForm.lean`.
The worktree-private root compilation also succeeds. The axiom audit of the
ten new principal/support results, three predecessor obstructions, the common
ancilla theorem, and five downstream declarations reports exactly `propext`,
`Classical.choice`, and `Quot.sound` for all nineteen declarations.

The forbidden-token and debug-command scans have no matches in the four new
modules. All their lines satisfy the 100-character limit. The branch duplicate
check finds no duplicate among 36 new or newly public declarations on
`github/main`. Normal hooks ran at each proof checkpoint.

The final `leanblueprint web` succeeds without warnings or errors in its log.
After that render, synchronization and the declaration checker pass for all
1888 entries. The four existing orphan marks in chapter 16 and two existing
statement-only marks in chapters 13/14 remain. An intermediate synchronization
found multiline Lean links unrecognized by the parser; putting each link on
its own line removed all six newly reported orphan marks. Paper-gap style and
reference checks pass, with the pre-existing note-verdict-marker warnings.
No full build or full CI was run; Main retains those gates and independent review.
