# Recovery of the Honest Pauli Strategy

## Mathematical Statement

The source is `lem:pauli-completeness`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1229-1421`.
For an admissible parameter tuple, the Pauli basis test has a value-one SPCC
strategy. The public Lean statement remains
`exists_spcc_value_one (P : AdmissibleParams)`, with no additional assumption.

The local space is indexed by `PauliRegister P` together with the auxiliary
binary register used by the Magic Square construction. The shared state is
the maximally entangled state of this product index, which is the paper's
tensor product of the Pauli-register EPR state and one EPR pair in the chosen
bipartite ordering.

Point and line measurements are coarse-grainings of a single Pauli basis
measurement. The line answers are actual coefficient lists of the substituted
encoding polynomial. The degree bounds proved in #297 justify truncation and
give the correct answer types; evaluation holds at every parameter, including
zero-direction lines. The Pauli trace measurements have the exact observable
and commutation identities in the source. When the phase is zero, commuting
trace effects define the Pair measurement. Otherwise the anticommuting
observables define the Magic Square measurements.

The recovered family covers all 26 question types, including every constraint
and variable type, and assigns zero effects to malformed answer constructors.
Commutation is proved on each supported graph edge and its reverse. For each
rejected answer pair the product of the corresponding effects is zero; EPR
consistency then gives zero rejected Born weight. Summing the normalized Born
weights yields value one.

The source makes Pair and Pair/W measurements trivial when the phase is
nonzero. The recovered witness retains the Pauli trace measurement for Pair/W
in that inactive case. This is a witness choice, not a change to the theorem:
the relevant Pair checks accept automatically then, Pair is trivial, and the
retained single-basis coarse-grainings still satisfy the required commutation
and consistency properties. The source's existential conclusion is unchanged.

## Source Manifest

The original worktree `issue-156-honest-pauli-strategy` is preserved at
`c7d3ea2c8d09e440fe77eb225b97da3f71d37276`. Its source files were read without
modifying its Git index, branch, or files. The saved blobs are:

| File below `MIPStarRE/QPBT/Test/Completeness/` | Saved Blob |
| --- | --- |
| `HonestStrategy.lean` | `3300a63d2e0e64d4713a91f19026a9b0fbc8599c` |
| `HonestStrategy/Assembly.lean` | `5e722bd23ead8c97e96d4fa167c194c554f247ee` |
| `Commutation.lean` | `d6d8c89110098027798e63a5738b641056af0a8b` |
| `Rejection.lean` | `28a80ce230c55f62bd90444c8158f3826a74a034` |

The current recovery worktree was initially clean at
`1c223a5f5b2f5c0af9483cc99b6d3771a3385bdc`. Ordinary fast-forwards brought it to
published main `551ee8cacde2b23613537300a9faa45a0d4fc74d` and then the published
#297 prerequisite head `956e10fa93df81f4d44bdc2eaa6615caf0d7a5dc` (PR298).
The original issue116 worktree remains preserved at
`f1dc470395734138ab5e8c4ff1fc485d1edce79a`.

Only the final constructor section and final proof were recovered into
`Test/Completeness.lean`. The current-main prefix containing the sampler,
distribution, and symmetry proofs was compared byte for byte after recovery:
all 7,990 characters from the module documentation through
`pauliBasisTestSymm_toGame` are unchanged. Four supporting imports were added.
The saved obsolete sampler implementations were not restored.

Two required Pauli projector lemmas are absent from the initial main base but
already published in PR207 at `42dc0a4`. The recovery reuses exactly that
83-line addition to `Algebra/Pauli.lean`: `pauliProj_transpose` and
`pauliProj_mul_pauliProj`. The resulting whole-file blob is
`d8b566fe1c24b403b72e4283086b27182ae062f8`, identical to PR207. All current-main
character, completeness, and positive-semidefinite results remain present.
This provenance does not assert that PR207 has merged.

## Public Interfaces

The following existing Magic Square support proofs are made public, with only
visibility and documentation changes; their hypotheses and proof bodies are
unchanged:

- `postprocess_effect_eq_zero_of_notMem`;
- `msStrategyMeasurement_incident_commute`;
- `msGame_support_incidence`;
- `msStrategyMeasurement_rejected_mul_on_support`;
- `msStrategyMeasurement_effect_transpose`;
- `heteroKron_mulVec_epr_eq_zero_of_mul_eq_zero`.

The honest construction derives the cell projectivity, commutation, transpose,
and joint-product hypotheses needed by these helpers. None is added to
`exists_spcc_value_one`. The unused generic Magic Square interfaces remain
private.

Existing public lemmas replace obsolete helper references:
`SandwichProduct.postprocess_isProjective`,
`SandwichProduct.postprocess_effect_of_injective`,
`MagicSquareRigidity.reflectionEffect_heteroKron_left`,
`sum_pauliProj_eq_one`, `posSemidef_pauliProj`, and `star_phaseSign`.
The two tensor/postprocessing identities use the current `leftTensor_finset_sum`
directly, so the old point-consistency module is not copied or made a proof
dependency of the honest construction.

The two generic placement helpers omit only their unused `DecidableEq V`
arguments. `tauObservable_conjTranspose` retains the finite-field hypothesis as
`Finite K`, choosing a `Fintype K` locally for its finite Fourier-sum proof.
This changes enumeration data into an equivalent finiteness assumption; it
does not assert the result by discarding the finiteness used in that proof.
No linter is disabled. Numerical blueprint citations in recovered documentation
are replaced by the corresponding stable labels.

## Fresh Validation

The recovered foundation, assembly, commutation, rejection, and final
completeness sources each pass direct Lean checks in the current recovery
worktree. The scoped build of `MIPStarRE.QPBT.Test.Completeness` recompiles the
final rejection and completeness modules successfully. The recovered modules
emit no linter warnings after the narrowly scoped binder and tactic-style
corrections; unrelated imported warnings remain unchanged.

A fresh import of the final compiled module verifies the original
`AdmissibleParams`-only existential statement and prints the axiom closures of
`honestStrategy`, its projectivity/consistency/SPCC theorems, supported-edge
commutation, malformed-answer rejection, both honest line checks, Magic Square
rejection, the final rejected-product theorem, and `exists_spcc_value_one`.
All eleven closures contain only `propext`, `Classical.choice`, and `Quot.sound`.
The earlier eight helper-closure checks and fourteen constructor-closure checks
also have only these standard axioms. A finite-cardinality check gives exactly
26 Pauli question types.

The source-statement guard reports no changed public header for source-labelled
declarations. The new proof-level blueprint marker for
`lem:pauli-completeness` is added only after the final axiom check passes.
The aggregate `MIPStarRE/QPBT.lean` source check also passes after rebuilding
the branch-private `LineMeasurement` artifact for the #297 definition relocation;
the initial aggregate check had found the old artifact's duplicate definition.
Blueprint web rendering and synchronization pass with 1,409 declarations.
Canonical CI, independent code/prose review, and service-owned merge remain
separate gates; these local proof checks do not replace them.

## Dependency Usage

The honest proof uses the definitions, degree bounds, and evaluation identities
of the separate #297 `LineMeasurement.Restriction` module. Its recovered
support modules no longer import the old `Observables.PointConsistency`
facade. They do not reference `tauLineProj`, `expLineOp`, `lineMeasExp`, the
expanded-line evaluation measurements, `ExpandedLineConclusions`, any of the
three expanded-line consistency theorems, or `exists_deltaLine` from the
remaining #116 packet. The aggregate build imports the wider project, but
those declarations are not assumptions or proof inputs of the honest strategy.
The final axiom closure is checked by importing `Test.Completeness` itself.
The #116 dependency edge is deliberately retained for independent assessment;
this source-based observation does not remove or waive it.

## Statement Integrity

- Paper assumptions: an admissible tuple for the Pauli basis test, including
  the finite binary field and the positive degree and dimension parameters.
- Lean assumptions: the same existing `P : AdmissibleParams`, with the fixed
  field model supplied by that record. No bridge, residual, chosen strategy,
  matrix identity, or consistency assumption is added.
- Paper conclusion: existence of a value-one SPCC strategy.
- Lean conclusion: existence of a symmetric strategy for `pauliBasisTestSymm P`
  that is SPCC and whose underlying strategy has value one.
- Verdict: faithful encoding, with the inactive Pair/W witness choice described
  above. Both the positive-parameter convention and coefficient representation
  are retained from current main.

The issue156 prerequisite edges, including the still-open #116 and #297, remain
unchanged by this recovery. Recovery and publication are not a claim that these
packets have merged or that the full QPBT soundness proof is complete. No B8
attempt is started and no mathematical-gap budget is reset.
