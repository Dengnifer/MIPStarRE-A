# QPBT tracker closure supplement: issues #77, #120, #123, #165

Read-only audit completed 2026-09-19. Repository evidence is pinned to published
`main` commit [`04f79c5071d020fc4578b9ae11808eff2daa575b`](https://github.com/Dengnifer/MIPStarRE-A/commit/04f79c5071d020fc4578b9ae11808eff2daa575b).
The designated worktree was at unpublished `cafe0b5` and was not used as evidence.
GitHub issue and sub-issue state was read through `local/bin/gh_common.py`.

## Dispositions

| issue | recommendation | reason |
|---|---|---|
| #77 | **needs-small-correction** | The proof is complete, but the issue requires the original unrestricted `sqrt epsilon` signature. The paper statement is false; published `exists_ms_rigidity` is the corrected theorem with two variable-agreement assumptions and `sqrt epsilon + sqrt delta`. The issue body must record that correction before closure. |
| #120 | **close-completed** | All five exact target declarations are proved, retain their supplied-`GlobalPairWitness` algebraic signatures, have proof-level blueprint completion marks and existing standard-axiom receipts. The open #119 dependency is stale for this conditional algebra and must not be read as completion of #119. |
| #123 | **needs-small-correction** | Seven named targets are present as named; the three original `tildeM...`/`tildeObs...` names are not mere renames: their `_ofGlobalPairWitness` forms have an explicit supplied-witness premise. The unconditional paper-facing composition is instead `exists_pulled_apart_consistency`, and `exists_extractionWitness` separately constructs its witness. Correct the tracker target map, then close without claiming #119 or #527. |
| #165 | **close-completed** | All eight children are closed `completed`; every target group across sampling, projective setup, exact/approximate winning implications, expanded points, point consistency/commutation and expanded lines is proved and linked by proof-level `\leanok`. |

## #77: Magic Square rigidity

Source lines [620-652](https://github.com/Dengnifer/MIPStarRE-A/blob/04f79c5071d020fc4578b9ae11808eff2daa575b/references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex#L620-L652)
state unrestricted rigidity from success alone. The repository's gap note proves
that assertion false and adopts cross-player agreement at variables 1 and 5 as
the missing hypothesis.

Acceptance map:

- **Exact original signature and seven bounds:** not met literally. Published
  [`exists_ms_rigidity`](https://github.com/Dengnifer/MIPStarRE-A/blob/04f79c5071d020fc4578b9ae11808eff2daa575b/MIPStarRE/QPBT/Test/MagicSquareTheorems.lean#L637-L650)
  has all seven conclusions, one universal constant, arbitrary POVMs and the
  zero-based indices 0/4, but also assumes two
  `msVariableConsistencyDefect <= delta` bounds and uses
  `sqrt epsilon + sqrt delta`. These assumptions are load-bearing corrections,
  not boundary assumptions.
- **Kernel-checked route/no bridge:** met for the corrected theorem. The proof
  is explicit at lines 651-756, including coarse/large-error and small-error
  branches; the blueprint theorem and proof carry `\leanok`. Existing review
  and gap-register receipts record standard-only axiom closure.
- **Statement-integrity record:** met for the corrected theorem, including POVM
  generality, quantifier order, indices, universal constant, Euclidean norm
  conversion, basis change and large-error branch, in
  [`qpbt_ms-rigidity-symmetric-strategies.tex`](https://github.com/Dengnifer/MIPStarRE-A/blob/04f79c5071d020fc4578b9ae11808eff2daa575b/docs/paper-gaps/qpbt_ms-rigidity-symmetric-strategies.tex#L68-L137).
- **Children/workflow:** #101-#105 and #183 are all closed `completed`.
- **Unresolved requirement:** update #77's acceptance/statement-integrity text
  to the adopted corrected theorem (or explicitly supersede the old target),
  then close. Do not describe the extra agreement assumptions as a rename.

## #120: marginal extraction measurements

The paper defines the marginals and pulled-apart projectors at
[lines 1421-1435](https://github.com/Dengnifer/MIPStarRE-A/blob/04f79c5071d020fc4578b9ae11808eff2daa575b/references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex#L1421-L1435).

All five unchanged targets are complete:

- [`tauDotProj_isProj`](https://github.com/Dengnifer/MIPStarRE-A/blob/04f79c5071d020fc4578b9ae11808eff2daa575b/MIPStarRE/QPBT/Extraction/Defs.lean#L207-L238)
  and [`sum_tauDotProj_eq_one`](https://github.com/Dengnifer/MIPStarRE-A/blob/04f79c5071d020fc4578b9ae11808eff2daa575b/MIPStarRE/QPBT/Extraction/Defs.lean#L246-L252).
- [`GlobalPairWitness.marginalPoly_isProjective`](https://github.com/Dengnifer/MIPStarRE-A/blob/04f79c5071d020fc4578b9ae11808eff2daa575b/MIPStarRE/QPBT/Extraction/Observables.lean#L66-L71),
  [`tildeM_isProj`](https://github.com/Dengnifer/MIPStarRE-A/blob/04f79c5071d020fc4578b9ae11808eff2daa575b/MIPStarRE/QPBT/Extraction/Observables.lean#L94-L121), and
  [`sum_tildeM_eq_one`](https://github.com/Dengnifer/MIPStarRE-A/blob/04f79c5071d020fc4578b9ae11808eff2daa575b/MIPStarRE/QPBT/Extraction/Observables.lean#L131-L152).
- Chapter 16 carries statement and proof completion at
  [`lem:s-w-marginals-projective`](https://github.com/Dengnifer/MIPStarRE-A/blob/04f79c5071d020fc4578b9ae11808eff2daa575b/blueprint/src/chapter/ch16_qpbt_extraction.tex#L93-L106),
  [`lem:tau-dot-product-projective`](https://github.com/Dengnifer/MIPStarRE-A/blob/04f79c5071d020fc4578b9ae11808eff2daa575b/blueprint/src/chapter/ch16_qpbt_extraction.tex#L118-L142), and
  [`lem:tilde-m-projective`](https://github.com/Dengnifer/MIPStarRE-A/blob/04f79c5071d020fc4578b9ae11808eff2daa575b/blueprint/src/chapter/ch16_qpbt_extraction.tex#L155-L175).
- Existing receipts: the issue-120 audit records all five closures as exactly
  `[propext, Classical.choice, Quot.sound]` and records focused Lean,
  declaration and blueprint checks.

The target statements deliberately take a supplied `GlobalPairWitness`; that is
faithful for these local postprocessing/projectivity facts and does not assert
the global construction. #120 has no sub-issues. Its sole open dependency is
#119, but no #119 completion is needed or claimed by closing this algebra packet.

## #123: extraction consistency and soundness

The source obligations are `lem:qld-construct-the-paulis` at
[1463-1481](https://github.com/Dengnifer/MIPStarRE-A/blob/04f79c5071d020fc4578b9ae11808eff2daa575b/references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex#L1463-L1481),
extraction at [1666-1860](https://github.com/Dengnifer/MIPStarRE-A/blob/04f79c5071d020fc4578b9ae11808eff2daa575b/references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex#L1666-L1860),
and soundness at [1431-1491](https://github.com/Dengnifer/MIPStarRE-A/blob/04f79c5071d020fc4578b9ae11808eff2daa575b/references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex#L1431-L1491).

Acceptance map:

- Exact named targets proved: [`sum_marginalPoly_pointMeas_approx_id`](https://github.com/Dengnifer/MIPStarRE-A/blob/04f79c5071d020fc4578b9ae11808eff2daa575b/MIPStarRE/QPBT/Extraction/Consistency.lean#L583-L619),
  [`marginalPoly_sub_pointMeas_approx_zero`](https://github.com/Dengnifer/MIPStarRE-A/blob/04f79c5071d020fc4578b9ae11808eff2daa575b/MIPStarRE/QPBT/Extraction/Consistency.lean#L720-L732),
  [`nonencodingMarginalMass_le`](https://github.com/Dengnifer/MIPStarRE-A/blob/04f79c5071d020fc4578b9ae11808eff2daa575b/MIPStarRE/QPBT/Extraction/Consistency.lean#L856-L864),
  [`exists_extractionWitness`](https://github.com/Dengnifer/MIPStarRE-A/blob/04f79c5071d020fc4578b9ae11808eff2daa575b/MIPStarRE/QPBT/Extraction/SourceUnitary.lean#L34-L52),
  [`deltaExtract_le_deltaQld`](https://github.com/Dengnifer/MIPStarRE-A/blob/04f79c5071d020fc4578b9ae11808eff2daa575b/MIPStarRE/QPBT/Extraction/Unitary.lean#L251-L260),
  [`pauli_soundness`](https://github.com/Dengnifer/MIPStarRE-A/blob/04f79c5071d020fc4578b9ae11808eff2daa575b/MIPStarRE/QPBT/Test/Soundness.lean#L52-L65), and
  [`pauli_soundness_qubit`](https://github.com/Dengnifer/MIPStarRE-A/blob/04f79c5071d020fc4578b9ae11808eff2daa575b/MIPStarRE/QPBT/Test/QubitForm.lean#L423-L445).
- The three old names are **not exact-signature renames**. Published
  [`tildeM_consistent_pointMeas_ofGlobalPairWitness`](https://github.com/Dengnifer/MIPStarRE-A/blob/04f79c5071d020fc4578b9ae11808eff2daa575b/MIPStarRE/QPBT/Extraction/SuppliedPointConsistency.lean#L107-L120),
  [its prime companion](https://github.com/Dengnifer/MIPStarRE-A/blob/04f79c5071d020fc4578b9ae11808eff2daa575b/MIPStarRE/QPBT/Extraction/SuppliedPointConsistency.lean#L226-L239), and
  [`tildeObs_selfConsistent_ofGlobalPairWitness`](https://github.com/Dengnifer/MIPStarRE-A/blob/04f79c5071d020fc4578b9ae11808eff2daa575b/MIPStarRE/QPBT/Extraction/ObservableConsistency.lean#L49-L60)
  universally quantify an explicit `w : GlobalPairWitness S deltaG`.
- The unconditional paper-facing replacement is
  [`exists_pulled_apart_consistency`](https://github.com/Dengnifer/MIPStarRE-A/blob/04f79c5071d020fc4578b9ae11808eff2daa575b/MIPStarRE/QPBT/Extraction/Construction.lean#L46-L101): it invokes
  `exists_globalPairWitness`, applies all three supplied-witness estimates to
  the same witness, and returns their maximum constant. Likewise
  `exists_extractionWitness` constructs the witness internally before calling
  [`exists_extractionWitness_ofGlobalPairWitness`](https://github.com/Dengnifer/MIPStarRE-A/blob/04f79c5071d020fc4578b9ae11808eff2daa575b/MIPStarRE/QPBT/Extraction/Unitary.lean#L173-L233).
- Blueprint status correctly separates the unconditional lemma from the
  conditional example at chapter 16 lines 250-313 and marks extraction and
  final soundness complete. Existing receipts give standard-only closure for
  the conditional extraction helper and final `pauli_soundness`.
- All twelve sub-issues are closed `completed`. The open dependency #119 is not
  itself completed by these compositions. The seed-indexed/divisibility source
  gap tracked by #527 also remains explicit.

Required small correction: replace the three stale exact-name criteria with the
unconditional `exists_pulled_apart_consistency` criterion plus a separate note
that the `_ofGlobalPairWitness` declarations are supplied-witness auxiliaries.

## #165: Chapter 14 observables

All children #110-#116 and #204 are closed `completed`; there are no open
children or blockers. The source passages were checked across sampling
[51-93](https://github.com/Dengnifer/MIPStarRE-A/blob/04f79c5071d020fc4578b9ae11808eff2daa575b/references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex#L51-L93),
projective setup and winning implications
[155-265](https://github.com/Dengnifer/MIPStarRE-A/blob/04f79c5071d020fc4578b9ae11808eff2daa575b/references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex#L155-L265),
expanded points [364-486](https://github.com/Dengnifer/MIPStarRE-A/blob/04f79c5071d020fc4578b9ae11808eff2daa575b/references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex#L364-L486),
and expanded lines [523-678](https://github.com/Dengnifer/MIPStarRE-A/blob/04f79c5071d020fc4578b9ae11808eff2daa575b/references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex#L523-L678).

The complete target map is:

- #110: [`LineDefs.lean:186`](https://github.com/Dengnifer/MIPStarRE-A/blob/04f79c5071d020fc4578b9ae11808eff2daa575b/MIPStarRE/QPBT/Observables/LineDefs.lean#L186-L193) and
  [`Anticommuting.lean:325`](https://github.com/Dengnifer/MIPStarRE-A/blob/04f79c5071d020fc4578b9ae11808eff2daa575b/MIPStarRE/QPBT/Observables/Anticommuting.lean#L325-L572).
- #111: [`Setup.lean:299`](https://github.com/Dengnifer/MIPStarRE-A/blob/04f79c5071d020fc4578b9ae11808eff2daa575b/MIPStarRE/QPBT/Observables/Setup.lean#L299) and
  [`Defs.lean:211`](https://github.com/Dengnifer/MIPStarRE-A/blob/04f79c5071d020fc4578b9ae11808eff2daa575b/MIPStarRE/QPBT/Observables/Defs.lean#L211-L701).
- #112/#113: [`WinImplications.lean:34-249`](https://github.com/Dengnifer/MIPStarRE-A/blob/04f79c5071d020fc4578b9ae11808eff2daa575b/MIPStarRE/QPBT/Observables/WinImplications.lean#L34-L249), all seven exact and six approximate checks.
- #114: [`ExpandedDefs.lean:315-780`](https://github.com/Dengnifer/MIPStarRE-A/blob/04f79c5071d020fc4578b9ae11808eff2daa575b/MIPStarRE/QPBT/Observables/ExpandedDefs.lean#L315-L780).
- #115: [`WinImplications.lean:275-312`](https://github.com/Dengnifer/MIPStarRE-A/blob/04f79c5071d020fc4578b9ae11808eff2daa575b/MIPStarRE/QPBT/Observables/WinImplications.lean#L275-L312) and
  [`PointConsistency.lean:717-750`](https://github.com/Dengnifer/MIPStarRE-A/blob/04f79c5071d020fc4578b9ae11808eff2daa575b/MIPStarRE/QPBT/Observables/PointConsistency.lean#L717-L750).
- #116: [`Restriction.lean:112`](https://github.com/Dengnifer/MIPStarRE-A/blob/04f79c5071d020fc4578b9ae11808eff2daa575b/MIPStarRE/QPBT/Observables/LineMeasurement/Restriction.lean#L112),
  [`Expanded.lean:114-277`](https://github.com/Dengnifer/MIPStarRE-A/blob/04f79c5071d020fc4578b9ae11808eff2daa575b/MIPStarRE/QPBT/Observables/LineMeasurement/Expanded.lean#L114-L277), and
  [`LineMeasurement.lean:134-315`](https://github.com/Dengnifer/MIPStarRE-A/blob/04f79c5071d020fc4578b9ae11808eff2daa575b/MIPStarRE/QPBT/Observables/LineMeasurement.lean#L134-L315).
- #204: the helper-promotion cleanup is closed completed and introduces no
  remaining chapter target.

Chapter 14 links these groups with proof-level `\leanok` at
`fact:omega-anticomm-prob`, `lem:projective-strategy-setup`,
`lem:qld-win-implications`, `lem:qld-win-implications-obs`,
`lem:expanded-point-measurement-properties`, `lem:qld-comm-cons`,
`def:expanded-line-measurement`, and `lem:qld-comm-line-cons`.
Existing packet receipts include standard-only axiom checks; issue #116's
preserved harness checked 16 closures as exactly
`[propext, Classical.choice, Quot.sound]`.

## Non-claims

This supplement does not alter or recommend closure of **#524, #598, #527, or
#295**. In particular, closing #123 would not discharge #527, and closing #120
would not discharge #119 or the printed combining gap #598.
