<!-- scout: scout-118-publication-20260906-01 2026-09-06 -->
## Mathlib scouting report — 2026-09-06

**Recommendation:** extract the three existing scalar proofs as one Lean-only auxiliary packet on current main. Keep the established two-player witness packet pending the actual #115–#117 merges. Neither packet completes the printed stronger error or global-pair construction.

Inspected checkpoint: `0f4ef05370350f4017439ebd839ef0561f13130f`. Main advanced during this assessment; the final comparison uses `928328ff4d45e5fdc2844b120329a2c241a3a58a`, also recorded by both remote-tracking main refs.

### Mathematical source

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:882`, `lem:qld-xz-lines`: paired-line POVMs with polynomial consistency error and axis-degree support.
- Same file, `:1020`, `lem:qld-4-13`: extended-line POVMs with both field-answer comparisons and printed error `poly(m²ε,md/q)`. The validated auxiliary instead establishes directly indexed, completed-answer comparisons with error `C*m*g(ε,md/q)`.
- Same file, `:1278` and `:1402`, proof of `lem:qld-4-7`: the existing scalar absorption proves the required numerical substitution; constructing the global projective measurements remains separate.
- Existing consumer audit: `audits/2026-09-06-issue118-point-error-dependency.md:125`. Its extraction and final-test consumers remain dependent on the missing global witness.

### Relevant Mathlib definitions

- `Real.rpow` — `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:35` — real powers underlying all three scalar bounds.

### Relevant Mathlib lemmas and theorems

- `Real.rpow_add_le_add_rpow` — `Mathlib/Analysis/MeanInequalitiesPow.lean:209` — subadditivity for exponents between zero and one.
- `Real.rpow_le_rpow_of_exponent_ge'` — `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:725` — exponent comparison on `[0,1]`, including zero.
- `Real.rpow_le_rpow_of_exponent_le` — same file, `:615` — exponent comparison above one.
- `Real.sqrt_le_sqrt` — `Mathlib/Analysis/Real/Sqrt.lean:209` — transports the supplied point-error majorant through square roots.

These are already used by the validated proofs; no replacement mathematical argument is needed.

### Relevant MIPStarRE declarations

All declaration names below have prefix `MIPStarRE.QPBT.`; locations refer to the checkpoint.

| Declaration | File:line | Publication assessment |
|---|---|---|
| `exists_conditioned_polynomial_bound` | `MIPStarRE/QPBT/Combining/Lines.lean:2154` | Proved; independent scalar conditioning estimate. |
| `exists_combining_polynomial_bound` | `MIPStarRE/QPBT/Combining/Apply.lean:1342` | Proved; independent scalar composition retaining the dimension factor. |
| `exists_globalPair_error_bound` | `MIPStarRE/QPBT/Combining/Apply.lean:1660` | Proved; independent global-pair numerical absorption. |
| `exists_combinedLinesWitness` | `MIPStarRE/QPBT/Combining/Lines.lean:2401` | Proved on the parent stack; paired-line construction. |
| `exists_extendedLinesWitness_established` | `MIPStarRE/QPBT/Combining/Apply.lean:1636` | Proved on the parent stack; supplies points and both completed-answer consistencies. |

The scalar packet needs only existing main definitions: `MIPStarRE.QPBT.IsPolyErr` and `MIPStarRE.QPBT.IsPolyErr₂` in `Games/ErrorFunctions.lean:27,44`; `MIPStarRE.QPBT.deltaLd` in `Test/LowDegreeGameTheorems.lean:374`; `MIPStarRE.QPBT.deltaQld` in `Test/SoundnessDefs.lean:35`; and admissible-parameter facts in `Test/PauliBasisTest.lean:37,51`.

### Suggested approach

1. **Extract the scalar packet mechanically.** Take the two scalar proofs introduced in `f6a340c8dc3c12566d9312215c578939efeb8b4a` and the global absorption proof from `0f4ef05`, preserving statements and proof bodies. A focused `Combining/ErrorBounds.lean` can import the existing definition modules and Mathlib inequalities. Their proofs require no point/line witness, soundness theorem, or new bridge assumption.
2. **Keep documentation scalar-specific.** Add auxiliary blueprint statements for exactly these inequalities. The checkpoint’s grouped polynomial-specialization node also certifies mass and symmetry results, and its global-absorption node references the unmerged witness node; neither should be copied wholesale into an independent scalar publication.
3. **Publish the witness packet after parent integration.** Its authored closure includes `Combining/Lines.lean`, `Lines/*`, `Claims.lean`, `Apply.lean`, `EvalDeficit.lean`, `SubLineDeficit.lean`, `OrderedPoints.lean`, `OverlapGap.lean`, and `UniformLinePoint.lean`, with matching witness documentation, blueprint entries, and gap notes. `Combining/Defs.lean`, `Linearity.lean`, `Points.lean`, `Points/*`, and the observable implementations are inherited prerequisite content. Integrate current parent results before selecting issue118 changes; copying the checkpoint tree would lose newer main work.

GitHub access through `gh_common.py issue-view 118` failed with sandbox `socket: operation not permitted`. The following distinguishes frozen GitHub evidence from locally available actual merge objects:

| Dependency | Available evidence |
|---|---|
| #115 / PR207 | Issue and PR open in snapshot `2026-09-06T02:15:57Z`; implementation remains unmerged into pinned main. |
| #116 / PR213 | Issue and PR open in that snapshot; implementation remains unmerged into pinned main. |
| #117 / PR212 | PR open in that snapshot; implementation remains unmerged. Current issue state unavailable. Checkpoint inherited head `6b4b75d408be5399a1867166bffcc3aa56de6e4b`. |
| #113 / PR195 | Actual merge on main: `928328ff4d45e5fdc2844b120329a2c241a3a58a`. Supersedes the snapshot’s open PR state. |
| #114 / PR178 | Actual merge: `5e657fe01f7e60f752ababde00f9aafd9a4afe4d`. |
| #201 / PR205 | Actual corrected-pasting merge: `223f01a10241e8006db04166fcfdd6acdff02663`. Checkpoint used the earlier `7d0af711c5c6769151e41cf091288855fdb409b0`. |
| #99 / PR138; #109 / PR153 | Actual merges: `d3eba7ec10aa2269f469c7bb72cd3d4a55badcce`; `22a426882ecedb36146990fb4fb059e11694b03d`. |

Inherited sampling, geometry, and distance prerequisites #110, #106, and #49 are already on pinned main. Live `blocked_by` edges and current issue118 comments could not be checked; the frozen open-PR snapshot contains no exact issue118-branch PR.

### Gaps to fill

- The scalar extraction is a dependency-supported publication candidate, **not yet validated on main**. Existing checkpoint checks and axiom audits passed; the extracted module will need normal focused validation, CI, and independent review.
- Two direct holes remain: `MIPStarRE.QPBT.exists_extendedLinesWitness_ofPointsWitness` at `Combining/Apply.lean:1486`, and `MIPStarRE.QPBT.exists_globalPairWitness` at `:1933`. Preserve both obligations and their source discrepancies.
- Avoid duplicating #241’s distinct `MIPStarRE.QPBT.deltaExtract_le_deltaQld` (`Extraction/Unitary.lean:122` on that branch). #244’s `MIPStarRE.QPBT.ExtendedLineGame.projectiveStrategy_value` (`Combining/ExtendedLineGame.lean:457`) preserves game value given a witness; it does not establish the required passing bound.

### Searched

Read committed-main scout prompts, frozen issue118 body, API notes, paper passages, existing consumer/validation audit, blueprint nodes, commit ancestry, parent diffs, declaration bodies, and #241/#244 branches. Searched Mathlib power/root modules by names and inequality shapes, plus main for all three scalar statements and related error expressions; no existing replacement for this scalar packet was found.

No files changed, builds, proof attempts, publication, or collaboration occurred. Preserve the original `2026-09-05T19:24:00Z` anchor and all twelve cumulative attempt/time records unchanged.