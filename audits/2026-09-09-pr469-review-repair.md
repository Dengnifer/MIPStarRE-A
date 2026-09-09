# PR469: Source Scope and Review Repair

This audit concerns the repair of the eleven findings in review 5151223421,
which reviewed commit `66b206233b49e08eb8aaa81c6c2482f64c9b7d12`.
It is an author statement-integrity audit, not an independent review.

## Source and Scope

The primary source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`:
`lem:qld-4-10` (689-709), `lem:qld-xz-lines` (882-961), the restricted
distribution discussion (1038-1061), `lem:qld-sublines` (1063-1116), and
`claim:17-1` through `claim:17-3` (1140-1239).

The authorized repair removes unsupported source certification. It does not
attempt the exhausted dimension-divisibility problem, add bridge assumptions,
or claim a new mathematical correction. At the dependency checks during this
repair, PR478's published head was
`25fa5893d0f2e3db4cbe37a450310a222ef9b3e7`. Its diff from the reviewed PR469
head adds the concrete X deficit and an import, not a source-realignment
correction. No unpublished content from its active checkout was used or changed.

## Statement Integrity

### Claims 17-1 and 17-3

- Paper assumptions: admissible projective strategy, the joint point and paired
  line measurements with their established error bounds, and the source
  seed-indexed subline distribution.
- Lean assumptions: the same strategy and measurement witness types, but
  `SubLineWitness` specifies the directly indexed extended-line marginal.
- Paper conclusions: complex correlation differences are small, with errors
  of order `sqrt(deltaQ)` and
  `sqrt(m) * (deltaP^(1/4) + deltaQ^(1/4) + epsilon^(1/4))`, respectively.
- Lean conclusions: the corresponding absolute real-part differences under
  the directly indexed law. The proofs supply the universal constant 2.
- Verdict: different distribution and weaker scalar conclusions. The proved
  declarations now end in `_re_direct` and are linked only to auxiliary
  blueprint entries displaying these differences. The original source
  targets remain unchanged and uncertified in the blueprint.

### Claim 17-2

- Paper assumptions: the concrete X-Z-X sandwich measurement, a projective
  strategy, and the source subline distribution, not an arbitrary line witness.
- Lean assumptions: the concrete sandwich and strategy, but the directly
  indexed subline witness. No additional marginal or consistency assumption.
- Paper conclusion: complex-modulus difference at most `C*m*sqrt(deltaLine)`.
- Lean conclusion: absolute real-part difference with that error scale under
  the directly indexed law, retained as an unfinished internal obligation.
- Verdict: construction domain preserved; scalar and distribution mismatches
  remain. `subline_remove_X_factor_re_direct` is not linked to the source
  claim. Its existing proof hole is tracked by issues #414 and #466 and the
  paper-gap note. Source complex-modulus targets remain in the blueprint.

### Completed Constructions

- Joint points: the paper and Lean assume a projective setting and conclude
  projective field-pair measurements with polynomial error and all four
  directed opposite-placement comparisons. Verdict: faithful encoding. The
  blueprint now describes the proved field-valued sandwich and
  orthonormalization construction on the original local spaces, rather than
  the source's binary linearity argument requiring additional padding.
- Restricted distributions: the paper and Lean use the original admissible
  dimension and restricted line laws. Both give normalization, mixture
  decomposition, and error factors `2*m` and `4*m^2`. Verdict: faithful encoding;
  only proof-status tags changed.
- Paired lines: the definition is exactly the paper's X-Z-X sandwich; summing
  Z gives the X effect by completeness and projectivity. Verdict: exact
  construction identities, now separately linked without certifying the
  unfinished evaluated consistency estimate.

## Finding Dispositions

These are repair claims for main to assess, not edits to the independent ledger.

| Finding | Repair |
| --- | --- |
| F1 | Separate real-part auxiliaries from unchanged complex source targets. |
| F2 | Re-export `Placement` from `PlacementSupport`; no duplicate declarations. |
| F3 | Reuse placed measurements, regrouping, completed-pair norm sum, product averaging, and optional-evaluation APIs. |
| F4 | Separate direct-law construction, uniform-point result, and scalar estimates from source-law entries. |
| F5 | Replace the intermediate `W^2`, `deltaQ`, and `sqrt(deltaQ)` by `W` adjoint times `W`, `4*deltaQ`, and `2*sqrt(deltaQ)`. |
| F6 | Synchronize the joint-point proof and its dependencies with orthonormalization. |
| F7 | Mark the proved restricted distributions and mixture estimates complete. |
| F8 | Remove the unmatched-statement tag from the correctly stated internal consistency obligation; retain its unfinished proof status. |
| F9 | Link the concrete paired-line construction and exact X marginal separately. |
| F10 | Correct the description of preceding and later coordinate blocks. |
| F11 | Remove the obsolete placement helper and replace the module-history terminology. |

## Remaining Obligations

No new `sorry` is introduced. The affected claim and line modules retain
`subline_remove_X_factor_re_direct` and
`combined_line_measurement_consistency`. The former requires the exact X
marginal and restricted X line-point deficit argument; the latter requires
the point-to-line and pasting argument. The complex scalar proofs and
source-distribution correspondence are not claimed complete. The gap note
`docs/paper-gaps/qpbt_subline-claims-line-marginal.tex` records both distinctions.

PR478 and its descendants will need to reconcile their claim names and source
scope with this repair. No review was dispatched or published by this author.

## Publication Checkpoint

The first checked publication of repair commit `ed064873` passed changed-file
Lean, blueprint rendering, and statement-integrity checks, then stopped before
transport because the reverse blueprint-coverage check found three merge bases
with `origin/main`. To preserve the history without bypassing that check, the
issue branch merged verified published main
`1c297a4b8fb8a74b64784ba4c8fe7e10d0ffc6ee`. Only the append-only event log
conflicted; both sides were retained. Incoming Lean changes were preserved.
The primary checkout was not modified by this repair.
