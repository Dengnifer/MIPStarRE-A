# Statement correction: the printed combined-lines error form (issue 598)

Date: 2026-09-19. Branch
`issue-598-printed-claim-statement-correction-20260919`.

## What this audit covers

The single `sorry` in `MIPStarRE/QPBT/Combining/Apply.lean`, carried by the
theorem `exists_extendedLinesWitness`, and its replacement by a `Prop`-valued
definition that records the same statement without asserting it.

## Statement-integrity audit

Paper locator: `lem:qld-4-13`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034`.
Blueprint node: `lem:qld-4-13`
(`blueprint/src/chapter/ch15_qpbt_combining.tex`).

| | Before | After |
|---|---|---|
| Lean name | `exists_extendedLinesWitness` | `PrintedExtendedLinesWitnessClaim` |
| Kind | `theorem` | `def ... : Prop` |
| Binders and body | the printed conclusion | **unchanged**, character for character |
| Proof | `sorry` | none: nothing is asserted |
| Blueprint mark | `\notready`, no `\leanok` | `\notready`, no `\leanok` (unchanged) |

- Paper assumptions: admissible parameters `(q, m, d)` and a projective
  strategy passing with error `epsilon`.
- Lean assumptions: the same, as the binders of the recorded proposition.
- Paper conclusion: existence of extended-line measurements with error
  `poly(m^2 * epsilon, md / q)`.
- Lean conclusion: none. The proposition is stated, not asserted.
- Verdict: **statement preserved, assertion withdrawn.** This is not a
  weakening of a theorem: no theorem with a weaker conclusion replaces it. The
  printed sentence is still written down in Lean, at the same node, with the
  same binders and the same error expression. What changed is that the
  development no longer claims it, and no longer owes a proof of it.

## Why this is the right correction here

The printed error form is established by neither route of the source proof and
no route to it is known (`docs/paper-gaps/qpbt_combined-lines-error-term.tex`).
It is also not refuted: `not_exists_combining_quarter_power_bound`
(`MIPStarRE/QPBT/Combining/ErrorObstruction.lean`) obstructs the first route,
but an upper bound on a defect need not be attained, so the obstruction is not
a counterexample. A claim that is neither proved nor refuted must not be
asserted, and the definition of done of issue 598 forbids removing it or
restating it at the established error. A `Prop` that is stated but not asserted
is the only construction that satisfies all three constraints at once.

## No implication theorem was added

Neither direction between `PrintedExtendedLinesWitnessClaim` and
`exists_extendedLinesWitness_established` follows by a short faithful argument,
so neither was added.

- Printed implies established: the printed form applies an arbitrary
  `IsPolyErr2` function to `m ^ 2 * epsilon`, contributing `m ^ (2 r)` for the
  function's exponent `r`. The established form carries the single prefactor
  `m` outside its error function. For `r > 1/2` the first is not dominated by
  the second uniformly in `m`, so no rewriting of the error function delivers
  the implication.
- Established implies printed: this is the direction the first route would take
  and is exactly what `not_exists_combining_quarter_power_bound` obstructs
  along that route.

Forcing either direction would need a new estimate, which is the open content
of issue 598 and is out of scope here.

## Dependency check

No declaration depended on `exists_extendedLinesWitness`. The sole consumer of
the node, `exists_globalPairWitness`, routes through
`exists_extendedLinesWitness_established`, which is proved and is unchanged by
this branch. The removal therefore breaks nothing; the three modules that
import `MIPStarRE/QPBT/Combining/Apply.lean` (`MIPStarRE/QPBT.lean`,
`MIPStarRE/QPBT/Extraction/Construction.lean`,
`MIPStarRE/QPBT/Extraction/SourceUnitary.lean`) build unchanged.

## Documentation updated

- `MIPStarRE/QPBT/Combining/Apply.lean`: module docstring and the def-site
  docstring, which now states what the paper prints, the locator, that the
  printed proof does not establish it, and points to the established theorem,
  to the obstruction theorem, and to the gap note.
- `MIPStarRE/QPBT/Combining/ErrorObstruction.lean` and
  `MIPStarRE/QPBT/Combining/Lines/SubLineJoint.lean`: the two cross-references
  to the old name.
- `blueprint/src/chapter/ch15_qpbt_combining.tex`: the `\lean{...}` link of
  `lem:qld-4-13` and its in-node comment; the closing paragraph of
  `rem:qld-4-13-source-defects`.
- `docs/paper-gaps/qpbt_combined-lines-error-term.tex`: new section
  `sec:printed-claim-correction`, and the three earlier passages that described
  the old theorem.
- `docs/paper-gaps/qpbt-gap-register.md`: the `lem:qld-4-13` row.

Historical audit files under `audits/` keep the old name; they are dated
records of what was true when they were written and are not revised.

## Blueprint marks

`lem:qld-4-13` keeps `\notready` and acquires no `\leanok`, on the statement
or on the proof. The established content of the node stays where it was, on the
formalization-support node `lem:qld-4-13-established`, which links the proved
theorem. Marking the source-labelled node would be statement drift: the
established theorem differs from the source lemma in its error form and in
three carrier respects (directly indexed questions, directly indexed
line-point law, `Option`-completed answers), as the register row records.
