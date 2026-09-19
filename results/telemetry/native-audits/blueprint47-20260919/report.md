# QPBT blueprint completion-status audit

Date: 2026-09-19

Worktree: `/home/drx/MIPStarRE-qpbt/.worktrees/issue-47-blueprint-completion-status-20260919`

Starting commit: `0acbabe827849c0e1fb7cb3fb114b1a375145706`

## Verdict

Five of the six targeted warnings were metadata-placement defects. The four
chapter-16 orphan warnings came from brace-spanning `\lean{...}` commands that
the orphan heuristic could not recognize. The chapter-14 header-only warning
came from placing `\leanok` on the first line of a multiline `\uses{...}`
command. Those five warnings are fixed without changing any mathematical prose,
statement, proof, or completion claim.

The remaining chapter-13 warning is justified and was not changed. The public
Lean theorem `MIPStarRE.QPBT.exists_ld_soundness` is source-faithful and
kernel-closed, but the blueprint proof block deliberately transcribes the
paper's printed tensor-code route. Its game-correspondence assertion and its
printed auxiliary-parameter choice remain open under issue #527. A proof-level
`\leanok` on that proof block would therefore certify proof prose that the
formalization does not implement.

## Warning classifications

1. `ch16_qpbt_extraction.tex:1480`, statement orphan for
   `thm:pauli-naimark-reduction-support`: false parser orphan. The node is a
   formalization-only result, not the unrestricted source theorem. Its Lean
   declarations construct the separate questionwise dilations, prove
   projectivity and exact value/state preservation, recover both full POVM
   families and their Pauli postprocessings by compression, construct the
   projective setting, and pull a supplied soundness witness back with exactly
   equal extracted-state distance. This matches the node, including its stated
   limitation that operator-family transfer is not proved there. Fixed by
   writing each existing declaration link as a complete `\lean{...}` command.

2. `ch16_qpbt_extraction.tex:1502`, proof orphan for the same node: false
   parser orphan inherited from the unrecognized statement link. The proof text
   matches `paddedStrategy`, `dilatedMeasurement`, compression, value
   preservation, and witness composition. The existing proof-level mark is
   justified and was not added or removed; the link normalization supplies its
   declaration context.

3. `ch16_qpbt_extraction.tex:1517`, statement orphan for
   `thm:pauli-naimark-operator-transfer-support`: false parser orphan. The Lean
   statements assume exactly a strategy, its questionwise Naimark dilation, and
   a soundness witness on the dilation, and conclude the displayed Alice and
   Bob bounds with coefficients 3 and 6. The node explicitly identifies this
   as formalization-only support and adds no source-theorem hypothesis. Fixed by
   splitting the two existing declaration links into complete commands.

4. `ch16_qpbt_extraction.tex:1540`, proof orphan for the same node: false
   parser orphan inherited from the statement formatting. The Lean proofs use
   the ground-range projection, its state-fixing property, the ideal EPR mirror
   identity, the compression estimate, and exact pullback identities, matching
   the blueprint proof. The existing proof-level mark is justified.

5. `ch13_qpbt_test.tex:245`, header-only `lem:ld-soundness`: justified and
   retained. Paper and Lean assumptions agree: universal `a >= 1` and
   `0 < b <= 1`; positive error; admissible `(q,m,d,k)`; a projective strategy;
   and success at least `1-epsilon`. `LdParams` packages the paper's domain
   conditions, and wrong-form answers are totalized by a fixed zero tuple to
   obtain a POVM. Paper and Lean conclusions agree in order and distribution:
   the two point/polynomial consistency bounds over uniform points and the
   global/global consistency bound without a question distribution, all at
   `deltaLd`. Verdict: exact statement with faithful boundary encoding. Lean's
   direct seed-compression proof is closed, but it avoids rather than proves
   the two open assertions in the printed proof. No metadata change is honest
   at this source-proof node.

6. `ch14_qpbt_observables.tex:1508`, header-only `lem:qld-comm-cons`:
   malformed completion metadata, fixed. The source assumes the successful
   projective setting established at the start of the analysis. Lean packages
   exactly this as `ProjectiveSetting P epsilon`. Item 1 is represented for all
   four directed opposite placements; averaging over the source's redundant
   `r` variable does not change the point relation. Item 2 is represented for
   all four same-register placements and both binary outcomes. The universal
   factors in Lean are faithful because the paper defines both approximation
   notations using `O(delta)`. `deltaAnticom = sqrt epsilon` satisfies the
   documented corrected polynomial-error predicate. Verdict: faithful
   statement and matching proof. Moving `\leanok` onto its own line makes the
   existing proof-level claim visible to the checker.

## Kernel closure

A focused Lean harness imported the four defining modules and ran
`#print axioms` for all 23 declarations linked by the audited nodes. Every one
reported exactly `[propext, Classical.choice, Quot.sound]`; none reported
`sorryAx` or a project-level axiom. This includes `exists_ld_soundness`, the
five chapter-14 declarations, all fourteen Naimark-reduction declarations, and
both operator-transfer theorems.

## Changes and checks

- Changed only `blueprint/src/chapter/ch14_qpbt_observables.tex` and
  `blueprint/src/chapter/ch16_qpbt_extraction.tex`.
- Diff size before commit: 18 insertions, 17 deletions; metadata only.
- `git diff --check`: passed.
- Label resolution passed for all four affected nodes.
- Refreshed the generated declaration inventory and reran blueprint sync:
  zero orphan `\leanok` warnings; chapter 14 is 85/85 proof-formalized and
  chapter 16 is 107/107; the only targeted warning left is the intentional
  `lem:ld-soundness` header-only warning; the checker reports the blueprint and
  Lean code in sync.
- `leanblueprint web`: exited successfully. It emitted missing-bibliography
  warnings because `web.bbl` was absent in the fresh worktree; no render error
  occurred.

No full build, canonical CI, push, PR, status write, primary-worktree source
edit, telemetry edit, Lean edit, script edit, or proof attempt was performed.
This audit makes no claim that all QPBT source statements are complete. The
known #524/#598 sites and the #527 printed-route correspondence obligations
remain explicit and outside this metadata repair.
