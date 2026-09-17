---
title: "Integration of the completed global polynomial-pair theorem"
date: 2026-09-14
purpose: "Receipt for the bounded, owner-authorized native integration delegate"
issue: "#513"
status: complete
---

# Scope

Local integration only, in `issue-513-independent-attempt3-20260912`.
The primary instructions, local README and DESIGN, source audit, and paper
passages were read before the sole mathematical-module edit. Initial status
was clean; the primary `worktree-setup.sh <worktree> --check` passed without
repair. The installed toolchain is Lean 4.32.0.

# Source of Truth

- Completed proof head: `097579724e42362f7b28aa850eb19213198dd41e`.
- Pinned incoming main: `391d6fcaa979d59647f3c8b3a7b049a13d4eac29`.
- Merge: `2527c63033d14a2b16505c4c28371e3f05df7c35`, with those two parents
  in that order; created by normal `git merge --no-ff --no-commit` and commit.
- Source audit: `audits/2026-09-14_issue-513_actual-error-absorption.md`.
- Paper: `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`,
  `lem:qld-4-7` (1267--1404), and the marginal displays at 914--930.

# Findings

There were no textual conflicts. Main newly exports
`CombinedPointsWitness.marginal_X_distance_le` and
`CombinedPointsWitness.marginal_Z_distance_le` through
`Points.WitnessMarginals`. Both declarations, including their proof bodies,
were byte-identical to the recovered copies in `Lines/PointComparison.lean`.
The sole manual Lean edit removes those duplicate copies and documents reuse
through the existing `Points` import. No mathematical statement changes.

All 77 incoming changed paths, including telemetry and history, were retained
with the normal merge result. The complete 78-path merge delta is recorded in
`.lake/Issue513IntegrationPaths.txt`; this receipt is the only later tracked
addition. The final head is the receipt commit immediately after the merge.

# Required Action

No local integration blocker remains. Read-only primary `gh_common.py`
queries confirmed that PR535 and issue513 are open and target this theorem.
PR535 remains the appropriate existing publication route by scope, but its
head is `1744bd9533055b9b43af9a8d46906cbafb69afdd` on
`issue-513-proof-exists-globalpairwitness`. It is not an ancestor of this
branch. The owner must reconcile that branch's history, publish through the
normal checked-push route, and align its local worktree with the published
head before using the existing gates. No branch was retargeted or published.

Exact next gate commands, for the owner after that reconciliation and
publication (not executed by this delegate):

```bash
python3 /home/drx/MIPStarRE-qpbt/local/bin/gh_common.py pr-view 535
/home/drx/MIPStarRE-qpbt/local/bin/ci.sh 535 --worktree /home/drx/MIPStarRE-qpbt/.worktrees/issue-513-proof-exists-globalpairwitness
/home/drx/MIPStarRE-qpbt/local/bin/review.sh 535
```

The review command follows green CI on the same published head and remains
the owner's separately managed independent lane.

# Validation

Normal pre-commit and reference-transaction hooks passed without overrides;
the primary merge-loss guard also passed on the committed merge. Whitespace
checks passed. The worktree was clean after the merge; the receipt is committed
separately, with final cleanliness checked before handoff.

Focused checks passed for incoming changed Lean modules, the repaired
`PointComparison.lean`, `Apply.lean`, and the `MIPStarRE/QPBT.lean` aggregate.
Existing private dependency products were reused. The initial recursive
checker was stopped to avoid rebuilding unchanged consumers of an aggregate
import; its completed checks remain in `.lake/Issue513IntegrationCheck.log`.
The final checker uses the pinned proof head to detect staged or committed
changes. Reproduction commands, from this assigned worktree:

```bash
python3 .lake/issue513-check.py MIPStarRE.QPBT.Combining.Apply MIPStarRE.QPBT
lake env lean .lake/Issue513FinalAxioms.lean
```

Final logs: `.lake/Issue513IntegrationFocused.log`,
`.lake/Issue513IntegrationAxioms.log`, and `.lake/Issue513IntegrationCommit.log`.
The full explicit signature, field expansion, and all thirteen axiom queries
are byte-identical to `.lake/Issue513FinalAxioms.log` from the completed proof.
Every queried closure contains exactly `propext`, `Classical.choice`, and
`Quot.sound`. Only the three preexisting separate line obligations warn about
`sorry`; no new hole, axiom, or proof bypass was introduced.

# Statement Integrity

Paper assumptions: admissible parameters and a projective Pauli strategy
passing with positive error. Lean assumptions: unchanged `AdmissibleParams`,
positive error, and `ProjectiveSetting`. Paper conclusion: universal constants
first, complete projective polynomial-pair measurements on both expanded local
spaces, and consistency for both bases on both sides. Lean conclusion:
unchanged `GlobalPairWitness` at `deltaQld`, with those four consistency bounds.
Verdict: faithful boundary encoding, with no extra assumption or changed
quantifier. The entire `Apply.lean` and `Witnesses.lean` files are unchanged.

# Review Use

This is integration evidence, not independent review or full-build evidence.
The completed proof, actual scalar bound, pair construction, blueprint
completion markers, separate line obligations, source-route gap status, and
completion audit are unchanged. CI, review, dispatch, publication, runtime
changes, other worktrees, and the frozen PR552 were outside this task.

# History And Costs

The former prover thread `01a09fc1-6d41-7ab1-8940-affe6e783ab1` completed at
12:15:52Z under its cumulative 25-minute MAX limit. Its audit and all earlier
costs are preserved without reset or reattribution. This integration has its
separate 15-minute limit from dispatch; the first clock query was 12:25:40Z.
Main records the authoritative native rollout span and usage after handoff.
No descendants were launched. Private compilation used the assigned
worktree's existing `.lake` storage, physically under its dedicated
`/data/users/drx/mipstarre-cache/lake/issue-513-independent-attempt3-20260912/`
directory; no shared hot-cache products were written.
