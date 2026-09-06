# Issue 201: the one-sided pasting assertion

## Decision and scope

The second review of PR 205 at `d1d7ea0b10fcec468bfc7c1348ffd87fa094d255`
disputes the source justification for the fourth comparison in
`exists_pasting_error`. Do not dismiss that finding because the restricted
theorem compiles or because its immediate application has the extra comparison.
Reopen the existing mathematical gap. Preserve the additive polynomial-error
correction, which has a separate counterexample and is not the present dispute.

Work only in `.worktrees/issue-201-pasting-error-contract`. Do not touch the
Claude-controlled worktrees for issues 118 or 174, any review mailbox, other
branches, or track B. No other worker owns the PR 205 worktree now. Do not push,
merge, dispatch other sessions, or repair unrelated review findings. Mechanical
review fixes remain the responsibility of `autofix.sh` after this investigation.

## Source and obstruction

Read these passages in their full mathematical context:

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-526`,
  `lem:pasting`, with `eq:pasting-1`, `eq:pasting-2`, and `eq:pasting-3`.
- The same file, lines 77-91 and 165-180: the definition of a symmetric
  strategy and the qualified statement that attention is almost always
  restricted to symmetric strategies. A definition alone is not an ambient
  assumption for every subsequent operator lemma.
- `references/neexp-paper/05_quantum_preliminaries.tex:995-1185`,
  `fact:low-degree-sandwich-on-steroids`, especially the register move near
  lines 1150-1175. Determine whether its hypotheses actually justify that move.
- `docs/paper-gaps/qpbt_pasting-product-error.tex`, especially the pinched
  defect, the one-sided obstruction, and the claimed source justification for
  `eq:pasting-1-sym`. Treat the previous adoption as a conclusion to verify,
  not as a substitute for source evidence.

The printed assumptions are a conditional collision bound, projectivity of
the second codeword family and the joint answer measurement, two forward
marginal comparisons, and self-consistency of the joint answer measurement.
The current Lean theorem additionally assumes the register-exchanged second
marginal comparison. Its proof uses that assumption in
`Games/Sandwich/Pasting/CodewordConsistency.lean` to control cross consistency,
then in `Games/Sandwich/Pasting/Assembly.lean` to bound fine commutators.

The existing note knows no counterexample to the one-sided theorem. Its proof
reduces the question to bounding the first-marginal defect after pinching by
the fine second-codeword measurement. Naive collision estimates introduce an
unacceptable factor depending on the number of codewords. A missing proof is
not evidence that adding a convenient hypothesis is a necessary correction.

## Required result

First seek an actual source passage establishing the claimed domain, or a
dimension-independent proof of the printed one-sided assertion. The target is
the original assumptions and conclusion, not merely deriving the extra
comparison; the latter need not follow even when the target conclusion does.
Use the existing proved matrix and measurement APIs rather than adding axioms,
assumed intermediate estimates, or custom copies of Mathlib results.

If a genuine source counterexample is found, verify it and compare the closest
sufficient corrections by logical strength. Any adopted correction requires a
proof, adversarial checks, and every downstream use to remain justified. A
definition or game change requires immediate return of an owner-decision
packet; do not implement it.

If the printed result remains unproved, report the precise named obligation.
Do not retain an unsupported restriction under the source theorem's name and
proof-complete blueprint marker. Paper-realignment may preserve the proved
restricted result separately and leave a tracked source-faithful obligation,
but that is incomplete work, not convergence or the project goal. Follow the
repository's explicit realignment and unfaithful-dependency policies.

Inspect all paper uses, blueprint descendants, and Lean consumers, including
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:938-962`,
`lem:qld-xz-lines`, `lem:qld-4-10`, and the combining/extraction chain. Read
other branches only through the primary repository's Git objects if needed;
do not access the protected issue 118 worktree. The current note's assertion
that there is only one use must itself be checked.

## Budget and validation

This is the third designated math-fix session on this gap. Prior sessions:

- `fable-mathfix-201-20260904T2345Z`: September 4, 23:45Z to September 5,
  03:20Z; terminated after output-limit failures.
- `fable-mathfix-201-pasting-s2-20260905T0700Z`: September 5, 06:52Z to
  07:19Z; adopted the disputed symmetry justification.
- Also retain the related partial Fable prover at 06:20Z-06:49Z. For safety,
  charge it as an additional gap-related session: this attempt consumes slot
  four of ten, not a fresh budget. Logged prior worker time totals about
  4 hours 31 minutes; the original start time and operator investigation time
  remain part of the cumulative record.

Do not exceed ten cumulative sessions or about 1.5 working days for this gap.
Return after a focused attempt rather than consuming the whole remaining
budget in one session. Report elapsed time and remaining obstacles honestly.

Use `MIPSTARRE_CODEX_MODEL=gpt-6-astra`, role `mathfix`, effort `ultra`.
Read `AGENTS.md`, the mathematical-gap protocol, and applicable local rules.
Validate each changed Lean file before broader checks; full builds use the
machine-wide lock and never write the hot cache. Do not weaken audit guards.
Commit only converged mathematics or independently valid documentation.
End with the paper/Lean assumption-and-conclusion audit, the downstream-use
analysis, exact files changed, checks performed, and any remaining obligation.
