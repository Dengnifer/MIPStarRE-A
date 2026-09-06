<!-- owner-inbox id=B8 status=open -->
### BLOCKER B8 — issue118 exhausts ten ordinary mathfix attempts

**Decision requested:** how should the remaining mathematical gap proceed after
the shared ten-attempt limit? Main will hold it unless the human owner explicitly
authorizes further bounded work or another disposition. Main recommends keeping
the agreed source-faithful goal; there is no sufficiently justified correction
to adopt. This is the required budget-exhaustion escalation, not a request to
weaken a theorem or change a game implicitly.

**Final accounting:** attempt10 ended2026-09-06T03:36:00Z, exit0,2373 seconds.
Carry17558 +2373 = **19931 working seconds across ten attempts**. The original
anchor remains2026-09-05T19:24:00Z. No eleventh ordinary attempt is launched;
an effort/account/telemetry change cannot reset this budget.

**What is and is not established.** The printed results are `lem:qld-xz-lines`
and `lem:qld-4-13` in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`, respectively
882--894 and1020--1034. Actual POVMs, degree support, all-placement overlap
integration, both-placement ordered-product replacement, and the first-player
extended-line estimate are proved. The established two-player witness is still
missing Bob's X-factor removal and Z-overlap deficit bounds at `(BB', AB'')`.
The stronger printed error and full downstream sufficiency remain unestablished.

The defects are distinct: an older internal helper incorrectly omitted its
arbitrary supplied point error; the unrestricted completed collision assertion
is false because distinct `T` and `T+1` both map to `none` on a zero-direction
line; and the second extended-line proof route uses an unsupported joint
restricted-product law. **No counterexample to either printed existence theorem
is claimed.** Conditioning only the required collision calculation and restoring
its mass repairs that step, not the entire source theorem. Keeping point-error
dependence, polynomial specialization and the first-route bound yielded useful
increments but did not satisfy all correctness/sufficiency/minimality/convergence
conditions. A joint-law assumption would not itself recover the printed error.

**Evidence:** commit76f82b6138a1ca5ddf9c7f2946d2ac673f993aa6 in the issue118
worktree. Targeted Lean plus affected root imports pass with private artifacts;
six inspected axiom closures contain only the standard trio; blueprint web,
1883 declaration checks, an18-page gap PDF and normal commit hooks pass. There
are zero holes in Lines and the same three existing holes in Apply. No new
source assumption, game change, fallback witness or final correction is adopted.
CI/review/merge have not certified this final increment.

The self-contained ten-attempt ledger, candidate comparisons, proof sketches,
counterexamples and source/consumer audit begin at
`audits/2026-09-06-issue118-point-error-dependency.md:3` in that worktree. Missing
aggregate consumer certification includes global-pair use1278--1282 and
extraction uses1423,1465--1492,1584,1627,1671 in the same paper mirror. Given-
witness issue244 construction does not supply the missing witness. Issues119
and its dependent source-theorem tails stay held; independent proofs and normal
publication/review continue. B7 is a separate already-posted owner decision and
remains unanswered. Once posted, B8 also waits for the human owner.
