# Exact ground-coordinate compression of finite measurements

Issue: #277. Session: `prover-277-20260906-01`.

## Source and auxiliary scope

The proof of `lem:qld-4-7` in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1278-1288`
applies Naimark dilation before classical low-degree soundness and again to
the resulting polynomial POVM, preserving consistency at each step.
Consistency is the averaged off-diagonal correlation defined in
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:232-248`.

`MIPStarRE/QPBT/Games/GroundCompression.lean` supplies a Lean-only auxiliary
for comparison of measurements on the enlarged and original spaces. It does
not prove or change `lem:qld-4-7`. The blueprint entry remains unchanged,
and the module has deliberately not been added to any shared re-export.

## Construction and proof

Let a finite POVM have effects \(M_a\) on \(I\times K\), and fix
\(k_0\in K\). Its compression has effects
\[
 C_a(i,j)=M_a((i,k_0),(j,k_0)).
\]
This is the principal submatrix along the inclusion \(i\mapsto(i,k_0)\).
Mathlib's `Matrix.PosSemidef.submatrix` proves positivity. Evaluating
\(\sum_a M_a=1\) at the distinguished coordinates proves
\(\sum_a C_a=1\). Both proofs are fields of the constructed
`Quantum.Measurement`; no extra proof obligations are input to the constructor.

For a finite outcome map \(f\), evaluation of a matrix sum gives
\[
 \operatorname{compress}(f_*M)=f_*(\operatorname{compress}(M)).
\]
`ground_compress_measurement_postprocess` proves equality of the complete
measurements using the existing measurement extensionality theorem.

For independent spaces \(I,J,K,L\), coordinates \(k_0,l_0\), and any
vector \(\psi\) on \(I\times J\), the existing `stateQForm_padState`
identity gives
\[
 \langle\operatorname{pad}(\psi),
 (A_a\otimes B_b)\operatorname{pad}(\psi)\rangle
 =\langle\psi,(C_a\otimes D_b)\psi\rangle.
\]
The Lean correlation theorem uses the real part of this equality, exactly
as in `vectorQForm` and `consistencyDefect`. Summing over unequal outcomes
and averaging proves `consistency_defect_ground_compress_measurement`.
The corresponding `IsConsistentWithin` equivalence retains the same error.
The postprocessing corollary allows question-dependent maps from distinct
original outcome types into a shared final alphabet.

Finally, `ground_compress_dilated_measurement` recovers the original POVM
from `dilatedMeasurement` at the `none` coordinate by the existing
`dilatedMeasurement_compression` theorem. The dilation is not reproved.

## Statement integrity

Paper assumptions and conclusion: the cited passage applies Naimark dilation
to POVMs and retains their consistency guarantees on the padded state.

Lean assumptions: finite coordinate and outcome types, decidable equality
where needed by the matrix and finite-sum APIs, distinguished ancilla
coordinates, POVMs, and an arbitrary bipartite vector. The consistency
identity allows every `Distribution X`; normalization is unnecessary for
this algebraic equality. Neither player spaces nor ancilla spaces are
identified. No bridge or conclusion-shaped hypothesis is introduced.

Lean conclusion: a complete positive compressed measurement, exact
commutation with outcome postprocessing, exact equality of bipartite
consistency defects, and recovery of the existing dilation's original POVM.
Verdict: exact auxiliary identities with faithful boundary hypotheses.
No paper-labelled theorem statement changes.

Projectivity is not a conclusion. Even the compression of the rank-one
projection with all four entries equal to \(1/2\) onto its first coordinate
is the scalar \(1/2\), which is not idempotent. Downstream use on the original
spaces must therefore apply the separate projective-rounding theorem and
account for its error. The polynomial-support argument is also separate.

## Verification

- Baseline `lake env lean MIPStarRE/QPBT/Games/StrategyClasses.lean` passed
  with its existing warning at line 886. The new declarations do not depend
  on that unfinished declaration.
- The new file passed `lake env lean` without diagnostics. A subsequent
  file-level check with `-o .lake/build/lib/lean/MIPStarRE/QPBT/Games/GroundCompression.olean`
  also passed after the postprocessing corollary was added.
- `rg -n 'sorry|axiom' MIPStarRE/QPBT/Games/GroundCompression.lean` produced
  no matches (exit 1). The forbidden-token and over-100-character scans
  also produced no matches.
- A separate `lake env lean --stdin` invocation imported the compiled module
  and ran `#print axioms` on all eight new declarations. Each closure was
  exactly `[propext, Classical.choice, Quot.sound]`.
- The source was checked against anti-patterns A1-A6: effects are actual
  principal submatrices, and proofs use Mathlib and established local APIs.
- Hook installation failed because the shared `.git/config` is read-only
  in this sandbox. The following `scripts/install_git_hooks.sh --check`
  passed: `core.hooksPath=.githooks`, with executable hooks already installed.

## Downstream handoff

The integrator owns the re-export and use in the global polynomial-pair
construction. The first declarations to inspect are
`groundCompressMeasurement` and
`consistency_defect_ground_compress_measurement_postprocess`.
There are no open obligations in this module. Independent review and
exact-head CI remain required before merging.

This auxiliary session does not change the B8 accounting: twelve mathfix
attempts, 24,242 seconds, anchor `2026-09-05T19:24:00Z`.

## Publication checkpoint

After the validation above, the exact staging operation was
`git add MIPStarRE/QPBT/Games/GroundCompression.lean audits/2026-09-06_ground-compression-277.md`.
It failed with exit 128 because Git could not create
`/home/drx/MIPStarRE-qpbt/.git/worktrees/issue-277-ground-compression/index.lock`:
`Read-only file system`. Both new files remain in the assigned worktree.
The session's approval policy is `never`; supported escalation is unavailable.
No alternate Git directory, sandbox, account, or publication route was used.

Consequently no commit, checked push, PR, exact-head CI, or independent review
was performed. Main must complete these steps from an authorized session;
the intended commit subject is
`feat(QPBT/Games): Add exact ground compression of measurements`.
Main should also record the shared-Git write denial in the primary telemetry
incident ledger; that ledger is outside this packet's edit ownership.

No full `lake build` was run. The new leaf is intentionally absent from root
imports and was checked directly; the required exact-head CI must follow the
commit and run through the normal machine-wide build lock. No build-lock
override was used.
