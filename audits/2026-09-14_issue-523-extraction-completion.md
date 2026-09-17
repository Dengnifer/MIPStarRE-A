---
title: "Issue 523: completion of conditional Pauli extraction"
date: 2026-09-14
purpose: >
  Records the complete proof of the unchanged supplied-witness extraction
  constructor, its axiom closure, and the separate source-facing obligations.
status: resolved
issue: "#523"
pr: "#544"
---

# Issue 523: completion of conditional Pauli extraction

## Scope

This continuation starts from clean commit
`6f9df517a14c5149e62ff6cf0b833e1a27e5ff03` in the existing issue523 worktree.
The first local clock observation was 08:39:42 UTC. The authorization is at
most 25 elapsed minutes, including validation, this audit, and normal-hook
commits. No descendant, full build, CI, review, publication, GitHub mutation,
or change to claims, accounts, or caps is part of this continuation.

The proof of `exists_extractionWitness_ofGlobalPairWitness` is complete at its
unchanged public statement. This resolves the concrete composition recorded
under Required Action in `2026-09-14_issue-523-pauli-comparison.md`. That audit,
the state-extraction audit, and every earlier checkpoint remain preserved.
The resolved status of this audit concerns the conditional constructor only.

## Source of Truth

The source is `lem:qld-unitary` in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1666-1860`,
particularly lines 1785-1858 and equations `eq:qld-unitary-6` through
`eq:qld-unitary-9`. The blueprint is
`blueprint/src/chapter/ch16_qpbt_extraction.tex`.
`docs/paper-gaps/qpbt_extraction-transfer.tex` records the corrected numerical
estimates, supplied global-witness conditionality, and downstream isometry
transfer. Audit organization follows `2026-04-29_audit-document-format.md`.

## Findings

### Exact overlap transport

`PauliTransport.lean` defines the complete measurement obtained by extending
each total-Pauli effect to its entire local extraction block and conjugating
by the corresponding swap. Coarse-graining commutes with these operations.
The identity between evaluation of `encodingPoly h` and `lowDegreeEnc h`
is definitional; no identity for decoding an arbitrary polynomial is used.

`swapped_block_overlap_eq` combines simultaneous unitary invariance with the
exact six-register reassociation. Its two specializations,
`swapped_pauli_overlap_alice` and `swapped_pauli_overlap_bob`, identify the
evaluated overlap on the jointly swapped state with one minus the corresponding
evaluated-Pauli/tilde consistency defect on `S.psiHat`. Bob's equation keeps
Alice's canonical effect on the left and Bob's total-Pauli effect on the right.
There is no assumption that the two local spaces or the strategy are symmetric.

### Full Pauli comparison

`ConcretePauliComparison.lean` transports `pauli_distance_on_ideal_le` to both
player orientations. Exchanging the auxiliary and extracted registers gives
the right-player version because the EPR vector is invariant under exchange.
`extraction_pauli_dist_eq_sum` identifies the full norm sum with the exact
`ExtractionWitness.pauli_close` expression on `S.idealExpState aux`.

For each side and basis, `extraction_pauli_dist_le` proves the bound

\[
  2\,\mathrm{defect}+2md/q+4\lVert\vartheta-\Delta\rVert.
\]

The defect is the already proved evaluated consistency defect on `S.psiHat`.
The estimate retains the complete answer sum and has no dimension or
answer-cardinality factor.

### Complete constructor

Let the previously proved state and evaluated-consistency constants be
\(C_S,C_E\). Before introducing any parameters or strategy, the proof chooses
\(C=\max\{C_S,C_E,18\}\) and then sets
\(\delta=\deltaConstructPaulis(C,\epsilon,\delta_G,m,d,q)\).
Monotonicity in the construction coefficient gives squared state error at
most \(16\delta\) and both evaluated defects at most \(\delta\).
The norm error is therefore at most \(4\sqrt\delta\), and each Pauli error is
at most \(2\delta+2md/q+16\sqrt\delta\).

For \(\delta\leq1\), `extraction_small_error_absorption` puts both errors below
the unchanged nested extraction scale. For \(\delta>1\), the existing
complete large-error witness applies. Both unitarity fields, normalized
auxiliary data, state closeness, and both players' comparisons in both bases
are assembled. The original target proof hole is removed; no helper hole or
new hypothesis replaces it.

## Statement Integrity

Paper assumptions: an admissible projective setting with the successful-test
premise; the global polynomial-pair measurement is obtained earlier in the
paper's argument. Paper conclusion: the two swap unitaries, a normalized
auxiliary state, state extraction, and both total-Pauli comparisons on the
ideal state, at the stated fourth-root extraction scale.

Lean assumptions: unchanged admissible parameters, \(0\leq\epsilon\leq1\),
\(0\leq\delta_G\), the projective setting, and the explicit supplied
`GlobalPairWitness`. Lean conclusion: unchanged `Nonempty ExtractionWitness`
at `deltaExtract C (deltaConstructPaulis C ...) ...`, with the universal
constant quantified before all parameters, strategies, and witnesses.
The public theorem header is byte-for-byte unchanged from the starting head.

Verdict: exact preservation of the existing conditional Lean statement and
its full conclusion. Relative to the source lemma, the supplied global
witness remains an extra assumption. Its `**Unfaithful:**` marker and
discharge plan remain. No new assumption, restriction, altered quantifier
order, or change to the nested error scale is introduced.

Only the matching conditional auxiliary blueprint node gains a statement-match
mark, after a fresh query of the actual target reports no `sorryAx`. Its
mathematical proof is recorded, but the proof-level completion mark is omitted
because the normal hook rejects that mark for any declaration retaining an
`**Unfaithful:**` marker, even on an explicitly conditional auxiliary node.
The source-labelled extraction node is explicitly `notready`.

## Required Action

No mathematical identity remains to close the issue523 conditional target.
Independent canonical CI and review remain for MAIN to schedule outside this
delegation. No merge or publication is authorized here.

The source theorem still requires `exists_globalPairWitness` and its
composition with the conditional constructor, as tracked by issue #123.
The later isometry comparison still requires the separate range-projection
transfer recorded under issue #47 in the gap note. None of the five original
`Consistency.lean` holes is filled or used as a proved fact by this work.

## Validation

Focused Lean compilation passed without warnings for `PauliTransport.lean`,
`ConcretePauliComparison.lean`, and the changed `Unitary.lean`. Private
dependency objects were produced only in this worktree's existing Lake root.
A temporary complete-constructor check passed before replacing the original
target proof. A subsequent fresh import of the updated target reported:

```text
MIPStarRE.QPBT.exists_extractionWitness_ofGlobalPairWitness
  [propext, Classical.choice, Quot.sound]
```

Seven further queries, covering both overlaps, simultaneous transport,
the swapped POVM, the right-player comparison, the exact distance sum, and
the concrete final bound, also report only these standard axioms. Temporary
check files are removed. The three changed Lean files contain no proof holes,
axiom declarations, forbidden proof-integrity tokens, or debug queries.
All are below 1000 lines and satisfy the 100-character line limit.

`leanblueprint web` passed. Blueprint synchronization passed with the same
thirteen existing statement/proof-mark warnings. `lake exe checkdecls
blueprint/lean_decls` resolved all 1,453 declarations. The hook installation
check passed with `core.hooksPath=.githooks`; the commit uses normal hooks.
The final terminal receipt records the commit result and exact head.
No full build or independent review is claimed.

The first normal-hook commit attempt stopped at
`scripts/audit_unfaithful_markers.py`: the conditional auxiliary's proof-level
`leanok` linked to the required `**Unfaithful:**` marker on the target. The
proof-level blueprint tag was removed while retaining both the conditional
statement-match tag and the Lean conditionality marker. No hook bypass or
weakening of the proof-debt policy was used; the same normal-hook commit is
retried with this correction. This presentation restriction does not change
the verified standard-axiom closure of the full Lean target.

## Provenance and Cost Preservation

This proof uses the preserved PR294/issue520/PR533/PR539 results and the state
and comparison estimates from the immediately preceding continuations.
The original state-extraction and Pauli-comparison audits retain their
frozen-input commit identifiers and recovery details.

The prior native state-construction span
`01a09edb-6c0b-7d03-8b93-c0999048791e` is
07:39:35.369Z-08:08:04.259Z, totaling 1,708.89 seconds, including the
63-second audit finalization. The prior Pauli-comparison span with identifier
prefix `01a09ef9` is 08:12:57.131Z-08:36:51.145Z, totaling 1,434.014 seconds.
Both are preserved, not replaced or counted a second time.

Historical EPR lower bounds remain 7,395 wall seconds, 24,256,025 input tokens
(23,113,344 cached), and 139,412 output tokens, with unknown historical
charges still explicitly unknown. Native token observations are cumulative
and nonadditive; no overlapping observations are summed. This continuation
adds its own elapsed work. MAIN records native telemetry after completion,
without resetting the episode or inventing unobserved token charges.

## Review Use

Check the two evaluated overlap identities first, then the exact full norm-sum
transport and the common-constant choice in the constructor. The decisive
closure evidence is the fresh query of the full target, not merely queries
of the analytic helpers. Keep the supplied-witness conditionality distinct
from kernel proof completeness and preserve the separate source-construction
and isometry-transfer obligations.
