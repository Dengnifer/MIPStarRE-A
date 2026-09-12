---
title: Qubit soundness from qudit soundness
date: 2026-09-12
purpose: >
  Records the corollary's exact coordinate transport, its unchanged statement,
  and the unresolved dependency on qudit soundness.
issue: "#528"
---

# Qubit soundness from qudit soundness

## Source and mathematical argument

Corollary `cor:pauli-binary`, in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1470-1492`,
follows from `thm:pauli` by composing its local isometries with the binary
coordinate isometries of `lem:pauli-binary`. The corresponding blueprint entry
is `cor:pauli-binary` in `blueprint/src/chapter/ch13_qpbt_test.tex`.

For the witness supplied by `pauli_soundness`, the constructor
`PauliSoundnessWitness.toQubit` preserves the auxiliary spaces and unit vector
and post-composes both local maps with the fixed binary coordinate permutation.
The three existing identities `qubit_state_error_to_qubit`,
`qubit_operator_distance_a_to_qubit`, and
`qubit_operator_distance_b_to_qubit` identify the resulting comparison quantities
exactly. Consequently the same constants `a` and `b` and the same value of
`deltaQld` bound all three quantities. No monotonicity estimate, enlargement of
constants, or additional success hypothesis is needed.

The new proof implements precisely this argument. It imports `Test.Soundness`
instead of `Test.SoundnessDefs`, which that module already imports. It does not
change the extraction modules or introduce a conditional helper.

## Remaining obligation

At the starting commit `ae124f8f09ee002444ac5b9711822c0f1daae142`,
`MIPStarRE.QPBT.pauli_soundness` in `Test/Soundness.lean` is still proved by
`sorry`. The corollary therefore has a complete coordinate-transport argument
but does not yet have a proof independent of `sorryAx`. Issue #529 owns the
missing qudit soundness proof. This change addresses #528 without claiming its
paper-level proof closure or closing its issue.

The earlier audit `audits/2026-09-06_binary-witness-transport-246.md` already
isolated the same existence obligation. This packet does not retry the analytic
extraction argument or treat a supplied `GlobalPairWitness` as a construction
from the paper hypotheses. The upstream extraction difficulties remain recorded
in `docs/paper-gaps/qpbt_extraction-transfer.tex`.

The blueprint already links the exact source statement and has only a
statement-level `\leanok`. Its proof has no `\leanok`, and both placements are
unchanged. The Lean module and theorem docstrings explicitly record the
unfinished dependency. Once #529 is proved, the axiom closure must be checked
again before claiming proof completeness.

## Provenance and prior costs

Before editing, the history of both soundness files was searched across all
saved Git refs, including main and saved PR branches. No completed proof of the
current corollary was found. The reused witness transport comes from
`966b9b8cb996406f3977434cee3e113a20a27800`; its shared arbitrary-index binary
algebra was consolidated in `815978233b44122e6c67c53e2b2770ecc1be9729` for
PR #255. Both are already present in the starting commit. No branch was copied
and no coordinate algebra was reproved.

The primary checkout's `results/telemetry/sessions.jsonl` records the following
earlier sessions for #246 and PR #255. Token columns reproduce the recorded
input and output counters, not a newly inferred billing total.

| Session | Wall seconds | Input tokens | Output tokens |
| --- | ---: | ---: | ---: |
| `prover-246-20260906-01` | 1473 | 3129770 | 26340 |
| `orc-246-20260906-01` | 959 | 2690487 | 18626 |
| `reviewer-pr255-20260906-01` | 464 | 820734 | 11148 |
| `orc-246-20260906-02` | 931 | 5491814 | 40286 |
| `reviewer-pr255-20260906-02` | 440 | 1970212 | 8082 |
| `prover-246-20260906-02` | 320 | 846311 | 5735 |

These six completed session intervals total 4587 seconds (76 minutes,
27 seconds). The two `orc-246` rows share a resumed thread, so their token
counters are not summed here. The additional `orc-246-native-20260907` row has
unknown additive usage and no completed wall duration; it contributes an
unknown cost, not zero. This is a lower bound on known prior session time, not
the total cost of all upstream soundness work. The present session is
`prover-528-20260912-01`; its final counters belong to the dispatcher record and
must be added to the existing history, without resetting that history.

## Statement integrity

- Paper assumptions: an admissible binary-field parameter tuple, a strategy
  succeeding with probability at least `1 - epsilon`, and a nonnegative error.
- Lean assumptions: the identical `AdmissibleParams`, nonnegative real error,
  and success inequality; the field and basis are stored in `P.model`.
- Paper conclusion: universal `a >= 1` and `0 < b < 1`, local isometries and a
  unit auxiliary state, with the state bound and both ideal-state operator-family
  bounds at the specified soundness error.
- Lean conclusion: the same quantifier order and constants, a
  `QubitSoundnessWitness`, the norm bound, and both squared operator-family
  distances over the original field-valued answer set, at unchanged `deltaQld`.
- Verdict: faithful boundary encoding; the public signature is unchanged.
  The existing binary factor-index correction documented in
  `docs/paper-gaps/qpbt_pauli-binary-factor-index.tex` is unchanged.

## Validation and next gate

- `lake env lean MIPStarRE/QPBT/Test/QubitForm.lean` passes without warnings.
- Fresh-source `lake env lean --stdin` axiom checks report only `propext`,
  `Classical.choice`, and `Quot.sound` for the witness constructor and all three
  transport identities. Both `pauli_soundness` and `pauli_soundness_qubit`
  additionally depend on `sorryAx`.
- The edited Lean file contains no `sorry`, `admit`, axiom declaration, or
  prohibited proof bypass. No new declaration was introduced.
- `git diff --check` and `scripts/install_git_hooks.sh --check` pass.
- The public signature matches the starting commit byte-for-byte, and the
  paper-facing proof-debt audit reports no header or conditional-name findings.
- Full-build and exact-head CI evidence must come from the primary checkout's
  `local/bin/ci.sh` after publication. Independent review is a subsequent gate;
  the author session does not launch it or merge the PR.
