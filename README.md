# MIPStarRE - the quantum Pauli basis test, formalized in Lean 4

This repository formalizes the **quantum Pauli basis test** from *MIP\* = RE*
([arXiv:2001.04383](https://arxiv.org/abs/2001.04383)) in Lean 4, together with
the classical low individual degree test on which it depends. The paper sources
are mirrored under `references/`; the Pauli basis test is stated in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex` and proved
in `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`.

The counts, locators, and status claims on this page were audited against source
commit `abb98018ec07d6ba5896907f5675f716c6e07a05` (September 21, 2026).

| | |
|---|---|
| Headline theorem | `MIPStarRE.QPBT.pauli_soundness` |
| Registered headline targets | 4, listed below |
| QPBT axiom assertions | 13 compile-time checks |
| Proof debt in `MIPStarRE/QPBT/` | no active `sorry`, `admit`, or project `axiom` declaration |
| Toolchain | Lean `v4.32.0`, Mathlib `v4.32.0`, pinned by the repository |
| Source size at the audited commit | QPBT: 332 Lean files / 106,458 lines; LDT: 326 files; Quantum: 11 files |

## What is formalized

The four registered QPBT headline targets are:

| Result | Lean declaration | Source and blueprint label |
|---|---|---|
| Soundness of the Pauli basis test | `MIPStarRE.QPBT.pauli_soundness` | `thm:pauli` |
| Qubit form of soundness | `MIPStarRE.QPBT.pauli_soundness_qubit` | `cor:pauli-binary` |
| Completeness at value one | `MIPStarRE.QPBT.exists_spcc_value_one` | `lem:pauli-completeness` |
| Quantum soundness of the low-degree game | `MIPStarRE.QPBT.exists_ld_soundness` | `lem:ld-soundness` |

`pauli_soundness` states that universal constants `a >= 1` and `0 < b < 1`
exist such that every admissible parameter tuple `P`, every `epsilon >= 0`, and
every strategy winning the Pauli basis test with probability at least
`1 - epsilon` admit local isometries and an auxiliary state. The state distance
and both players' distances for the **raw prescribed-answer Pauli effects** are
bounded by

```text
deltaQld a b epsilon P.m P.d P.q
  = a * (P.m * P.d)^a
      * (epsilon^b + P.q^(-b) + 2^(-b * P.m * P.d)).
```

The theorem's public statement matches `thm:pauli`. Its Lean proof uses a
directly indexed replacement for the source's unsatisfiable seed-indexed
divisibility route and proves the transfer from completed internal Pauli effects
to the raw effects in the theorem. The unresolved obligations in the printed
route remain documented; they are not hypotheses of the Lean theorem. See
[`docs/DEVIATIONS.md`](docs/DEVIATIONS.md) and the theorem index below.

### Non-vacuity and a small-error regime

`MIPStarRE/QPBT/Test/NonVacuity.lean` proves both that the hypotheses can be met
and that the conclusion is quantitatively non-trivial. For

```text
q = 2^(2*n + 1),  m = 1,  d = n + 1,  epsilon = 0,
```

`nonVacuousParams n` is admissible, and every admissible Pauli test has a
value-one strategy. For any constants `a >= 1`, `b > 0`, and any `eta > 0`, the
quantity `deltaQld a b 0 1 (n + 1) (2^(2*n + 1))` tends to zero as `n` tends to
infinity. Consequently `pauli_soundness_nontrivial` supplies admissible
parameters and a value-one strategy for which the state distance and both raw
operator distances are all less than `eta`.

This is an existential regime along a growing parameter family at
`epsilon = 0`. The formalization does not provide a numeric value of `a` or `b`,
nor an explicit or uniform positive-`epsilon` threshold at a fixed parameter
tuple. `tendsto_deltaQld_eps_zero` separately records right-continuity at zero.

## Status and evidence

### Proof integrity

For the QPBT track, criterion C1 of the repository's authoritative completion
gate scans for `sorry` and `admit` sites with the shared comment-aware rule,
project `axiom` and `constant` declarations, and prohibited native evaluation:

```bash
python3 scripts/completion_gate.py check --track qpbt
```

The C1 line is the proof-integrity result. The command can still exit nonzero
while independent completion criteria remain pending. Comments and strings are
removed before this scan, and the generated comparator challenge lies outside
the QPBT Lean root.

The source-size figures above are reproduced with:

```bash
find MIPStarRE/QPBT -type f -name '*.lean' | wc -l
find MIPStarRE/QPBT -type f -name '*.lean' -print0 | xargs -0 wc -l | tail -1
```

### Axiom audit

`MIPStarRE/QPBT/Test/AxiomAudit.lean` checks 13 declarations during
elaboration. Each check prints the axiom closure and fails unless it is exactly
`propext`, `Classical.choice`, and `Quot.sound`; `sorryAx` is rejected.

The four registered targets are the four declarations in the first table. The
nine additional supporting assertions are:

- `MIPStarRE.QPBT.honestStrategy_isSPCC`
- `MIPStarRE.QPBT.exists_combinedLinesWitness`
- `MIPStarRE.QPBT.exists_extendedLinesWitness_established`
- `MIPStarRE.QPBT.exists_globalPairWitness`
- `MIPStarRE.QPBT.exists_actual_rounded_global_pair_error_bound`
- `MIPStarRE.QPBT.exists_projective_setting_isometry_bounds`
- `MIPStarRE.QPBT.exists_arbitrary_strategy_isometry_bounds`
- `MIPStarRE.QPBT.pauli_soundness_deltaQld_ofExtractionWitness`
- `MIPStarRE.QPBT.exists_symmetric_projective_strategy_approx`

The audit module is an explicit CI target and is intentionally not imported by
the ordinary `MIPStarRE.QPBT` umbrella.

### Preserved printed claims

Two problematic printed claims are retained as `Prop`-valued definitions. A
`Prop` declaration records a proposition; it does not prove it.

- `PrintedExtendedLinesWitnessClaim` preserves the printed error expression of
  `lem:qld-4-13`, but it is **not** a verbatim encoding of the paper statement.
  It uses directly indexed questions, an `Option`-completed answer alphabet,
  and the corrected sum-form `IsPolyErr₂` contract. The proved result used by
  soundness is `exists_extendedLinesWitness_established`.
- `PrintedSymmetricProjectiveAttainmentClaim` records the printed attainment
  form of `lem:symmetric-strat`. It is used by
  `not_forall_printedSymmetricProjectiveAttainmentClaim`, which refutes the
  universal claim on the current Lean domain using an empty-answer game. The
  proved nonempty-answer replacement is
  `exists_symmetric_projective_strategy_approx`.

Neither printed claim is consumed as a premise by `pauli_soundness`. The exact
carrier differences, counterexample scope, and corrected alternatives are in
[`docs/QPBT-theorem-index.md`](docs/QPBT-theorem-index.md) and
[`docs/DEVIATIONS.md`](docs/DEVIATIONS.md).

### Independent comparator status

Independent four-target comparator acceptance is **pending**. At the September
21, 2026 audit, open PR #663 at commit
`85a9181201b3a2323e11063578e1fd58bb2296f4` contained a candidate split challenge
for the four registered targets: one root plus 30 generated module files, with
exactly four intentional root theorem stubs. Generation, elaboration, a
disposable challenge build, and local CI passed.

Those checks are not comparator acceptance. A later diagnostic at source
`a3683e9b` and candidate `73cb8a3d` reported
`DIAG-TOTAL 0`, and Lean's default kernel accepted the solution. The diagnostic
still used the fake-landrun path and ran with nanoda disabled, so it is not an
official comparator run. A real landrun with nanoda and a final merged-main
library pin remain pending.

## Build and check

Install [elan](https://github.com/leanprover/elan), then run from the repository
root:

```bash
lake exe cache get
lake build MIPStarRE.QPBT
lake build MIPStarRE.QPBT.Test.AxiomAudit
lake build MIPStarRE
(cd blueprint && leanblueprint web)
lake exe checkdecls blueprint/lean_decls
python3 scripts/blueprint_leanok_axioms.py --ci
```

The QPBT target builds the development; the audit target runs the 13 checks.
The root `MIPStarRE` target is needed before the full blueprint axiom check,
because blueprint declarations also import LDT modules. Building only QPBT left
two required LDT artifacts absent in the recorded clean-project experiment.

Lake 5 in this toolchain has no `-j` or `--jobs` option. `LEAN_NUM_THREADS`
controls Lean's internal worker threads; it is not a cap on the number of Lean
processes scheduled by Lake.

### Recorded clean-project timing

`results/telemetry/clean-clone-build-20260921.md` records a measurement at
source commit `05df4b74fea7d291050909102c737e6b03d85ba6` on a 128-core Intel Xeon
Platinum 8358P host with 503 GiB RAM. With the project `.lake/build` directory
absent, but Mathlib oleans reused from a read-only prebuilt package store, this
command took 803 seconds:

```bash
nice -n 10 env LEAN_NUM_THREADS=16 \
  lake build MIPStarRE.QPBT MIPStarRE.QPBT.Test.AxiomAudit \
    MIPStarRE.QPBT.Test.NonVacuity
```

It compiled 602 project modules (9,313 jobs); the largest observed process used
5.10 GB, and the sampled aggregate peak across 21 concurrent processes was
84.3 GB. A subsequent `lake build MIPStarRE` compiled 12 additional modules in
26 seconds and enabled the full blueprint axiom check.

This was a clean **project** rebuild, not a fully cold clone-to-build timing:
dependency download and Mathlib compilation were excluded. The figures are tied
to that host, source revision, and cache state and should not be extrapolated as
a general hardware requirement or current end-to-end build time.

## Repository layout

```text
MIPStarRE/
|-- QPBT/       quantum Pauli basis test
|-- LDT/        classical low individual degree test
`-- Quantum/    reusable matrix, Hilbert-space, and measurement infrastructure
```

`blueprint/src/` contains the mathematical blueprint, `references/` the paper
mirrors, `docs/` reviewer and contributor documentation, and
`scripts/comparator/` the independent-checking tooling. `local/` and
`results/telemetry/` describe the local development workflow and are not proof
dependencies.

## Further reading

| Document | Purpose |
|---|---|
| [`docs/ARTIFACT.md`](docs/ARTIFACT.md) | Artifact evaluation sequence |
| [`docs/QPBT-theorem-index.md`](docs/QPBT-theorem-index.md) | Paper, Lean, blueprint, and axiom map |
| [`docs/DEVIATIONS.md`](docs/DEVIATIONS.md) | Reviewer-facing source deviations |
| [`docs/paper-gaps/qpbt-gap-register.md`](docs/paper-gaps/qpbt-gap-register.md) | Detailed QPBT gap register |
| [`docs/comparator.md`](docs/comparator.md) | Comparator protocol and historical records |
| [`docs/CONTRIBUTING.md`](docs/CONTRIBUTING.md) | Contribution and review rules |
| [`docs/PROOF_INTEGRITY.md`](docs/PROOF_INTEGRITY.md) | Proof-integrity policy |

## License

Licensed under the Apache License 2.0; see [`LICENSE`](LICENSE).
