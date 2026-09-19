# MIPStarRE — the quantum Pauli basis test, formalized in Lean 4

This repository contains a machine-checked formalization of the **quantum
Pauli basis test** of *MIP\* = RE* ([arXiv:2001.04383](https://arxiv.org/abs/2001.04383)),
together with the classical **low individual degree test** it is built on
(*Quantum soundness of the classical low individual degree test*,
[arXiv:2009.12982](https://arxiv.org/abs/2009.12982)). The source sections are
mirrored in-repo under `references/`; the Pauli basis test is developed in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex`.

| | |
|---|---|
| Headline theorem | `MIPStarRE.QPBT.pauli_soundness`, `MIPStarRE/QPBT/Test/Soundness.lean:52` |
| Proof debt | none — **0 `sorry`**, 0 `admit`, 0 project `axiom` declarations |
| Axioms used | `propext`, `Classical.choice`, `Quot.sound` only |
| Toolchain | Lean `v4.32.0`, Mathlib `v4.32.0` (rev `81a5d257c8e4`), pinned in `lean-toolchain` and `lake-manifest.json` |
| Size | Pauli development 330 Lean files / 105,319 lines; `MIPStarRE/LDT/` 326 files; `MIPStarRE/Quantum/` 11 files |

## What is formalized

The Pauli basis test is a two-player nonlocal game whose soundness is one of the
rigidity ingredients of *MIP\* = RE*. The headline results:

| Result | Lean declaration | File |
|---|---|---|
| Soundness of the Pauli basis test (blueprint `thm:pauli`) | `pauli_soundness` | `MIPStarRE/QPBT/Test/Soundness.lean:52` |
| Qubit form of soundness (`cor:pauli-binary`) | `pauli_soundness_qubit` | `MIPStarRE/QPBT/Test/QubitForm.lean:423` |
| Completeness: a value-one strategy exists (`lem:pauli-completeness`) | `exists_spcc_value_one` | `MIPStarRE/QPBT/Test/Completeness.lean:266` |
| Quantum soundness of the low-degree game (`lem:ld-soundness`) | `exists_ld_soundness` | `MIPStarRE/QPBT/Test/LowDegreeGameTheorems.lean:82` |

`pauli_soundness` states: there are constants `a ≥ 1` and `0 < b < 1` such that
for every admissible parameter tuple `P` and every `ε ≥ 0`, every strategy for
the Pauli basis test with value at least `1 - ε` admits local isometries and an
auxiliary state under which the strategy's state is within
`deltaQld a b ε P.m P.d P.q` of the ideal state, and both players' operator
families are within the same bound of the ideal Pauli observables. The error
scale carries the admissible sizes as explicit arguments —
`deltaQld (a b ε : ℝ) (m d q : ℕ)`, `MIPStarRE/QPBT/Test/SoundnessDefs.lean:35` —
because it is `a · (m·d)^a · (ε^b + q^(-b) + 2^(-b·m·d))`: the bound depends on
the admissible sizes `m`, `d` and `q` as well as on `ε`, which is what the
`q^(-b)` and `2^(-b·m·d)` terms express. As in the source, the constants are
existentially quantified and no regime in which `deltaQld < 1` is exhibited;
see [`docs/DEVIATIONS.md`](docs/DEVIATIONS.md).

Every headline declaration carries a docstring naming both its blueprint node
and the exact source line range it formalizes, for example
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`
for `pauli_soundness`.

The classical low individual degree test underneath is
`MIPStarRE.LDT.Test.mainFormal`; the Pauli development imports it and does not
re-derive it.

## Status

- **No proof debt.** There is no `sorry`, `admit`, `native_decide`, `unsafe`
  declaration or project-introduced `axiom` anywhere in the Lean sources under
  `MIPStarRE/`. In the `.lean` files of the whole tree the word `sorry` occurs
  exactly four times: twice in prose inside docstrings
  (`MIPStarRE/LDT/Test/AxiomAudit.lean:81`,
  `MIPStarRE/QPBT/Combining/Apply.lean:57`), once in prose in
  `scripts/comparator/challenge_header.lean:14`, and once as real syntax in
  `scripts/comparator/challenge_footer.lean:44` — the footer of a
  statement-only challenge template that is supposed to be unproved (see
  "Independent checking" below). One further file is Lean-shaped without
  carrying the `.lean` extension: `scripts/comparator/expected/Challenge.lean.expected`,
  the checked-in expected assembly of that same template, repeats the prose
  mention (line 14) and the template's `sorry` (line 802);
  `scripts/comparator/README.md:14` mentions it in prose as well. These counts
  are about source files: the string also
  occurs throughout the development records under `results/telemetry/` and in
  the documentation, so a bare `git grep sorry` over the whole tree returns
  thousands of lines.
- **Standard axioms only.** The headline theorems depend on `propext`,
  `Classical.choice` and `Quot.sound` and on nothing else. There is no
  dedicated Pauli-test axiom-audit module yet — the existing
  [`MIPStarRE/LDT/Test/AxiomAudit.lean`](MIPStarRE/LDT/Test/AxiomAudit.lean)
  covers the classical low-degree track only — so the check is made by asking
  Lean directly; the command is under "Build and check" below. Repository-wide,
  the pre-push gate (`.githooks/pre-push`) runs
  [`scripts/blueprint_leanok_axioms.py`](scripts/blueprint_leanok_axioms.py)
  `--ci`, which runs `#print axioms` on every blueprint declaration marked
  `\leanok` and fails if any of them depends on `sorryAx`.
- **Statement corrections are documented, not hidden.** Where the source
  paper's printed statement is wrong, or where its printed proof does not
  establish the printed claim, the deviation is recorded rather than papered
  over. There are 20 Pauli-test gap notes (45 notes in total; the directory
  also holds `command.tex`, `template.tex`, `policy.tex` and
  `proof-gap-protocol.tex`, which are not notes) under
  `docs/paper-gaps/`, summarized in the register linked below. Two printed
  claims that are not established are carried as `Prop`-valued definitions
  which state the source sentence without asserting it, so the printed form
  stays visible and stays unproved.
- **Independent checking.** There is no comparator challenge for
  `pauli_soundness` yet. What can be re-checked outside this repository today
  is the classical low individual degree test underneath: the statement
  `MIPStarRE.LDT.Test.mainFormal` has a challenge repository at
  [LionSR/LDT-comparator](https://github.com/LionSR/LDT-comparator), which
  re-declares the statement against Mathlib alone and runs the Lean comparator
  against this library; the setup is described in
  [`docs/comparator.md`](docs/comparator.md), and the template it is assembled
  from lives under `scripts/comparator/`. The analogous challenge for the
  Pauli statement has not been built: `Dengnifer/QPBT-comparator` is so far a
  placeholder holding only a licence and a toolchain pin.

## Build and check

Install [elan](https://github.com/leanprover/elan); it reads `lean-toolchain`
and fetches Lean `v4.32.0` automatically. From the repository root:

```bash
lake exe cache get              # fetch the pinned Mathlib build cache (required)
lake build MIPStarRE.QPBT       # build the Pauli basis test development
lake build MIPStarRE            # build everything (QPBT, LDT, Quantum)
```

To reproduce the axiom claim, ask Lean for the axiom closure of a headline
declaration:

```bash
lake build MIPStarRE.QPBT.Test.Soundness
printf 'import MIPStarRE.QPBT.Test.Soundness\n#print axioms MIPStarRE.QPBT.pauli_soundness\n' > AxiomCheck.lean
lake env lean AxiomCheck.lean
```

`propext`, `Classical.choice` and `Quot.sound` are the only axioms that should
appear; in particular `sorryAx` must not. The same recipe applies to the other
three headline declarations, with their own modules imported.

To type-check a single file, which is the fastest iteration loop:

```bash
lake env lean MIPStarRE/QPBT/Test/Soundness.lean
```

### Build time and machine requirements

Timings below are the recorded ones from `results/telemetry/builds.jsonl`
(1,608 rows), all measured on one machine: a 128-core Intel Xeon Platinum 8358P
at 2.60 GHz with 503 GiB of RAM.

| Kind of build | Rows | Median | Range |
|---|---|---|---|
| Incremental build of touched modules | 1,248 | 37 s | 17 s – 4,428 s |
| Fresh worktree seeded from a warm local cache | 172 | 75 s | 5 s – 25,052 s |

Recent fresh-worktree builds of the full tree took 219 s, 227 s, 229 s and
502 s. The 25,052 s (≈ 7 h) outlier is a single from-scratch run of
2026-08-30 that also compiled 20 Mathlib files the cache failed to deliver;
it predates most of the Pauli development and is not a measurement of the
current tree.

**A clean-clone build of `MIPStarRE.QPBT` has not yet been timed and recorded.**
All rows above were produced with a warm local build cache, so they are lower
bounds on what a fresh clone costs. Budget accordingly, and expect the
`lake exe cache get` download of Mathlib to dominate the first build. 23 files
raise `maxHeartbeats` and 17 raise `synthInstance.maxSize`; these are
elaboration-budget options, not soundness escapes.

The blueprint is built with [`leanblueprint`](https://github.com/PatrickMassot/leanblueprint):

```bash
leanblueprint pdf     # PDF output
leanblueprint web     # HTML output
```

`leanblueprint` also generates `blueprint/lean_decls`, the list of declarations
the blueprint cross-references; `lake exe checkdecls blueprint/lean_decls`
verifies that each one exists.

## Repository layout

```
MIPStarRE/
├── QPBT/          # Quantum Pauli basis test — the contribution
│   ├── Algebra/        # finite fields, low-degree codes, lines, Pauli matrices
│   ├── Games/          # nonlocal games, strategies, operator distances
│   ├── Observables/    # observable algebra for the test
│   ├── Combining/      # combining lines and points into global objects
│   ├── Extraction/     # extracting Pauli observables from a strategy
│   ├── Test/           # the test, completeness, soundness, qubit form
│   └── State.lean
├── LDT/           # Classical low individual degree test (12 submodules)
└── Quantum/       # Reusable finite-dimensional Hilbert space and POVM layer
```

`MIPStarRE.lean` re-exports `MIPStarRE.Quantum`, `MIPStarRE.LDT` and
`MIPStarRE.QPBT`.

Top-level directories:

| Path | Contents |
|---|---|
| `MIPStarRE/` | Lean sources (above) |
| `blueprint/src/` | LaTeX blueprint, 16 chapters; `ch11`–`ch16` cover the Pauli basis test |
| `references/` | In-repo TeX mirrors of the source papers (`qpbt-paper`, `ldt-paper`, `neexp-paper`, `nv-paper`, `cs-paper`), used as line-precise citation targets |
| `docs/` | Artifact documentation, gap notes, contributor guides, style rules |
| `audits/` | Dated dependency-scouting reports written during development |
| `scripts/` | Reference-paper splitter, declaration checker, comparator tooling |
| `local/` | The AI-assisted development workflow (issue, PR, CI and review drivers) |
| `results/telemetry/` | Session, build and stage records produced by that workflow |

`local/` and `results/telemetry/` document **how** the formalization was
produced. They are research data about an AI-assisted development process and
are not part of the mathematical artifact; nothing in `MIPStarRE/` depends on
them, and they can be ignored when evaluating the proofs.

## Where to read more

| Document | What it covers |
|---|---|
| [`docs/ARTIFACT.md`](docs/ARTIFACT.md) | How to evaluate this repository as an artifact: what to check and in what order |
| [`docs/QPBT-theorem-index.md`](docs/QPBT-theorem-index.md) | Every headline result: paper statement → Lean name → file:line → blueprint node → axioms |
| [`docs/DEVIATIONS.md`](docs/DEVIATIONS.md) | Where the formalization departs from the printed source, and why |
| [`docs/paper-gaps/qpbt-gap-register.md`](docs/paper-gaps/qpbt-gap-register.md) | The gap register: 18 of the 20 Pauli-test notes, each linking a source statement, its blueprint label, the correction and the Lean status. `qpbt_combined-points-field-valued.tex` and `qpbt_subline-claims-line-marginal.tex` have no row yet |
| [`docs/comparator.md`](docs/comparator.md) | Independent re-checking with the official Lean comparator |
| [`blueprint/src/`](blueprint/src/) | The LaTeX blueprint: the informal argument, node by node, cross-referenced to Lean |
| [`docs/CONTRIBUTING.md`](docs/CONTRIBUTING.md) | PR and issue conventions, review checklist |
| [`docs/PROOF_INTEGRITY.md`](docs/PROOF_INTEGRITY.md) | The rules the development holds itself to about faithful statements |

## Licence

Licence: to be added by the repository owner before submission.
