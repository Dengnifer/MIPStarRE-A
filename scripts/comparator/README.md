# Comparator challenge generation

This directory generates the self-contained statement files `Challenge.lean`
used by companion repositories — for the low individual degree test,
[LDT-comparator](https://github.com/LionSR/LDT-comparator), and for the quantum
Pauli basis test,
[QPBT-comparator](https://github.com/Dengnifer/QPBT-comparator) — to verify,
with the official
[leanprover/comparator](https://github.com/leanprover/comparator), that this
library proves the target theorems.  Background and trust model:
`docs/comparator.md`.

A generated file imports only Mathlib and re-declares, verbatim and in
dependency order, every declaration in the kernel closure of its target
statements, each with a provenance comment; the targets themselves are stated
with `sorry`.

## Challenges

Each challenge is one configuration file under `challenges/`:

| file | targets | expected copy | challenge repository |
|---|---|---|---|
| `challenges/ldt.json` | `MIPStarRE.LDT.Test.mainFormal` | `expected/Challenge.lean.expected` | [LDT-comparator](https://github.com/LionSR/LDT-comparator) |
| `challenges/qpbt.json` | `MIPStarRE.QPBT.pauli_soundness`, `pauli_soundness_qubit` | `expected/ChallengeQPBT.lean.expected` | [QPBT-comparator](https://github.com/Dengnifer/QPBT-comparator) |

A configuration names the Lean modules the extractor imports, the target
theorems whose statement closure it takes, the header and footer files wrapped
around the assembled body, the checked-in expected copy, and the per-challenge
elaboration-context tables (`extras`, `module_preludes`).  The schema, with the
meaning of every key, is documented at the top of `challenge_config.py`; unknown
keys are rejected, so a typo fails loudly rather than silently dropping context.

`require_expected` distinguishes a challenge that must stay regenerated (`true`,
a missing expected copy is an error) from one still being developed (`false`,
a missing expected copy is reported and skipped).

Adding a challenge means adding a configuration file, a header and a footer —
no generator code changes and, for the machine-wide guard in `local/bin/ci.sh`,
no CI change either, because that guard passes no `--challenge` and therefore
checks every configuration it finds.

## Drift guard and regeneration

The repository keeps each generated challenge checked in under `expected/`.  The
final `.expected` suffix keeps these generated, intentionally monolithic
fixtures out of the 1000-line project-source guard.  The PR CI guard regenerates
every configured challenge in a temporary directory and byte-compares it with
the checked-in copy; it never writes `Challenge.lean` at the repository root.

Run the deterministic guard from the repository root (requires a built
library).  With no `--challenge` every configured challenge is checked:

```sh
python3 scripts/comparator/check_challenge_drift.py --root .
python3 scripts/comparator/check_challenge_drift.py --root . --challenge qpbt
```

Add `--challenge <name>` (repeatable) to restrict the run to one challenge.

To update a checked-in expected copy after an intentional statement or
dependency change, run the exact maintenance command:

```sh
python3 scripts/comparator/check_challenge_drift.py --root . --update
```

That command refuses a challenge whose configured header or footer file is not
in the tree, and reports it as an error while still updating the others: the
copy it would write omits those statements, and once such a copy exists the
`require_expected: false` skip no longer applies, so every later drift run
would report a challenge that states nothing as current.

To generate a challenge somewhere else without touching the checked-in copy —
the usual loop while filling in a new challenge's context tables:

```sh
python3 scripts/comparator/check_challenge_drift.py --root . \
    --challenge qpbt --write /tmp/Challenge.lean
```

The update command performs the documented extraction and assembly pipeline in a
temporary directory (shown here for the QPBT challenge):

```sh
# 1. extract the closure of the challenge's target statements (a Lean
#    metaprogram mirroring comparator's runForUsedConsts traversal).  The
#    drift checker renders a copy of the extractor with the challenge's
#    `imports` substituted for the import block, because a Lean module header
#    cannot be computed at elaboration time, and passes the targets in
#    MIPSTARRE_COMPARATOR_TARGETS.  With that variable unset the file closes
#    the LDT main theorem:
MIPSTARRE_COMPARATOR_TARGETS="MIPStarRE.QPBT.pauli_soundness,MIPStarRE.QPBT.pauli_soundness_qubit" \
  lake env lean scripts/comparator/extract_closure.lean > closure.tsv
awk -F'\t' 'NF==4' closure.tsv > closure.clean.tsv

# 2. assemble the challenge body (topological order, namespace handling)
python3 scripts/comparator/assemble_challenge.py closure.clean.tsv \
    --challenge qpbt > draft.lean
cat scripts/comparator/challenge_qpbt_header.lean draft.lean \
    scripts/comparator/challenge_qpbt_footer.lean \
    > scripts/comparator/expected/ChallengeQPBT.lean.expected
```

Then copy the expected file into the matching comparator repository as
`Challenge.lean`, bump the `rev` pin in its `lakefile.toml` to the library
commit it was generated from, and run its `./verify.sh` (its CI also runs on
every push).

## Maintenance notes

- A challenge's `extras`/`module_preludes` tables carry elaboration context
  (attribute commands, `CoeFun` instances, `variable`/`open` blocks) that the
  kernel closure cannot see.  Extend them if regeneration produces compile
  errors in that challenge's `Challenge.lean`; the assembler fails loudly if one
  of the challenge's own table keys no longer matches any extracted
  declaration.  The tables are per challenge, so an LDT key never constrains the
  QPBT closure or the other way round.
- A `module_preludes` entry is one scope, or a list of scopes each covering a
  line range (`first`/`last`) of its module: a module needs one scope per source
  section whose context differs.  A scope opened with `noncomputable section` in
  the source is marked `"noncomputable": true`, because the definitions inside
  such a section carry no `noncomputable` keyword of their own.
- The target statements in each footer mirror the theorems in the library:
  `challenge_footer.lean` mirrors
  `MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean`, and
  `challenge_qpbt_footer.lean` mirrors `MIPStarRE/QPBT/Test/Soundness.lean`
  and `MIPStarRE/QPBT/Test/QubitForm.lean`.  If a library statement changes,
  update the footer too — comparator fails with "theorem statement do not
  match" until the two agree.
- Declarations without a source range (compiler-generated congruence lemmas
  and `autoParam` helpers) are emitted as explanatory comments; they
  regenerate identically during elaboration of the challenge file.
- A configured header or footer file that is not in the tree is reported and
  omitted, so a challenge under development can be generated before its footer
  exists.  That omission is confined to `--write`: `--update` refuses such a
  challenge rather than checking in a copy without that part.
- A closure declaration cannot be `private`: a private name is qualified by its
  defining module, so the challenge file could never re-declare it under the
  library's name.  Closure members found to be private are made public in the
  library (see `docs/comparator.md`, "Environment alignment").
