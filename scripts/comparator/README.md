# Comparator challenge generation

This directory generates the self-contained statement files used by the
companion challenge repositories to verify, with the official
[leanprover/comparator](https://github.com/leanprover/comparator), that this
library proves the headline theorems.  Background and trust model:
`docs/comparator.md`.

Two challenges are configured today, one entry each in `challenges.py`:

| Challenge | Target theorems | Generated file | Challenge repository |
|---|---|---|---|
| `ldt` | `MIPStarRE.LDT.Test.mainFormal` | `expected/Challenge.lean.expected` | [LDT-comparator](https://github.com/LionSR/LDT-comparator) |
| `qpbt` | `MIPStarRE.QPBT.pauli_soundness`, `MIPStarRE.QPBT.pauli_soundness_qubit` | `expected/ChallengeQPBT.lean.expected` | [QPBT-comparator](https://github.com/Dengnifer/QPBT-comparator) |

Each generated file imports only Mathlib and re-declares, verbatim and in
dependency order, every declaration in the kernel closure of the target
statements, each with a provenance comment; the target theorems themselves are
stated with `sorry`.

## Adding or changing a challenge

`challenges.py` is the single source of truth: one `Challenge` entry carries
the target theorem names, the header and footer that frame the generated file,
the path of the checked-in expected copy, and the two elaboration-context
tables described under *Maintenance notes*.  A new challenge therefore needs an
entry, a header, a footer, and one CI drift step — no generator code changes.

The extractor is shared.  It imports the root module of every configured
challenge and reads its roots from the `COMPARATOR_TARGETS` environment
variable (whitespace-separated, defaulting to the LDT root), so a new challenge
whose targets live outside the current imports also needs its root module added
to `extract_closure.lean`.

## Drift guard and regeneration

The repository keeps each generated challenge checked in under
`scripts/comparator/expected/`.  The final `.expected` suffix keeps these
generated, intentionally monolithic fixtures out of the 1000-line
project-source guard.  The PR CI guard regenerates each challenge in a
temporary directory and byte-compares it with the checked-in copy; it never
writes a challenge file at the repository root.

Run the deterministic guard from the repository root (requires a built
library).  With no `--challenge` every configured challenge is checked:

```sh
python3 scripts/comparator/check_challenge_drift.py --root .
python3 scripts/comparator/check_challenge_drift.py --root . --challenge qpbt
```

To update the checked-in expected copies after an intentional statement or
dependency change, run the exact maintenance command:

```sh
python3 scripts/comparator/check_challenge_drift.py --root . --update
```

or, for one challenge only, add `--challenge ldt` / `--challenge qpbt`.

The update command performs the documented extraction and assembly pipeline in a
temporary directory (shown here for the QPBT challenge):

```sh
# 1. extract the closure of the statements of the challenge's targets
#    (a Lean metaprogram mirroring comparator's runForUsedConsts traversal)
COMPARATOR_TARGETS="MIPStarRE.QPBT.pauli_soundness MIPStarRE.QPBT.pauli_soundness_qubit" \
  lake env lean scripts/comparator/extract_closure.lean > closure.tsv
awk -F'\t' 'NF==4' closure.tsv > closure.clean.tsv

# 2. assemble the challenge file (topological order, namespace handling)
python3 scripts/comparator/assemble_challenge.py closure.clean.tsv \
    --challenge qpbt > draft.lean
cat scripts/comparator/challenge_qpbt_header.lean draft.lean \
    scripts/comparator/challenge_qpbt_footer.lean \
    > scripts/comparator/expected/ChallengeQPBT.lean.expected
```

Then copy the expected file into the challenge repository as `Challenge.lean`,
bump the `rev` pin in its `lakefile.toml` to the library commit it was
generated from, and run its `./verify.sh` (its CI also runs on every push).

## Maintenance notes

- A challenge's `extras`/`module_preludes` tables carry elaboration context
  (attribute commands, `CoeFun` instances, `variable`/`open` blocks) that the
  kernel closure cannot see.  Extend them if regeneration produces compile
  errors in the generated file; the script fails loudly if a table key no
  longer matches any extracted declaration.
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
- A closure declaration cannot be `private`: a private name is qualified by its
  defining module, so the challenge file could never re-declare it under the
  library's name.  Closure members found to be private are made public in the
  library (see `docs/comparator.md`, "Environment alignment").
