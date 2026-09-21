# Comparator challenge generation

This directory generates the self-contained statement files used by the
companion challenge repositories to verify, with the official
[leanprover/comparator](https://github.com/leanprover/comparator), that this
library proves the headline theorems.  Background and trust model:
`docs/comparator.md`.

One challenge is generated per track that names headline theorems in
`local/project.json`; `challenges.py` turns those tracks into the registry.
The default track uses `challenge_header.lean` / `challenge_footer.lean`, a
second track `challenge_<track>_header.lean` / `_footer.lean`.  The challenge
repository is `project.comparator_slug`.  A repository whose tracks are not
written yet has no challenge, and every command below says so and exits 0.

| Challenge | Target theorems | Generated file | Challenge repository |
|---|---|---|---|
| `<track>` | the track's headline theorems | the track's `expected_challenge` | `<comparator_slug>` |

Each generated file imports only Mathlib and re-declares, verbatim and in
dependency order, every declaration in the kernel closure of the target
statements, each with a provenance comment; the target theorems themselves are
stated with `sorry`.

## Adding or changing a challenge

The registry is derived: a track in `local/project.json` with headline
theorems becomes a challenge whose targets are those theorems and whose
checked-in copy is the track's `expected_challenge`.  What a config file cannot
hold — the elaboration-context tables described under *Maintenance notes* —
lives in `EXTRAS` and `MODULE_PRELUDES` of `challenges.py`, keyed by challenge
name.  A new challenge therefore needs a track, a header, a footer, and one CI
drift step — no generator code changes.

The extractor is shared.  It imports the library root and reads its roots from
the `COMPARATOR_TARGETS` environment variable (whitespace-separated; empty by
default), so a challenge whose targets live outside the root's imports also
needs its module added to `extract_closure.lean`.

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
python3 scripts/comparator/check_challenge_drift.py --root . --challenge <track>
```

To update the checked-in expected copies after an intentional statement or
dependency change, run the exact maintenance command:

```sh
python3 scripts/comparator/check_challenge_drift.py --root . --update
```

or, for one challenge only, add `--challenge <track>`.

The update command performs the documented extraction and assembly pipeline in
a temporary directory (shown here for the default track, whose challenge files
carry no track in their name):

```sh
# 1. extract the closure of the statements of the challenge's targets
#    (a Lean metaprogram mirroring comparator's runForUsedConsts traversal)
COMPARATOR_TARGETS="$(python3 scripts/comparator/challenges.py targets)" \
  lake env lean scripts/comparator/extract_closure.lean > closure.tsv
awk -F'\t' 'NF==4' closure.tsv > closure.clean.tsv

# 2. assemble the challenge file (topological order, namespace handling)
python3 scripts/comparator/assemble_challenge.py closure.clean.tsv > draft.lean
cat scripts/comparator/challenge_header.lean draft.lean \
    scripts/comparator/challenge_footer.lean \
    > "$(python3 scripts/comparator/challenges.py expected)"
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
- The target statements in each footer mirror the theorems in the library,
  character for character: `challenge_footer.lean` mirrors the file that
  declares the default track's headline theorem.  If a library statement
  changes, update the footer too — comparator fails with "theorem statement do
  not match" until the two agree.  The footer is also the repository's one
  intentional `sorry`: keep the `theorem mainFormal` / `:= by` / `sorry` shape
  that `scripts/generate_badges.py` subtracts from the sorry count.
- Declarations without a source range (compiler-generated congruence lemmas
  and `autoParam` helpers) are emitted as explanatory comments; they
  regenerate identically during elaboration of the challenge file.
- A closure declaration cannot be `private`: a private name is qualified by its
  defining module, so the challenge file could never re-declare it under the
  library's name.  Closure members found to be private are made public in the
  library (see `docs/comparator.md`, "Environment alignment").
