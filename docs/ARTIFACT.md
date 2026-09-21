# The artifact

**Status: a form, not a record.** No snapshot has been cut from this repository
yet. This page says what an artifact snapshot of this project contains, how a
reviewer checks it, and how a maintainer cuts one — with `<angle brackets>`
wherever the project has to fill in its own facts. Criterion C7 of
[`local/protocols/completion.md`](../local/protocols/completion.md) requires
this page, filled in, at the declared commit.

Two audiences: a **reviewer** who received the tarball and wants to check that
the claimed theorems really are proved, and a **maintainer** cutting the next
snapshot.

The artifact is a **release snapshot of the mathematical development**, not the
working repository. `scripts/make_artifact.sh` produces it from a tagged commit,
and every copy carries a `MANIFEST.txt` naming the commit it came from.

**Never write a number, a timing or a claim into this page that has not been
measured on this repository.** "Not yet measured" is an acceptable entry; an
inherited number is not.

---

## What is in it

| path | what it is |
|---|---|
| `<LeanRoot>/`, `<LeanRoot>.lean` | the Lean development — the contribution |
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | the pinned build: Lean and every dependency by exact revision |
| `blueprint/src/` | the blueprint, cross-referenced to the Lean names with `\lean{}` / `\leanok` |
| `docs/` | the mathematical documentation: the theorem index, the deviations page, the gap notes |
| `references/` | the TeX sources of the papers, third-party material — see below |
| `scripts/comparator/` | the generator for the self-contained challenge statement file |
| `scripts/blueprint_leanok_axioms.py` | the blueprint/axiom consistency check |
| `scripts/make_artifact.sh` | the script that produced the snapshot, so the packaging is itself auditable |
| `MANIFEST.txt` | source commit, file count, Lean line total, toolchain, dependency revisions, leak-scan and self-containment results |

## What is not in it, and why

**The AI-workflow layer.** This development is produced with a local
agent-orchestration layer: `local/`, `results/telemetry/`, the `.github/` tree,
`.githooks/`, `audits/` and the scripts and documents that only serve that
layer. It stays in the source repository because it is research material in its
own right, but it is not part of the mathematics, and it dominates the
repository's size. Excluding it also removes, with no history rewrite, the
tracked files that mention the build host's home path.

## Third-party material: the paper sources

If the snapshot ships the paper mirrors under `references/`, this page must say
so and say why, and the manifest must repeat the licence position:

> These files are the work of their own authors and are **not** covered by the
> licence that ships with the snapshot and governs the development itself. They
> are kept for reference and for line-precise citation; their own terms govern
> any further use or redistribution.

**Why they ship**, when they do: Lean docstrings and the theorem index cite
their source as `references/<mirror>/<file>.tex:<lines>`, so with the sources
inside the snapshot a reviewer can read the paper statement next to the Lean
statement without reconstructing the split from arXiv.

**Locator report.** `MANIFEST.txt` records how many of the cited
`references/<mirror>/<file>.tex` paths resolve inside the snapshot. It is a
report, not a gate. Every locator that does not resolve is listed in this page
with the reason.

**Leak scan.** The scan that gates packaging treats these files like any other:
a home path or a key-shaped string inside `references/` still fails the run.
A forgiveness is scoped by path and by content, carries a written reason in the
script, and is never blanket.

## Verifying the artifact as a reviewer

### 1. Install the pinned toolchain

```sh
cd <unpacked snapshot>
cat lean-toolchain          # elan installs this on first use
```

### 2. Fetch the dependency cache and build

```sh
lake exe cache get
lake build <LeanRoot>
```

**Expected cost.** Fill in from a measured run:
`lake exe cache get` downloads `<size>`; plan on `<RAM>` and `<disk>`; the
build took `<time>` on `<machine>`. Until a cold clean-clone build has been
timed and recorded, say exactly that — warm incremental timings from the
development are lower bounds, not a measurement of what a reviewer will pay.

### 3. Check that nothing is assumed

The development claims to depend on no axioms beyond Lean's three standard ones
— `propext`, `Classical.choice`, `Quot.sound` — and on no `sorry`, `admit`,
`native_decide`, `unsafe` or `@[extern]` escape hatch.

The check that settles the first half is Lean's own `#print axioms`: it reports
the complete axiom closure of a declaration and, unlike a text search, cannot
be misled by prose. The snapshot ships an audit module per track that runs it
at build time and **fails the build** when a closure is not exactly those
three:

```sh
lake build <LeanRoot>.<Track>.Test.AxiomAudit
```

To read the closures directly instead, elaborate a scratch file at the root of
the unpacked snapshot:

```lean
import <LeanRoot>.<Track>

#print axioms <fully.qualified.headline.theorem>
```

`#print axioms` does **not** report `native_decide`, `unsafe` or `@[extern]`,
which move trust outside the kernel without leaving an axiom behind. A text
search is the check for those and for `axiom` declarations:

```sh
grep -rn --include='*.lean' -E '^[[:space:]]*axiom |\b(sorry|admit|native_decide|unsafe)\b|@\[extern' <LeanRoot>/
```

Expected output: at most a handful of matches, every one inside a comment or a
docstring that *discusses* an escape hatch rather than using one. This page
lists each surviving match at the snapshot's commit and says which is which. A
match in code position — a bare `sorry` in tactic position, or a line that
really begins a declaration with `axiom` — is a genuine escape hatch. `grep`
cannot tell prose from code, which is why the `#print axioms` run above is the
check that counts.

### 4. Headline statements

List each headline theorem with its Lean name, its file and line, its blueprint
label and its paper locator. `docs/theorem-index.md` tabulates them and the
supporting statements; that table is the intended entry point. Each docstring
names its blueprint label and its paper locator, and the locator resolves
inside the snapshot when the mirrors ship.

### 5. Independent statement check

The headline statements are also reproduced, with their whole kernel closure
and with the theorems left as `sorry`, in a separate challenge repository, so
that the official comparator can confirm that *this* library proves *that*
statement with no shared definitions to hide behind. `scripts/comparator/` is
the generator and [`comparator.md`](comparator.md) holds the trust model and
the record.

### 6. Blueprint

```sh
pip install leanblueprint
leanblueprint web      # or: leanblueprint pdf
```

The blueprint is the paper-to-Lean map: every node carries the declaration it
corresponds to, and `\leanok` marks what is formalized.

## Cutting a release (maintainers)

```sh
git tag -a <tag> -m "<artifact snapshot>"
git push github <tag>
scripts/make_artifact.sh <tag> <outdir>          # [options] <git-ref> <out-dir>
```

`--keep-tree` leaves the unpacked snapshot beside the tarball for inspection,
`--no-pdf` skips the gap-note PDF build, and `--help` is the authority on all
of them.

The script extracts the snapshot, builds the gap-note PDFs when their makefile
is present, writes the `MANIFEST.txt`, runs the leak scan, and prints the
tarball path and its checksum. It **exits non-zero without packaging** if the
leak scan finds a home path, a key-shaped string or an e-mail address that is
not allow-listed with a written reason in the script.

Then verify the snapshot the way a reviewer would, in a scratch directory and
**from the tarball alone** — never in the working tree, whose dependency cache
would mask a missing dependency:

```sh
cd $(mktemp -d) && tar xzf <outdir>/<name>.tar.gz
cd <name> && lake exe cache get && lake build <LeanRoot>
```

Attach the tarball and its checksum to the release, and record the clean-clone
build's wall-clock time and machine under **Expected cost** above.

### Double-blind venues

If the venue is double-blind:

```sh
scripts/make_artifact.sh --anonymize <tag> <outdir>
```

This rewrites the author-identifying strings listed in the script's rules and
tags the tarball `-anon`. The rules are derived from `project.github_slug`, so
no personal name or address is committed to this repository; add the rest for
one run through the environment, one `<literal> :: <replacement>` per line:

```sh
MIPSTARRE_ANON_RULES='Ada Lovelace :: Anonymous Author
ada@example.org :: anonymous@example.invalid' \
  scripts/make_artifact.sh --anonymize <tag> <outdir>
```

At most one rule may have an e-mail address on its left-hand side. The rewrite
is not taken on trust: the script itself ships,
so the pass runs over its own rules list, and before packaging anything the run
searches the whole snapshot — including text extracted from every PDF, which a
stream editor cannot rewrite — for each of those strings and refuses rather
than package a survivor.

It does **not** touch the paper sources under `references/`, and it should not:
those are published third-party works whose authors are the cited paper
authors, not the submitters.

It is **not by itself sufficient**. The commit history, the issue and
pull-request links in the documentation, and any hosted blueprint would still
identify the authors. A double-blind submission needs a fresh single-commit
repository built from the anonymized snapshot, not merely this flag.

## Keeping the two exclusion lists in step

What ships is decided **twice**, on purpose:

- `INCLUDE` / `EXCLUDE` in `scripts/make_artifact.sh` — an explicit allow-list,
  so a new top-level directory never joins the artifact by accident;
- the `export-ignore` attributes in `.gitattributes` — applied by `git archive`
  itself, so a plain archive or a hosted source tarball is clean too.

A path excluded in one should be excluded in the other, and the second guard is
the weaker: it is a deny-list, so a new workflow-only file has to be added by
hand, whereas the allow-list drops anything it has not been told about.
`scripts/` is the mixed directory — a few entries ship, the rest do not — and
`git archive` does not descend into a directory it was told to ignore, so a
child of an ignored directory cannot be re-admitted. Whichever decision is made
about the paper mirrors, record it in `.gitattributes` as a line **or** as a
comment, so the decision is visible where somebody would otherwise change it.

The leak scan is the backstop. It is fail-closed — nothing is packaged on a hit
— and forgives only through an entry carrying a written reason: one form for a
pattern that is safe anywhere, another for one that is safe only in named
paths. PDFs are covered too: any PDF in the snapshot has its text extracted and
scanned with everything else, and the run stops rather than ship a PDF it could
not read, so cutting a release with the gap notes built needs a PDF text
extractor installed.
