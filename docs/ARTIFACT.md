# The ITP artifact

This page is for two audiences: a **reviewer** who received the artifact
tarball and wants to check that the claimed theorems really are proved, and a
**maintainer** who has to cut the next snapshot.

The artifact is a **release snapshot of the mathematical development**, not the
working repository. It is produced by `scripts/make_artifact.sh` from a tagged
commit, and every copy carries a `MANIFEST.txt` naming the commit it came from.

## What is in it

| path | what it is |
|---|---|
| `MIPStarRE/`, `MIPStarRE.lean` | the Lean 4 development — the contribution |
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | the pinned build: Lean 4 and all ten dependencies by exact revision |
| `blueprint/src/` | the LaTeX blueprint, cross-referenced to the Lean names with `\lean{}` / `\leanok` |
| `docs/` | the mathematical documentation, including `docs/paper-gaps/` (the register of gaps found in the source papers) |
| `references/` | the TeX sources of the five source papers — third-party material, see below — so that every `file.tex:lines` locator in the docstrings resolves inside the snapshot |
| `scripts/comparator/` | the generator for the self-contained `Challenge.lean` statement file used by the independent challenge repository |
| `scripts/blueprint_leanok_axioms.py` | the blueprint/axiom consistency check |
| `scripts/make_artifact.sh` | the script that produced this snapshot, so the packaging is itself auditable |
| `MANIFEST.txt` | source commit, file count, Lean code-line total, toolchain, Mathlib revision, leak-scan and self-containment results |

## What is **not** in it, and why

**The AI-workflow layer.** This development was produced with a local
agent-orchestration layer: `local/`, `results/telemetry/`, `.github/` prompts
and workflows, `.githooks/`, `audits/`, `home_page/`, `docbuild/`, and the
scripts and docs that only serve that layer. It stays in the source repository
because it is research material in its own right, but it is not part of the
mathematics and it dominates the repository's size (the telemetry session logs
alone are roughly 200 MB). Excluding it also removes, without any history
rewrite, the ~2,456 tracked files that mention the build host's home path.

## Third-party material: the paper sources, `references/`

The snapshot ships the TeX sources of the five papers the development is
formalized from (owner decision, 2026-09-19, following the companion
low-degree-test repository, which likewise keeps its paper sources in the
public repository):

| path | paper | arXiv |
|---|---|---|
| `references/qpbt-paper/` | *MIP\* = RE* (primary source) | arXiv:2001.04383 |
| `references/neexp-paper/` | *NEEXP in MIP\** (secondary source) | arXiv:1904.05870 |
| `references/ldt-paper/` | low individual degree test | arXiv:2009.12982 |
| `references/nv-paper/` | Natarajan–Vidick | arXiv:1610.03574 |
| `references/cs-paper/` | see `references/cs-paper/SOURCE.md` | — |

**Why they ship.** Lean docstrings, `docs/QPBT-theorem-index.md` and
`docs/DEVIATIONS.md` cite their source as
`references/<paper>/<file>.tex:<lines>`. With the sources in the snapshot every
one of those locators resolves inside the tarball, and a reviewer can read the
paper statement next to the Lean statement without reconstructing the
per-section split from arXiv. The directories are plain per-section splits of
the papers' arXiv sources.

**Licence.** These files are the work of their own authors and are **not**
covered by this repository's licence (see the *Licence* section of `README.md`;
the licence for the development itself is the repository owner's to set). They
are kept here for reference and for line-precise citation; their own terms
govern any further use or redistribution. The `MANIFEST.txt` of every snapshot
repeats this.

**Leak scan.** The scan that gates packaging (below) treats these files like
any other: a home path or a key-shaped string inside `references/` still fails
the run. The one forgiveness is scoped to `references/` by path and to
e-mail addresses by content — the corresponding-author addresses printed in the
papers' own front matter, which are third-party material reproduced as
published, not contact addresses of this development. It is recorded as a
`LEAK_ALLOW_IN` entry in `scripts/make_artifact.sh` with that reason, and a
blanket entry was deliberately not used: the scan must still catch an address of
ours anywhere else in the snapshot.

## Verifying the artifact as a reviewer

### 1. Install the pinned toolchain

```sh
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh   # if elan is not installed
cd <unpacked snapshot>
cat lean-toolchain     # leanprover/lean4:v4.32.0 — elan installs this on first use
```

### 2. Fetch the Mathlib build cache and build

```sh
lake exe cache get
lake build MIPStarRE.QPBT
```

**Expected cost.** `lake exe cache get` downloads several GB. Plan on **16 GB
of RAM** and tens of GB of disk: 38 files in the development raise
`maxHeartbeats` and 65 raise `synthInstance.maxSize`, so this is not a laptop
build. Honest statement of the evidence we have: the maintainers' build
telemetry records 1,608 builds of this development, but every one is an
*incremental, warm-cache* build (the two most recent took 79 s and 556 s); the
only full-rebuild record, 25,052 s (7 h), is from 2026-08-30 and predates most
of the QPBT development. **A cold clean-clone build of `MIPStarRE.QPBT` has not
yet been recorded**; when one is, its wall-clock time and machine replace this
paragraph. Budget several hours.

### 3. Check that nothing is assumed

The development claims to depend on no axioms beyond Lean's three standard
ones — `propext`, `Classical.choice`, `Quot.sound` — and on no `sorry`,
`admit`, `native_decide`, `unsafe` or `@[extern]` escape hatch.

The check that settles the first half is Lean's own `#print axioms`: it reports
the complete axiom closure of a declaration, and unlike a text search it cannot
be misled by prose. Put this in a scratch file at the root of the unpacked
snapshot and elaborate it with `lake env lean scratch.lean`:

```lean
import MIPStarRE.QPBT

#print axioms MIPStarRE.QPBT.pauli_soundness
#print axioms MIPStarRE.QPBT.pauli_soundness_qubit
#print axioms MIPStarRE.QPBT.exists_spcc_value_one
#print axioms MIPStarRE.QPBT.exists_ld_soundness
```

Each of the four must report exactly `[propext, Classical.choice, Quot.sound]`.
A `sorryAx` in a closure would mean the theorem is not proved; a project
`axiom` would appear in the list under its own name.

The snapshot also ships one standing axiom-audit module, for the classical
low-individual-degree layer underneath the Pauli test. It runs `#print axioms`
at build time and fails the build when a declaration's closure is not the one
recorded beside it:

```sh
lake build MIPStarRE.LDT.Test.AxiomAudit
```

There is no such module for the QPBT layer yet — the scratch file above is the
check for the four headline theorems.

`#print axioms` does not report `native_decide`, `unsafe` or `@[extern]`, which
move trust outside the kernel without leaving an axiom behind. A text search is
the check for those, and for `axiom` declarations:

```sh
grep -rn --include='*.lean' -E '^[[:space:]]*axiom |\b(sorry|admit|native_decide|unsafe)\b|@\[extern' MIPStarRE/
```

**Expected output: a handful of matches, every one of them inside a comment or
a docstring that discusses an escape hatch rather than using one.** At the
commit named in `MANIFEST.txt` there are three: two are the word `sorry` in
backticks (`MIPStarRE/QPBT/Combining/Apply.lean`, describing a source proof
that was open in the paper, and `MIPStarRE/LDT/Test/AxiomAudit.lean`), and one
is a docstring line in `MIPStarRE/QPBT/Test/QubitForm.lean` that happens to
begin with the word "axiom". A match in code position — a bare `sorry` in
tactic position, or a line that really begins a declaration with `axiom` —
would be a genuine escape hatch. `grep` cannot tell prose from code, which is
why the `#print axioms` run above is the check that counts.

### 4. Headline statements

The main theorem is `pauli_soundness` in `MIPStarRE/QPBT/Test/Soundness.lean`;
its qubit form is `pauli_soundness_qubit` in `MIPStarRE/QPBT/Test/QubitForm.lean`,
completeness is `exists_spcc_value_one` in `MIPStarRE/QPBT/Test/Completeness.lean`,
and the low-degree soundness statement is `exists_ld_soundness` in
`MIPStarRE/QPBT/Test/LowDegreeGameTheorems.lean`. Each carries a docstring
naming its blueprint label and its paper locator. Where the snapshot ships a
theorem index (`docs/QPBT-theorem-index.md`), that table is the intended entry
point. The paper locator in each docstring is a path under `references/`, which
ships, so it can be opened directly in the unpacked snapshot.

### 5. Independent statement check (optional)

The statement of the main theorem is also reproduced, with its whole kernel
closure and with the theorem itself left as `sorry`, in a separate challenge
repository — <https://github.com/Dengnifer/QPBT-comparator> — so that the
official [`leanprover/comparator`](https://github.com/leanprover/comparator) can
confirm that *this* library proves *that* statement, with no shared definitions
to hide behind. `scripts/comparator/` in this snapshot is the generator, and
`docs/comparator.md` explains the trust model.

### 6. Blueprint

```sh
pip install leanblueprint
leanblueprint pdf     # or: leanblueprint web
```

The blueprint is the paper-to-Lean map: every node carries the Lean
declaration it corresponds to, and `\leanok` marks what is formalized.

## Cutting a release (maintainers)

```sh
git tag -a itp-2027-artifact-v1 -m "ITP artifact snapshot"
git push github itp-2027-artifact-v1
scripts/make_artifact.sh itp-2027-artifact-v1 /tmp/artifact
```

The script extracts the snapshot, builds the gap-note PDFs when
`docs/paper-gaps/Makefile` is present, writes the MANIFEST, runs the leak scan,
and prints the tarball path and its sha256. It **exits 2 without packaging**
if the leak scan finds a home path, a key-shaped string or an e-mail address
that is not allow-listed with a reason in the script.

Then verify the snapshot the way a reviewer would, in a scratch directory and
from the tarball alone — never in the working tree, whose Mathlib cache would
mask a missing dependency:

```sh
cd $(mktemp -d) && tar xzf /tmp/artifact/mipstarre-qpbt-artifact-*.tar.gz
cd mipstarre-qpbt-artifact-* && lake exe cache get && lake build MIPStarRE.QPBT
```

Attach the tarball and its sha256 to the release, and record the clean-clone
build's wall-clock time and machine in section 2 above.

### Double-blind venues

ITP has historically been single-blind, and the target edition's call for
papers governs. If a double-blind submission is ever needed:

```sh
scripts/make_artifact.sh --anonymize <tag> /tmp/artifact
```

This additionally rewrites the author-identifying strings listed in
`ANON_RULES` in the script (the GitHub owner name inside URLs, the upstream
project name and host, the author name and address) and tags the tarball
`-anon`. It does **not** touch the source papers under `references/`, and it
should not: those are published third-party works, and their authors are cited
authors, not the submitters. It is **not** by itself sufficient: the commit
history, the issue and PR links in the docs, and the hosted blueprint would
still identify the authors, so a double-blind submission needs a fresh
single-commit repository built from the anonymized snapshot, not merely this
flag.

## Keeping the two exclusion lists in step

What ships is decided twice, on purpose:

- `INCLUDE` / `EXCLUDE` in `scripts/make_artifact.sh` — an explicit allow-list,
  so a new top-level directory never joins the artifact by accident;
- the `export-ignore` attributes in `.gitattributes` — applied by `git archive`
  itself, so a plain `git archive` or a GitHub source tarball is clean too.

A path excluded in one should be excluded in the other, and the second guard is
the weaker of the two: it is a deny-list, so a new workflow-only file has to be
added to it by hand, whereas the allow-list drops anything it has not been told
about. `scripts/` is the one mixed directory — three entries ship, the roughly
thirty workflow-only ones do not — and `git archive` does not descend into a
directory it has been told to ignore, so a child of an ignored directory cannot
be re-admitted. The deny-list therefore excludes the workflow-only scripts by
glob (`scripts/*.py`, `scripts/*.sh`, `scripts/*.lean`, `scripts/tests/`) and
re-admits the two shipped top-level files with `-export-ignore`;
`scripts/comparator/` is never matched and ships under both guards.
`references/` is named in `.gitattributes` too, as a comment rather than an
`export-ignore` line, so that the decision to ship it is visible where somebody
would otherwise add the line back. Checked on 2026-09-19 after that change: a
plain `git archive` of the repository and `scripts/make_artifact.sh` produce the
same 860 files, the snapshot adding only its `MANIFEST.txt`.

The leak scan is the backstop: it is what caught an upstream developer's home
path in `docs/reports/` and got that directory excluded. It is fail-closed —
exit 2, nothing packaged — and forgives a hit only through an entry that
carries a written reason: `LEAK_ALLOW` for a pattern safe anywhere (the RFC 2606
placeholder domains) and `LEAK_ALLOW_IN` for one safe only in named paths (the
papers' own author addresses under `references/`). PDFs are covered too: any
PDF in the snapshot has its text extracted with `pdftotext` and scanned with
everything else, and the run stops rather than ship a PDF it could not read, so
cutting a release with the gap notes built needs `poppler-utils` installed.
