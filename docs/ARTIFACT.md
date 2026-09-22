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
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | the pinned Lean toolchain and nine Lake package revisions |
| `blueprint/src/` | the LaTeX blueprint, cross-referenced to the Lean names with `\lean{}` / `\leanok` |
| `docs/` | the mathematical documentation, including `docs/QPBT-theorem-index.md`, `docs/DEVIATIONS.md`, and the source-gap register under `docs/paper-gaps/` |
| `references/` | the TeX sources of the five source papers — third-party material, see below — so that the paper locators can be checked inside the snapshot; the report below records two existing exceptions |
| `scripts/comparator/` | the generator and checked-in Mathlib-only challenge tree used by the independent comparator repository |
| `scripts/blueprint_leanok_axioms.py` | the blueprint/axiom consistency check |
| `scripts/make_artifact.sh` | the script that produced this snapshot, so the packaging is itself auditable |
| `MANIFEST.txt` | source commit, file count, Lean code-line total, toolchain, Mathlib revision, leak-scan and self-containment results |

## What is **not** in it, and why

**The AI-workflow layer.** This development was produced with a local
agent-orchestration layer: `local/`, `results/telemetry/`, `.github/` prompts
and workflows, `.githooks/`, `audits/`, `home_page/`, `docbuild/`, and the
scripts and docs that only serve that layer. It stays in the source repository
because it is research material in its own right, but it is not part of the
mathematics and contains host-specific operational records. Evidence needed by
a tarball reviewer is therefore stated in this page or in another shipped file;
an excluded telemetry, audit, or `local/` path is not an artifact locator.

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

**Why they ship.** Lean docstrings, `docs/QPBT-theorem-index.md`, and
`docs/DEVIATIONS.md` cite their source as
`references/<paper>/<file>.tex:<lines>`. With the sources in the snapshot all
but the two locators listed below resolve inside the tarball, and a reviewer can
read the paper statement next to the Lean statement without reconstructing the
per-section split from arXiv. The directories are plain per-section splits of
the papers' arXiv sources.

**Licence.** These files are the work of their own authors and are **not**
covered by the Apache-2.0 `LICENSE` that ships with the snapshot and governs the
development itself. They are kept here for reference and for line-precise
citation; their own terms govern any further use or redistribution. The
`MANIFEST.txt` of every snapshot repeats this.

**Locator report.** `MANIFEST.txt` records how many of the
`references/<paper>/<file>.tex` paths cited in the Lean sources, the blueprint
and the docs actually resolve inside the snapshot. It is a report, not a gate:
a locator may name a section the per-file split arranges differently. The
gap-note template's fill-in placeholder is not counted (the mirrors' file names
are lower case, so a locator with a capital in it is a form to complete rather
than a citation). At the commit named in the MANIFEST two do not resolve —
`references/ldt-paper/commutativity_points.tex` and
`references/ldt-paper/projectivization.tex`, cited from
`MIPStarRE/LDT/CommutativityPoints/AnswerTheorems.lean` and
`MIPStarRE/LDT/MakingMeasurementsProjective/Orthonormalization.lean`. They
predate this packaging work and are tracked separately; the surrounding
docstrings also name their blueprint labels, which do resolve.

**Internal-link report.** The packaging script also reports relative Markdown
links whose targets do not ship. In the historical preflight pinned below it
found two dead links among 198 checked, both in
`docs/paper-gaps/qpbt-gap-register.md`: one to
`local/protocols/completion.md` and one to `local/protocols/issues-prs.md`.
Those workflow documents are excluded intentionally. They are the two known
internal-link limitations; they are not missing `docs/DEVIATIONS.md` links.

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

### 2. Fetch the Mathlib build cache, build, and run the audits

```sh
lake exe cache get
lake build MIPStarRE
lake build MIPStarRE.QPBT.Test.AxiomAudit
lake build MIPStarRE.LDT.Test.AxiomAudit
python3 scripts/blueprint_leanok_axioms.py --ci
```

The full `MIPStarRE` target must precede the blueprint audit. A QPBT-only build
does not produce two LDT oleans needed by that audit, and its on-demand fallback
does not recursively build missing dependencies. The two compile-time axiom
modules are not imported by the umbrella targets, so they must also be named
explicitly.

**Measured project-build cost, with exact scope.** At library commit
`05df4b74fea7d291050909102c737e6b03d85ba6`, a fresh `--no-local` clone with an
empty `.lake/build` ran

```sh
nice -n 10 env LEAN_NUM_THREADS=16 \
  lake build MIPStarRE.QPBT MIPStarRE.QPBT.Test.AxiomAudit \
    MIPStarRE.QPBT.Test.NonVacuity
```

in 803 seconds (13 minutes 23 seconds), compiling 602 project modules with zero
errors. The pinned dependencies were supplied as prebuilt oleans from a
read-only store; `lake exe cache get`, dependency download, and dependency
compilation were not part of the 803 seconds. From that built state,
`lake build MIPStarRE` compiled 12 additional modules in 26 seconds, after
which `python3 scripts/blueprint_leanok_axioms.py --ci` passed 1,837
declarations. This historical run did not include the separately named LDT
axiom-audit target.

The host was a 128-core Intel Xeon Platinum 8358P at 2.60 GHz with 503 GiB of
RAM. Lake scheduled up to 21 Lean processes despite `LEAN_NUM_THREADS=16`; the
largest single-process RSS was 5.10 GB and the sampled sum across Lean and Lake
processes peaked at 84.3 GB. These are measurements, not minimum hardware
requirements. A reviewer starting without cached dependencies must additionally
pay the download and unpack cost of `lake exe cache get`; no end-to-end timing
including that step has been recorded. The 803-second run is historical evidence
at its named commit, not a timing for the manifest commit in an arbitrary
tarball and not a final artifact build.

### 3. Check that nothing is assumed

The development claims to depend on no axioms beyond Lean's three standard
ones — `propext`, `Classical.choice`, `Quot.sound` — and on no `sorry`,
`admit`, `native_decide`, `unsafe` or `@[extern]` escape hatch.

The check that settles the first half is Lean's own axiom collector, the same
mechanism used by `#print axioms`: it reports the complete axiom closure of a
declaration and, unlike a text search, cannot be misled by prose. The snapshot
ships two compile-time audit modules. The QPBT module fails unless each of
thirteen named declarations has exactly
`{Classical.choice, Quot.sound, propext}`. The LDT module applies the same exact
standard-axiom check to its theorem route and a no-`sorryAx` check to selected
definition and interface declarations:

```sh
lake build MIPStarRE.QPBT.Test.AxiomAudit
lake build MIPStarRE.LDT.Test.AxiomAudit
```

`MIPStarRE.QPBT.Test.AxiomAudit` covers the four headline theorems and nine
further load-bearing statements; the printed axiom lines stay in the build log
as the positive record. Neither audit module is imported from the umbrella
targets. This keeps the metaprogram checks out of ordinary downstream imports,
but also means a plain `lake build MIPStarRE` does not run them.

To read the closures directly instead, put this in a scratch file at the root of
the unpacked snapshot and elaborate it with `lake env lean scratch.lean`:

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

`#print axioms` does not report `native_decide`, `unsafe` or `@[extern]`, which
move trust outside the kernel without leaving an axiom behind. A text search is
the check for those, and for `axiom` declarations:

```sh
grep -rn --include='*.lean' -E '^[[:space:]]*axiom |\b(sorry|admit|native_decide|unsafe)\b|@\[extern' MIPStarRE/
```

Inspect every match: each must be inside a comment or docstring discussing an
escape hatch rather than using one. At frozen package commit
`73c493c8638a098043733205fe6f155dc6d733d1` the command returned four prose
matches: `sorry` in the QPBT combining docstring and both axiom-audit docstrings,
plus a QPBT qubit-form docstring line beginning with "axiom". A bare `sorry` in
tactic position or an actual `axiom` declaration would be a genuine escape
hatch. `grep` cannot distinguish prose from code, which is why the compile-time
axiom audits above are decisive for their registered declarations.

### 4. Headline statements

The main theorem is `pauli_soundness` in `MIPStarRE/QPBT/Test/Soundness.lean`;
its qubit form is `pauli_soundness_qubit` in `MIPStarRE/QPBT/Test/QubitForm.lean`,
completeness is `exists_spcc_value_one` in `MIPStarRE/QPBT/Test/Completeness.lean`,
and the low-degree soundness statement is `exists_ld_soundness` in
`MIPStarRE/QPBT/Test/LowDegreeGameTheorems.lean`. Each carries a docstring
naming its blueprint label and its paper locator. `docs/QPBT-theorem-index.md`,
which ships, tabulates these four and the supporting statements with their Lean
names, blueprint labels and paper locators; that table is the intended entry
point. The paper locator in each docstring is a path under `references/`, which
ships, so it can be opened directly in the unpacked snapshot.

### 5. Independent statement check (optional)

The four headline statements are reproduced, with their union of kernel
closures and with the targets themselves left as `sorry`, in a separate
challenge repository — <https://github.com/Dengnifer/QPBT-comparator> — so that
the official [`leanprover/comparator`](https://github.com/leanprover/comparator)
can confirm that this library proves those statements with no shared project
definitions to hide behind. `scripts/comparator/` is the generator, and
`docs/comparator.md` is the canonical verification record and trust-model
description.

Official run 35638601720 accepted all four targets at challenge commit
`360402fdf4a39399f94331452d6e5d0a35c144be`. Both Lake pins selected library
commit `ecb97d1f66eec1e6fad964f144f78b91ce1fab36`. The run used real landrun,
enabled nanoda, and recorded acceptance by nanoda and Lean's default kernel.
Those exact pins establish closure equality for that run; they do not establish
source faithfulness, completion criteria, or a final artifact build. The exact
commands, pins, and residual trust are recorded in `docs/comparator.md`.

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
from the tarball alone. The Mathlib cache supplies dependency oleans, but the
project build directory must belong to the unpacked snapshot:

```sh
cd $(mktemp -d) && tar xzf /tmp/artifact/mipstarre-qpbt-artifact-*.tar.gz
cd mipstarre-qpbt-artifact-*
lake exe cache get
lake build MIPStarRE
lake build MIPStarRE.QPBT.Test.AxiomAudit
lake build MIPStarRE.LDT.Test.AxiomAudit
python3 scripts/blueprint_leanok_axioms.py --ci
```

Attach the tarball and its sha256 to the release, and record the clean-clone
build's wall-clock time and machine in section 2 above.

### Historical packaging preflight, not a final artifact build

The model-free packaging preflight completed at 2026-09-21T20:06:21Z against
the frozen source commit `73c493c8638a098043733205fe6f155dc6d733d1`. The
authored package contained 956 files including its manifest and 673 project Lean
files (`MIPStarRE/` plus `MIPStarRE.lean`). It built 49 gap-note PDFs, pruned 339
LaTeX intermediates, extracted and leak-scanned all 49 PDFs, found every
`MIPStarRE` import path inside the snapshot, and passed the package leak scan.
Its tarball SHA256 was
`abe7dec8f285dae88b9661aff7e7f2d80f6304d05e74d4a46451982eee003852`.

The same preflight exercised the anonymization rewrite with `--no-pdf`; its
907-file package was self-contained and passed the leak scan, with SHA256
`d94aaf0e8a024e4851c86f6f8dae85782077fb604030e21858d0a35030a07936`.
Both manifests reported the two excluded-workflow Markdown links and the two
historical LDT paper locators documented above. The preflight predates merged
PR #672. It did not build Lean from the packaged tree, run the final
source-faithfulness gates, or certify completion, and neither tarball is the
final artifact.

### Double-blind venues

ITP has historically been single-blind, and the target edition's call for
papers governs. If a double-blind submission is ever needed:

```sh
scripts/make_artifact.sh --anonymize <tag> /tmp/artifact
```

This additionally rewrites the author-identifying strings listed in
`ANON_RULES` in the script (the GitHub owner name inside URLs, the upstream
project name and host, the author name and address) and tags the tarball
`-anon`. The rewrite is not taken on trust: the script itself ships, so the
pass runs over its own rules list as well, and before packaging anything the
run searches the whole snapshot -- including the text extracted from every
PDF, which `sed` cannot rewrite -- for each of those strings and exits `2`
rather than package a survivor. It does **not** touch the source papers under
`references/`, and it should not: those are published third-party works, and
their authors are the cited paper authors, not the submitters. It is **not** by itself
sufficient: the commit history, the issue and PR links in the docs, and the
hosted blueprint would still identify the authors, so a double-blind
submission needs a fresh single-commit repository built from the anonymized
snapshot, not merely this flag.

## Keeping the two exclusion lists in step

What ships is decided twice, on purpose:

- `INCLUDE` / `EXCLUDE` in `scripts/make_artifact.sh` — an explicit allow-list,
  so a new top-level directory never joins the artifact by accident;
- the `export-ignore` attributes in `.gitattributes` — applied by `git archive`
  itself, so a plain `git archive` or a GitHub source tarball is clean too.

A path excluded in one should be excluded in the other, and the second guard is
the weaker of the two: it is a deny-list, so a new workflow-only file has to be
added to it by hand, whereas the allow-list drops anything it has not been told
about. `scripts/` is the one mixed directory: the comparator directory and two
top-level scripts ship, while workflow-only entries do not. `git archive` does
not descend into a directory it has been told to ignore, so a child of an
ignored directory cannot be re-admitted. The deny-list therefore excludes the
workflow-only scripts by glob (`scripts/*.py`, `scripts/*.sh`,
`scripts/*.lean`, `scripts/tests/`) and re-admits the two shipped top-level
files with `-export-ignore`; `scripts/comparator/` is never matched and ships
under both guards. `references/` is named in `.gitattributes` too, as a comment
rather than an `export-ignore` line, so that the decision to ship it is visible
where somebody would otherwise add the line back.

The exact retained full-PDF evidence is the frozen preflight above; moving file
counts are read from each package's `MANIFEST.txt`, not inferred from an older
repository-wide count. Generated PDFs are not tracked in git and therefore
cannot appear in a plain `git archive`. LaTeX intermediates are pruned because
they are not part of the artifact and because `.fls` and `.fdb_latexmk` record
the absolute build directory.

The leak scan is the backstop: it is what caught an upstream developer's home
path in `docs/reports/` and got that directory excluded. It is fail-closed —
exit 2, nothing packaged — and forgives a hit only through an entry that
carries a written reason: `LEAK_ALLOW` for a pattern safe anywhere (the RFC 2606
placeholder domains) and `LEAK_ALLOW_IN` for one safe only in named paths (the
papers' own author addresses under `references/`). PDFs are covered too: any
PDF in the snapshot has its text extracted with `pdftotext` and scanned with
everything else, and the run stops rather than ship a PDF it could not read, so
cutting a release with the gap notes built needs `poppler-utils` installed.
