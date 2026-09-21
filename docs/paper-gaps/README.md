# Paper-gap notes

Every statement in this formalization that departs from the source paper it
cites is justified here. A *paper-gap note* is a standalone LaTeX document that
quotes the printed statement, says precisely what is wrong with it or what
cannot be reconstructed from the printed proof, and states the corrected form
the formalization uses instead. The notes are the reviewer-facing evidence
behind the per-statement **gap register**, which is the repository's summary of
every deviation from the source papers.

Nothing here is a to-do list. A note exists because a correction was already
made; reading one should let a reviewer check that correction against the paper
without opening any Lean file.

**This directory currently holds the protocol and the harness only: no notes
have been written yet.** The files below are the machinery; the notes and the
register come from the project.

| File | What it is |
|---|---|
| [`policy.tex`](policy.tex) | when a gap is documented, and in what form — the style guide for this directory |
| [`proof-gap-protocol.tex`](proof-gap-protocol.tex) | what the formalization does when a printed statement is kept but its printed proof is blocked |
| [`template.tex`](template.tex) | the model note; start every new note from it |
| [`command.tex`](command.tex) | macros shared by every note; not compiled on its own |
| [`references.bib`](references.bib) | the shared bibliography |
| [`Makefile`](Makefile) | the build and the standalone check |

## Building the notes

```sh
make -C docs/paper-gaps          # compile every note into docs/paper-gaps/build/
make -C docs/paper-gaps check    # compile, then fail on any LaTeX error or
                                 # unresolved reference, citation or label
make -C docs/paper-gaps pages    # page count per note
make -C docs/paper-gaps clean    # remove docs/paper-gaps/build/
```

Requirements: `latexmk`, `pdflatex` and `bibtex` from any current TeX
distribution, plus the `amsmath`, `amssymb`, `braket`, `hyperref` and `xurl`
packages. No project-specific tool is needed — that is the point of the
Makefile. `build/` is ignored by the repository `.gitignore` and **no PDF is
committed**; the artifact packaging step builds the PDFs at release time.

`make check` is the standalone gate. The repository's own CI additionally runs
the blueprint tool's `paper-gaps check` (the `paper-gaps` step of
`local/bin/ci.sh`), which validates cross-note slugs and registered source keys.
The two are complementary: CI checks that the notes refer to each other and to
the papers consistently, `make check` checks that they typeset.

## Writing a new note

1. Copy [`template.tex`](template.tex) to
   `docs/paper-gaps/<key>_<slug>.tex`, where `<key>` is the source key
   registered for the paper in the project's blueprint-tool configuration.
2. Follow [`policy.tex`](policy.tex): notation matches the cited source through
   [`command.tex`](command.tex), and Lean identifiers, file paths and issue
   numbers appear in footnotes only.
3. Quote the printed statement, say exactly which step fails, state the
   corrected statement, and show why the correction is **sufficient** for every
   downstream use in the paper and in the blueprint.
4. Add a row to the track's gap register (`tracks.<name>.gap_register` in
   [`local/project.json`](../../local/project.json), conventionally
   `docs/paper-gaps/<track>-gap-register.md`).

## The gap register

One file per track, one row per note, with these columns:

| Column | What it holds |
|---|---|
| Note | the note's file name, linked |
| Source statement | the paper's label and locator |
| Blueprint label | the node that carries the corrected statement |
| Correction status | `corrected`, `open`, `withdrawn` — the note's own verdict |
| Lean status | `formalized`, `stated`, `not started` |
| Issues | the tracking issues, if any |

Criterion C3 of [`../../local/protocols/completion.md`](../../local/protocols/completion.md)
reads this register and requires **every** row to have a terminal status before
a track may be declared finished. A note without a row, or a row without a
status, blocks completion — which is the point: a deviation nobody classified
is a deviation nobody checked.

## See also

- [`policy.tex`](policy.tex) — when a gap is documented, and in what form.
- [`proof-gap-protocol.tex`](proof-gap-protocol.tex) — what the formalization
  does when a printed statement is kept but its printed proof is blocked.
- [`../../local/protocols/completion.md`](../../local/protocols/completion.md)
  — criterion C3, which the register answers.
