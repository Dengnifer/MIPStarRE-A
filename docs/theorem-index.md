# Theorem index

**Empty — the project fills this in.** This page is the intended entry point
for a reviewer: every headline result and every supporting statement, with its
paper statement, its Lean name, its file and line, its blueprint node and its
axiom closure.

Criterion C7 of
[`../local/protocols/completion.md`](../local/protocols/completion.md) requires
it (a track registers it in `artifact_files`), and
[`ARTIFACT.md`](ARTIFACT.md) sends reviewers here first.

One table per track, headline results first:

| Paper statement | Lean declaration | File:line | Blueprint node | Axioms |
|---|---|---|---|---|
| `<label>`, `references/<mirror>/<file>.tex:<lines>` | `<fully.qualified.name>` | `<LeanRoot>/<path>.lean:<line>` | `<node label>` | `propext, Classical.choice, Quot.sound` |

Rules for the table:

- Every headline result of `tracks.<name>.headline` in
  [`../local/project.json`](../local/project.json) appears, and nothing claims
  to be headline that is not registered there.
- The axiom column is copied from an actual `#print axioms` run, not asserted.
- A statement that departs from the printed source links its paper-gap note in
  the paper-statement cell.
- A statement that is stated but not proved says so, in its own row, rather
  than being left out.
