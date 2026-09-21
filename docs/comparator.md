# Comparator verification of the headline theorems

**Status: empty.** No challenge has been built and no comparator run has been
recorded in this repository yet. Everything below says what this document must
contain once a track reaches that point, and how to get there. Criterion C5 of
[`local/protocols/completion.md`](../local/protocols/completion.md) reads the
record blocks in this file; a track without one cannot be declared finished.

Do not leave a sentence in this file that is not true of this repository. A
comparator record is evidence, and a plausible-sounding paragraph about a run
nobody made is the one thing that would make the evidence worthless.

---

## 1. What the comparator is, and why the challenge lives elsewhere

The official [`leanprover/comparator`](https://github.com/leanprover/comparator)
is the top level of the escalating checks in the Lean reference manual's
[Validating Proofs](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
chapter. It compares, constant by constant, the full kernel closure of a
*statement* written in a trusted environment against the same statement as this
library proves it — so a proof cannot hide behind a definition the checker
never sees.

The challenge therefore lives in a **separate repository**
(`project.comparator_slug` in `local/project.json`), which depends on this
library **pinned by commit**:

- `Challenge.lean` there imports **only Mathlib** and re-declares, verbatim and
  in dependency order, every declaration in the comparator-relevant closure of
  the headline statements, then states each theorem with `sorry`. It is the
  entire human audit surface, and it is the whole point: keep it short,
  notation-free and reviewed.
- `Solution.lean` there imports this library, which proves the theorems under
  the same fully qualified names.
- Its CI runs the comparator on every push: a real sandbox, an external kernel
  checker in addition to Lean's, and a fresh re-check.

Creating that repository is an action outside this one, and therefore an
**owner permission**, not a decision the main session may take.

## 2. What this repository contributes

1. **Environment alignment.** Because the comparison is on elaborated terms,
   every module contributing a declaration to the closure must elaborate in the
   same environment the Mathlib-only challenge file will: they use the full
   `import Mathlib`, directly or through a shared base module, and carry a
   comment saying not to narrow that import.
2. **No `private` in the closure.** A `private` declaration's real name is
   qualified by its defining module, so a challenge file in another module can
   never re-declare it under the library's name. Dropping `private` is the
   smallest faithful edit: no statement, definition body or proof script
   changes, only the visibility of names the statement already depends on.
3. **Regeneration tooling.** `scripts/comparator/` holds the closure extractor
   (a Lean metaprogram mirroring the comparator's own constant walk) and the
   assembler that produce `Challenge.lean`, plus the drift check that
   byte-compares the checked-in expected copy against a fresh generation.

The challenge registry itself comes from `local/project.json`: one challenge
per track that names headline theorems. Adding a challenge means registering a
track with its `headline` theorems, writing a header and a footer, and adding a
CI drift step — no generator code changes — plus importing the new root module
in the extractor when the targets live outside the current imports. Only the
hand-written elaboration context that the kernel closure cannot carry
(`EXTRAS`, `MODULE_PRELUDES`) lives in `scripts/comparator/challenges.py`, and
both ship empty with one commented example. See
`scripts/comparator/README.md` for the exact pipeline, and check the drift with

```bash
python3 scripts/comparator/check_challenge_drift.py --root .            # verify
python3 scripts/comparator/check_challenge_drift.py --root . --update   # regenerate
```

## 3. The record format — what the gate reads

One block per track, in this file, and the shape is **not** free: criterion C5
of `scripts/completion_gate.py` parses it.

- The block begins with a line that is *exactly* the marker
  `<!-- completion-gate: track=NAME -->`, where `NAME` is the track's name in
  `tracks` of `local/project.json`. Nothing else may be on that line.
- Every line after it that begins with `-` is read as `key: value`. The first
  line that does not begin with `-` ends the block.
- These five keys must all be present and non-empty — the gate names each
  missing one and fails:

| Key | What it must say |
|---|---|
| `challenge-repository` | the challenge repository, `<owner>/<repo>-comparator` |
| `verified-library-commit` | the **full 40-character** commit of this library that the challenge repository verified; it must be an ancestor-or-equal of the commit being declared |
| `expected-challenge` | the repository-relative path of the checked-in expected copy, exactly the one `tracks.<name>.expected_challenge` registers |
| `drift-check` | where the regeneration drift check runs, and its last result |
| `covered-theorems` | the fully-qualified headline theorems, comma-separated |

The empty form to copy, one per track:

```markdown
<!-- completion-gate: track=NAME -->
- challenge-repository:
- verified-library-commit:
- expected-challenge:
- drift-check:
- covered-theorems:
```

Prose about the run — the date, the checkers, the sandbox, the deviations, who
read `Challenge.lean` — goes **below** the block, after a blank line, in
ordinary paragraphs or a table. Keeping it out of the `- key: value` lines is
what lets the gate parse the record at all.

**`covered-theorems` must list every headline theorem the track registers**
(`tracks.<name>.headline` in `local/project.json`), and every one of those
names must also occur in the registered expected copy. The record is written by
hand by the session that wants to declare the track finished, so it is never
its own evidence: the gate checks it against the challenge file. A record that
covers a subset fails C5; that is the criterion's whole job.

This file currently contains **no record block**, because no comparator run has
been made here.

## 4. Checklist against the *Validating Proofs* guide

Fill the status column with what is actually true here, or leave it as
`not yet`.

| Level | Requirement | Status |
|---|---|---|
| 2 | `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound` | `<the track's axiom-audit module>` |
| 3 | an independent re-check of the compiled environment | `<the checker and where it runs>` |
| 4 | statement written in a trusted environment, separate from the proof code | `Challenge.lean` imports only Mathlib (CI-enforced), separate repository, library pinned by commit |
| 4 | sandboxed build, export and kernel replay | `<the sandbox, or "not yet">` |
| 4 | an external checker in addition to the Lean kernel | `<the checker, or "not yet">` |
| 5 | no native evaluation | excluded by the permitted-axiom set — the comparator rejects any extra axiom |
| — | statement review: custom notation and type classes must not obscure meaning | the human step; record who read it and when |

Record every deliberate deviation from the comparator's adversarial setup with
its reason. A trusted checkout may legitimately reuse prebuilt artefacts or
omit an escape guard; an unexplained deviation is a hole.

## 5. Residual trust

Lean's logical soundness, the comparator's own plumbing, the sandbox, a
simultaneous bug in every checker, and **human error in `Challenge.lean`
itself**. The last one is the reason the challenge file is kept short,
notation-free and read by a person: everything else in it is machine-checked to
agree with the library, but that it states the intended theorem is not
checkable by any tool.

When a track's record is written, say explicitly what a human had to audit and
could not delegate: that the objects the challenge defines are the paper's
objects, that the error functional is the paper's, and that the packaging of
hypotheses smuggles nothing in.

## 6. Benchmark use (optional)

A self-contained challenge statement is also submission-ready for a
comparator-based benchmark such as
[`leanprover/lean-eval`](https://github.com/leanprover/lean-eval): port the
statement module to the benchmark's toolchain, tag the theorem as a problem,
add the manifest entry it asks for, and open a pull request there. Solvers then
edit only the submission file, and scoring is comparator acceptance.
