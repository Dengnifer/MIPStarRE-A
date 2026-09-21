# Completion protocol — definition of done

Normative. This protocol says when a formalization **track** may be declared
finished, and forbids the declaration until a model-free gate agrees. Amend it
only through `local/protocols/meta.md` (`EVOLUTION.md` entry, cited trigger).

Trigger for its existence, owner, 2026-09-19: *"some protocol(s) in the
workflow should ensure that when the project finishes, the formalization is
done without caveat, and satisfies the lean comparator"*; earlier the same day,
*"i want zero sorry"*.

## 1. Scope

A **track** is a Lean subtree, the blueprint chapters describing it, its
paper-gap register, its axiom-audit file, its blueprint exemption table, its
comparator record and its artifact file set. The per-track data is §6. A
repository has one track by default (`project.track`); nothing here is specific
to any project or any paper.

**Declaring finished** means any public statement that the track is complete: a
completion comment on the track's umbrella issues (the ones §6 registers),
closing those issues, tagging a release, or a README/status page that says the
track is done.

## 2. Finished without caveat

A track is finished without caveat at a commit when all seven criteria hold *at
that commit*.

**C1 — Proof integrity.** Zero term-level `sorry`, `admit`, project `axiom` or
`constant` declaration, `native_decide` / `decide +native`, or
`Lean.trustCompiler` under the track's Lean root. The sorry-site rule is the
one in `results/telemetry/owner-tools/estimate.sh` (`SORRY_SITE_RE`), and there
is exactly **one** implementation of it: `scripts/completion_gate.py` loads that
line from that file and never restates it. Explicit axiom declarations are
found with `DECL_RE` of `scripts/audit_lean_axiom_declarations.py`, imported
rather than copied.

**C2 — Headline axioms.** Every headline theorem of §6 depends only on
`propext`, `Classical.choice` and `Quot.sound`. The check is a committed
`AxiomAudit` Lean file for the track that carries one audit command per
headline theorem — an `assert_standard_axioms`-style command that prints the
axiom set and fails elaboration unless it is exactly those three — and is built
in CI. The gate
checks that the file
exists and covers the table; the axiom values themselves come from the build
and are reported as delegated.

**C3 — Paper gaps terminal.** Every data row of the track's paper-gap register
carries a `Terminal status` cell reading exactly `corrected` or
`no-difference`:

- `corrected` — a documented statement correction that **meets the four
  adoption conditions of `local/protocols/issues-prs.md`** — correctness,
  sufficiency, minimality ("the closest sufficient statement to the source,
  with no unnecessary hypothesis or weakened conclusion and no change to the
  source semantics") and Lean convergence — and carries its three artifacts: a
  gap note, a corrected blueprint node citing it, and, where the printed claim
  is not proved, the printed claim preserved as a non-asserted `Prop` beside
  the corrected one, so a reader can see both. The
  artifacts are evidence that a correction was adopted; they are not a route
  around those conditions, and a row whose correction weakens a conclusion is
  not terminal however complete its artifacts are.
- `no-difference` — the formalization and the source statement agree; nothing
  to correct.

No row may read `open`, `pending` or `sorry`. No headline theorem statement may
be weaker than the source paper except through a `corrected` row.

**C4 — Blueprint marked.** Every blueprint node of the track that carries
`\lean{...}` also carries `\leanok`, or appears in the track's exemption table
with a written reason; `scripts/blueprint_leanok_axioms.py --ci` exits 0. A
node is any environment the repository's blueprint parser recognises: the gate
reads that list out of `_TEX_ENV_BEGIN_RE` in `scripts/blueprint_lean_sync.py`
instead of keeping its own, so an `example` or `remark` node with a Lean link
counts exactly as a theorem does. Which nodes are the track's is read off the
tree and not off section 6: besides the chapters registered there, the gate
reads every other `.tex` beside them whose `\lean{...}` names a declaration
under the track's Lean root, and judges those nodes too, so a node of the track
that lives in a chapter shared with another track is in scope whether or not
its chapter is listed. The
exemption table is the only place a permanently unmarked node may live, and a
row there is a caveat that must be defensible in the paper.

**C5 — Lean comparator.** A comparator challenge exists covering every headline
theorem; the in-repository expected challenge is free of regeneration drift
(`scripts/comparator/check_challenge_drift.py` for that track's expected copy
passes in CI); and the track's comparator record (§6, `docs/comparator.md`)
states the challenge repository, the library commit that repository last
verified with the official `leanprover/comparator` (`permitted_axioms` limited
to the three standard axioms, external kernel check enabled where the platform
allows), and the expected-copy path. That verified commit must be an
ancestor-or-equal of the commit being declared finished, with no Lean change to
the statement closure in between — which is exactly what a passing drift check
proves.

The record is a block in `docs/comparator.md` that opens with the exact marker
`<!-- completion-gate: track=<name> -->` and continues with `- key: value`
lines until the first line that does not begin with `-`. The five keys the
gate requires, all non-empty, are `challenge-repository`,
`verified-library-commit` (a full 40-character hash), `expected-challenge`,
`drift-check` and `covered-theorems`; §3 of
[`../../docs/comparator.md`](../../docs/comparator.md) carries the empty form.

The coverage half of C5 is decided against the challenge, never against the
record alone. The record's `expected-challenge` must be exactly the expected
copy §6 registers for the track, and every headline theorem of §6 must occur in
that file by its fully-qualified name — the name the assembler of
`scripts/comparator/` writes for each declaration of the closure. A record that
lists a headline theorem the registered expected copy never names fails C5:
`covered-theorems` is written by hand in the same document, by the same session
that wants to declare the track finished, so it may not be its own evidence.
That the challenge *elaborates* to the same statements is the drift check and
the comparator run, both delegated to CI.

**C6 — Docs truthful.** No README, status page or estimate may advertise a
nonzero open-site count once C1 holds. Every doc the track registers (§6) must
exist: a registered doc that has been renamed or deleted fails C6 rather than
being skipped, so the criterion can never report a green run over zero docs.

**C7 — Artifact readiness.** "Done" means ready to be attached as an artifact
to an ITP submission (owner, 2026-09-19), so every file such a submission needs
is committed at the declared commit: the files §6 registers for the track
(`artifact_files`) and the snapshot script it registers (`artifact_script`). The gate checks that each of them exists and fails
closed naming the missing ones; that the script *produces* a snapshot whose
leak scan passes is a run, and is reported as delegated like C2, C4 and C5.
A missing artifact file is main's to-do list, not a caveat that may be carried
into a completion statement.

## 3. Where the comparator challenge lives

The challenge repository lives **outside** this repository and outside any
umbrella repository: a separate repository of its own, named by
`project.comparator_slug` in `local/project.json` (`docs/comparator.md`). Three
reasons, in order of weight:

1. *Validating Proofs* level 4 requires the statement to be written in a
   trusted environment separate from the proof code. A challenge inside this
   repository would be elaborated in the same environment it is meant to check.
2. The challenge must depend on this library **pinned by commit**. A repository
   cannot meaningfully pin a commit of itself, and the pin is the evidence C5
   rests on.
3. An umbrella repository, where one exists, is not the main session's to
   modify (`local/personas/main.md`).

What stays here: the generator (`scripts/comparator/`), the expected copy, the
drift check, and the comparator record. Creating the challenge repository is an
action outside this repository and is therefore an **owner action**, not a main
decision.

## 4. Who enforces this

The main session, or the acting main, **may not** post a completion statement
on the track's umbrella issues, close them, or tag a release unless

    python3 scripts/completion_gate.py check --track <track>

exits 0 on the exact commit being declared, and the gate's output is attached
to the completion comment. A gate run on any other commit is not evidence.

A failing gate is **not an owner blocker**. It is main's to-do list: no owner
inbox comment is filed for it, and the work it names is ordinary development.

The gate is deliberately **not** part of the blocking PR CI: it would fail every
PR until the comparator challenge exists. `local/bin/ci.sh` has no non-blocking
step class — every step it records is blocking — so CI is left unchanged, and
the gate is run by hand before a completion statement.

## 5. The gate

`scripts/completion_gate.py` is python3, standard library only, no network and
no model call. `check --track <t> [--repo-root R] [--commit C] [--json]` prints
one PASS/FAIL line per criterion with `file:line` evidence, and exits 0 only
when every mechanically checkable criterion passes. Criteria with a half that
needs a run the gate does not perform (C2 axiom values, C4 `--ci` run, C5 drift
regeneration, C7 snapshot leak scan) print as
`DELEGATED` once their static half holds — never as `PASS`, so no completion
comment can quote a green line for a check nobody ran — while a failing static
half is still `FAIL`. `DELEGATED` does not turn a failing run green and does
not by itself make one green either: the delegated halves are read off the CI
run of the same commit. Unit tests:
`scripts/tests/test_completion_gate.py`.

## 6. Registered tracks

**The registry is `local/project.json`, under `tracks.<name>`.** This section
says what a track's row set means; the values live in that file, and the gate
reads them from there. A repository with no registered track is a valid,
freshly instantiated repository: the gate says so in one line and exits
non-zero, rather than crashing or reporting a green run over nothing.

### The fields

| Field in `tracks.<name>` | What it names |
|---|---|
| `lean_root` | the track's Lean subtree, relative to the repository root |
| `headline` | the track's headline results: a list of `[lean name, blueprint label]` pairs |
| `blueprint_chapters` | the chapter files that describe the track |
| `gap_register` | the register of gaps found in the source paper for this track |
| `axiom_audit` | the committed Lean file whose build asserts C2 |
| `leanok_exemptions` | the table of blueprint nodes exempt from `\leanok`, each with a written reason |
| `comparator_doc` | the document, and the block inside it, holding the comparator record |
| `expected_challenge` | the checked-in expected assembly of the challenge statement file |
| `truthful_docs` | the status documents C6 holds to the truth |
| `artifact_files` | the files an artifact submission needs, C7 |
| `artifact_script` | the snapshot script, C7 |
| `umbrella_issues` | the issues a completion statement would be posted on |

Every path-valued field is a repository-relative path that must exist at the
declared commit; a registered path that has been renamed or deleted **fails**
the criterion that reads it, and is never skipped.

### Example

```jsonc
// local/project.json — EXAMPLE, invented, for shape only
"tracks": {
  "main": {
    "lean_root": "WeakDep",
    "headline": [
      ["WeakDep.TailBounds.tail_bound", "thm:tail"],
      ["WeakDep.Limits.clt", "thm:clt"]
    ],
    "blueprint_chapters": [
      "blueprint/src/chapter/ch04_tail_bounds.tex",
      "blueprint/src/chapter/ch05_limits.tex"
    ],
    "gap_register": "docs/paper-gaps/main-gap-register.md",
    "axiom_audit": "WeakDep/Test/AxiomAudit.lean",
    "leanok_exemptions": "docs/completion/main-leanok-exemptions.md",
    "comparator_doc": "docs/comparator.md",
    "expected_challenge": "scripts/comparator/expected/Challenge.lean.expected",
    "truthful_docs": ["README.md"],
    "artifact_files": ["README.md", "docs/theorem-index.md", "docs/DEVIATIONS.md",
                       "docs/ARTIFACT.md", "LICENSE"],
    "artifact_script": "scripts/make_artifact.sh",
    "umbrella_issues": [12]
  }
}
```

### Invariants the registry must hold

1. **The headline set is the paper's, and the challenge generator's `targets`
   equal it.** They are two names for one set, and C5 checks the coverage: a
   generator that covers a subset of the headline table fails C5 *by
   construction*. Widen the generator; never shrink the table to meet it.
2. **The blueprint-chapter list is the track's own chapters, not the whole of
   C4's scope.** The gate also judges any node in another chapter whose
   `\lean{...}` names a declaration under the track's Lean root, so a chapter
   missing from the list narrows nothing — it only hides the chapter from
   whoever reads this registry.
3. **Adding a track** means adding one `tracks.<name>` object with every field
   above, in one commit, together with whatever new files it names. Nothing
   else changes: no gate code, no protocol text.
4. **The gate never invents a default.** A missing field, an unknown track name
   or an empty registry is an error with a message naming what is missing.

A unit test under `scripts/tests/` reads this section's field table and fails
when the registry's per-track object gains or loses a field without a matching
row here, so the registry and this protocol cannot drift apart silently.
