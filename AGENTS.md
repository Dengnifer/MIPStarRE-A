# AGENTS.md

Instructions for coding agents working in this repository. This is the
**single source of truth** for agent conventions. Claude Code agents should
also read `CLAUDE.md` for Claude-specific notes; a session a human opened at
the repository root to formalize a paper reads `local/personas/meta.md` first
instead.

> **About the examples below.** This document was written while the workflow it
> describes formalized one particular paper, and some of its examples still
> name that project's modules, theorems, directories and issue numbers. The
> **policy** is paper-agnostic: read every such example as a shape, not as a
> fact about this repository. Where an example names a Lean module root, read
> `project.lean_root` from `local/project.json`; where it names a paper mirror,
> read the mirrors listed in `paper_mirrors`; where it names an issue number,
> read `issues.*`. If an example contradicts this repository's actual tree,
> the tree wins — and fixing the example is a welcome, cheap contribution.

## Project overview

This repository is a Lean 4 + Mathlib formalization of one research paper,
built with an AI-assisted workflow that runs locally. What is being formalized,
where it lives and what it is called are recorded in
[`local/project.json`](local/project.json) — the library name, the Lean root
module, the track, the repository slug, the paper mirrors and the issue
numbers. Every script and every protocol reads them from there.

Issues, pull requests, their evidence and merges live on GitHub, reached only
through `local/bin/gh_common.py`; CI, review and auto-fix **execute locally**.
Read `local/README.md` and `local/DESIGN.md` before doing workflow actions; the
`## Local Operations` section below is the short version.

Key locations:

- `references/<mirror>/` — per-section TeX mirrors of the source papers, used
  as line-precise citation targets. `SOURCE.md` in each one records the arXiv
  URL, the date and the copyright position; `README.md` records the split.
- `blueprint/src/` — the LaTeX blueprint with Lean cross-references
  (`\lean{}`, `\leanok`, `\uses{}`)
- `<LeanRoot>/` — the Lean codebase, matching the blueprint
- `docs/paper-gaps/` — dated notes on defects found in the source papers
- `audits/` — dated audit reports, scouting notes and repair plans
- `local/`, `results/telemetry/` — the workflow layer and its records

**Canonical source hierarchy** (use in this order):

1. `references/` paper mirrors — the TeX source of the papers
2. `blueprint/src/chapter/` — the active blueprint
3. `<LeanRoot>/` — the Lean development

Always read the paper source before formalizing or proving a statement. The
paper contains the precise definitions, theorem statements and proof strategies
the Lean code must faithfully represent. When stuck on a `sorry` site or a
proof, go back to the paper's TeX — the answer is almost always there. Do not
guess or try random tactics without first understanding the paper's argument.

## Repository layout

The Lean tree mirrors the blueprint's chapters: one subdirectory per chapter
group, each typically with a `Defs.lean` and a `Theorems.lean`, and a root
module that re-exports them. `local/project.json` names the root;
`local/chapter-plan.json` (written at bootstrap) names the chapters and the
Lean subpath of each.

Top-level directories:

| Path | Contents |
|---|---|
| `<LeanRoot>/` | Lean sources |
| `blueprint/src/` | the LaTeX blueprint, one file per chapter |
| `references/` | per-section TeX mirrors of the source papers |
| `docs/` | documentation, gap notes, contributor guides, style rules |
| `audits/` | dated scouting and audit reports |
| `scripts/` | paper splitter, audits, comparator tooling, completion gate |
| `local/` | the AI-assisted development workflow |
| `results/telemetry/` | session, build and stage records produced by that workflow |

`local/` and `results/telemetry/` document **how** the formalization was
produced. They are research data about the process, not part of the
mathematical artifact; nothing under the Lean root depends on them.


## Quick Start — Build and Check Commands

Run commands from the repository root unless noted otherwise.

### First-time setup

```bash
lake exe cache get
lake build
scripts/install_git_hooks.sh
scripts/install_git_hooks.sh --check
```

Run the hook check in every fresh worktree before preparing a PR.  The hooks
move fast statement-integrity, proof-debt, changed-file Lean, and blueprint-sync
checks to the local workflow so CI is not spent on preventable statement drift.

### Full project build (CI-equivalent)

```bash
lake build
```

### Fast single-file type-check (default iteration loop)

```bash
lake env lean <LeanRoot>/<Chapter>/Defs.lean
```

### Check for proof holes in one file

```bash
rg -n "sorry|axiom" <LeanRoot>/<Chapter>/Defs.lean || true
```

### Check for proof holes in the whole project

```bash
rg -n "sorry|axiom" <LeanRoot>
```

### Declaration checker

```bash
lake exe checkdecls blueprint/lean_decls
```

Use this when blueprint declaration lists need to match Lean declarations.

### Blueprint build

```bash
leanblueprint pdf    # PDF output
leanblueprint web    # HTML output (use as default for quick checks)
```

In CI, blueprint linting effectively runs `leanblueprint web` from `blueprint/`.

### What counts as a single test

This repository does not have a conventional unit-test suite. The closest
single-test commands are:

- **Lean work**: `lake env lean path/to/File.lean` and
  `rg -n "sorry|axiom" path/to/File.lean || true`
- **Blueprint work**: `leanblueprint web`
- **Whole-repo verification**: `lake build` and
  `lake exe checkdecls blueprint/lean_decls`

### Recommended validation sequence

For a Lean file change:

1. Type-check the edited file with `lake env lean ...`
2. Scan that file for `sorry|axiom`
3. If the change affects imports or shared declarations, run `lake build`

For blueprint changes:

1. Run `leanblueprint web`
2. If declaration links changed, run `lake exe checkdecls blueprint/lean_decls`

## Toolchain

- **Lean**: v4.32.0 (from `lean-toolchain`)
- **Mathlib**: v4.32.0 (from `lakefile.toml`)

Those two files are the answer, not this prose: if they disagree with the lines
above, they win and the lines above are the bug. Never run `lake update`.

Important `lakefile.toml` options:

- `relaxedAutoImplicit = false` — declare all variables explicitly
- `pp.unicode.fun = true`
- `weak.linter.mathlibStandardSet = true`
- `maxSynthPendingDepth = 3`

## Proof-Filling Order

**The order is not written here; it is read off the work.** Fill proofs in the
dependency order of the blueprint graph — a node's `\uses{}` closure before the
node — and take the next item from the tracker tree, where a packet is ready
exactly when it is an open leaf whose every `blocked_by` issue is closed
(`local/bin/ready_packets.py`). Definitions and preliminaries come before the
statements that use them; the chapter that wraps the induction or the final
assembly comes last, because it consumes everything else.

Do not start from the final theorem and guess intermediate facts. Do not invent
a private ordering either: if the blueprint graph and the tracker disagree,
that disagreement is a defect to report, not a licence to choose.

## Faithful Formalization Policy

A declaration is a formalization of a paper theorem only when its public Lean
statement matches the cited paper statement, up to faithful formal encoding.
Changing a Lean theorem away from the corresponding statement in
`references/<key>-paper/` is strongly discouraged and should occur only when a
faithful formal encoding or a documented mathematical necessity requires it.
This applies to every declaration advertised as a formalization of a paper
result, not only to theorems currently undergoing repair.  The check is on the
hypotheses as well as the conclusion.  A theorem whose
conclusion has the right shape but whose assumptions include an extra
load-bearing bridge input or hypotheses bundle is a conditional theorem, not
the paper theorem.
The project goal is to eliminate such conditional bridges, not to normalize
them as permanent infrastructure.

If the only available Lean theorem has extra assumptions, the blueprint must
not mark the source-labelled paper entry as matched by that theorem.  Either
leave the source-labelled entry without `\leanok`, or state the restricted or
conditional result as a separate Lean-only blueprint entry whose hypotheses are
displayed explicitly.  A scope-restricted theorem may be marked `\leanok` only
against a blueprint statement that explicitly states the restriction; it must
not be presented as the unrestricted source theorem.

When a stricter-hypothesis Lean theorem is the only available version near a
source theorem, the discrepancy must have a paper-gap note or tracking issue.
The note should identify the missing hypothesis, explain why it is not part of
the cited statement, and state the plan for eliminating the restriction,
deriving it internally, or moving the result out of the source-labelled route.

This rule applies especially to declarations named after paper labels such as
`mainFormal`, `selfImprovement`, `mainInduction`, or other theorem names linked
from the blueprint by `\lean{...}` and `\leanok`.

Before editing any theorem tagged with a paper label (`thm:*`, `lem:*`,
`prop:*`):

1. Read the corresponding statement in `references/<key>-paper/`.
2. Preserve the public Lean theorem statement, except for hypotheses that are
   genuinely part of the faithful encoding of the paper's domain.
3. Do not add bridge inputs, residual packages, repair hypotheses, producer
   assumptions, generic hypotheses or assumptions bundles, or arbitrary
   implication hypotheses to the paper theorem.
4. If a missing intermediate fact is needed, first state that fact as a named
   lemma or theorem to be proved from the paper hypotheses.
5. Do not add a conditional helper merely to keep a file compiling.  A
   conditional helper may remain temporarily only when the proof content it
   preserves is mathematically useful, the source-faithful theorem remains
   visible, and the helper has a paper-gap note, a named construction theorem
   or proof-obligation target, and an explicit discharge or deletion plan.  Its
   name must show that it is conditional without making the assumption look like
   an acceptable source hypothesis, for example
   `mainFormal_ofInternalObligations`, `selfImprovementFromObligations`, or a
   name ending in `_ofObligations`.
6. Do not point a source-labelled blueprint theorem to the conditional helper
   with `\leanok`.

When reviewing an existing bridge, residual, repair, producer, or package
hypothesis, first try to recover any genuine proof content from its construction
and turn that content into a source-faithful lemma.  If the bridge does not
actually follow from the paper hypotheses, do not preserve the paper theorem as
a strengthened statement.  Restore the paper-aligned theorem statement and leave
the missing proof obligation explicit, even if that means reintroducing a
tracked `sorry` during a repair PR.

Some side conditions are not deviations: positivity needed to define a
division, nonemptiness of a finite type, decidability instances, field-model
instances, and similar boundary hypotheses may be faithful encodings of
assumptions that the paper leaves implicit.  These should still be reviewed and
documented if they are mathematically load-bearing.  The forbidden pattern is
different: moving an unproved step of the proof into the theorem statement, such
as a `BridgeHypotheses`, `Input`, `Residual`, `Package`, `RepairInput`,
`Producer`, generic `Hypotheses`, or generic `Assumptions` assumption that the
paper theorem does not assume.  These assumptions
should not be introduced merely to keep a file compiling or to avoid a `sorry`;
they require explicit mathematical justification and a planned discharge.

In the origin project's tree, for instance, the final theorem `mainFormal` was reserved for the statement of
`\Cref{thm:main-formal}`: from a projective strategy passing the low individual
degree test, it produces the three final consistency conclusions.  A theorem
with an extra hypothesis such as
`hbaseBridge : ... → MainFormalRepairedBridgeHypotheses ...` is temporary
scaffolding at best; it must not be the declaration advertised as
`thm:main-formal`.  The corresponding paper-aligned version should remain
visible, even if its proof is temporarily unfinished during repair.

Every agent changing a paper-labelled theorem must finish with a statement
integrity audit:

- paper assumptions;
- Lean assumptions;
- paper conclusion;
- Lean conclusion;
- verdict: exact, faithful boundary hypotheses, extra assumptions, weakened
  conclusion, or strengthened conclusion.

### Paper-realignment mode

When a theorem, definition, or hypothesis field has already drifted away from
`references/<key>-paper/`, a repair PR may temporarily reintroduce `sorry` in
order to restore the source-faithful statement.  In this mode, statement
faithfulness is the first invariant: keeping a divergent proof intact merely to
avoid `sorry` preserves a theorem that the paper does not state.

Paper-realignment mode is narrow.  It applies only to edits whose purpose is to
remove wrong hypotheses, delete divergent fields, restore a paper theorem
statement, or replace a conditional theorem by a paper-facing statement plus a
named proof obligation.  Such a PR must:

1. cite the paper passage by label or line range in the relevant docstring;
2. cite the paper-gap note or tracking issue that records the divergence;
3. identify every introduced or retained `sorry` and the construction theorem,
   proof-obligation theorem, or source-faithful lemma expected to discharge it;
4. avoid unrelated refactors, notation changes, or proof-engineering churn.

During paper realignment, every restated definition, hypothesis field, or
paper-facing theorem must have a docstring that lets a reviewer tell whether
the statement is present in the paper or is a Lean-only proof obligation.  A
name such as `Bridge`, `Residual`, `Repair`, `Package`, `Input`, or `Producer`
is not by itself a mathematical source citation.

### Unfaithful dependency markers

A theorem or lemma is **unfaithful** when its proof relies on a hypothesis,
helper, bridge, residual, repair input, or conditional theorem that is known not
to follow from the cited paper statement.  This includes the case where the
public theorem statement is source-shaped but the proof calls a conditional
helper whose load-bearing hypothesis is not yet derived from the paper
hypotheses.

Such a declaration must carry a docstring section beginning with
`**Unfaithful:**`.  The marker must name the load-bearing deviation, cite the
paper-gap note or issue that documents it, and state the planned discharge.  A
minimal form is:

```text
**Unfaithful:** This proof currently relies on `<hypothesis or helper>`,
which is not derived from `<paper label or line range>`.  Documented in
`docs/paper-gaps/<note>.tex` or issue `#N`.  Elimination: prove
`<construction theorem>` from the paper hypotheses.
```

The marker propagates through dependencies: a theorem whose proof transitively
uses an unfaithful declaration is itself unfaithful until the dependency is
replaced by a source-faithful proof.  Remove the marker only when the cited
deviation has been discharged.

Not every discrepancy requires the full `**Unfaithful:**` marker.  If the paper
has a local typo, a documented numerical strengthening, or a genuine scope
restriction, use a lighter docstring marker such as `**Local fix:**` or
`**Scope restriction:**`, citing the relevant paper-gap note.  These lighter
markers are for mathematically correct local corrections; `**Unfaithful:**` is
reserved for load-bearing assumptions or proof steps still missing from the
paper hypotheses.

## Code Conventions

### Imports

- Keep imports at the top of the file
- One import per line
- Follow existing local import style
- Prefer the smallest correct import set, but do not churn imports unnecessarily
- Preserve re-export-file structure: `<LeanRoot>.lean` and each track's `<LeanRoot>/<Track>.lean`
- Before adding a new import, check whether the needed declaration already
  comes from an existing local re-export import

### File structure

Every `.lean` file must have:

1. imports
2. a module docstring starting with `/-!` (title, main definitions, references)
3. namespace / opens / variables
4. declarations

### Formatting

- **Line length**: max 100 characters
- **Spacing**: spaces around `:` and `:=`
- **`by` placement**: at end of the preceding line (`... := by`), never on its
  own line
- **Indentation**: 2 spaces for proof body; 4 spaces for continuation of
  theorem statement
- **Top-level commands**: flush-left
- Avoid orphaned parentheses. Prefer readable multiline formatting over dense
  tactic blocks.

### Naming conventions

Follow Mathlib naming plus project-local conventions:

- Theorems / proofs / proposition-valued terms: `snake_case`
- Structures / inductives / classes / Prop names / Type names: `UpperCamelCase`
- Functions / non-Prop terms: `lowerCamelCase`
- Use American English spelling in declaration names

Project-preferred variable names:

- `q` — alphabet size / finite field order
- `n`, `m` — dimensions
- `σ` — strategies
- `P` — projective measurements
- `G` — graphs (hypercube expansion)

For full details, see the lean-conventions `MATHLIB_naming` and `MATHLIB_style` references.

### Types and signatures

- Give explicit types for declaration arguments
- Give explicit return types for definitions
- Do not rely on auto-implicit variables (forbidden by `relaxedAutoImplicit`)
- Prefer existing project structures and Mathlib-compatible types over ad hoc
  wrappers
- Be skeptical of scaffolding that compiles but cannot support real proofs later

### Documentation

Required:

- **Module docstrings** for every file — `/-! # Title ... ## References ... -/`
- **Docstrings** on every `def`, `structure`, `class`, and significant `theorem`
- Mathematical prose in Lean docstrings and comments should follow
  `docs/mathematical_language.md`
- Cite blueprint nodes by their stable LaTeX label, for example blueprint
  `lem:cl-concat`. Do not store blueprint line numbers in Lean docstrings. When
  reviewing, derive the current span with
  `python3 scripts/blueprint_citations.py resolve lem:cl-concat`.
- Cite paper mirrors by a paper label when one exists, or by a repository path
  plus a narrow anchored passage when the source has no suitable label. Paper
  mirror line ranges are acceptable because those mirrors are immutable.

When formalizing a statement from the blueprint, add corresponding `\lean{...}`
and `\leanok` tags in the relevant `blueprint/src/chapter/*.tex` file.

## Proof Engineering

### Search before proving

- Prefer existing Mathlib lemmas
- Reuse local API from the library's own shared directories (`Basic/`, `Preliminaries/`, …)
- Use file-local helper lemmas only when they genuinely reduce duplication
- Scout Mathlib first: `exact?`, `apply?`, `#find?`, grep Mathlib source
- See `audits/` for chapter-by-chapter Mathlib dependency analysis

### Mathlib integration

The project depends heavily on Mathlib for finite-dimensional complex matrices,
Hermitian/PSD operators, and spectral theory. When proving lemmas:

- Reuse existing Mathlib lemmas rather than reproving
- Prefer Mathlib types over custom definitions
- Do not re-declare standard Mathlib lemmas (e.g., custom matrix transpose
  lemmas when `Matrix.transpose_*` exists)

For a pedagogical register of external lemmas not explained in the paper,
see `docs/external-lemmas-pedagogy.md`. This includes Schwartz–Zippel,
Fourier orthogonality, Cauchy–Schwarz for approximate measurements, CFC,
and external result statements (Polishchuk–Spielman, Raz–Safra).

For the policy on temporary conditional scaffolding and blueprint
synchronization, see `docs/formalization-patterns.md`.

### Validation ladder

1. `lake env lean path/to/File.lean`
2. `lake build`

Do not jump straight to full builds for every small edit.

### Lean-specific advice

- Prefer small, composable lemmas over giant fragile proofs
- Reuse `SubMeas`, `Measurement`, tensor-placement, PSD, and trace lemmas
  already in the repo
- Check `docs/api_surface.md` for useful obligation-closing lemmas
- If changing statements, confirm against paper and blueprint first
- Never add axioms or weaken statements without explicit justification

## Mathematical Documentation Style

Write repository prose for mathematicians and mathematical physicists. Prefer a
clear, precise, and unhurried expository style: introduce the object under
discussion, state the mathematical relation being used, distinguish hypotheses
from conclusions, and avoid informal process language when a standard
mathematical phrase is available.

When writing docstrings, audit notes, PR descriptions, or blueprint-adjacent
comments, use terminology from the standard mathematical literature, the paper
being formalized, and the local formalization. Do not invent slang or private shorthand for
mathematical objects. The goal is prose that a third-party reader can understand
without having read the agent conversation that produced the change.

### Paper-gap notes

For the proof-gap terminology used to distinguish source theorems, internal
proof obligations, and conditional helpers, follow
`docs/paper-gaps/proof-gap-protocol.tex`.  For documentation of discrepancies
between the cited paper, the blueprint, and Lean, follow
`docs/paper-gaps/policy.tex`. In particular, such notes should be
mathematical prose for mathematicians and mathematical physicists who have not
read the issue discussion: introduce notation, state the cited assertion,
isolate the calculation or logical obstruction, compare with the blueprint and
Lean statement, and give a clear verdict. If Lean uses a Mathlib result or
construction not present in the cited argument, explain that replacement
pedagogically before naming the formal declaration. If the cited assertion is
false and a counterexample is available, explain the counterexample in prose and
use any Lean declaration only as verification.

## Proof Integrity

### Blockers (must be resolved before merge)

See the lean-conventions `PROOF_INTEGRITY` reference and `docs/project_conventions.md` for the full catalog.

**Direct proof holes**: `sorry`, `admit`

**Kernel / type system bypasses**: `native_decide`, `unsafeCast`, `unsafeCoerce`,
`lcProof`, `ofReduceBool`, `ofReduceNat`

**Axiom smuggling**: unjustified `axiom` declarations

**Circular reasoning**: proofs that assume the statement being proved as a local
hypothesis, or helper lemmas that essentially restate the main goal.

**Castle-in-the-air (ungrounded proofs)**: custom re-declarations of standard
Mathlib lemmas; `axiom` or `sorry`-based helpers for facts already in Mathlib;
chains of custom lemmas that never bottom out in Mathlib or Lean core.

**Scaffolding that blocks real formalization**: definitions or theorem statements
that do not faithfully represent the actual mathematics, making them impossible
to connect to real Mathlib-based proofs. Ask: *Can a real proof be built on top
of this?*

### Warnings

Placeholder tactics (`exact?`, `apply?`, `library_search`) should be replaced
with concrete results. Debug artifacts (`dbg_trace`, `#check`, `#eval`,
`#print`) should be removed from proof files. See the lean-conventions `PROOF_INTEGRITY` reference for
the full warning catalog.

### Anti-patterns

Subtler proof-evasion patterns that pass kernel-level checks yet still fail to
prove the claimed mathematics are catalogued in `docs/anti_patterns.md`:
conclusion-shaped hypotheses, definitional sleight-of-hand, zero-fallback
branches, trivial default witnesses, Mathlib-bypass castles, and external
`*Statement` smuggles. Reviewers should consult this file alongside
the lean-conventions `PROOF_INTEGRITY` reference and `docs/project_conventions.md`.

## PR and Commit Conventions

PRs are GitHub pull requests (opened by `local/bin/pr_open.py`, merged by
`local/bin/pr_merge.py`); `#N` in PR bodies and commit messages is the GitHub
issue number. Titles, bodies, and commit rules below are unchanged from the
parent project.

### PR title format

```
type(scope): short description
```

| Type       | When to use                                      |
|------------|--------------------------------------------------|
| `feat`     | New definition, lemma, theorem, or module         |
| `fix`      | Bug fix (broken proof, wrong identifier, etc.)    |
| `refactor` | Restructuring without changing API surface        |
| `docs`     | Documentation or blueprint changes only           |
| `style`    | Formatting, naming, or docstring cleanup only     |
| `ci`       | CI/CD workflow changes                            |
| `chore`    | Dependency bumps, linting, toolchain updates      |

**Scope** is a shortened module path under the Lean root — a chapter directory,
or `blueprint`. Omit the Lean root prefix itself.

### PR body template

Every PR body must contain three sections:

```markdown
### Motivation
- Why this change is needed. Cite the issue and paper/blueprint location.

### Description
- State precisely what changed.

### Testing
- What was verified and how (e.g., `lake build`, `rg -n "sorry|axiom"`).

---
Addresses #N
```

Use `Addresses #N` (keeps the issue open) or `Closes #N` (auto-closes on merge).

### Commit messages

- **Imperative mood** in the subject line ("Add", not "Added")
- Subject under 72 characters
- When squash-merging, the commit message should match the PR title format

## Review Process

Every PR touching Lean code is reviewed by a dedicated local reviewer session
(`local/bin/review.sh`, dispatched after green local CI; a session never
reviews its own diff) against these criteria:

1. **Proof correctness** — No unexplained `sorry`. No `axiom` unless discussed.
2. **Mathlib style** — Follow the lean-conventions `MATHLIB_naming` and `MATHLIB_doc` references.
3. **Paper terminology** — Public Lean names and documentation should use
   terminology from the paper and blueprint. See `docs/mathematical_language.md`.
4. **Linter hygiene** — Fix warnings, don't mask them with broad
   `set_option linter.<name> false` blocks.
5. **Type safety** — No universe mismatches, coercion problems.
6. **Performance** — Avoid expensive tactics on large types.
7. **Modularity** — Are new lemmas general enough to be reused?
8. **Documentation** — Every new `def` and major `theorem` must have a docstring.
9. **Blueprint sync and paper origin** — Add `\lean{}` and `\leanok` tags for
   formalized statements only when the Lean statement matches the source.
   Record formalization-only auxiliary lemmas explicitly.
10. **Scaffolding integrity** — Verify scaffolding aligns with Mathlib.
11. **Statement drift** — Compare source-labelled theorem statements with the
   paper and flag new hypotheses, weakened conclusions, changed quantifier
   order, altered error parameters, or bridge/residual packages moving toward
   a paper theorem.
12. **Proof-evasion anti-patterns** — Review against `docs/anti_patterns.md`.

For full details, see `docs/CONTRIBUTING.md` and the lean-conventions `MATHLIB_pr-review` reference.

## Blueprint and Documentation Work

If modifying blueprint material:

- Keep chapter structure under `blueprint/src/chapter/`
- Ensure `leanblueprint web` succeeds
- Keep Lean declaration references valid
- Sync theorem labels with Lean names
- Add `\lean{LeanDeclName}` and `\leanok` tags for formalized statements

For blueprint style conventions, see `docs/blueprint_style_guide.md`.

For temporary conditional scaffolding and the `\lean{}`/`\leanok` tagging
strategy, see `docs/formalization-patterns.md`.

## Agent Rule Sources

Checked in this repository snapshot:

- No `.cursorrules`
- No `.cursor/rules/`
- No `.github/copilot-instructions.md`

### Skills

The `texra-lean-skills` plugin (texra-ai/texra-lean-skills) carries the
canonical Mathlib-style, proof-integrity, and prose convention texts as the
`lean-conventions` skill. Claude Code installs it automatically via
`.claude/settings.json`; other agents install it by cloning the
repository and symlinking the skill directories into their skill
location, as described in its README.
PaperLib-local addenda to those conventions live in
`docs/project_conventions.md`, which restates no shared rule.

Use this file together with:

| File | Purpose |
|------|---------|
| `CLAUDE.md` | Claude Code-specific notes (minimal pointer to this file) |
| `docs/CONTRIBUTING.md` | PR format, issue templates, label taxonomy, review checklist |
| `lean-conventions` skill | Mathlib style, naming, documentation, PR review, proof integrity, prose style (canonical; installed) |
| `docs/project_conventions.md` | PaperLib-local addenda to the shared conventions |
| `docs/anti_patterns.md` | Subtler proof-evasion patterns |
| `docs/proof_frontier_review.md` | Review checklist for construction theorems and residual inputs |
| `docs/mathematical_language.md` | Project-local terminology rules |
| `docs/blueprint_style_guide.md` | Blueprint notation and section conventions |
| `docs/api_surface.md` | Useful obligation-closing lemmas for `SubMeas` |
| `docs/paper-gaps/policy.tex` | Paper-gap documentation conventions |
| `docs/paper-gaps/proof-gap-protocol.tex` | Protocol distinguishing source theorems, proof obligations, and conditional helpers |
| `docs/formalization-patterns.md` | Conditional scaffolding, blueprint sync, split imports, and bridge records |
| `docs/external-lemmas-pedagogy.md` | Pedagogical notes on Mathlib and external lemmas |
| `docs/ci-automation.md` | GitHub-era CI/CD reference (inactive; see `local/`) |
| `docs/pr_review_management.md` | GitHub-era review-bot reference (lessons still apply; mechanism replaced by `local/protocols/review.md`) |
| `local/DESIGN.md` | Local operations architecture and invariants |
| `local/protocols/` | Normative protocols (meta, build cache, CI, review, auto-fix, issues/PRs, sessions) |
| `local/personas/` | System prompts for locally dispatched agent roles |
| `audits/` | Chapter-by-chapter scouting reports |
| Pinned memories (external agent tooling) | Agent session memory maintained by the agent runtime; not a directory in the repository checkout. Pinned memories contain accumulated project lessons |

## Local Operations

This repository runs its whole workflow locally. The short version every
agent must know:

- **Build reuse.** A hot main cache lives under `$MIPSTARRE_CACHE_ROOT`
  (`paths.cache_root` in `local/project.json`, exported by
  `local/bin/session/config.sh`);
  fresh worktrees get it via `local/bin/worktree-setup.sh` (which also
  installs git hooks and resets dirty vendored packages). Never run
  `lake update`; never write to the cache; at most one full `lake build`
  runs machine-wide (the scripts take the lock for you).
- **Lifecycle.** GitHub issue → branch `issue-<number>-slug` + worktree →
  agent sessions → `local/bin/ci.sh` → `local/bin/review.sh` → optional
  `local/bin/autofix.sh` → `local/bin/pr_merge.py`. CI and review evidence are
  exact-head commit statuses (`local-ci/*`, `local-review/summary`); merges go
  through GitHub with an exact-SHA guard. Details: `local/README.md`,
  `local/protocols/issues-prs.md`.
- **Sessions.** Worker sessions start only through `local/bin/dispatch.sh`
  (roles: orc, prover, reviewer, simplifier, blueprint, splitter, scout;
  `mathfix` is the source-statement repair lane under
  `local/protocols/issues-prs.md` section 6), so token and time telemetry stays
  complete. Which model and effort each role gets is `session.workers` in
  `local/project.json` plus the routing rules in `local/model-policy.json` — no
  model name belongs in this document. Lease-backed native descendants are
  retired; `local/protocols/sessions.md` retains their history.
- **Owner inbox.** The pinned owner-inbox issue (`issues.owner_inbox` in
  `local/project.json`) receives only permission blockers whose risk extends
  beyond project development; main decides and records questions whose only
  risk is failure to finish the project. Changing the stated project goal is
  outside main's authority and needs an owner decision there. Use one comment
  per blocker and at most ten visible plain-language lines: what is stuck,
  lettered options, one recommendation, and `DECISION B<n>: <letter>`; details
  are folded. Routine progress goes to the progress issue
  (`issues.progress`), never to the owner inbox.
- **Telemetry duty.** Incidents go to `results/telemetry/events.md`;
  protocol changes follow `local/protocols/meta.md` and are ledgered in
  `local/protocols/EVOLUTION.md`.
- **Fix commits**: `autofix.sh`'s automated commits are prefixed
  `[codex-auto-fix]` / `[codex-review-fix]` exactly (the review skip keys on
  them); operator and worker repairs use plain `fix(review): …` /
  `fix(ci): …` subjects so they are reviewed. Issue titles, slugs, and branch
  names stay bracket-free.

## Practical Defaults for Agents

When editing Lean code:

1. Read the paper source
2. Read the target Lean file and nearby supporting files
3. Type-check the single file
4. Scan for `sorry|axiom`
5. Run `lake build` only when the local change is stable

When editing blueprint files:

1. Read the matching paper source and chapter file
2. Update Lean links carefully
3. Run `leanblueprint web`

Prefer minimal, dependency-aware changes that preserve the project's theorem
structure.
