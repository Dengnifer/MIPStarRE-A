# Bootstrap protocol — from an arXiv URL to a running project

Normative. This is the stage plan the meta session follows after the first hour
of [`meta-session.md`](meta-session.md) §3. Each stage has **entry criteria**,
**who does it**, the **exact commands**, **exit criteria** (checked
mechanically wherever a command can check them), the **telemetry rows** to
write, and the **preconditions** — the pitfalls a first run walks into, stated
as things to have arranged *before* the stage starts.

Nothing in this file names a paper, a library, a repository or a machine.
Everything comes from [`local/project.json`](../project.json) and the `KIT_*`
variables exported by `local/bin/session/config.sh`.

**Stage names** used in `results/telemetry/stages.jsonl` (the schema is in
[`meta.md`](meta.md), which allows extending the list):

`0-preflight` · `1-references` · `2-inventory` · `3-blueprint` ·
`4.1-minimal-skeleton` · `4.2-full-skeleton` · `4.3-proofs` · `4.4-completion`

Every stage writes at least two rows:

```json
{"ts":"<ISO-8601 with offset>","stage":"<stage>","event":"start","note":"<what and why, one line>"}
{"ts":"<ISO-8601 with offset>","stage":"<stage>","event":"end","note":"<what exists now, with the numbers>"}
```

plus a `milestone` row whenever something worth citing later happens (a fleet
finishing, a first green build, a merged PR). Write them **when the thing
happens**; a stage ledger reconstructed afterwards is not research data.

---

## Stage 0 — preflight and instantiate

**Entry.** A fresh clone of the kit, an arXiv URL, and a human who asked for
the paper to be formalized.

**Who.** The meta session, alone. No model work, no workers.

**Preconditions (what has to be true before, not discovered during)**

- The machine's prerequisites are three separate things and each must be
  *exercised*, not asked: a binary on `PATH`, an authenticated API credential,
  and git transport. A credential diagnostic can lie; a real call cannot.
- The build toolchain is **asserted, never installed** by piping a URL into a
  shell. If it is absent, that is an owner request.
- The runtime cache root must be writable **and** reachable from whatever
  sandbox the sessions run under. A repository that is writable does not imply
  a writable lock directory.
- The dependency manifest is pinned. Never run the package manager's `update`.

**Commands**

```bash
python3 scripts/preflight.py                       # add --no-probe to skip the key probe
python3 scripts/bootstrap_project.py --lean-root <Name> --github-slug <owner>/<repo> \
        --arxiv <id-or-url> --title "<paper title>" [--track <track>] --dry-run
python3 scripts/bootstrap_project.py --lean-root <Name> --github-slug <owner>/<repo> \
        --arxiv <id-or-url> --title "<paper title>" [--track <track>]
scripts/install_git_hooks.sh --install
scripts/install_git_hooks.sh --check
. local/bin/session/config.sh && env | grep '^KIT_'
bash local/bin/service/keyrot-install.sh --dry-run   # read the plan first
bash local/bin/service/keyrot-install.sh             # worker routing on this machine
```

`bootstrap_project.py` also takes `--key <short>` (the paper-mirror key, so the
mirror is `references/<key>-paper/`; the default is the Lean root in lower
case), `--comparator-slug`, `--cache-root`, `--tmux`, `--keep-git` and
`--force`; `--help` is the full list.

`keyrot-install.sh` copies the rotation shim to `<cache_root>/owner-bin/codex`
and creates one rotation home per key in `local/project.json`. Put
`<cache_root>/owner-bin` **first** on `PATH` afterwards, so `codex` means the
shim; the service scripts do that for themselves, an interactive shell does
not. It never reads or prints a key: a key whose `codex_home` does not exist is
reported and skipped.

**Exit criteria**

- `preflight.py` exits 0.
- `install_git_hooks.sh --check` exits 0.
- `command -v codex` resolves inside `<cache_root>/owner-bin`, and
  `keyrot-install.sh` reported a rotation home for every key.
- `python3 scripts/project_config.py get project.lean_root` prints the chosen
  Lean root, and the placeholder root no longer appears outside `docs/origin/`.
- `git log --oneline | wc -l` is 1: the project starts with fresh history.
- `python3 -m unittest discover -s scripts/tests -p 'test_*.py'` runs clean on
  the instantiated tree.

**Telemetry.** `0-preflight` start/end; the end note records the machine (cores,
RAM), the toolchain version and which prerequisites had to be installed by the
owner.

---

## Stage 1 — fetch and split the paper

**Entry.** Stage 0 exit criteria hold. `project.arxiv` lists at least one id.

**Who.** The meta session runs the fetcher; the **splitter** persona
(`../personas/splitter.md`) checks the result when the source does not split
cleanly.

**Preconditions**

- arXiv sources are frequently **CRLF**. Text-mode I/O silently normalizes line
  endings, which once let a verifier report byte-identity for two files that
  differed on every line. The splitter reads **bytes**, normalizes
  deliberately, verifies byte-identity modulo exactly that normalization, and
  deletes its output when the check fails.
- arXiv packages commonly ship a precompiled bibliography and **no** BibTeX
  source. That is valid, not a defect; keep it and rename it so a later
  bibliography run cannot clobber it.
- The whitespace check in the pre-commit hook must not apply to the mirror:
  byte-faithful third-party text is not ours to reformat.
- Only `.tex .bib .bbl .sty .cls` are kept. Figures are dropped.

**Commands**

```bash
python3 scripts/fetch_arxiv_source.py <arxiv-id-or-url> \
        --dest references/<key>-paper --title "<paper title>"
python3 scripts/split_reference_paper.py \
        references/<key>-paper/arxiv-source/<main>.tex references/<key>-paper \
        --arxiv <arxiv-id> --title "<paper title>"
```

The fetcher prints the exact `split_reference_paper.py` line for the main file
it found; copy that rather than guessing which `.tex` is the main one. It takes
`--from-archive <file>` to unpack a local e-print instead of downloading,
`--licence` when the abstract page cannot be read, and `--force` to replace an
existing mirror.

Repeat for each secondary source in `project.arxiv`.

**Exit criteria**

- `references/<key>-paper/` holds `NN_<slug>.tex` files plus a `README.md`
  manifest with the arXiv id, the split date, the tool and the exact source
  line range of every file, beside the untouched `arxiv-source/` download.
- `references/<key>-paper/SOURCE.md` records the URL, the date, the sha256, why
  the mirror exists, and that copyright remains with the paper's authors.
- The splitter's verification passed (it exits non-zero and removes its output
  otherwise). Do not pass `--no-verify` on a real run.
- `paper_mirrors` in `local/project.json` names every mirror, so the audits
  that cite the paper stop enumerating directory names.

**Telemetry.** `1-references` start/end; the end note gives file counts per
mirror and states that byte-identity was verified modulo line-ending
normalization.

---

## Stage 2 — statement inventory

**Entry.** Stage 1 exit criteria hold.

**Who.** A fan-out of **inventory** workers
(`../personas/inventory.md`), one per section or per small group of sections,
dispatched detached. The main session, if one is already running, dispatches
them; otherwise the meta does, under a bounded takeover (`meta-session.md` §11).

**Preconditions**

- **Pass large fan-in data by file path.** A synthesis prompt that embedded the
  merged output of seven readers stalled and made no progress. Readers write
  files; the synthesizer is given paths.
- **Worker output is file-based**, not "the final message". A worker that dies
  mid-response must leave its partial work behind.
- **Per-model budget.** Parallel plans need a budget column: a whole fan-out
  once failed at dispatch on one account limit.
- Every run of the fleet needs an adversarial cross-cutting verifier at the
  end. Per-worker self-checks all passed while four cross-worker contract
  breaks survived.

**Commands**

```bash
bash local/bin/dispatch.sh --role splitter --persona local/personas/inventory.md \
     --issue <N> --worktree .worktrees/<name> \
     -- "Inventory sections <a>-<b>; write <outfile>"
```

`dispatch.sh --help` lists the roles it accepts; `inventory` is not one of
them, so the reading fleet runs as `splitter` — the paper-handling role, whose
default sandbox is `workspace-write`, which these workers need because each one
writes its own inventory file — with the inventory persona passed explicitly. A
repository-relative `--persona` is read from the trusted ref, not from the
worktree.

**Exit criteria**

- One inventory file per section under `audits/`, each row carrying: the
  statement's label and kind, its exact source locator (`references/<mirror>/<file>.tex:<lines>`),
  a one-sentence restatement, what it depends on, and whether the printed proof
  establishes the printed claim.
- A single merged inventory, produced by a verifier that read the files rather
  than their contents inline, listing: the headline results, the dependency
  edges between statements, the statements that will need definitions not in
  the library, and every place where the source looks wrong.
- The count of statements and the count of suspected source defects are both
  written down. Expect the second number to be non-zero.

**Telemetry.** `2-inventory` start/end plus one `milestone` per fleet with its
wall time and token note.

---

## Stage 3 — blueprint

**Entry.** Stage 2 exit criteria hold.

**Who.** The **blueprint** persona (`../personas/blueprint.md`), one worker per
chapter, plus an independent audit pass. Reviewed through the normal PR
lifecycle — this is also the project's first dogfooding of issue → PR → CI →
review → merge.

**Preconditions**

- **Expect the first blueprint PR to discover that the paper is wrong
  somewhere.** Have the paper-gap mechanism ready before the PR opens:
  `docs/paper-gaps/` holds the protocol, the policy and the note template; a
  genuine source defect becomes a dated note, never a silently conditioned
  statement.
- **Review loops do not converge on their own.** Finding counts across rounds
  on the origin's first blueprint PR went 33 → 26 → 18 → 12 → 17 → 15. A fresh
  reviewer each round has no memory of prior adjudications and unbounded depth
  on new prose. The round cap and operator adjudication in
  [`review.md`](review.md) are not optional; a bootstrap without them hangs on
  its first PR.
- The dependency graph is designed **backward from the headline theorem**.
- Prose contains no Lean identifiers; cross-references go by label, never by
  number.

**Chapter plan.** Write it first, as data, from
[`../templates/chapter-plan.example.json`](../templates/chapter-plan.example.json):
a `tracker` object, one `chapters` entry per blueprint chapter and one
`packets` entry per unit of work, each with a plan-local `id`, a title, a body
(inline or `body_file`), its labels and its `blocked_by` prerequisites. It is
the input to stage 4.2's tracker tree, so it is worth getting right before any
prose is written.

**Node conventions that must survive into every chapter**

| Marker | Meaning |
|---|---|
| `\lean{Namespace.decl}` | the Lean declaration this node corresponds to |
| `\leanok` | this node is formalized and its Lean side is proved |
| `\uses{...}` | the nodes this node's statement or proof depends on |
| `\proves{label}` | this proof environment proves that statement |
| `\notready` | the node's Lean side does not exist yet |

A node without `\lean{}` is prose. A node with `\leanok` and a `sorry` beneath
it is a false claim and the blueprint/axiom check exists to catch it.

**Faithfulness rule.** A blueprint node that claims to be a paper statement
must state the paper's statement — hypotheses as well as conclusion. A node
whose conclusion has the right shape but whose hypotheses carry an extra
load-bearing input is a *conditional* statement and must say so. Where the
source is wrong, the node states the **corrected** statement and cites its gap
note; the printed form stays visible in the note, not silently replaced.

**Commands**

```bash
leanblueprint web            # render; also writes blueprint/lean_decls
leanblueprint pdf
python3 scripts/check_blueprint_latex.py --root blueprint/src
python3 scripts/blueprint_lean_sync.py --root . --ci    # the sync check CI runs
bash local/bin/ci.sh <pr-number>
bash local/bin/review.sh <pr-number>
```

**Exit criteria**

- `leanblueprint web` and `leanblueprint pdf` both build clean.
- Every chapter of the plan exists; every node carries either `\lean{}` or an
  explicit reason to be prose; every `\uses{}` resolves.
- Every suspected source defect from stage 2 is either resolved (the statement
  was fine) or has a dated note under `docs/paper-gaps/` and a corrected node.
- The blueprint PR is merged through the normal gate — green CI at the exact
  head, an independent review, findings resolved or adjudicated.

**Telemetry.** `3-blueprint` start/end, one `milestone` for the chapter draft
and one for the merge, with node counts, gap-note count and the number of
review rounds.

---

## Stage 4.1 — minimal Lean skeleton

**Entry.** Stage 3 exit criteria hold. A headline theorem node exists with its
`\uses{}` closure.

**Who.** One orchestrating worker dispatched for this single job, with prover
workers under it.

**Preconditions**

- **Scaffolding overbuild is the most expensive failure this project knows.**
  A bounded six-script adaptation once ran 17 hours and 21 commits for +14.6k
  lines with zero mathematical progress. The forcing functions are mechanical:
  the per-commit line budget on the workflow layer, hooks under a minute, no
  new abstraction layers, and "after a workflow change merges, the next
  dispatched item MUST be mathematics". Check the budget hook is installed
  before this stage starts.
- **Verification must compare at the representation level of the claim.** A
  check that cannot fail is worse than no check, because the next session
  trusts it.
- **Never point the build system at a live worktree.** The package store is
  shared and content-addressed; a dependency aimed at a working tree corrupts
  it for every other checkout.

**Target.** The headline theorem's *statement* plus the transitive closure of
the definitions it needs, everything else `sorry`. No proofs.

**Commands**

```bash
bash local/bin/worktree-setup.sh .worktrees/<branch>
bash local/bin/dispatch.sh --role orc --issue <N> --worktree .worktrees/<branch> \
     -- "Minimal skeleton: state <headline node> and the transitive closure of its definitions; every proof position is sorry; lake build must be green"
lake build
lake exe checkdecls blueprint/lean_decls
```

**Exit criteria**

- `lake build` is green.
- The headline declaration exists with the statement the blueprint node names,
  and `lake exe checkdecls blueprint/lean_decls` resolves every `\lean{}` in
  the closure.
- Every hole is a `sorry` in **proof** position; there is no project `axiom`,
  no `native_decide`, no `unsafe`, no conditional bridge hypothesis smuggled
  into a statement.
- The count of `sorry` sites is recorded; it is the project's starting debt.

**Telemetry.** `4.1-minimal-skeleton` start/end with the file count,
declaration count, closure size, `sorry`-site count and build wall time.

---

## Stage 4.2 — full skeleton, tracker tree, cache, first CI

**Entry.** Stage 4.1 exit criteria hold.

**Who.** One worker per chapter writes a **brief**
([`../templates/skeleton-brief.md`](../templates/skeleton-brief.md)); the main
session adjudicates each brief into a binding issue contract **before** any
implementation starts; then one lane per packet.

**Preconditions**

- A brief is adjudicated into an issue contract *before* implementation. The
  origin's expensive rework came from implementing an unadjudicated brief.
- **The commit message is not the record.** The issue and PR bodies are.
- **Archive research evidence before rewriting its consumers**: move first, in
  its own commit, then change what reads it.
- **Warm before you adopt.** After any toolchain or dependency change, warm the
  cache first and only then point worktrees at it; a stale warm cache turns a
  planned zero-cost seed into a multi-hour rebuild.
- **Every restore mechanism needs an answer for the empty store.** A cold path
  that silently recomputes for hours is a bug even though it terminates.
- **Always invoke workflow tools through the primary checkout's path**, never
  through a worktree's copy: a branch's copy can predate a protocol fix.

### 4.2a Skeleton with `sorry` stubs and blueprint links

Each chapter's Lean subtree is filled in with the **statements** of its nodes,
every proof `sorry`, and each declaration carrying a docstring that names its
blueprint label and the exact source locator it formalizes. Each blueprint node
gains its `\lean{}` link and keeps `\notready` until the Lean side exists.

```bash
lake build
lake exe checkdecls blueprint/lean_decls
python3 scripts/blueprint_leanok_axioms.py --ci
```

### 4.2b Tracker and packet tree

```bash
python3 local/bin/tracker_tree.py local/chapter-plan.json --dry-run
python3 local/bin/tracker_tree.py local/chapter-plan.json
python3 local/bin/ready_packets.py --root "$KIT_TRACKER_ROOT"
```

The plan file is positional. Its shape is
[`../templates/chapter-plan.example.json`](../templates/chapter-plan.example.json)
and the docstring of `local/bin/tracker_tree.py`; a run writes the created
issue numbers back into the plan, so an interrupted run adopts instead of
duplicating.

The tree is the record: a tracking issue per chapter, a packet issue per unit
of work as a native sub-issue, and one dependency edge per prerequisite. A
packet is **ready** when it is an open leaf whose every blocking issue is
closed. Dependency bullets inside an issue body are commentary, never the
record. Write the tracker root into `issues.tracker_root` in
`local/project.json`.

### 4.2c Cache warm-up

```bash
bash local/bin/cache-warmer.sh --ref main
bash local/bin/cache-warmer.sh --status
bash local/bin/worktree-setup.sh .worktrees/<branch>
bash local/bin/warm-worktree.sh .worktrees/<branch> --status
```

One writer warms the cache; consumers get copy-on-write clones and never write
back; at most one full build runs machine-wide at a time.

### 4.2d First CI run

```bash
bash local/bin/ci.sh <pr-number>
```

**Exit criteria for stage 4.2**

- `lake build` green with the full skeleton in place.
- Every chapter has a tracking issue; every packet is a leaf with its
  dependency edges; `ready_packets.py` prints a non-empty list.
- `cache-warmer.sh --status` reports a warm cache, and a fresh worktree builds
  from it in minutes rather than hours.
- One full `ci.sh` run has passed on a real PR, publishing one status per step
  bound to the exact head plus a manifest comment.
- `issues.progress`, `issues.owner_inbox` and `issues.tracker_root` are set in
  `local/project.json`.

**Telemetry.** `4.2-full-skeleton` start/end, a `milestone` per adjudicated
brief and per opened tracker, and the first `builds.jsonl` rows.

---

## Stage 4.3 — proofs

**Entry.** Stage 4.2 exit criteria hold, and a main session is running.

**Who.** The main session, continuously, under
[`main-cycle.md`](main-cycle.md). The meta session supervises under
[`meta-session.md`](meta-session.md) §4 and does not intervene in packet
selection.

This stage has no separate command list: the turn in `main-cycle.md` §2 *is*
the procedure. It is by far the longest stage.

**Exit criteria**

- Zero `sorry`, `admit`, project `axiom`, `native_decide` or compiler-trust
  escape under the track's Lean root.
- Every blueprint node is `\leanok` or listed in the exemption table with a
  written reason.
- Every paper-gap note has a terminal status.

**Telemetry.** `4.3-proofs` start, `milestone` rows at stage boundaries with
the snapshot numbers, `4.3-proofs` end when the exit criteria hold.

---

## Stage 4.4 — completion, comparator, artifact

**Entry.** Stage 4.3 exit criteria hold.

**Who.** The main session; the meta session for the one owner permission this
stage needs.

**Preconditions**

- The headline table and the challenge generator's targets must agree **by
  construction**. In the origin project they did not, and the comparator
  criterion failed for that reason alone.
- Every module contributing to the statement closure must see the full library
  import, so that a library-only challenge file elaborates to bit-identical
  terms; and no closure declaration may be `private`, because a private name is
  qualified by its defining module and cannot be re-declared elsewhere.
- **Creating the challenge repository is an owner permission** (it is a second
  repository, outside this one). Ask once, in two lines.
- The artifact script is fail-closed on its leak scan. A snapshot is not cut
  until the scan passes; a PDF that cannot be read stops the run rather than
  shipping unexamined.

**Commands**

```bash
python3 scripts/completion_gate.py check --track "$KIT_TRACK"
python3 scripts/comparator/check_challenge_drift.py --root . --update
scripts/make_artifact.sh <tag> <outdir>
scripts/make_artifact.sh --anonymize <tag> <outdir>      # only if the venue is double-blind
```

**Exit criteria — the definition of done**

1. `scripts/completion_gate.py check --track <track>` exits 0 on the **exact**
   commit being declared, and its output is attached to the completion comment.
   See [`completion.md`](completion.md) for what each criterion means.
2. The official comparator accepts the challenge for **every** headline theorem
   of the track, in the separate challenge repository, with the library pinned
   by commit.
3. `docs/comparator.md` records the accepted run: the challenge repository, the
   pinned commit, the date, and which theorems were accepted.
4. The artifact files exist and are truthful, and `make_artifact.sh` produces a
   snapshot whose leak scan passes.

No completion statement, no issue closure and no release tag before all four.
A failing gate is the main session's to-do list, not an owner blocker.

**Telemetry.** `4.4-completion` start/end; the end note names the commit, the
gate result and the comparator run.

**Then**: the meta session writes the closing report
([`../templates/owner-report.md`](../templates/owner-report.md)) and retires.

---

## The pitfalls, as one list

Keep this list beside you during a bootstrap; every line is something that
already happened once.

| # | Pitfall | Where it bites |
|---|---|---|
| 1 | A seed or clone that looks clean but is months stale | stage 0 |
| 2 | A warm cache invalidated by a toolchain bump — a planned free seed becomes a multi-hour rebuild | stages 0, 4.2 |
| 3 | A restore mechanism with no empty-store case | stage 4.2 |
| 4 | Silent line-ending normalization defeating a byte-identity verifier | stage 1 |
| 5 | Scaffolding overbuild: unbounded infrastructure work with no product forcing function | stages 4.1, 4.2 |
| 6 | An oversized fan-in prompt that stalls the synthesizer | stage 2 |
| 7 | Byte-capped truncation cutting a multibyte character and breaking every dispatch | stage 2 onward |
| 8 | A parallel plan with no per-model budget column | stage 2 |
| 9 | Multi-worker drafts that pass every self-test and break four cross-worker contracts | stages 1–2 |
| 10 | Review loops that do not converge without a round cap and adjudication | stage 3 onward |
| 11 | A source obstruction handled as a silent statement condition instead of a gap note | stage 3 |
| 12 | Binary discovery, API authentication and git transport treated as one prerequisite | stage 0 |
| 13 | A sandbox that admits repository writes but not the shared runtime lock root | stage 0 |
| 14 | Workflow tools invoked from a worktree's stale copy | stage 4.2 onward |
| 15 | Disk exhausted by many copies of the dependency store | stage 4.2 onward |
| 16 | `lake update`, or a dependency pointed at a live worktree | every stage |
| 17 | The commit message treated as the record | stage 4.2 onward |
| 18 | Consumers rewritten before the evidence they read was archived | stage 4.2 |
| 19 | A headline table and a challenge generator that disagree | stage 4.4 |
