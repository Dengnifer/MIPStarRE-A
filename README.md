# Formalization kit — point an agent session at a paper and walk away

This repository is a **kit for formalizing a mathematics paper in Lean 4**, not
a formalization. It holds the machinery: a bootstrap path from an arXiv URL to
a Lean skeleton and a blueprint, a local issue/pull-request/CI/review/merge
workflow, a session layer that starts and supervises an autonomous main session
with detached workers, a model-free completion gate, and the protocols the
whole thing follows — including the rule by which those protocols change.

You clone it, open an agent session in the folder, and say which paper.

---

## Quickstart

```bash
git clone --depth 1 --branch <tag> <this-repository> my-paper
cd my-paper
```

Open a Claude Code (or codex) session at the repository root and say:

> formalize https://arxiv.org/abs/XXXX.XXXXX

The session reads `CLAUDE.md`, becomes the **meta session**
(`local/personas/meta.md` → `local/protocols/meta-session.md`), runs the
machine preflight, asks you the three questions below, instantiates the project
under the name you choose, and then follows `local/protocols/bootstrap.md`:
fetch and split the paper → statement inventory → blueprint → Lean skeleton →
proofs → completion gate → independent comparator check.

After that it contacts you only when something is genuinely yours to decide,
and when the project is finished.

## Prerequisites

The kit asserts these; it never installs them for you. `python3
scripts/preflight.py` checks each one separately, by exercising it.

| What | Why |
|---|---|
| `elan` + `lake` | Lean 4 and the pinned dependency set (`lean-toolchain`, `lake-manifest.json`) |
| `python3` (3.10+) | every tool in `scripts/` and `local/bin/` — standard library only, no third-party packages |
| `git` | fresh history, hooks, worktrees |
| `gh` **and** an authenticated GitHub API credential | issues, pull requests, statuses, merges. A working git transport is a *separate* prerequisite from an authenticated API |
| `tmux` | the main session runs in a pane the supervisor can read |
| a coding-agent CLI on `PATH` | the main session and the workers |
| LaTeX + `leanblueprint` | the blueprint's PDF and web output |
| disk and RAM | a Mathlib-scale build; budget tens of gigabytes and several hours for the first one |

A many-core machine is not required but changes the wall-clock story
completely; the workflow is written for one machine with a shared, warm build
cache.

## What the meta session will ask you

Once, at the start, in one message — and, after that, only for things outside
the project:

1. **The library name and the GitHub repository** to use.
2. **Which keys or logins it may use, and the limit on each.** A key is a
   *name* in `local/project.json` mapped to a directory that already holds the
   login. No credential ever enters this repository, a log or a message.
3. **Permission to create the two GitHub repositories** (the project and its
   comparator challenge) and to push to them.

Everything else — the chapter plan, the Lean architecture, which packet is
next, the review policy, the merge contract, the model mix within the keys you
allowed — it decides itself, records, and tells you in one line. The rule it
follows is in `local/protocols/meta-session.md` §12: ask only when the risk
goes beyond the project's development.

## What runs where

| Layer | Where it lives | What it does |
|---|---|---|
| meta session | your terminal | supervises; talks to you; never proves |
| main session | a `tmux` pane on the work machine | the operator: briefs, dispatches, gates, records |
| workers | detached processes, own worktrees | the mathematics |
| session layer | `local/bin/session/` | launch, message, goal keeper, key watch, pause, stand-down, status |
| service layer | `local/bin/service/` | merge daemon, lanes, review gate, trains, records — all model-free |
| project workflow | `local/bin/`, `scripts/`, `.githooks/` | issues, pull requests, CI, review, audits, completion gate |
| project identity | `local/project.json` | names, paths, issues, caps, keys — read by everything |
| runtime state | `$KIT_STATE_DIR` (outside the repository) | goal text, markers, claims, logs, the running handoff file |

CI, reviews and merges **execute locally**; GitHub holds the record. The
`.github/` tree is kept as frozen reference for the mechanisms the local
scripts replace, and is not executed here.

## How the rules evolve

The protocols under `local/protocols/` are normative until amended. An agent
that finds one wrong does not deviate: it records the friction in
`results/telemetry/events.md`, and an amendment is made with a cited trigger
and an entry in `local/protocols/EVOLUTION.md`. No trigger, no amendment. That
is `local/protocols/meta.md`, and it is what makes the kit improve instead of
drifting.

## Honest status

- The workflow this kit is made of was **proven on exactly one project**: a
  Lean formalization of a research paper, taken from an empty repository to
  zero `sorry` with an independent comparator check, over about three weeks,
  by a supervised autonomous session with detached workers.
- The **bootstrap path itself is new**, and it was deliberately tested lightly.
  What was exercised: the unit tests under `scripts/tests/` (about 1,140, all
  offline); the live fetch and the byte-exact split on one real arXiv e-print
  (a 200-page paper, 16 section files); and, on a scratch copy, the whole
  instantiation path — rename, fresh git history, first commit with the hooks
  installed, a second commit passing the pre-commit hook.
- What was **not** exercised: the session layer and the service layer have
  only ever run against stand-ins (a stub `tmux`, a stub agent CLI, a stub
  `gh`). No live main session has been started from this tree, no pull request
  has gone through its merge service, and nobody has followed the playbook
  from an arXiv URL to a finished project a second time. Expect to fix small
  things in the first hours; record each one in `results/telemetry/events.md`
  and amend the protocol that misled you (`local/protocols/meta.md`). The first
  project built from this kit is the experiment.
- Nothing here removes the need for a human who understands the mathematics.
  The kit's own protocols say where a source paper is wrong, not whether the
  formalization is worth having.

### Relation to `LionSR/oh-my-formalization`

`oh-my-formalization` is a **starter template**: a Lean package, a blueprint, a
paper-gap mechanism and CI, with a human in the loop deciding each step. This
kit is the **autonomy layer** on the same blueprint and paper-gap lineage
(`texra-blueprint`): a supervising meta session, a main session with detached
workers, merge and review gates, a completion gate, a comparator challenge, and
protocols that amend themselves.

## Provenance

The commit of the project this kit was extracted from is recorded in
[`local/kit/ORIGIN_COMMIT`](local/kit/ORIGIN_COMMIT), and the script that
performed the extraction is `local/kit/extract.sh`. The origin project's own
protocol-amendment ledger is kept under `docs/origin/` as **evidence, not
law**: nothing there is normative for a project built from this kit, and no
rule may be cited from it.

## Where to read next

| Document | What it covers |
|---|---|
| [`local/protocols/meta-session.md`](local/protocols/meta-session.md) | the supervising session's playbook |
| [`local/protocols/bootstrap.md`](local/protocols/bootstrap.md) | the stage plan, with entry and exit criteria |
| [`local/protocols/main-cycle.md`](local/protocols/main-cycle.md) | the main session's standing cycle |
| [`local/protocols/completion.md`](local/protocols/completion.md) | the definition of done |
| [`local/README.md`](local/README.md) | the operator's tour of the workflow |
| [`local/DESIGN.md`](local/DESIGN.md) | why the workflow is shaped the way it is |
| [`AGENTS.md`](AGENTS.md) | the conventions every agent in the repository follows |

## Licence

See [`LICENSE`](LICENSE). A project instantiated from this kit chooses its own
licence for the mathematics it produces.
