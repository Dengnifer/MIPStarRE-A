# CLAUDE.md

Guidance for Claude Code (claude.ai/code) working in this repository.

## Which file to read first

**If a human opened this session at the repository root and asked you to
formalize a paper, or to act as the meta session**, you are the **meta
session**. Read, in order:

1. [`local/personas/meta.md`](local/personas/meta.md) — who you are, and who
   you are not;
2. [`local/protocols/meta-session.md`](local/protocols/meta-session.md) — your
   playbook: the first hour, supervision, keys, pause, stand-down, the rule for
   contacting the owner.

Then act. Do not start reading the mathematics; you supervise, you do not
prove.

**Every other agent** — provers, reviewers, blueprint writers, scouts,
inventory readers, the main session — reads
[`AGENTS.md`](AGENTS.md) first. It is the single source of truth for agent
conventions, build commands, code style and the proof-integrity rules. Your own
persona under `local/personas/` says what else to read.

If you are unsure which you are: a session that was dispatched with a role and
a task is a worker; a session a human is talking to at the repository root is
the meta session.

## Claude-specific notes

- Lean files in this repository often exceed a context window; use `rg`/`grep`
  to locate definitions, and search the vendored dependencies under
  `.lake/packages/` rather than reading whole modules.
- When stuck on a statement or a proof, read the paper source under
  `references/` — the per-section mirror of the paper this project formalizes.
  The answer is almost always in the source; guessing tactics without the
  paper's argument is how sessions burn hours.
- Prefer `lake env lean <LeanRoot>/Path/To/File.lean` for fast iteration; run a
  full `lake build` only before handing a worktree back for merge (the scripts
  serialize full builds machine-wide).
- `AGENTS.md` and this file are consumed by coding agents (Claude Code and the
  codex CLI). Keep this file minimal, and keep `AGENTS.md` short enough to be a
  session-start read.

## Toolchain notes

- The pinned Lean and Mathlib versions are in `lean-toolchain` and
  `lakefile.toml`; those two files are the answer, not a version written into
  prose here. Never run `lake update`.
- On a toolchain bump: if any file-scope
  `set_option backward.isDefEq.respectTransparency false` is introduced while
  porting, replace it by a local-scope alternative before merge. That option is
  a temporary crutch; the permanent fix is repairing the instance or
  type-synonym definition that needed it.
