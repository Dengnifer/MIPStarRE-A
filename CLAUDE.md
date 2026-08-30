# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in
this repository.

**See `AGENTS.md` for all agent conventions, build commands, code style, and
proof-integrity rules.** This repository has a single, consolidated agent guide at
`AGENTS.md`. Read that first.

## Claude-specific notes

- When stuck, read the original paper source in `references/` (QPBT:
  `qpbt-paper/`, secondary `neexp-paper/`; LDT: `ldt-paper/`).
- Lean files in this repo often exceed Claude's context window; use `rg`/`grep` to
  locate definitions and search for lemmas in `.lake/packages/mathlib/`.
- Prefer `lake env lean MIPStarRE/Path/To/File.lean` for fast iteration; only run
  `lake build` before handing a worktree back for merge (the scripts serialize
  full builds machine-wide).
- The `AGENTS.md` and `CLAUDE.md` files are consumed by coding agents
  (Claude Code and codex CLI); keep this file minimal and keep `AGENTS.md`
  from growing beyond a session-start read (~700 lines today).

## Toolchain upgrade notes

- **Current**: Lean v4.32.0 / Mathlib v4.32.0 (from `lean-toolchain`
  and `lakefile.toml`)
- For future toolchain bumps: if any file-scope
  `set_option backward.isDefEq.respectTransparency false` usages are introduced
  during porting, replace them by local-scope alternatives before merge. This
  option should only be used temporarily; permanent fixes involve repairing
  instance or type-synonym definitions.
