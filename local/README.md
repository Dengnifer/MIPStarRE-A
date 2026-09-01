# Local operations — operator guide

This directory is the operative workflow of the repository: the local
replacement for the parent project's GitHub Actions layer. Architecture and
invariants: [`DESIGN.md`](DESIGN.md). Protocol changes: follow
[`protocols/meta.md`](protocols/meta.md).

## The lifecycle at a glance

```
issue  →  branch + worktree  →  agent session(s)  →  local CI  →  review
  →  (auto-fix loop)  →  merge gate  →  main  →  cache warmer refresh
```

1. **File an issue**: `local/bin/issue_new.py --title "..." --label ...` opens
   a GitHub issue and prints its number; `--parent N` attaches it as a native
   sub-issue. The brief for it goes in `local/briefs/`.
2. **Open a PR**: create branch `issue-<number>-slug`, worktree under
   `.worktrees/`, run `local/bin/worktree-setup.sh` there, then
   `local/bin/pr_open.py --branch issue-<number>-slug --title "..." --issue N`,
   which pushes the branch and opens the GitHub PR.
3. **Dispatch agents**: only via `local/bin/dispatch.sh --role prover
   --issue NNNN --worktree .worktrees/<name> -- "task"`. Session telemetry
   lands in `results/telemetry/`.
4. **CI**: `local/bin/ci.sh PPPP` (build via hot cache + audits + blueprint
   checks) → per-step `local-ci/*` statuses and the manifest PR comment.
5. **Review**: `local/bin/review.sh PPPP` — runs only after green CI; publishes
   one exact-head COMMENT review plus the `local-review/summary` status.
6. **Auto-fix** (optional, the repository's auto-fix label on the PR):
   `local/bin/autofix.sh PPPP --mode auto`, capped, serialized.
7. **Merge**: `local/bin/pr_merge.py PPPP` — the gate; refuses on red CI,
   missing review, or unresolved findings, and merges via GitHub with the
   exact-SHA guard. Then pokes the cache warmer.
8. **Housekeeping / site**: `local/bin/housekeeping.sh all`,
   `local/bin/site.sh all`.

## Ground rules for agents

- Read `AGENTS.md` first; the faithfulness policy and proof-integrity
  blockers are unchanged from the parent project.
- Never run `lake update`. Never write to the hot cache. Full `lake build`
  goes through the machine-wide lock (`warm-worktree.sh`/`ci.sh` handle it).
- One session never reviews its own diff.
- Sessions are dispatched, resumed, and archived only via `dispatch.sh`.
- Invoke workflow tools through the primary checkout's path
  (`/…/MIPStarRE-dev/local/bin/…`), never through a worktree's copy — a
  branch's copy can predate protocol fixes (EVOLUTION.md, 2026-08-30).
- Friction with any protocol → log it in `results/telemetry/events.md`;
  propose amendments per `protocols/meta.md`.
