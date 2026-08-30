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

1. **File an issue**: `local/bin/issue_new.py --title "..." --template formalization`
   → `issues/NNNN-slug.md`. Tracking issues use `--template tracking` and
   `--parent`.
2. **Open a PR**: create branch `issue-NNNN-slug`, worktree under
   `.worktrees/`, run `local/bin/worktree-setup.sh` there, then
   `local/bin/pr_open.py --issue NNNN --branch issue-NNNN-slug --title "..."`.
3. **Dispatch agents**: only via `local/bin/dispatch.sh --role prover
   --issue NNNN --worktree .worktrees/<name> -- "task"`. Session telemetry
   lands in `results/telemetry/`.
4. **CI**: `local/bin/ci.sh NNNN` (build via hot cache + audits + blueprint
   checks; manifest in `prs/NNNN-*/ci/`).
5. **Review**: `local/bin/review.sh NNNN` — runs only after green CI; verdict
   and findings in `prs/NNNN-*/reviews/`.
6. **Auto-fix** (optional, flag `auto_fix: true` in `pr.md`):
   `local/bin/autofix.sh NNNN --mode auto`, capped, serialized.
7. **Merge**: `local/bin/pr_merge.py NNNN` — the gate; refuses on red CI,
   missing review, or unresolved findings. Refreshes `origin/main` alias and
   pokes the cache warmer.
8. **Housekeeping / site / bookkeeping**: `local/bin/housekeeping.sh all`,
   `local/bin/site.sh all`, `local/bin/track.py`, `local/bin/validate_tree.py`.

## Ground rules for agents

- Read `AGENTS.md` first; the faithfulness policy and proof-integrity
  blockers are unchanged from the parent project.
- Never run `lake update`. Never write to the hot cache. Full `lake build`
  goes through the machine-wide lock (`warm-worktree.sh`/`ci.sh` handle it).
- One session never reviews its own diff.
- Sessions are dispatched, resumed, and archived only via `dispatch.sh`.
- Invoke workflow tools through the primary checkout's path
  (`/…/MIPStarRE-dev/local/bin/…`), never through a worktree's copy — a
  branch's copy can predate protocol fixes, and before the registry-root
  fix it forked the registry (EVOLUTION.md, 2026-08-30).
- Friction with any protocol → log it in `results/telemetry/events.md`;
  propose amendments per `protocols/meta.md`.
