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

1. **File an issue**: `local/bin/issue_new.py --title "..." --body-file b.md --label ...` opens
   a GitHub issue and prints its number; `--parent N` attaches it as a native
   sub-issue. Record each prerequisite, including one already closed, with
   `local/bin/gh_common.py add-blocked-by ISSUE PREREQUISITE`; the command is
   safe to repeat. The brief for the issue goes in `local/briefs/`.
2. **Open a PR**: create branch `issue-<number>-slug`, worktree under
   `.worktrees/`, run `local/bin/worktree-setup.sh` there, then
   `local/bin/pr_open.py --branch issue-<number>-slug --title "..." --body-file pr.md --issue N` (the body follows the PR template in `local/protocols/issues-prs.md`),
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

**Choosing the next packet.** `local/bin/ready_packets.py` walks the packet tree
under the Stage 4.3 tracker #47 — chapter trackers, their packets, and nested
chains such as Magic Square rigidity — and prints the open leaf packets whose
GitHub issue dependencies (`blocked_by`) are all closed. `--all` adds the
blocked packets with their open blockers, `--json` feeds the lane launcher, and
`--root N` restricts the walk to one tracker. Prerequisites live in those edges
only: the "Dependencies" bullets in a packet body are commentary
(`protocols/issues-prs.md` §1). A merged packet closes its issue and therefore
unblocks its dependents with no edit anywhere.

## Telemetry

**Optional useful-work queue:** default-disabled `local/bin/useful_queue.py`
admits only main-selected packets. Limits, adoption and reviewed deployment:
`protocols/useful-queue.md`, `briefs/257-useful-admission-queue.md`.

Session, stage, build, and incident records live under `results/telemetry/` as
described in [`protocols/meta.md`](protocols/meta.md). The
[`design-decisions.md`](../results/telemetry/design-decisions.md) register is
the short, chronological index of owner and operator choices that shaped the
workflow; each row points to the longer primary record. Record reasoning in the
pointed event or owner log rather than expanding the index into a second log.

## Ground rules for agents

- Read `AGENTS.md` first; the faithfulness policy and proof-integrity
  blockers are unchanged from the parent project.
- Never run `lake update`. Never write to the hot cache. Full `lake build`
  goes through the machine-wide lock (`warm-worktree.sh`/`ci.sh` handle it).
- Publish branches through `checked-push.sh` (used internally by `pr_open.py`,
  `github-sync.sh`, and `autofix.sh`) so the gate finishes before push transport
  starts.
- One session never reviews its own diff.
- Sessions are dispatched, resumed, and archived only via `dispatch.sh`.
- Invoke workflow tools through the primary checkout's path
  (`/…/MIPStarRE-dev/local/bin/…`), never through a worktree's copy — a
  branch's copy can predate protocol fixes (EVOLUTION.md, 2026-08-30).
- After merging `main` or a stack parent, preserve every incoming-only path.
  The reference-transaction hook checks the exact merge object before the
  branch ref moves, while the pre-commit hook checks the pending index when a
  merge is committed later. Both run `local/bin/merge_loss_guard.py`.
  `merge_loss_guard.py --repo <worktree> --commit HEAD` audits a merge already
  committed by a lane whose branch copy predates the hooks.
- Friction with any protocol → log it in `results/telemetry/events.md`;
  propose amendments per `protocols/meta.md`.
