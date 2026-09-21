# Local operations — operator guide

This directory is the operative workflow of the repository: the local
replacement for a hosted CI/review/merge layer, plus the session layer that
runs the project unattended. Architecture and invariants:
[`DESIGN.md`](DESIGN.md). Protocol changes: follow
[`protocols/meta.md`](protocols/meta.md).

**Start here, depending on who you are.**

| You are | Read |
|---|---|
| the supervising session a human is talking to | [`personas/meta.md`](personas/meta.md) → [`protocols/meta-session.md`](protocols/meta-session.md) |
| bootstrapping a new paper | [`protocols/bootstrap.md`](protocols/bootstrap.md) |
| the main session | [`personas/main.md`](personas/main.md) → [`protocols/main-cycle.md`](protocols/main-cycle.md) |
| a dispatched worker | `AGENTS.md`, then your role's page under [`personas/`](personas) |

**Everything project-specific is in [`project.json`](project.json)** — the
library name, the Lean root, the track, the repository slugs, the cache root,
the tmux session, the issue numbers, the session layout and the key names. Read
it with `python3 scripts/project_config.py get <dotted.key>`, or source
`bin/session/config.sh` and use the `KIT_*` variables. Never hard-code a value
this file already holds.

## The directories

| Path | What is in it |
|---|---|
| `bin/` | the workflow engine: issues, pull requests, CI, review, auto-fix, merge, cache, site |
| `bin/session/` | starting and supervising the main session: launch, message, goal keeper, key watch, pause, resume, stand-down, status |
| `bin/service/` | the model-free services: merge daemon, lanes, review gate, trains, records |
| `protocols/` | the normative documents; `meta.md` governs how they change |
| `personas/` | one page per role, including the supervising session and the main session |
| `templates/` | goal, briefing, stand-down, handover section, skeleton brief, chapter plan, owner report |
| `briefs/` | one design brief per issue, committed |
| `registry/` | the declaration-claim registry that guards against duplicate work |
| `kit/` | provenance: the origin commit this tree was extracted from, and the extraction script |

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
   lands in `results/telemetry/`. Lease-backed native descendants are retired;
   `protocols/sessions.md` retains their history separately.
4. **CI**: `local/bin/ci.sh <pr-number>` (build via hot cache + audits +
   blueprint checks) → per-step `local-ci/*` statuses and the manifest PR
   comment.
5. **Review**: `local/bin/review.sh <pr-number>` — runs only after green CI;
   publishes one exact-head COMMENT review plus the `local-review/summary`
   status.
6. **Auto-fix** (optional, the repository's auto-fix label on the PR):
   `local/bin/autofix.sh <pr-number> --mode {ci|blueprint|review|auto}`, capped,
   serialized.
7. **Merge**: `local/bin/pr_merge.py <pr-number>` — the gate; refuses on red CI,
   missing review, or unresolved findings, and merges via GitHub with the
   exact-SHA guard. Then pokes the cache warmer.
8. **Housekeeping / site**:
   `local/bin/housekeeping.sh {standup|stale-audit|linter-sweep|readme-freshness|all}`
   and `local/bin/site.sh {blueprint|badges|docs|assemble|all}` (each script's
   `--help` is the authority on its subcommands).

**Choosing the next packet.** `local/bin/ready_packets.py` walks the packet tree
under the tracker named by `issues.tracker_root` — chapter trackers, their
packets and nested chains — and prints the open leaf packets whose
GitHub issue dependencies (`blocked_by`) are all closed. `--all` adds the
blocked packets with their open blockers, `--json` feeds the lane launcher, and
`--root N` restricts the walk to one tracker. Prerequisites live in those edges
only: the "Dependencies" bullets in a packet body are commentary
(`protocols/issues-prs.md` §1). A merged packet closes its issue and therefore
unblocks its dependents with no edit anywhere.

## Telemetry

Session, stage, build, and incident records live under `results/telemetry/` as
described in [`protocols/meta.md`](protocols/meta.md). The
[`design-decisions.md`](../results/telemetry/design-decisions.md) register is
the short, chronological index of owner and operator choices that shaped the
workflow; each row points to the longer primary record. Record reasoning in the
pointed event or owner log rather than expanding the index into a second log.

## Ground rules for agents

- Read `AGENTS.md` first: the faithfulness policy and the proof-integrity
  blockers are normative for every agent in this repository.
- Never run `lake update`. Never write to the hot cache. Full `lake build`
  goes through the machine-wide lock (`warm-worktree.sh`/`ci.sh` handle it).
- Publish branches through `checked-push.sh` (used internally by `pr_open.py`,
  `github-sync.sh`, and `autofix.sh`) so the gate finishes before push transport
  starts.
- One session never reviews its own diff.
- Worker sessions use `dispatch.sh`; the native lease and review transport in
  `sessions.md` are historical and must not be used for new work.
- Invoke workflow tools through the **primary checkout's** path
  (`$KIT_REPO_ROOT/local/bin/…`), never through a worktree's copy — a branch's
  copy can predate a protocol fix.
- After merging `main` or a stack parent, preserve every incoming-only path.
  The reference-transaction hook checks the exact merge object before the
  branch ref moves, while the pre-commit hook checks the pending index when a
  merge is committed later. Both run `local/bin/merge_loss_guard.py`.
  `merge_loss_guard.py --repo <worktree> --commit HEAD` audits a merge already
  committed by a lane whose branch copy predates the hooks.
- Friction with any protocol → log it in `results/telemetry/events.md`;
  propose amendments per `protocols/meta.md`.

## Declaring a track finished

The end of a track is gated like every other step of the lifecycle.
[`protocols/completion.md`](protocols/completion.md) is the definition of done
— zero proof debt, a built axiom audit over the headline theorems, terminal
paper-gap rows, marked or explicitly exempted blueprint nodes, a comparator
challenge pinned to an ancestor commit and naming every headline theorem,
truthful status docs, and the files an ITP artifact submission needs — and
`scripts/completion_gate.py check --track <track>` is the model-free checker
that decides the mechanically checkable part of it. No completion statement,
umbrella-issue closure or release tag without a passing run on the exact
commit. The gate is intentionally outside the blocking PR CI.
