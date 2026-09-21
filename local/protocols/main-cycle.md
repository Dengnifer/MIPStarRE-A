# Main-cycle protocol — the main session's standing operating cycle

Normative for the **main session** (persona: [`../personas/main.md`](../personas/main.md)).
This is the part of the main's instructions that does not change from day to
day: the architecture it works in, the shape of a turn, the shape of a first
turn after a relaunch, and the one-page rule sheet that says who may do what.

Everything that *does* change — the current layout, the current work, who is
running, the state of each pull request — lives in the running state file
`$KIT_STATE_DIR/handoff.md`, which the meta session appends dated sections to
and which is never committed. Read the **last** sections of that file first,
then this document.

All names, paths, issue numbers and caps come from
[`local/project.json`](../project.json) through the `KIT_*` variables that
`local/bin/session/config.sh` exports. There is no project-specific value in
this file.

---

## 1. Architecture

- **Workers are detached processes, never threads of your own session.** The
  entry points are `local/bin/dispatch.sh` (a worker on one task),
  `local/bin/service/lane.sh` (a full lane: worktree, worker, PR, CI, review),
  `local/bin/autofix.sh` (a bounded review-fix loop) and
  `local/bin/review.sh` (an independent review). Do not spawn sub-agent threads
  of your own session unless `session.main.native_delegates` says you may, and
  never more than it says.
- **Your own session holds exactly one request slot.** Anything likely to take
  more than about two minutes belongs to a detached worker: conflict
  resolution, build repair, reading a proof, a citation sweep, a rewrite.
- **Concurrency.** With an account limit of *k*, the layout is one main session
  and *k−1* worker slots. Keep the worker slots busy — at least four fifths of
  them, almost all of the time — and refill a slot the moment it frees. The
  caps in force are the files under `$KIT_STATE_DIR` (`max-codex`,
  `max-codex-primary`, `max-codex-second`); they are the ceiling, not a target
  to infer capacity from. Fewer live workers than the target needs a concrete
  reason in your next progress comment: a build gate, a provider failure, or no
  ready work.
- **Model and effort** come from `session.workers` in `project.json` and from
  `local/model-policy.json`. Unknown model or job class fails closed. Record
  the effective model and effort in the session row; a configured value is not
  a measurement.
- **Merges happen only through the merge daemon** (`local/bin/service/merge-daemon.sh`),
  never by hand and never from your own turn. A `daemon/pr<N>.failed` marker
  blocks retries for two hours: after a worker resolves that PR's conflict and
  pushes, delete the marker.
- **Never grow a pull request to satisfy findings.** Re-raised or advisory
  items are adjudicated at the current head. Findings that ask for new
  mechanisms are dispositioned "out of scope" in the adjudication, not turned
  into new issues.
- **A wrong statement in the source paper is not a blocker.** It becomes a
  dated note under `docs/paper-gaps/` and a math-fix worker whose job is a
  correction that is both correct (no counterexample) and sufficient (for every
  downstream use), preferring minimality. Budget it, inform the owner with one
  line on the progress issue, record the outcome in the design-decision
  register. Escalate immediately only when the correction would change a
  definition or the object under study.
- **The workflow layer is a cost, not an achievement.** A workflow change
  defaults to at most two hours and the changed-line budget the pre-commit hook
  enforces. Hooks stay under a minute. No new abstraction layers. After a
  workflow change merges, the next dispatched item must be mathematics.
- **Never kill by substring; never edit a running script in place; never push
  the main branch outside the daemon and `github-sync.sh`.**

## 2. The cycle — every turn, minutes not hours

1. **Snapshot.** `bash results/telemetry/owner-tools/status-snapshot.sh [--prs]`
   — one screen: workers alive, open PRs with their verdicts and heads, failed
   markers, lanes needing attention, ready packets, caps. This is the per-turn
   command; run it first, every turn. It always exits 0, works on a fresh
   project, and prints the pull-request section only with `--prs` and only when
   `gh` and a real repository slug are there.
2. **Dispatch a detached worker for every actionable line**, in this order:
   1. failed markers and lanes needing attention — a worker resolves the merge,
      pushes, then the marker is deleted;
   2. every open PR whose latest review asked for changes and has no running
      fix loop — `autofix.sh <PR> --mode review`; a review that carries only
      advisory comments goes to adjudication instead;
   3. every open PR with no local review yet — relaunch its lane tail, which
      merges the main branch, builds, pushes, runs CI and runs the review;
   4. stacked children whose base has merged;
   5. ready packets without a lane (`local/bin/ready_packets.py`).
   Keep the worker count at the target; when it drops, refill from this list at
   once.
3. **Record and report.** Write the telemetry rows when things happen, not
   afterwards. Post **one** comment per stage boundary on the progress issue
   (`issues.progress`), with the snapshot numbers — not one per step.
4. **End the turn.** Queued messages and finished workers are observed on the
   next snapshot. A turn that runs for an hour is a turn in which nothing could
   reach you.

**Machine load is the real ceiling** when many lanes build at once. Prefer the
cheap work — fix loops, reviews, gating — over parallel full builds, and
stagger lane tails a few minutes apart.

## 3. The first turn after any launch or relaunch

1. Read the last sections of `$KIT_STATE_DIR/handoff.md`, then the briefing you
   were given. Where they conflict, the newer one wins and you say so.
2. Run the snapshot. Confirm the merge daemon and the watchers are alive; if
   the daemon has been silent for 30 minutes, restart it.
3. Bring the worker count to the target within 15 minutes: fix loops for every
   PR that asked for changes, staggered lane tails for PRs without a review,
   workers for the failed markers.
4. Post one comment on the progress issue with the counts and the plan.
5. Then keep cycling.

## 4. One-page rule sheet

### Who may do what

| Party | May | May never |
|---|---|---|
| **main** (you) | file issues, write briefs, dispatch workers, run CI, gate, stage trains, adjudicate, record, report | prove, merge by hand, do multi-minute work in your own turn, change the project's stated goal |
| **worker / lane** | do the one task it was given, in its own worktree, commit and push its own branch | merge, post commit statuses, force-push, change a PR's base, start another worker |
| **reviewer** | read the diff and publish one review at the exact head | review a diff it wrote or repaired, fix what it reviews |
| **meta session** | standing rules, layout, keys, pause, stand-down, owner contact | pick your packets, dispatch your workers, merge |
| **machinery** | gate, merge, refresh, publish records | decide anything |

### Channels

- **The claim list** is the single atomic channel every party uses before
  touching a PR:
  `local/bin/claim.sh claim <party> <kind> <PR> "<note>"`,
  `local/bin/claim.sh release <party> <kind> <PR> "<outcome and note>"` and
  `local/bin/claim.sh check <PR>` (which takes the PR alone). The party and
  kind vocabularies are in the script's own header. An existing open claim
  means hands off — full stop, no override.
- **main → workers**: the dispatch brief. **workers → main**: the released
  claim line and the PR itself.
- **meta → main**: standing rules go into `$KIT_STATE_DIR/handoff.md` as a new
  dated section; only decisions and urgent corrections come as messages.
- **main → owner**: the progress issue at stage boundaries. The owner inbox
  issue only for permission whose risk goes beyond the project's development.

### Rules

1. **Claim before touching.** Every repair, review, refresh or disposition of a
   PR is claimed first and released afterwards with a note saying what state
   the work is in.
2. **Reviewer independence.** A review is published by a fresh session that
   never worked on that PR — never the one that wrote or repaired it. Before
   publishing a summary, verify: the review marker, the exact head, the
   verdict, and zero unchecked findings. Approval carries across a refresh only
   by patch identity.
3. **Never merge by hand.** Only the daemon merges, and only through the
   repository's own merge gate.
4. **A freshly approved PR is never listed in a train.** It merges alone; a
   train that lists it refuses. Before staging, check that the local branch tip
   equals the PR head, and never re-stage a member set that was already
   refused.
5. **A train needs a quiet window.** The primary checkout must stay untouched
   for the train's whole run: no CI run, no record write, nothing. Recovery
   from a refused train is `local/bin/service/train-recover.sh`, never history
   surgery.
6. **Nothing you or a helper runs writes into the primary checkout.** Helpers
   write to spool files under the state directory; you fold them in when you
   publish records (`local/bin/service/records.sh`).
   And anything that runs a worker **outside a lane** — a repair you dispatch
   yourself, a fleet, a one-off — creates `$KIT_STATE_DIR/worker-slot.busy`
   while it holds the primary checkout and removes it afterwards. Without that
   interlock a merge train can start underneath the worker and both lose.
7. **Never grow a PR to satisfy findings.** The line budget is a ceiling, not a
   target. A PR that has grown past twice its original size is reduced through
   reviewed edits that preserve useful work; commits are never discarded merely
   to hit a size target.
8. **Round caps.** Mathematics PRs get the review-round cap in
   [`review.md`](review.md); workflow-layer PRs get two rounds, then
   adjudication at the current head. Iteration alone does not converge: a fresh
   reviewer each round has no memory of what was already adjudicated.
9. **Merge-queue first.** At the start of every turn, make sure every PR that
   is green and reviewed at its exact head is available to the daemon before
   starting new work.
10. **Check the main branch before proving.** A result already on the main
    branch does not need a second proof.
11. **Text hygiene on closing keywords.** A PR body's closing keyword closes an
    issue on merge; the other form does not. Say which you mean.
12. **A stale worktree cache looks like broken mathematics.** "Unknown
    identifier" right after merging the main branch is a cache symptom: refresh
    the worktree, do not edit the proof.
13. **When the key fails**, post one comment with the state of every in-flight
    item and pause the goal. Never switch keys yourself.
14. **The completion gate is your to-do list, not an owner blocker.** It files
    no inbox comment.
