# Main handoff: <YYYY-MM-DD> <run label or stop reason>

<!--
HOW TO USE THIS FILE  (local/personas/main.md, "Standing reports", item (c);
local/protocols/full-speed-mode.md section 6)

Copy to results/telemetry/owner-handoffs/<YYYY-MM-DD>-main.md and fill it in
when the run pauses. Two rules:

1. EVERY NUMBER IS MEASURED BY THIS SESSION, not copied from an operator or
   owner message. The 2026-09-12 handoff reads "Owner listed eight merges"
   because the operator's message was the source; the ninth merge was found
   only by a later GitHub read. Measure with:

     bash results/telemetry/owner-tools/status-snapshot.sh --prs
     local/bin/run_mode.py show
     git rev-parse github/main
     gh pr list --state open --limit 100 --json number,headRefOid,isDraft
     gh search prs --merged --json number  (or the daemon's own merge log,
        cross-checked against GitHub)

   State the instant of the measurement. A number you could not measure is
   written as "unknown", never as zero and never as an estimate.

2. Keep the two memory disciplines of meta.md: this file is an append-only
   report, never rewritten later. Corrections are a dated note in the next
   handoff, not an edit here.

Delete every section that has nothing to record. Delete this comment.
-->

Closing measurement: <ISO instant>, main <full SHA>.
Run: <run.label from run_mode.py show>, <start>..<stop>, speed <fast|default>.
The goal is **paused for scheduling**, not complete and not blocked. Do not
resume automatically; resume only on the owner's explicit word.

Closing progress comment: <URL of the one comment on the progress issue>.
No prose was posted on the estimate issue.

## Closing result

- Direct proof holes on main: <N> at <start> to <M> now (measured at <instant>).
- Merges this run, verified on GitHub: <count> — <numbers>. Name the source of
  the count and the latest merge commit SHA.
- Open PRs: <total>; ready-to-merge and still open: <count> with the reason for
  each (the last `ready_report.py` comment is the measurement, not a guess).
- What is claimed and what is not: state plainly which results are proved,
  which depend on an unfinished lemma, and which are wrappers over open work.

## First tasks on resumption

Ordered, each with the exact head SHA, the evidence already published, and the
one next action. No task without a SHA.

1. <PR / issue>: <state at <SHA>>; <next action>.
2. ...

## Proof checkpoints

One bullet per live packet: PR / issue, published head, CI and review state on
that exact head, what is proved, what remains, and where the partial work
lives. Never discard a worktree or a budget; record the cumulative attempt
count and working time for every gap under `issues-prs.md` section 6.

## Runtime and evidence

- Run mode at the stop: `run_mode.py show` output — caps per account, occupancy
  floor, speed, dispatch cutoff, issue numbers.
- Measured limits observed this run (`watchdog/capacity/limit-estimate.json`):
  per account `measured_limit`, `observed_refusal_floor`, `external_inferred`.
  These seed the next run's starting caps.
- Endpoint health at the stop, and any outage with its window.
- Live workers at the final census, by account, with their session names; who
  owns stopping them.
- Runtime inventories to preserve under `~/.cache/mipstarre-dev/watchdog/`:
  <paths>.
- Telemetry committed / deliberately uncommitted for the daemon to publish:
  <state>.
- Confirm explicitly: no manual PR merge, no direct push to main, no credential
  or permission change, no proof-integrity mechanism touched.

## Open owner items

Only items on the owner inbox that are still open, one line each with its id.
An item already posted there waits for the owner; do not re-decide it here.
