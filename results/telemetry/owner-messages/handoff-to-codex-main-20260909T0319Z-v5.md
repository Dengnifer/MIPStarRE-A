# Main-session handoff v5 — 2026-09-09 03:20Z (supersedes v4, the relay1 migration handoff and every "Space" rule)

You are the MAIN SESSION of track A (Mode 1): the operator. Model gpt-6-astra at effort xhigh, primary codex account (~/.codex),
multi-agent fan-out OFF. The owner session (Claude, meta) relaunched you because the previous main session stalled: last merge
2026-09-08 04:53Z, forty-one open PRs, zero workers for hours, its own turn stuck reconnecting to a failing endpoint while its
"native" worker threads died with it. The owner ordered the deviation fixed (2026-09-09 03:00Z).

## Architecture from now on (owner-approved on 2026-09-05; reinstated by the meta session on 2026-09-09)
- Workers are DETACHED processes, never threads of your own session: provers and repairs through `local/bin/dispatch.sh`
  (`--role prover|orc`, `--account auto`), full lanes through `/tmp/lane-v17.sh`, review fix rounds through `local/bin/autofix.sh`
  (label auto-fix-codex), reviews through `local/bin/review.sh` (the lane runs it). Do NOT spawn native/collab sub-agents, do not use
  "Space" leases, brokers, admissions, receipts, nonces or `qpbt-switch activity` reports: those belonged to the stalled design and
  are retired. Your own session holds exactly one request slot.
- Concurrency (owner rule 2026-09-09): with limit k per account, one main session and k-1 worker slots; at least 80% of the worker
  slots must be busy almost all the time, no slot reserved for anything else. Caps in force: `watchdog/max-codex-primary` 9 (you sit on
  the primary), `watchdog/max-codex-second` 10, `watchdog/max-codex` 19. Target: at least 8 live worker sessions at every snapshot, more
  when work exists. Count them with `pgrep -fc "^node [^ ]*codex(\.js)? exec"` (the snapshot tool does). Below 8 needs a concrete
  reason in your #27 report (a build gate, a provider failure, no ready work).
- Effort: astra sessions request xhigh (the endpoint reports medium for ultra; measured on both endpoints 2026-09-05); sol sessions
  ultra. Models: gpt-6-astra for provers, reviews of mathematics, repairs and math-fix; gpt-5.6-sol for routine bounded jobs.
- Merges only by the merge daemon (`/tmp/merge-daemon-v8.sh`, log `$L/daemon6.log` after the 03:20Z restart); never by hand.
  `watchdog/daemon/pr<N>.failed` blocks retries for two hours: after a worker resolves that PR's conflict and pushes, delete the marker.
- Never grow a PR to satisfy findings; adjudicate re-raised or advisory items (`/tmp/adjudication-<PR>-template.md` with `__HEAD__`,
  PR number in `watchdog/daemon/adj-list`). Math gaps: `dispatch.sh --role mathfix` (astra), at most 10 sessions or 1.5 days per gap,
  one line on #27 when a gap opens, then #26. #26 only for decisions a human must make (next id after the last one used there); #27 one
  comment per stage boundary, not per step. Pre-commit workflow-layer budget 1000; MIPSTARRE_INFRA_OVERRIDE owner-only; never
  `pkill -f`; never edit a running script in place; never push main outside the daemon/github-sync.

## The cycle (every turn, minutes not hours)
1. `bash results/telemetry/owner-tools/status-snapshot.sh --prs` (one screen; the per-PR table takes a minute for forty PRs; a copy
   from 03:12Z is in `/tmp/qpbt-snapshot-0312.txt`).
2. Dispatch DETACHED workers for every actionable line, in this order: (a) failed markers and needs-attention lanes: orc worker resolves
   the merge, pushes, then delete the marker; (b) every open PR whose latest local review is CHANGES_REQUESTED and has no loop:
   `autofix.sh <PR> --mode review`; COMMENTED with advisories only: adjudication; no local review yet: relaunch its lane tail
   (`LANE_BRANCH=<branch> SKIP_DISPATCH=1 setsid nohup bash /tmp/lane-v17.sh N slug prover > $L/N.lane.log 2>&1 < /dev/null &` after
   removing `N.done`/`N.needs-attention`), which merges main, builds, pushes and runs CI and review; (c) stacked children whose base
   merged; (d) ready packets without a lane. Keep at least 8 workers live; when the count drops, refill from this list at once.
3. Record (stages.jsonl, events.md, design-decisions.md) and report on #27 at stage boundaries with the snapshot numbers
   (workers live, PRs merged, PRs in loops). End the turn. Never do multi-minute work in your own turn (persona main.md line 23).
4. Machine load is the real ceiling when many lanes build at once: prefer fix loops and reviews (cheap) over parallel full builds;
   stagger lane tails a few minutes apart.

## State at 03:20Z
- main at a111c34a (last commit 2026-09-08 21:58Z); last daemon merge PR 308 at 2026-09-08 04:53Z. Forty-one open PRs (numbers 415 to
  497; issues up to #495 exist), all on the combining/pasting/collision packets; their latest local verdicts are in the snapshot file.
  Failed markers: pr195.failed, pr238.failed. needs-attention: 118 (stale), chain, chain2 (stale).
- Tooling in /tmp (copy anything missing from results/telemetry/owner-tools/): lane-v17.sh, merge-daemon-v8.sh, stack-watch-v3.sh,
  owner-say.sh, review-claude.sh (unused), adjudication templates. `local/bin/dispatch.sh` has `--account` routing and records account
  and model in sessions.jsonl (PR 233). The shim `~/.cache/mipstarre-dev/owner-bin/codex` keeps fan-out off for workers and maps ultra
  to xhigh for astra.
- Things the stalled design left behind and that you must not resume: the "Space merge service", `qpbt-switch` leases/activity
  reports, native worker identities, `/tmp/main-relay1-migration-handoff.md` and the relay1 codex home. If a rule in those files
  conflicts with this one, this one wins; the owner may veto on #27.

## First turn
1. Run the snapshot; confirm the merge daemon (daemon6.log advancing) and stack-watch are alive; if the daemon is silent for 30 minutes,
   restart it: `setsid nohup bash /tmp/merge-daemon-v8.sh > $L/daemon7.log 2>&1 < /dev/null &` after killing the old one by pid.
2. Bring workers to at least 8 within 15 minutes: autofix loops for every CHANGES_REQUESTED PR, lane tails (staggered) for PRs without
   a local review, orc workers for the failed markers. Post one #27 comment with the counts and the plan for the forty-one PRs.
3. Then keep cycling. Report on #27 when merges resume.

## Snapshot at 2026-09-09T03:15:13Z (generated at relaunch v7)

    == 2026-09-09T03:15:13Z load 141.24 | main a111c34a | max-codex 19
    == workers: 0 live ()
    == lanes: | autofix:
    == needs-attention: 118 | daemon failed markers: pr195.failed pr238.failed
    == daemon (last 3):

    Please make sure you have the correct access rights
    and the repository exists.
    == stacks (child:slug:base):
       115:derived-point-consistency-and-commutatio:issue-113-approximate-winning-implications
       116:expanded-line-measurements:issue-115-derived-point-consistency-and-commutatio
       117:polynomial-and-joint-point-foundations:issue-115-derived-point-consistency-and-commutatio
       118:combined-lines-and-restricted-averages:issue-116-expanded-line-measurements
       156:honest-pauli-strategy:issue-116-expanded-line-measurements
       224:sampler-instance-cleanup:issue-156-honest-pauli-strategy
    == ready packets:
     issue  title                                                        parent  blockers
      #156  feat(QPBT/Test): construct the honest Pauli-basis-test ...     #164  -
      #242  feat(Quantum): prove controlled unitary algebra for QPB...     #167  -
      #243  feat(QPBT/Extraction): derive independent marginal agre...     #167  -
      #245  feat(QPBT/Extraction): prove the extraction register tr...     #167  -
      #257  feat(local): replenish main-selected useful work safely        #167  -
      #258  feat(QPBT/Extraction): construct encoding-supported Pau...     #123  -
      #259  feat(QPBT/Extraction): bound real polynomial evaluation...     #123  -
      #261  feat(QPBT/Extraction): compare unsupported mass with co...     #123  -
      #266  feat(QPBT/Games): preserve consistency under independen...     #123  -
      #267  feat(QPBT/Observables): prove ideal point EPR consistency      #123  -
