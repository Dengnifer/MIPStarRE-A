# Handoff to the codex main session (gpt-6-astra) — written by the owner session, 2026-09-05

This file overrides every older helper reference (lane-v14, merge.sh, rerun_review.sh, /tmp/qpbt-main-handoff.md).
Read it first, then ~/.codex/prompts/goal.md, local/personas/main.md, AGENTS.md, and the last three #27 reports.

## Mode and roles
- Mode 1: you (codex main, model gpt-6-astra) operate track A in /home/drx/MIPStarRE-qpbt. The owner session
  (Claude) watches #26/#27 for 90 minutes after this handoff, then only #26/#27; it intervenes on stalls.
- Workers: codex gpt-5.6-sol through local/bin/dispatch.sh (lanes below). The owner-launched Claude agents that were
  running at the handoff finish on their own (list below); do not touch their worktrees until released on #27.
- Math-fix (source-level gaps): now `MIPSTARRE_CODEX_MODEL=gpt-6-astra local/bin/dispatch.sh --role mathfix --effort ultra`
  (the guard in dispatch.sh admits it). Rule: at most 10 math-fix sessions or about 1.5 working days per gap, then a
  BLOCKER on #26; tell the owner by one line on #27 when a gap is opened (veto possible); record the gap in
  results/telemetry/events.md and the decision in results/telemetry/design-decisions.md. Definition or game changes
  go to #26 immediately.

## Tooling that is live on ghz (all under ~/.cache/mipstarre-dev/watchdog, "$L" = watchdog/lanes)
- Lane runner: `setsid nohup bash /tmp/lane-v17.sh <issue> <slug> prover > $L/<issue>.lane.log 2>&1 < /dev/null &`
  creates/warms the worktree, dispatches a codex prover with the issue body, merges github/main, builds, opens the PR,
  runs ci.sh and review.sh; markers $L/<issue>.done / .needs-attention. Tail of an existing branch (no dispatch):
  `LANE_BRANCH=<branch> SKIP_DISPATCH=1 setsid nohup bash /tmp/lane-v17.sh <issue> <slug> prover ...` after removing
  the old markers. v17 stops with needs-attention when a merge of main would silently drop paths main carries (#222).
  Never edit /tmp/lane-v17.sh in place while lanes run (bash reads scripts incrementally): copy to a new name.
- Merge daemon: /tmp/merge-daemon-v8.sh (log $L/daemon5.log) merges every PR that passes the gates and publishes main
  through local/bin/github-sync.sh. Never merge by hand. `pr<N>.failed` markers under watchdog/daemon block retries
  for two hours (delete to retry). Adjudications: /tmp/adjudication-<PR>-template.md with __HEAD__, PR listed in
  watchdog/daemon/adj-list (first line ADJUDICATION, one head=<40-hex>, one ledger line per unresolved finding with
  an em-dash). Stack-watch /tmp/stack-watch-v3.sh propagates merged parents into $L/stacks children (issue:slug:base).
- Review fix rounds: add the label auto-fix-codex to the PR and run
  `setsid nohup local/bin/autofix.sh <PR> --mode review > $L/<issue>.autofix.log 2>&1 < /dev/null &` (cap 5, pushes,
  re-runs ci.sh and review.sh --force-review). Reviews of new heads: the lane does it; by hand `local/bin/review.sh <PR>`.
- Pre-commit workflow-layer budget is 1000 lines (owner decision B6); a merge head containing github/main is measured
  against github/main. MIPSTARRE_INFRA_OVERRIDE is owner-only; never self-grant.
- Never `pkill -f <substring>`; use anchored pgrep. Never run anything under /home/drx/MIPStarRE-auto. Never push to
  main outside the daemon/github-sync (telemetry commits go through github-sync.sh or `git push github main`).
- Telemetry duties: stages.jsonl transitions, events.md entries for incidents and milestones, design-decisions.md rows
  for choices; codex sessions are captured by dispatch.sh in sessions.jsonl; the owner session's Claude agents are in
  owner-sessions.jsonl (do not edit it).

## Claude work still running at the handoff (leave these worktrees alone until released on #27)
- .worktrees/issue-118-combined-lines-and-restricted-averages: Fable math-fix session 1 on claims 17-2/17-3 of
  lem:qld-sublines (gap: deficit-form Cauchy-Schwarz, marginal identification, joint (line, point) mixture).
- .worktrees/issue-174-replace-blueprint-line-range-citations-i (PR 202): Opus repair of a conflicted merge of main;
  afterwards the owner session relaunches the lane tail.
- Review mailbox ~/.cache/mipstarre-dev/watchdog/claude-reviews (PRs 178, 185): Opus reviewers answer; the lanes 112
  and 114 publish the reviews. Do not answer or delete mailbox requests.

## Queue and dependencies
- Formalization packets: #135 (tail lane running; packet complete), #119 waits for #109 (PR 153) and #118; #120 waits
  for #114 (PR 178) and #119; #121 after #120; #123 after #109, #115, #116, #119, #121. #156 (honest strategy,
  exists_spcc_value_one proved) is stacked on 116: open its PR once PR 213 (#116) merges.
- Stacks ($L/stacks): 113 on 112, 115 on 113, 116 and 117 on 115, 118 and 156 on 116; PR 212 (#117), 213 (#116),
  195 (#113), 207 (#115) wait for their bases; stack-watch handles propagation.
- Infrastructure issues available for codex lanes: #215 (mature alias block; touches open branches: coordinate),
  #224 (DecidableEq on the model field), #89, #59, #9-#14, #22, #24, #30-#34, #52.
- Owner inbox #26: next free BLOCKER id B7. Post only decisions the human owner must make; never decide for them.

## Snapshot at 2026-09-05T15:45:27Z (generated)

main: c1b001a; open PRs: 230,229,228,227,225,213,212,207,205,202,195,185,178,153

daemon pid: 2950602; stack-watch pid: 2950610; live codex sessions: 5; autofix loops: autofix.sh  autofix.sh 153 autofix.sh 225 autofix.sh 227

lanes running: 112 135 201 218 222

lanes (last log line):
- 220: == 2026-09-05T11:59:24Z lane done
- 222: == 2026-09-05T15:45:36Z local/bin/review.sh 230
- 23: == 2026-09-04T02:42:18Z lane done
- 48: == 2026-09-04T00:52:17Z lane done
- 49: == 2026-09-04T08:41:09Z lane done
- 60: == 2026-09-04T09:13:51Z lane done
- 61: == 2026-09-04T05:26:42Z lane done
- 62: == 2026-09-04T00:15:56Z lane done
- 63: == 2026-09-04T12:24:28Z lane done
- 64: == 2026-09-04T07:22:38Z lane done
- 65: == 2026-09-04T04:06:27Z lane done
- 66: == 2026-09-04T03:32:59Z lane done
- 67: == 2026-09-04T05:48:52Z lane done
- 68: == 2026-09-04T09:19:11Z lane done
- 69: == 2026-09-04T10:07:26Z lane done
- 70: == 2026-09-04T09:30:52Z lane done
- 71: == 2026-09-04T09:58:51Z lane done
- 72: == 2026-09-04T01:57:55Z lane done
- 73: 2026-09-04T03:22:18Z no commits ahead of main for #73
- 74: == 2026-09-04T09:50:25Z lane done
- 75: == 2026-09-04T06:13:25Z lane done
- 76: == 2026-09-04T10:52:41Z lane done
- 84: == 2026-09-04T01:23:08Z lane done
- 8: == 2026-09-04T07:41:15Z lane done
- 91: == 2026-09-04T08:55:20Z lane done
- 97: == 2026-09-04T11:56:53Z lane done
- 98: == 2026-09-04T14:23:09Z lane done
- 99: == 2026-09-04T10:44:03Z lane done
- carry: edits failed
- pr41: local-review/summary success APPROVED (code=APPROVED, prose=n/a), 0 unresolved

markers: 101.done 102.done 103.done 104.done 105.done 106.done 107.done 108.done 109.done 110.done 111.done 113.done 114.done 115.done 116.done 118.needs-attention 125.done 127.done 128.done 129.done 130.done 131.done 132.done 133.done 134.done 146.done 157.done 159.done 172.done 173.done 174.needs-attention 176.done 177.done 180.done 181.done 182.done 183.done 190.done 196.done 199.done 19.done 200.done 204.done 208.done 210.done 216.done 219.done 220.done 23.done 48.done 49.done 60.done 61.done 62.done 63.done 64.done 65.done 66.done 67.done 68.done 69.done 70.done 71.done 72.done 73.done 73.needs-attention 74.done 75.done 76.done 84.done 8.done 91.done 97.done 98.done 99.done

stacks:
- 113:approximate-winning-implications:issue-112-exact-winning-implications
- 115:derived-point-consistency-and-commutatio:issue-113-approximate-winning-implications
- 116:expanded-line-measurements:issue-115-derived-point-consistency-and-commutatio
- 117:polynomial-and-joint-point-foundations:issue-115-derived-point-consistency-and-commutatio
- 118:combined-lines-and-restricted-averages:issue-116-expanded-line-measurements
- 156:honest-pauli-strategy:issue-116-expanded-line-measurements

worker model: gpt-6-astra (watchdog/model.txt); main model: gpt-6-astra
