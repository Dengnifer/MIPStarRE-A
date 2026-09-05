# Hand-back from the owner session (Mode 2 -> Mode 1), 2026-09-04 13:03Z

Reason: the owner's Claude budget window. The owner session takes the operator role back at
14:50Z (it will send you a handover message; then report on #27 and exit as on 2026-09-03).
This file overrides any older helper references in the standing briefing (lane-v4, merge.sh,
rerun_review.sh are retired).

## Standing rules (unchanged unless marked NEW)
- Merge green PRs first. NEW: the MERGE DAEMON does it. `/tmp/merge-daemon-v5.sh` is running
  (log `~/.cache/mipstarre-dev/watchdog/lanes/daemon5.log`, merged list `watchdog/daemon/merged`):
  every loop it merges each open PR whose exact head is CI-green and review-clean, refreshing
  stale bases in parallel. Do NOT run `local/bin/pr_merge.py` yourself and do NOT push to main.
  Adjudicated merges: post the ADJUDICATION comment (review.md section 12: first line
  `ADJUDICATION`, exactly one `head=<40-hex>` line, one `- [x] F<n> - fixed in <sha> | moot: ... |
  out of scope: ... | deferred to issue #N: ...` per unresolved finding), then append the PR number
  to the single line in `~/.cache/mipstarre-dev/watchdog/daemon/adj-list`.
- Lean PRs: repair up to about 4 review rounds, then adjudicate; workflow/docs PRs: 2 rounds.
- Codex concurrency cap 7 (`watchdog/max-codex`); launches serialize on `watchdog/launch.lock`.
  Lane runner: `bash /tmp/lane-v14.sh N slug prover` (detached with setsid nohup, log to
  `watchdog/lanes/N.lane.log`). Env: `LANE_BRANCH=issue-N-slug` (stacked branch), `SKIP_DISPATCH=1`
  (worktree already holds the finished work: merge main, build, push, PR, CI, review),
  `SKIP_REVIEW=1` (stacked PR whose base PR is still open). Repairs: write
  `watchdog/lanes/N.repair.md` (the findings plus instructions; see 106.repair.md, 131.repair.md)
  and run lane-v14 with dispatch on; `N.thread` resumes the same worker. Markers: `N.done`
  (`PR= HEAD=`), `N.needs-attention` (last error line).
- Stacked packets: registry `watchdog/lanes/stacks` (issue:slug:base-branch);
  `/tmp/stack-watch.sh` (running) re-runs a lane with review once the base head reaches main.
  Propagate base fixes upward with `git merge <base-branch>`; after any merge into a stacked
  worktree the lane runs `lake build MIPStarRE.QPBT` itself (v14).
- Merge conflicts in `MIPStarRE/QPBT/Games/CondLinear*.lean` today were all blueprint line-range
  citations in docstrings: abort the merge, write a repair note asking the worker to redo the
  merge and recompute the ranges (wording in 106.repair.md), relaunch the lane. Workflow issue
  #174 proposes label-based citations (operator-level, later).
- No Claude anywhere on ghz. Never `pkill -f <substring>` (kill anchored PIDs only). Never touch
  `/home/drx/MIPStarRE-auto`, `Dengnifer/MIPStarRE-B`, tmux `auto`. `MIPSTARRE_INFRA_OVERRIDE=1`
  is owner-granted only.
- Owner inbox #26: post only what the human owner must decide, and never decide a posted item.
  Pending there: the Magic Square rigidity correction (`exists_ms_rigidity` is false as stated;
  options 1-3). Packet #172 is ON HOLD until the owner answers; #105 is blocked by #172.
- Paper gaps: every source-paper gap (wrong mathematics) gets a `docs/paper-gaps/` note and a
  blueprint fix (`docs/paper-gaps/proof-gap-protocol.tex`); #173 audits the existing notes
  (launch it as a lane when a slot frees; it is docs-only).
- Every 8 h `~/bin/estimate.sh` posts the completion estimate to #168 (automatic; leave it).
- Reports to #27 every ~2 h or at milestones; blockers only to #26.

## In flight (see the generated snapshot at the end)
- 112: its codex worker runs detached (dispatch pid 2322069, started 12:23Z); a watcher runs the
  lane tail (SKIP_DISPATCH, SKIP_REVIEW) when it exits. Worktrees 112 and 114 were cut from the
  111 branch before its resync: they carry a duplicate `mem_linePoints_lineRepMap`
  (Combining/DirectLowDegree/Geometry.lean:236 vs Algebra/Lines.lean:130) and the pre-repair
  #98 content. When their workers finish and their tails fail: `git merge` the current
  `issue-111-projective-setup-point-observables` (after 111's own resync lane lands), delete the
  Geometry.lean copy, then rerun the tail (`SKIP_DISPATCH=1 SKIP_REVIEW=1`).
- Stacks: PR 170 (#133) on PR 161 (#131); PRs 162/169 (#103/#104) on PR 149 (#102); PRs 152,
  160, 153, 155 (#107, #108, #109, #110) on PR 150 (#106); #111, #112, #114 on the 107 branch.
- PR 161 finding F1 (sorryAx via `ldGame.μ_prob`) is resolved by PR 150 (#106 proves μ_prob);
  when 150 merges, refresh 161 and adjudicate F1 as moot if the reviewer re-raises it.
- Next packets when unlocked: `python3 local/bin/ready_packets.py` (on main after PR 171 merges;
  until then run it from `.worktrees/issue-159-packet-tree-ready/local/bin/`). Candidates: #113
  after #112's PR opens (stack on it), #134 after #132, #116 after #115/#110/#106, #156 continues
  on its branch after #116. #124, #125, #127, #128 close when PR 151 merges (their content is in it).
- #105 stays parked (clean worktree, stacked on #104) until #26 is answered.

## Each iteration
1. `ls watchdog/lanes/*.done *.needs-attention`; for each done lane read the review verdict
   (`gh pr view N --json reviews --jq '.reviews[-1].body'`): findings -> repair note + lane;
   clean -> the daemon merges it.
2. needs-attention: read the last lines of `N.lane.log` and the named log; fix and relaunch.
3. Keep 7 codex slots busy with ready packets (stack on the branch of open-PR blockers).
4. Post to #27.

## Snapshot at 2026-09-04T13:03:08Z (generated)

main: 4eaf968; open PRs: 171,170,169,162,161,160,158,155,154,153,152,151,150,149

daemon pid: 4008724; stack-watch pid: 55749; live codex: 6

lanes (last log line):
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
- 98: == 2026-09-04T13:00:53Z review.sh 158
- 99: == 2026-09-04T10:44:03Z lane done
- carry: edits failed
- pr41: local-review/summary success APPROVED (code=APPROVED, prose=n/a), 0 unresolved

markers: 101.done 103.done 104.done 107.done 108.done 109.done 110.done 125.done 127.done 128.done 130.done 133.done 159.done 19.done 23.done 48.done 49.done 60.done 61.done 62.done 63.done 64.done 65.done 66.done 67.done 68.done 69.done 70.done 71.done 72.done 73.done 73.needs-attention 74.done 75.done 76.done 84.done 8.done 91.done 97.done 99.done

stacks:
- 109:ld-transport-bounds:issue-107-pauli-sampler-canonical-params
- 110:observables-sampling-bounds:issue-107-pauli-sampler-canonical-params
- 108:pauli-test-completeness:issue-107-pauli-sampler-canonical-params
- 107:pauli-sampler-canonical-params:issue-106-ld-geometry-sampling
- 103:ms-approximate-anticommutation:issue-102-ms-projective-dilation
- 104:ms-swap-isometry:issue-103-ms-approximate-anticommutation
- 133:ld-transport-error-bound:issue-131-ld-pass-conversion
- 111:projective-setup-point-observables:issue-107-pauli-sampler-canonical-params
- 105:ms-rigidity-constants:issue-104-ms-swap-isometry
- 114:expanded-point-operators:issue-111-projective-setup-point-observables
- 112:exact-winning-implications:issue-111-projective-setup-point-observables
