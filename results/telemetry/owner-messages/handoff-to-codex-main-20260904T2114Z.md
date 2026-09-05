# Hand-back from the owner session (Mode 2 -> Mode 1), 2026-09-04 (about 21:10Z)

The owner session retires after this hand-back; NO takeover is scheduled. You (codex main) own the
operator loop until the owner says otherwise. This file overrides older helper references.

## Control plane (current)
- Merge daemon: `/tmp/merge-daemon-v6.sh` (running; log `~/.cache/mipstarre-dev/watchdog/lanes/daemon5.log`;
  merged list `watchdog/daemon/merged`). It merges every open PR whose exact head is CI-green and
  review-clean, or which is listed in `watchdog/daemon/adj-list` AND has a template
  `/tmp/adjudication-<PR>-template.md` (with `__HEAD__`), refreshing stale bases first. Do NOT run
  `pr_merge.py` by hand and do NOT push to main. To adjudicate: post the ADJUDICATION comment at the exact
  head (review.md section 12 format; the em-dash `—` before the disposition is mandatory), write the
  template file, append the PR number to the single line of `adj-list`, and remove `watchdog/daemon/pr<N>.failed`
  if present (failed PRs are retried only after 2 h).
- Lane runner: `/tmp/lane-v15.sh N slug prover|orc` (detached: `setsid nohup ... > watchdog/lanes/N.lane.log`).
  Env: `LANE_BRANCH=issue-N-slug`, `SKIP_DISPATCH=1` (worktree already holds the work: merge main, full
  build, push, PR, CI, review), `SKIP_REVIEW=1` (stacked PR whose base PR is still open). Repairs: write
  `watchdog/lanes/N.repair.md` (findings + instructions) and run the lane with dispatch on; `N.thread`
  resumes the same worker. Before checking whether a lane runs, use the anchored pattern
  `pgrep -f "^bash /tmp/lane-v1[345].sh N "` (an unanchored pgrep matches your own shell).
- Stacked packets: registry `watchdog/lanes/stacks` (issue:slug:base-branch); `/tmp/stack-watch.sh`
  (running) re-runs a lane with review once the base head reaches main. Propagate base fixes upward
  with `git merge <base-branch>`; a merge of main after a base PR lands often conflicts in
  `Games/CondLinear*.lean`, `Test/LowDegreeGame.lean` (the `μ_prob` proof: take main's) and blueprint
  citations: abort, write a repair note with the conflicted file list, relaunch with dispatch.
- Codex cap 10 (`watchdog/max-codex`); launches serialize on `watchdog/launch.lock`.
- Build products live on the NVMe pool: every worktree's `.lake` is a symlink to
  `/data/users/drx/mipstarre-cache/lake/<branch>` (lane-v15 creates it); the package store and hot-main
  are symlinked there too. NEVER leave untracked files or directories in a worktree (review.sh refuses a
  dirty tree). `/tmp/lake-to-data.sh worktrees|cleanup` migrates leftovers.
- Owner inbox #26: post ONLY decisions the human owner must make, as `### BLOCKER B<n> — title` with the
  marker `<!-- owner-inbox id=B<n> status=open -->`, at most 10 plain lines above the fold, details in
  `<details>`; keep the "Open now" table in the issue body current; the owner answers `DECISION B<n>: ...`;
  then post `RESOLVED B<n>` and flip the marker. Never decide a posted item yourself. Next free id: B6.
  OPEN: B5 (Magic Square rigidity: symmetric strategies alone do not repair thm:ms-rigidity; options A′
  symmetric+consistent (recommended), B one-way form, C extra game questions). Until answered: #172's
  statement change and #105 stay on hold (PR 192 carries only the gap note and blueprint remark).
- Paper gaps: every source-paper gap (wrong mathematics) gets a `docs/paper-gaps/` note and a blueprint
  fix (`docs/paper-gaps/proof-gap-protocol.tex`); the register is `docs/paper-gaps/qpbt-gap-register.md`
  (merged in PR 184). Encoding errors on our side (e.g. #201, the pasting contract) are operator-decidable.
- Review rounds: Lean PRs about 4 rounds then adjudicate; workflow/docs PRs 2 rounds; never grow a PR
  to satisfy findings; blockers about proof integrity (a `\leanok` that overclaims, a docstring that calls a
  helper the paper theorem) must be fixed, not deferred.
- Reports to #27 every ~2 h or at milestones. The 8-hourly estimate to #168 is automatic (cron).
- No Claude anywhere on ghz; never `pkill -f <substring>`; never touch `/home/drx/MIPStarRE-auto`.

## Each iteration
1. `ls watchdog/lanes/*.done *.needs-attention`; for each done lane read the review verdict
   (`gh pr view N --json reviews --jq '.reviews[-1].body'`): findings -> repair note + lane; clean -> the
   daemon merges it; at the round cap -> adjudicate (template + adj-list).
2. needs-attention: read the last lines of `N.lane.log` and the named log; conflicts -> repair note.
3. Keep the codex slots busy: `python3 local/bin/ready_packets.py --all` lists ready and blocked packets;
   stack new packets on the branch of their open-PR blockers (create the worktree, symlink `.lake` to
   /data first, add the registry line, launch with `LANE_BRANCH` and `SKIP_REVIEW=1`).
4. Post to #27.

## State at hand-back (written by the owner session, 2026-09-04 21:15Z)
- Merged this window: PRs 149, 186, 187, 161, 150, 184, 162, 170, 194. Main is at 5b94709 or later.
- Adjudicated and waiting for the daemon: PR 179 (#132; template /tmp/adjudication-179-template.md; refresh needed, stale base).
- In codex repair (round shown): PR 169 (#104, r1), PR 152 (#107, r2), PR 193 (#180, r1), PR 202 (#174 citations, r1), PR 198 (#190 /data support, r5: deletion-safety blockers, strict spec in 190.repair.md), PR 203 (#196 sandwich, r1). Adjudicate PR 198 and PR 203 leftovers after their next round; PR 169/152/193 are at rounds 1-2.
- Provers running: #115 (codex continuation for the last target expPoint_self_cons; route in 115.repair.md; its PR is stacked on #113 = PR 195), #201 (pasting error contract, stacked on #196 = PR 203).
- Publishing: #134 (PR 191, partial; its remaining targets need a full prover session: quantitative point-reference lemmas under the common-reference spec on issue #134 and exists_directSimultaneousPolynomialMeasurements).
- Stacked and waiting for bases: PRs 153, 155, 160 (on #107 = PR 152), 175 (#111), 178 (#114), 185 (#112), 195 (#113), 191 (#134), 192 (#172 docs), 193/194 done. Registry: watchdog/lanes/stacks.
- Owner decision open: B5 on #26 (Magic Square rigidity correction; A-prime recommended). #172's statement change and #105 wait for it. Do not decide it.
- Next packets when unlocked: #116 (after #110 = PR 155 and #115), #117 (after #109 = PR 153 and #115), #135 (after #134), #156 (after #116); follow-ups #199, #200, #204 (cleanup), #183 (PR 188 open).
- Estimate: ~69 open sorry sites in MIPStarRE/QPBT (was 197 at the start); the 8-hourly cron posts to #168.

## Snapshot at 2026-09-04T21:14:46Z (generated)

main: 5b94709; open PRs: 203,202,198,197,195,193,192,191,189,188,185,179,178,175,169,160,155,153,152

daemon pid: ; stack-watch pid: 1479421; live codex: 6

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
- 98: == 2026-09-04T14:23:09Z lane done
- 99: == 2026-09-04T10:44:03Z lane done
- carry: edits failed
- pr41: local-review/summary success APPROVED (code=APPROVED, prose=n/a), 0 unresolved

markers: 101.done 102.done 103.done 106.done 108.done 109.done 110.done 111.done 112.done 113.done 114.done 125.done 127.done 128.done 129.done 130.done 131.done 132.done 133.done 134.done 146.done 157.done 159.done 172.done 173.done 176.done 177.done 181.done 182.done 183.done 19.done 23.done 48.done 49.done 60.done 61.done 62.done 63.done 64.done 65.done 66.done 67.done 68.done 69.done 70.done 71.done 72.done 73.done 73.needs-attention 74.done 75.done 76.done 84.done 8.done 91.done 97.done 98.done 99.done

stacks:
- 109:ld-transport-bounds:issue-107-pauli-sampler-canonical-params
- 110:observables-sampling-bounds:issue-107-pauli-sampler-canonical-params
- 108:pauli-test-completeness:issue-107-pauli-sampler-canonical-params
- 111:projective-setup-point-observables:issue-107-pauli-sampler-canonical-params
- 105:ms-rigidity-constants:issue-104-ms-swap-isometry
- 114:expanded-point-operators:issue-111-projective-setup-point-observables
- 112:exact-winning-implications:issue-111-projective-setup-point-observables
- 113:approximate-winning-implications:issue-112-exact-winning-implications
- 115:derived-point-consistency-and-commutatio:issue-113-approximate-winning-implications
- 201:pasting-error-contract:issue-196-quantitative-sandwich-theorem
