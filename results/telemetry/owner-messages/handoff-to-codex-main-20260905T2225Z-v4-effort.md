# Main-session handoff v4 — 2026-09-05 19:10Z (consolidated; supersedes v3 and every older helper reference)
You are the MAIN SESSION of track A (Mode 1): the operator. Model gpt-6-astra, second codex account (CODEX_HOME at
~/.cache/mipstarre-dev/codex-home-yxy), multi-agent fan-out off. There is no owner session watching after 19:30Z; the human
owner reads #26 and #27 only. Run the project the way the owner session ran it on 2026-09-05: fifteen merges by 17:24Z with 4-10
workers live, every review answered within minutes by a fix loop or an adjudication, math gaps handed to math-fix sessions with one
line on #27, everything recorded in telemetry.
## The cycle (every turn, minutes not hours)
1. `bash results/telemetry/owner-tools/status-snapshot.sh --prs` — one screen: workers per account, lanes, autofix loops,
   needs-attention lanes, daemon failed markers, daemon tail, stacks, ready packets, per-PR verdict and unresolved count, #26.
2. Act on every actionable line by dispatching DETACHED workers. Never do work that takes more than about two minutes yourself
   (persona main.md line 23): conflict resolution, build repair, citation migration, reading a proof — all go to
   `local/bin/dispatch.sh --role orc --issue N --pr P --worktree W --sandbox workspace-write -- "<task>"` or to a lane tail.
   Order: (a) daemon failed markers `watchdog/daemon/pr<N>.failed` and `<issue>.needs-attention` lanes: a worker resolves the merge
   of github/main in that worktree and pushes; then delete the failed marker so the daemon merges; (b) every open PR with unresolved
   findings and no loop: `local/bin/autofix.sh <PR> --mode review` (label auto-fix-codex; loops serialize per PR); only advisories
   left: adjudication (`/tmp/adjudication-<PR>-template.md` with `__HEAD__`, PR number in `watchdog/daemon/adj-list`); APPROVED:
   nothing, the daemon merges; (c) after a merge: stack children whose base merged (`$L/stacks`, child:slug:base) get their tail
   relaunched if stack-watch did not (`LANE_BRANCH=<branch> SKIP_DISPATCH=1 setsid nohup bash /tmp/lane-v17.sh N slug prover
   > $L/N.lane.log 2>&1 < /dev/null &`, after removing N.done/N.needs-attention); (d) ready packets without a lane:
   `setsid nohup bash /tmp/lane-v17.sh N slug prover > $L/N.lane.log 2>&1 < /dev/null &` (astra by default; prefix
   `MIPSTARRE_CODEX_MODEL=gpt-5.6-sol` only for really easy tasks; `MIPSTARRE_FIX_MODEL=gpt-5.6-sol` for autofix).
3. Record at once: stages.jsonl transitions, events.md entries for incidents and milestones, design-decisions.md rows for choices.
4. Report on #27 at stage boundaries (merges, gaps opened or closed, mode changes) with the snapshot's numbers. #26 only for
   decisions a human must make (`### BLOCKER B<n> — title`, marker `<!-- owner-inbox id=B<n> status=open -->`, next id B7);
   never decide for the owner once posted.
5. End the turn. Queued owner messages arrive only between turns.
## Standing rules
- Owner correction, September 5 22:18Z: no extra independent triage dispatches
  on top of the review pipeline. #27 gets at most one comment per actual merge,
  gap, or mode change, not publication/CI/review micro-milestones. Prioritize
  PR195 ->207 ->213/212. PR195 already has live repair supervisor1587780:
  conflict resolved and committed27316a9 at21:37:58Z; checked-push validation
  continues. Do not duplicate it; clear failed marker after publication and
  verify stack propagation after actual merge. PR205 adjudication template and
  adj-list were already configured; completed pre-existing triage report was
  published as exact-head review5123227589 at71bedeb to discharge the daemon's
  actual gate4 refusal, then pr205.failed cleared. No new triage was dispatched.
- Merges only by the merge daemon (/tmp/merge-daemon-v8.sh, log $L/daemon5.log); never by hand. Never grow a PR to satisfy
  findings; adjudicate re-raised or advisory items instead of looping. Codex concurrency: about 19 worker slots over two accounts,
  routed automatically by the PATH shim (owner-bin/codex v2, log watchdog/account-router.log); never set CODEX_HOME yourself.
  Parallelism means workers, not your own effort, and never dispatch merely to fill slots: critical path first.
- Critical path: PR 185 -> 195 -> 207 -> 213/212 -> #118/#156; PR 153 merged -> #119 (stack on the #118 branch) -> #120 -> #121
  -> #123; PR 205 (#201) feeds #118. Infrastructure lanes (#215, #224, #231 if still open) only when they do not compete with
  chain builds; the machine load is the real limit when several lanes build at once.
- Math-fix on source-level gaps: `MIPSTARRE_CODEX_MODEL=gpt-6-astra local/bin/dispatch.sh --role mathfix --effort ultra`, at most
  10 sessions or about 1.5 working days per gap, then #26; one line on #27 when a gap opens (owner may veto); record in events.md
  and design-decisions.md. Definition or game changes go to #26 immediately.
- Pre-commit workflow-layer budget 1000 lines; MIPSTARRE_INFRA_OVERRIDE is owner-only. Never `pkill -f`; never touch
  /home/drx/MIPStarRE-auto; never edit a running bash script in place; never push main outside the daemon or github-sync.
- Effort stays ultra for every codex session. Reviews and fixers you launch use MIPSTARRE_CODEX_MODEL/MIPSTARRE_REVIEW_MODEL from
  ~/.profile (gpt-6-astra).
- At low context: append your state summary to this file, post it on #27, continue after compaction; the owner relaunches you with
  /tmp/relaunch-main-v4.sh when needed.
## Open items at 19:10Z (act on them in the first turn)
- PR 185 (#112) APPROVED, conflict fixed and pushed by lane 112: delete watchdog/daemon/pr185.failed once the lane's review is
  green; the daemon merges; then check propagation into 195.
- PR 225 (#210) COMMENTED with one advisory; merge of github/main in progress in its worktree since 18:22Z (lane 210 running):
  when pushed, adjudicate and delete pr225.failed.
- PR 233 (#232, dispatch.sh account routing) APPROVED; daemon refresh conflicted in .worktrees/issue-232-dispatch-account-routing
  (marker pr233.failed): repair worker, push, delete the marker. After it merges: replace owner-bin/codex by
  owner-bin/codex.v1-20260904 (fan-out off only) and set watchdog/max-codex-primary 10 / max-codex-second 9.
- PR 178 (#114) prose 1 finding, PR 202 (#174) 1 finding: autofix loops relaunched 18:54Z; PR 205 (#201) 5 findings, lane 201
  running (math-fix session 3 result: the reverse second-marginal premise does not follow from the source; the recorded decision
  keeps eq:pasting-1-sym as an added hypothesis; adjudicate what re-raises that, autofix the rest).
- #118 branch at 691b671 (claims 17-2/17-3 proved); remaining: conditional lem:qld-4-13 forms and the combined-lines witness from
  lem:pasting after PR 205 merges. #119 is dispatchable stacked on the #118 branch. needs-attention markers 118 and 73 are stale.
- Two durable follow-ups (sol lanes): amend local/personas/main.md with the cycle above and the two-minute delegation rule;
  refresh ~/.codex/prompts/goal.md (both homes) with the cycle, the two accounts and the critical-path priority.
## Snapshot at 2026-09-05T19:16:58Z (generated at relaunch)
    == 2026-09-05T19:19:38Z load 48.20 | main 946f67a | max-codex 20
    == workers: 5 live (.codex=1 codex-home-yxy=4 )
    == lanes: 112 114 210 232 | autofix:  205
    == needs-attention: 118 73 | daemon failed markers:
    == daemon (last 3):
    == 2026-09-05T19:17:23Z refreshing PR 185 (issue-112-exact-winning-implications)
    == 2026-09-05T19:17:23Z refreshing PR 225 (issue-210-general-k-combining-reduction)
    == 2026-09-05T19:17:23Z refreshing PR 233 (issue-232-dispatch-account-routing)
    == stacks (child:slug:base):
       113:approximate-winning-implications:issue-112-exact-winning-implications
       115:derived-point-consistency-and-commutatio:issue-113-approximate-winning-implications
       116:expanded-line-measurements:issue-115-derived-point-consistency-and-commutatio
       117:polynomial-and-joint-point-foundations:issue-115-derived-point-consistency-and-commutatio
       118:combined-lines-and-restricted-averages:issue-116-expanded-line-measurements
       156:honest-pauli-strategy:issue-116-expanded-line-measurements
       224:sampler-instance-cleanup:issue-156-honest-pauli-strategy
    == ready packets:
     issue  title                                                        parent  blockers
      #112  feat(QPBT/Observables): prove exact winning implications       #165  -
      #114  feat(QPBT/Observables): prove expanded point operators         #165  -
      #201  fix(QPBT/Games): encode the pasting error contract as t...     #163  -
      #210  feat(QPBT/Combining): simultaneous polynomial measureme...     #166  -
    == #26 open blockers: 0
## Effort finding and tasks (owner session, 2026-09-05 22:25Z) — do these in your first cycle, before anything else
- Measured: the astra endpoint does not honour `model_reasoning_effort = "ultra"`; the response reports `medium`. It honours
  `xhigh` (and `high`). sol maps `ultra` to `max`. So every astra session launched with the config default or `--effort ultra`
  (all lanes, reviews, autofix fixers, math-fix, and the previous main sessions) actually ran at medium. The owner wants the
  highest honoured effort: astra sessions must request `xhigh`; sol sessions keep `ultra`. This session runs at xhigh.
- Tasks (all small; the first two are sol lanes or direct edits by you, the third a reviewed PR):
  1. `~/.profile`: `export MIPSTARRE_REVIEW_EFFORT=xhigh` (review.sh pins it) next to the model exports; verify with
     `bash -lc "echo \$MIPSTARRE_REVIEW_EFFORT"`.
  2. `~/.cache/mipstarre-dev/owner-bin/codex` (the PATH shim): when `-m gpt-6-astra` is present, rewrite any
     `model_reasoning_effort="ultra"` argument to `"xhigh"` and, when no effort argument is present, add
     `-c model_reasoning_effort="xhigh"`; leave sol untouched. Copy the shim to a new name before editing (never edit a running
     script in place), test with `codex exec --skip-git-repo-check --sandbox read-only -m gpt-6-astra "Reply OK"` under
     `RUST_LOG=debug` and confirm the `response.completed` event reports `xhigh`.
  3. `local/bin/dispatch.sh` (issue to file, lane on sol, reviewed PR): per-model effort ceiling: an astra model with
     `--effort ultra` or no `--effort` dispatches with xhigh; the mathfix guard accepts xhigh with astra; record the effective
     effort in sessions.jsonl. Protocol note in local/protocols/sessions.md and an EVOLUTION.md entry citing the 22:25Z events entry.
  4. Record the finding in events.md (incident) and a design-decisions.md row; one line on #27.
- Until 1-2 are done, prefix your own dispatches with `MIPSTARRE_REVIEW_EFFORT=xhigh` and pass `--effort xhigh` to dispatch.sh for
  astra workers (mathfix: `--effort ultra` is still what the guard demands until task 3 lands; the shim then rewrites it).
## Snapshot at 2026-09-05T22:23:16Z (generated at relaunch v6)
    == 2026-09-05T22:24:16Z load 55.26 | main e885c8b | max-codex 19
    == workers: 3 live (.codex=1 codex-home-yxy=2 )
    == lanes: | autofix:
    == needs-attention: 113 118 201 | daemon failed markers: pr195.failed pr205.failed
    Automatic merge failed; fix conflicts and then commit the result.
    2026-09-05T22:21:41Z merging github/main conflicted in /home/drx/MIPStarRE-qpbt/.worktrees/issue-201-pasting-error-contract
    == 2026-09-05T22:21:46Z PR 205 still stale after refresh
      #113  feat(QPBT/Observables): prove approximate winning impli...     #165  -
