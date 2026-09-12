# Full speed mode run of 2026-09-12 (04:17Z-08:33Z) — what happened and where the owner had to step in

Project: Lean 4 formalization of the quantum Pauli basis test, repo Dengnifer/MIPStarRE-A, checkout /home/drx/MIPStarRE-qpbt on host ghz
(128 cores, shared with other users' jobs; load 90-150 during the run). Track A pipeline: a codex "main session" (gpt-6-astra) in tmux
`qpbt` runs the operating cycle; detached codex workers are started only through local/bin/dispatch.sh (roles prover/reviewer/orc/...);
lanes (/tmp/lane-v17.sh, now v20) merge main, build, push, run CI (local/bin/ci.sh) and review (local/bin/review.sh); a merge daemon
(/tmp/merge-daemon-v9h.sh + /tmp/daemon-scan.py) refreshes approved PRs and merges them through local/bin/pr_merge.py gates; a
"meta" Claude session on the owner's Mac operates over ssh (scp a script to /tmp, run it with one ssh line). Two codex keys: primary
`~/.codex` (relay-us7) and second `~/.cache/mipstarre-dev/codex-home-yxy` (api.finite-dimensional.space); caps in
`~/.cache/mipstarre-dev/watchdog/max-codex-{primary,second}` and `max-codex`; router local/bin/account_router.py; PATH shim
`~/.cache/mipstarre-dev/owner-bin/codex` (copy in snapshot/tmp-scripts/codex-shim.sh) forces fan-out off, xhigh, and today rewrites
gpt-5.6-sol -> gpt-6-astra and adds service_tier="priority".

## Owner interventions this time (each one is a defect of the workflow to remove or automate)

1. Capacity: the owner had to tell us the concurrency limits several times (5 on the primary key; 10 -> 40 -> 20 -> 30 on the yxy key), confirm that a
   local forked Claude session shares the yxy key, and finally limit that session to 2 slots. Meanwhile ~90 worker sessions died: the primary
   endpoint returned 503 for an hour (69 deaths), and sessions above the real yxy limit died after five "Concurrency limit exceeded" retries.
   Nothing measured the real limit, detected the dead endpoint, or adapted the caps; the meta did it by hand (caps 39 -> 29 -> 20 -> 18 -> 14 -> 12 -> 6 -> 14 -> 22 -> 0).
2. Occupancy: the owner asked repeatedly why slots were idle ("should be close to 30"). Causes: dispatch failures (model_policy.py rejects
   an explicit astra request for routine jobs; autofix.sh defaults MIPSTARRE_FIX_MODEL=gpt-6-astra so every fixer died at preflight), lanes
   in CPU-bound build/CI phases, an empty dispatch queue while the main session wrote long reports. The meta filled slots by dispatching
   tens of workers directly (autofix loops, lane tails, orc repairs, review re-runs) and by nudging the main session.
3. Progress visibility: the owner asked "is the project progressing?" and then demanded a one-line estimate on #168 every 30 minutes in
   the exact format of /home/drx/bin/estimate.sh (bold headline + one <sub> line) and nothing else on #168; progress prose belongs on #27.
   The main session had posted multi-line reports on #168; the meta had to reformat one and add a cron.
4. Merge throughput: the owner asked why ready PRs were not merging and set the rule "a ready-to-merge PR left open needs a good reason".
   Causes: every merge makes the other refreshed heads stale (gate 2b), refresh lanes conflicted with main (23 branches), append-only
   telemetry logs (results/telemetry/events.md etc.) conflicted on nearly every merge, the daemon's pr<N>.failed markers (2 h backoff)
   silently blocked PRs after systemic lane failures, PAR was 1-3. Fixes applied only in /tmp or in the ghz git config: union merge driver
   in .git/info/attributes, PAR=8, cleared markers, fix-lane.sh orc repairs. The merge train PR 507 (local/bin/pr_train.py) never landed.
5. Lane runner defects found and fixed only in /tmp/lane-v17.sh (v18-v20): the pre-push preflight gate diffed REMOTE_HEAD..HEAD (hundreds of
   `lake env lean` runs after merging main; now diffs github/main..HEAD); modules outside the MIPStarRE.QPBT import closure
   (Combining.Points.Absorption, MarginalContraction) have no olean after the umbrella build so the gate failed on every lane (now the
   changed modules are built explicitly; the umbrella import gap in MIPStarRE/QPBT/Combining/Points.lean itself is still open); lanes
   must be numbered by ISSUE number because pr_open.py adopts the open PR through the issue (meta lanes numbered 1000+PR died after the
   push); PR 213's lane worktree held a different branch than the PR (refresh never pushed).
6. Speed tier and schedule: the owner switched fast/default speed three times by hand (service_tier="priority" in the shim; the main TUI
   never got it) and set the schedule by messages (work 4 h, extend 1 h, finalize, "pause within 15 minutes"). The pause needed a kill of
   leftover workers at a deadline (final-pause.sh), the earlier pause script had wiped the crontab once (sed delimiter bug), the resume
   script was patched by a side session.
7. Message delivery to the main session: owner-say v2 hung for 20 minutes on a stale "esc to interrupt" line; the goal keeper resumes a
   paused goal every 2 minutes; the main session's long turns (25 min) delayed dispatches; the model policy rewrite in the shim means
   sessions.jsonl records the policy's model (sol) while the session ran astra (telemetry inaccuracy, noted in events.md).
8. Superseded/duplicate work: PRs 329/334/336/337 already on main but open; two loops on one branch (autofix + prover); PR 342 oversized file
   (never auto-fixed); 20 stale 1xxx lanes.

## Timeline (UTC)
04:17 resume; 04:21-04:35 waves 1-3 (autofix loops, lane tails), 21 workers at 04:35; 04:47 orc resolvers for 23 conflicted merges, 32
workers at 04:50, 39 at 04:55; 05:05-05:26 caps chase (deaths on yxy), first merge PR 525 at 05:26; 05:15 lane v18, 05:28 v19, 05:36 v20 +
issue numbering; 05:44 failed markers cleared, daemon PAR=8; 05:59 primary key 503s -> cap 0, 25 reviews re-run; 06:12-06:38 caps 26 ->
6; 06:50 default speed; 07:02 union merge driver; 07:28 fast speed again; 08:13 finalize; 08:18 freeze; 08:33 pause. Merges: 525 530
532 263 280 281 282 251 256 (9). Holes on main 20 -> 19; #168: 21 of 197 sites open (89%), 9 proved in open PRs.

## Where the current tooling lives (snapshot layout)
- snapshot/repo: AGENTS.md, CLAUDE.md, local/ (bin, protocols, personas, briefs, DESIGN.md, README.md, model-policy.json), .githooks/,
  results/telemetry/{events.md (read only the "## 2026-09-12" sections near the end), design-decisions.md, owner-handoffs/,
  owner-tools/, owner-messages/}.
- snapshot/tmp-scripts: the operator scripts that exist only in /tmp on ghz (lane-v17.sh = lane runner v20, merge-daemon-v9h.sh,
  daemon-scan.py, fix-lane.sh, conflict-resolve.sh, autofix-loop.sh, owner-say.sh v4, owner-say-v3.sh, goal-keeper-v2.sh,
  owner-pause*.sh, final-pause.sh, owner-resume.sh, tick.sh, speed-*.sh, main-session-astra-v3.sh, stack-watch-v3.sh,
  qpbt-main-handoff-v5.md, the meta-wave*.sh launchers, codex-shim.sh) and wf-bin/ (the owner's cron scripts: estimate.sh,
  qpbt-watchdog.sh, owner-heartbeat-check.sh, astra-poll.sh).
- snapshot/watchdog: meta-dispatched.txt, wave logs, final-pause.log, caps-before-pause, crontab.txt, stages-tail.jsonl.

## Goal of this refinement
Next time the owner starts a full speed run they should give ONE briefing (keys and their limits, duration or "until my word", speed
tier, pause deadline) and then only receive the half-hourly #168 one-liner and #27 progress. Everything the owner had to do this time
must be automated, made a one-file switch, or turned into a self-healing mechanism, with the fixes living in the repository (local/bin,
local/protocols, personas, owner-tools) rather than in /tmp. Repository changes must respect AGENTS.md and local/protocols (reviewed
PRs, one PR per issue, no proof-integrity changes); operator scripts that must stay outside the repo are documented and installed by a
versioned installer.
