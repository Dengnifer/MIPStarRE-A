# CPA HTTP503 Pause

## Trigger and Containment

Main observed the following error in the actual stream of
orc-676-20260922-02, thread01a0c5a1-a6c7-7f01-b325-6419a9be39b8:
HTTP503 Service Unavailable, auth_unavailable, with the upstream reason
server_is_overloaded. The SDK subsequently made progress after automatic
retries. This is NOT evidence of quota exhaustion. Nevertheless, the standing
owner instruction explicitly requires a pause on cpa401/403/429/503, without
fallback, so main applies that rule literally.

Source evidence: /tmp/main-fix678-locator-drift-20260922.log and its preserved
session capture. Observation began with the20:22:22Z census on2026-09-21.
No direct probe, key switch, native delegate, proxy or subscription login was
performed. A watchdog/key-disabled/cpa marker records the precise reason,
including the distinction from confirmed quota exhaustion.

Caps were reduced from2/0/2 to0/0/0. Main set paused, goal-keeper.stop,
key-watch.stop, meta-pause-watch.stop and daemon/stop; the keeper, key watch and
historical pause watcher were stopped. The merge daemon subsequently exited.
The two live worker PIDs were signalled; issue673had already finished normally.
No codex exec process remains. Worktrees, commits, dirty fixtures and captured
evidence were preserved. Do not probe or re-enable cpa until the owner explicitly
authorizes it; space-3 and the other retired keys remain unavailable.

The only remaining operational job is model-free PR677 publication/CI,
PID809912, allowed to finish its current work. Its wrapper tests the cpa
disabled marker before any review dispatch, so it will stop there. A detached
records flush will preserve its final manifest and automatic telemetry without
starting models or restarting the daemon. Main sends /goal pause through the
existing tmux session; no completion or blocked-goal status is fabricated.

## Exact Work State

- Official comparator run35638601720 genuinely accepted all four targets with
  real-landrun, nanoda and Lean's default kernel. Candidate360402fdf4a39399f94331452d6e5d0a35c144be
  pins service-merged libraryecb97d1f66eec1e6fad964f144f78b91ce1fab36.
  The permanent record is not merged yet.
- PR677: author repair0c87485f30c4be7af0c84b7594708ae9ffd9b251 completed exit0
  with58passing tests. Guarded refreshed head9c3d759b37824449c8844498d07b7dd00d36cb1f
  is checked-published after the normal full build resolved missing
  PrintedClaims.olean. Complete CI is running; its build step passed41s.
  Prior adverse review5271230771 remains; a second independent review is
  required and is not authorized while paused. Wrapper/log prefix:
  /tmp/main-build-publish-ci-review677-repair-20260922.
- PR675: exactb7ebf9532831aa00cd1fb21f30f3215be7cb4b29 has full green CI and
  independent hard approval5271454834, reviewer wall672s exit0. The review
  verifies the retained printed contracts and counterexamples, explicitly NOT
  terminal adoption of either correction. Both register rows remain pending;
  main still must adjudicate the reported unchanged-C3 obstruction. Recheck
  freshness and use normal service/train rules after authorization to resume.
- Issue673: clean, unpublished head
  dd1e56e8460b0b358799e74b900d400aab77a0c9 over proof4c24f504b60afd3d3b0a128675089f0521bc80f2.
  The note-field repair and normal hooks passed. Author orc-673-20260922-02
  completed exit0, actual639s against configured600s; all costs are retained.
  No PR, canonical CI, or independent source review yet. Worktree:
  .worktrees/issue-673-prime-pauli-eigenbasis-20260922.
- PR678 / issue676: public and local headce5634de027a380c7299364f823abcaafb1fae97.
  Full Lean/axiom builds passed; CI fails on seven shifted source-locator
  comments. The generated Subspaces.lean fixture is now dirty and uncommitted;
  preserve it, inspect the full diff and finish checks/normal commit before
  publication. The source bridge remains partial; RREF correspondence is not
  proved. Worker orc-676-20260922-02 was stopped on the cpa rule. Its wrapper
  reports exit0/statusdone, wall385s, usageunknown, but there is no final
  receipt or verified repair commit. Do NOT interpret that transport status as
  task completion. Worktree: .worktrees/issue-676-canonical-complement-alignment-20260922.
- PR669: exact1186b548dccaf61da351ae103ba76c10fc1961c2, complete green CI,
  third combined adverse review5271377709, five findings/four distinct defects.
  Final bounded repair is prepared in /tmp/main-fix669-third-review-prepared-20260922.md
  and waits for canonical PR677 service merge. One ordinary full review remains;
  no fifth-round reset is authorized.
- Issue679: artifact-guide correction is prepared, unadmitted and without a
  worktree/PR. Brief /tmp/main-artifact-guide-followup-20260922.md includes actual
  preflight evidence and excludes files owned by669/677.
- Parked infrastructure PR552/554/556/561 remain parked. Issue168 and archived
  issue26 were not updated. Source672 is merged as392b550d613cdb09ccce95c8491f60cc194cb6eb.

## Completion Is Still False

At sourcedcffa512: C1PASS333QPBTfiles/no holes; C3FAIL11of21nonterminal rows;
C4FAIL7of528unmarked nodes; C5recordnotmerged; C2/C7delegated. The frozen
source-equivalent c9c0b456 tree regenerates all31challenge files without drift.
The initial primary-checkout drift failure was stale build products and is
retained separately, not fixed by changing fixtures.

Packaging preflight at73c493c8 built and scanned49gap-note PDFs, and authored
plus anonymized-no-PDF packages passed leak scans. Two excluded-workflow links
and two historical LDT paper locators remain. This predates672and is not the
final artifact or final-tree Lean build. Raw-Pauli blocker668was already fixed.

## First Actions After Explicit Authorization

Inspect final677CI/records logs; obtain second independent record review and
service merge, then repair669 against that canonical record. Publish clean673
through normal refreshed CI and independent source review. Complete dirty678
locator synchronization and first review. Gate approved675with exact-head and
freshness rules, and adjudicate its substantive source-contract objection
without weakening completion criteria. Admit679when a model slot is genuinely
free. Preserve all budgets, original reviews, failed logs and uncommitted work.
