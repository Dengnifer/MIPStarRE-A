# Issue 237 / PR 238: primary relay and Astra max

The access blocker described in this historical preparation was lifted when
the owner resumed main on September 6 with unrestricted tool permissions.
The dispatch-specific update is `/tmp/qpbt-237-relay-max-access-restored.md`.
It records current host occupancy, completed workers, and the safe ceiling.

## Authority and dispatch conditions

The current owner authority is preserved at
`results/telemetry/owner-messages/qpbt-owner-relay-max-brief.md`.
It supersedes all historical dual-account, xhigh, and Sol instructions,
including the earlier decisions inside the archived meta packet.

Amend the existing issue 237 / PR 238 with one bounded worker, using the
primary checkout's `local/bin/dispatch.sh`, explicit `--account primary`,
`--effort max`, and `MIPSTARRE_CODEX_MODEL=gpt-6-astra`. Set supervisor
`MIPSTARRE_CODEX_ACCOUNT=primary`, review/fixer models to `gpt-6-astra`,
and review effort to `max`. Do not launch this worker until host-level
occupancy and the existing worktree writer have been verified. This brief
does not authorize bypassing the main session's rejected permission escalation.

Keep the whole workflow episode below 1000 changed lines and two hours;
do not use an infrastructure override. Include the existing PR's changes
when measuring scope. Do not introduce another client or scheduling framework.

## Observed state at 2026-09-05T23:44Z

- The local registry records `orc-237-20260906-01` (Sol, primary) done at
  23:40:30 UTC. Its PR head was `954c1bc004aae12cfff60a8a27b8eac6259f5327`.
- `reviewer-pr238-20260906-01` completed at 23:36:15 UTC and approved that
  old xhigh-policy head. The report records 28 dispatcher/router tests;
  the implementer records exact-head CI including 537 workflow tests.
  These are historical reports, not verification of the new owner policy.
- The daemon log records a main-refresh conflict at 23:36:44 UTC. The
  issue-237 worktree has an unresolved `results/telemetry/events.md`, and
  `pr238.failed` exists. Preserve all incoming-only paths and telemetry.
- The issue-113 recovery and issue-118 attempt-7 captures have recent writes,
  but their host process state is not visible inside this main sandbox.
  Do not infer completion, kill a PID, or restart from that observation.
- Main's canonical snapshot cannot reach GitHub (`socket: operation not
  permitted`). Its zero-worker count is invalid because only namespace-local
  processes are visible. A dispatcher dry run did not reach admission and
  was terminated after five seconds; a separate runtime-lock directory
  creation failed with `Read-only file system`.

## Required implementation

1. Read a persistent `primary` / `both` account mode on every dispatch.
   Default and current mode must be primary. An explicit later owner action
   is required to restore both; retain secondary credentials, config, and
   session history, along with the prior two-account capacity settings.
2. Primary's total relay limit is 12 including interactive main. Reserve one
   main slot, admit at most 11 workers, and subtract any additional use of
   that key. Reconcile live processes and reservations without double
   counting or treating unobservable host processes as dead. Primary
   saturation must queue or fail closed, never spill to the second key.
3. Fix the router's admission-on-timeout bug and disabled-account handling.
   Secondary selection, including resume affinity, must not override
   primary-only mode. Establish a truthful primary continuation path for
   secondary work: preserve checkpoints and old thread/account history,
   link continuation records, and keep the same shared mathematical budget.
   If direct cross-account resume is unsupported, reject it explicitly and
   continue from a checkpoint in a fresh primary session; never relabel the
   old thread's account or reset the gap budget.
4. Amend the existing effort normalization to literal `max`: omitted,
   legacy `ultra`, and `xhigh` Astra arguments must request max. Every role,
   including easy workers, reviewers, fixers, and mathfix, must use
   `gpt-6-astra` at max. Reject or normalize conflicting active-policy
   choices; remove active Sol selection paths. The mathfix guard must accept
   max. Telemetry must record the actual launch request, not infer backend
   compute or rewrite historical measurements.
5. Update the owner-authorized `~/.profile` review export and runtime shim,
   and prepare the future main launcher from
   `/tmp/qpbt-main-relay-max-v1.sh`. Use a versioned replacement and atomic
   installation; never edit a running shell script in place. Preserve
   credentials, unrelated configuration, and disabled automatic fan-out.
   These runtime writes require owner-approved access, not a worker escape
   from the main sandbox. Do not run new provider probes.
6. Synchronize applicable active launchers, supervisors, policy documents,
   and the protocol evolution ledger. Historical telemetry remains
   append-only; its obsolete policy records must not be silently rewritten.

## Safe transition and acceptance

First inspect authoritative host handles and the actual account/model/effort
of every project session. Prevent further secondary/Sol admissions and
safely interrupt affected workers through the dispatcher-owned lifecycle,
letting captures and terminal accounting finish. Preserve uncommitted proof
work, ongoing builds, and worktree ownership; then continue under primary/max.
Do not treat an observation timeout as a terminal worker. For issue 118,
retain the original gap anchor, ten-attempt limit, and all charged working
time: the owner brief reports 9852 seconds across six completed attempts,
with attempt 7 in progress. Reconcile attempt 7 before considering another.

Test mode changes on successive dispatches, explicit second requests,
secondary-affinity resume, disabled/zero capacity, full-capacity timeout,
concurrent reservations, main/additional-key occupancy, and preserved both
settings. Test every role and omitted/ultra/xhigh/max efforts without paid
provider calls. Include truthful launch telemetry and fan-out assertions.

Resolve the existing refresh conflict without losing either side's records;
use normal checked publication, exact-head CI, and the normal independent
reviewer on primary/Astra/max. No extra triage review, manual merge, or
premature failed-marker removal. Old-head approval cannot certify the
amended head. Only the merge daemon merges after the gates pass.

Return a concise report of exact head, tests, installed runtime version,
host-verified admissions and transitions, unchanged budget anchor and
charges, and any concrete permission blocker. Main owns the single #27
mode-boundary report and then resumes the mathematical critical path:
PR195 -> PR207 -> PR213/PR212 -> issue118/issue156.

## Follow-up at 2026-09-05T23:49:14Z

The registry now records `orc-113-20260906-06` done at 23:47:33 UTC, with a
terminal capture and report. Its local checkpoint is
`f1d1d3c7a1f421b255aec30c485ce593ad8e4905`. Do not restart that recovery.
The worker reports checked publication and nine successful CI contexts, but
its final GitHub observation was open/unmerged, mergeable=false, and missing
exact-head review status. The fourth-round approval cannot automatically
carry forward because the full-patch fingerprint changed. Preserve the
review cap and prior dispositions; do not add a fifth review or triage lane.
Main must refresh authoritative GitHub evidence when access is restored.

The canonical snapshot now shows only pr238.failed; marker disappearance is
not merge evidence. Issue118 attempt7 still has no terminal capture event or
last report, and host handles remain unobservable. Its recent capture writes
do not authorize a restart or establish current account/model/effort.
