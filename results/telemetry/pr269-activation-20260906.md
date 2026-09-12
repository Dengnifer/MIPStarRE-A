# PR269 terminal-cleared integration and queue activation

Session: `orc-252-20260906-07`. Runtime:
`~/.cache/mipstarre-dev/pr269-integration-20260906T080400Z/`.
This is a new operation; the earlier adverse-head HOLD and its snapshots remain intact.

## Normal Integration

Main's exact-head terminal disposition 5124691248 approves
`27669521936684b60768906d223c52df33f3de40` after the two independent model reviews.
The live review text matches the recorded unmarked-body SHA256; GitHub's canonical
review marker accounts for the full-body hash difference. All nine fresh CI
statuses and `local-review/summary` were success. No third model review ran.

Only detached `qpbt-merge-daemon-pr269-2766952.sh`, PID 4108172, invoked the
primary `pr_merge.py 269 --no-warm-cache`. All normal gates passed without
adjudication or a hook bypass. GitHub merged PR269 as
`ba299326ebde0d9f94fc9b4e9b557ce776e8f1cf`; canonical primary main and origin/main
fast-forwarded to that commit before the daemon ended at 08:08:46 UTC.

`attempt-1/` retains a stable snapshot of 158 pending telemetry paths,
46,395,001 bytes, the unique stash
`1664884773333aa68dc08ae626baed7b5cd738e3`, its verified bundle, and retained
old inodes. Restoration finished at 08:08:59 UTC with all incoming prefixes
and saved raw-row multiplicities verified. A second verification checked all
158 current primary paths against the retained inodes. Backups and stash remain.
Primary authentication contents were neither read nor copied; automatic writers
were not stopped. The locked issue257 worktree was retained by normal cleanup guards.

## Reviewed Queue

All four installed entrypoints matched both the approved head and clean primary
main: `useful_queue.py`, `account_router.py`, `dispatch.sh`, and `review.sh`.
`activation.json` records their hashes and supervisor PID/start identity
4113611 / 170635254, launched at 08:09:51 UTC with `--run --watch 5`.

Only main's revision-three READY selection was installed: issues 243, 244, 246.
Its queue SHA256 is
`dc90a42058743500f7c497f1b764523b574b62f358ab2dfb1b300ae025cb531e`.
Fresh preparation and installed queue checks verified task hashes, clean exact
worktree heads, native prerequisite #63, actual PR88 merge
`4eaf9681c5670e6895f21541d0a458fae793a55c`, ancestry, and absence of live owners.
Issues 239, 241, 242, 245 were not automatically admitted.

| Issue | Admission UTC | Session | Ticket |
| --- | --- | --- | --- |
| 243 | 08:10:00 | prover-243-20260906-02 | cccc03cad2e5477b85c42d8bcce82aae |
| 244 | 08:10:11 | prover-244-20260906-02 | 8c97d1457c7a449693d2aa715c4e3f00 |
| 246 | 08:10:23 | prover-246-20260906-02 | ab2721671bb4407da61aa56f82245877 |

`~/.cache/mipstarre-dev/useful-queue/` retains the one-shot intent, ticket,
launch logs, receipts when terminal, state, and append-only events. Real primary
Astra sessions began and completed commands; this is actual admission evidence.
The detached read-only monitor PID 4129074 records session/thread identities,
client PID/start identities, completed commands, publication, terminal receipts,
and owner floor counts in `operation-observations.jsonl` and `operation-latest.json`.

HTTP/ALL proxy variables were removed; the relay and loopback hosts are explicit
NO_PROXY entries. Primary-only allocation 11 and the conservative recovery ceiling
10 remain; requested worker effort is xhigh, not provider-measured effort.
At 08:13:02 the census counted six workers/reservations, below floor eight.
All three selected packets were already admitted. No later replacement admission
after a terminal worker ending has yet been observed; admission and command
counts do not establish that additional claim.

## Cache Recovery

After restoration released primary integration, one detached canonical warmer
started at 08:09:30 UTC, PID 4111532, pinned to actual main `ba299326` with
`--lock-timeout 14400`. Its normal writer lease and full-build lock were used.
No productive worktree was refreshed or restarted.

The warmer completed successfully at 08:11:11 UTC. Published snapshot
`snap-20260906T081109Z-ba299326ebde` has status `complete`, the exact merged SHA,
and configuration key
`ce2a00c4ed264b375191755c0044ef2d07f11c728408560ec2424e49bb328e18`.
Both `MIPStarRE/QPBT/Observables/WinImplications/Approx.olean` and
`MIPStarRE.olean` exist and are nonempty. `warmer-result.json` records verification.
This discharges the earlier cache-warming deferral; it does not remove existing
tracked proof holes or certify future consumer builds.

## Terminal Observation and Permission Hold

At 08:16:03 UTC this integration session latched queue HOLD after observing
actual `socket: operation not permitted` failures in worker GitHub requests,
then stopped only supervisor PID 4113611 after verifying its start identity.
No productive worker was signaled, no packet was renamed or retried, and no
permission setting was changed. `permission-hold.json` records this action.

All three workers completed before HOLD. Their terminal captures and handoffs
are published, the receipts bind to their original tickets, and the supervisor
released all three tickets before stopping. Session registry rows 865, 866, 867
record primary/Astra/xhigh, exit zero, and actual endings at 08:15:12, 08:15:22,
08:15:50 UTC, respectively. Queue `done` events followed at 08:15:16, 08:15:26,
08:15:52. Receipt `ts` records launch time, so it is not used as an ending time.

The workers completed local Lean checks and exact patch/blob preservation
comparisons, but every worker reported sandbox-denied GitHub access. None
integrated current main, pushed, or started new CI. A successful dispatcher
receipt therefore confirms session completion and evidence publication, not
completion of the assigned proof-publication task. The three final handoffs are
`results/telemetry/sessions/prover-{243,244,246}-20260906-02.last.md`.

No subsequent packet admission occurred after any ending: all revision-three
packets had already been admitted while capacity was available. Thus actual
admissions, useful local checks, and worker endings are observed, while
ending-triggered replacement and the eight-worker floor remain unproven.

The detached observation monitor completed after all receipts and the successful
warmer result were present. Main must disposition the access-permission failure
before changing permissions, clearing HOLD, reconciling or authorizing another
attempt. Retain the original intents, receipts, events, captures and all
preservation backups; a new packet ID must not disguise a retry.
