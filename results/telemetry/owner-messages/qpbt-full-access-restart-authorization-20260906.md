# Owner authorization and restart checkpoint

Owner message states receipt at 2026-09-06T10:33Z; recorded by reviewed main
around10:38Z, thread `01a0760d-31c7-7200-964d-29437ee7febe`.

The owner explicitly authorizes meta to restart qpbt-main in full-access mode on
ghz and qpbt-main to use that mode for assigned Track A workers. Existing project
scope, credential, proof-integrity, review and merge restrictions remain. Safety
monitoring remains enabled. This supersedes the temporary sandboxed-restart
limit. Meta performs the same-thread process restart with primary relay/Astra
max and fresh auth; main retains all assignment decisions afterward.

Main checkpoints and yields at the requested safe boundary. The outgoing
process still uses workspace-write and specific supported approval requests;
it has not changed credentials, accounts, permissions or monitoring. Existing
workers, three live normal pipeline controllers, worktrees and telemetry
artifacts are preserved. Checkpoint:
`/tmp/qpbt-main-checkpoint-20260906T1038Z.md`.

At the10:37:53Z census, B8 attempt13 was the sole live model worker. Controllers
474635 (PR207 CI/review),474968 (issue278 publication) and475810 (issue279
publication) were live. They are not counted toward the model-worker floor.
The goal remains active, with floor8/target11 and durable queue recovery unmet.

An independent automatic-approval decision rejected the proposed #27 recovery
checkpoint publication for potential disclosure of internal operational state.
No post or substitute retry occurred. The proposed body and decision details
are preserved in the checkpoint; the restart does not erase that rejection.
