# Permission change across goal continuation

Observed on2026-09-07 in legacy reviewed thread
`01a0760d-31c7-7200-964d-29437ee7febe`.

The user selected full access using `/permission`. The session's persisted
`turn_context` records show:

| UTC | Sandbox | Approval policy | Reviewer |
| --- | --- | --- | --- |
| 04:39:04.553 | workspace-write | on-request | user |
| 04:54:30.674 | danger-full-access | never | user |
| 05:15:31.404 | workspace-write | on-request | user |

The final row is the subsequent automatic goal continuation. The setting
therefore changed between turns; the full-access selection did apply to the
intervening user turn. The cause of the later replacement has not been verified
in the CLI implementation. This evidence does not justify changing credentials,
editing saved permission settings, disabling approval controls, or replaying a
previously rejected operation. The prior assurance that no further approvals
would be requested described the then-current policy, not a durable correction.

Source: the selected permission fields from the local rollout named
`rollout-2026-09-06T17-29-31-01a0760d-31c7-7200-964d-29437ee7febe.jsonl`.
No raw conversation stream, authentication material or private configuration is
included. Sandbox access and approval policy are separately documented in the
[official Codex security reference](https://learn.chatgpt.com/docs/security).

## Current project boundary

The project migrated to native main
`01a076bc-f4ad-7813-805b-c8b4dac71a14`. Its current committed owner instructions
select Space, literal Astra Ultra, five total sessions, four native descendants
and zero external admissions. They supersede the older relay/Max/Xhigh settings
embedded in this retained goal. This thread has no native delegation tools.

The last known native lease still names PID1792844/start174304094. An approved
exact-PID check on2026-09-07 found that PID absent; the lease was not released or
replaced. The broader canonical census failed on a protected process environment,
so native occupancy remains unknown. Merge-service PID2178864 was observed live.
Its completed05:17:52.537585Z tick reported dirty primary and no fresh exact-head
CI/review candidate, with local and remote main both
`0efa4ecb7abc50343705e2fd245df71c6e12c59d`.

No second worker pool, legacy author retry, new effort probe, permission change
or merge attempt was started. The completed diagnostic results and two requested
owner receipts were incorporated as new local telemetry files. Existing changes
to estimates.jsonl were left untouched. At incorporation time, normal telemetry
commit/publication and native coordinator recovery remained outstanding; that
incorporation operation made no GitHub publication.
