# Design decisions register (track A, QPBT)

One line per owner or operator design choice that shaped the workflow, newest last. Each entry
points to the primary record (owner-log.md, events.md, an issue or a PR). This file is the
index for the research paper on self-evolving formalization workflows; keep entries short and
add the long reasoning to the pointed record.

| date (UTC) | decision | who | rationale (short) | record |
|---|---|---|---|---|
| 2026-09-03 23:11 | Mode 2: the owner's Claude session operates the loop over ssh; codex workers stay on ghz via dispatch.sh; watchdog nudges through #26 | owner | eight-hour stall and reviewer churn under the codex main session | owner-log 2026-09-03, stages.jsonl event=takeover |
| 2026-09-04 ~05:00 | Merge daemon: every CI-green, review-clean (or adjudicated) PR is merged automatically after a fresh-base refresh; no manual pr_merge | operator | merge latency was the fresh-base gate, not conflicts | owner-tools/merge-daemon.sh, owner-log |
| 2026-09-04 ~07:00 | Stacked packets: branch from the prerequisite PR branch, register in stacks, re-review when the base lands | operator | dependency chains otherwise serialize the whole chapter | owner-log 07:25Z, 08:35Z; EVOLUTION.md |
| 2026-09-04 08:15 | Level 2: Claude subagents as a second prover pool over ssh, telemetry in owner-sessions.jsonl | owner | codex concurrency alone left the machine idle | owner-log, qpbt-operator-modes memory |
| 2026-09-04 11:05 | No Fable provers; Opus and codex 1:1; codex saturates its share | owner | Fable budget reserved for orchestration | owner-log 11:05Z |
| 2026-09-04 12:05 | 8-hourly completion estimate (percent implemented, days to go) on pinned #168, two lines | owner | owner wants two numbers, quickly | ~/bin/estimate.sh, estimates.jsonl |
| 2026-09-04 12:14 | Packet tree: chapter parents under #47, GitHub blocked_by edges, ready_packets.py | owner+operator | learned from LionSR/MIPStarRE #449 | #159, PR 171, EVOLUTION.md |
| 2026-09-04 12:58 | Every source-paper gap (wrong mathematics) is recorded as a paper-gap note and fixed in the blueprint (proof-gap protocol) | owner | gaps are research data; no silent drift | #172, #173/PR 184, register qpbt-gap-register.md |
| 2026-09-04 13:03 | Owner inbox #26: only decisions the human owner must make; operator never decides a posted item; BLOCKER/DECISION format, outdated comments hidden | owner | #26 unreadable otherwise; owner authority over source-level changes | #26 body, owner-log 15:20Z |
| 2026-09-04 14:59 | Track B discarded; track A uses the full codex concurrency of 10 | owner | one track | owner-log 14:59Z |
| 2026-09-04 15:26 | B4/B5: Magic Square rigidity restricted to symmetric and consistent strategies (A′, latitude for A″), #115 routed to #103's anticommutation theorem | owner | theorem false as printed; section 14 needs only anticommutation | #26 B4/B5, #105, #172 |
| 2026-09-04 15:55 | Build products on the NVMe pool /data (per-worktree .lake symlinks, store and hot-main moved) | owner (go) | root volume 9x slower for fsync writes and filling | owner-log 15:55Z, #190 |
| 2026-09-04 17:25 | Merge daemon v6 re-reads the adjudication list every loop; adjudication templates per PR | operator | v5 silently skipped PRs adjudicated after start-up | owner-log 17:25Z |
| 2026-09-04 22:10 | Mode 2 again; subagents codex : Opus : Fable = 5:5:2 (Fable provers allowed again) | owner | throughput; Fable for the hardest analytic packets | owner-log 22:45Z |
| 2026-09-04 22:35 | Math-gap rule: a Fable/astra math-fix session finds a correct and sufficient corrected statement first, iterating with Lean; #26 only if it does not converge (10 sessions or 1.5 working days) | owner (defaults by operator, confirmed 23:05) | #26 reserved for human decisions; the fleet resolves mathematics itself | #26 body, events.md 2026-09-04, owner-log 22:35Z |
| 2026-09-05 00:35 | Subagent ratio codex : Opus : Fable = 5:5:1 (was 5:5:2); running tasks continue | owner | Fable budget; Opus carries provers, repairs and pre-reviews | owner-log 00:35Z |
