## Owner mode boundary — primary relay / Astra max

Observed 2026-09-06T01:03:31Z on ghz. Owner-approved access is restored; the earlier
permission blocker is resolved without deleting credentials or session history.

- Every new project dispatch is explicitly primary, gpt-6-astra, literal max;
  automatic Codex fan-out stays disabled. One worker is live:
  `orc-237-20260906-02`, dispatcher PID2326711, thread
  `01a0743a-7924-7f21-a0fd-2936af092d6c`; host arguments verify primary/max.
- Relay limit is 12 including main. Three other interactive primary-home
  sessions are conservatively reserved and left untouched, so the current
  worker ceiling is **8**, not 11. Old 19/10/9 settings are preserved for an
  explicit future owner switch to both. No secondary/Sol project worker remains.
- The old issue237 Sol worker, issue113 secondary recovery, and issue118
  secondary attempt7 all finished through dispatch accounting. Attempt7
  preserves commit `cd1815e1`; final duration 2600 seconds brings the shared
  budget to **12452 seconds across 7/10 attempts**, anchor September 5,
  19:24 UTC unchanged. Its construction increment is recorded; no final source
  correction is adopted, and scalar specialization / Apply remain open.
- At 01:04:50 UTC the two project supervisors were restarted after verified
  termination of their old handles: daemon PID2339019, stack watcher
  PID2339020. Both environments explicitly select primary and Astra/max for
  worker, reviewer, and fixer paths. PR238's bounded worker owns the existing merge
  conflict plus reviewed mode/timeout/resume/effort changes and versioned
  runtime mitigation. Persistent fail-closed routing is **not yet merged**.
  Normal exact-head CI and independent review follow; only the daemon merges.
- PR195 recovery is published at `f1d1d3c7`; terminal gating still needs an
  exact-head disposition without resetting its fourth-round cap. Next
  critical chain remains PR195 -> PR207 -> PR213/PR212 -> issue118/issue156.

Meta remains oversight only. No new provider probes, extra triage review,
manual merge, or mathematical budget reset.
