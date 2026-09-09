## Owner concurrency boundary — three independent lanes active

Verified on ghz at 2026-09-06T01:28:21Z: **3 project workers of 8 available**, plus main
and three other primary-home interactive uses: **7 of the 12 relay slots**.
All three actual Codex processes request primary gpt-6-astra and literal
`model_reasoning_effort="max"`; fan-out is disabled. No secondary/Sol project
session is live, and the existing PR238 worker was not interrupted.

- **PR238 / issue237:** `orc-237-20260906-02`, supervisor2326711, continues the
  bounded routing/effort implementation and normal publication/CI gates.
  The installed versioned shim already enforces max. Independent mathematics
  does not wait for this PR's completion or review.
- **PR195 / issue113:** `orc-113-20260906-07`, supervisor2384295, starts from
  `f1d1d3c7` for current-base conflict recovery, checked publication, exact-head
  CI, and a factual delta manifest for terminal operator disposition. The
  **four-full-review cap remains**: no fifth review or extra triage lane.
- **Issue118:** `mathfix-118-20260906-08`, supervisor2384296, continues from
  `cd1815e1` on scalar specialization, line-witness assembly, and Apply.
  **Attempt8/10 carries12452 seconds**; the original September 5, 19:24 UTC
  anchor is unchanged. This is a fresh primary continuation, not a resume of
  the old secondary thread. Its old dispatcher guard uses a legacy caller
  spelling, but an offline argument test and the actual client process both
  verify literal max; no provider probe or false effort/account claim is used.

Binding downstream dependencies were read from GitHub: issue115 / PR207 has
only issue113 still open; issue116 / PR213 and issue117 / PR212 each have only
issue115 still open. Advance PR207 **after PR195 actually merges**, then run
PR213 and PR212 tails concurrently **after PR207 actually merges**, checking
ownership and dependencies again. No downstream tail was started in advance.

Verified primary/max daemon2339019 and stack watcher2339020 remain running.
Normal CI/review and daemon-only merges remain mandatory. Spare capacity is
reserved for useful work, not filled merely to reach a worker-count target.
