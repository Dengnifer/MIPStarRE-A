# Throughput measurement correction, 2026-09-08

This directory preserves the bounded owner throughput diagnosis and the
contemporaneous meta-watch state used by the primary integration coordinator.

The `51/170` observation counts recorded in the audit are worker-lifecycle
checks. They are not a percentage of elapsed time and are not measurements of
simultaneous provider API requests. The owner's separate dashboard observation
was 6--8 API requests; direct current API telemetry was unavailable.

The meta-watch snapshot records four new Sol Ultra proof-construction lanes:
issues #367 (line-polynomial proofs), #368 (individual-degree proof), #369
(extended-point specification), and #370 (tilde-measurement algebra). At this
boundary their work was not merged into `main`. In particular, the two closures
published in PR #372 and the closure published in PR #374 do not reduce the
recorded main-branch count of 47 QPBT `sorry` tokens until normal CI, review,
and service gates complete.

The 95% floor and 90% coverage thresholds in the meta-watch state are a meta
interpretation for a sustained observation window, not API utilization claims
or changes to the owner allocation. The allocation remains total 10, main 1,
native worker slots 9, useful-worker floor 8, and external 0.

The later 14:00 snapshot corrects the same-period denominator again: after
excluding queue-alert records, 51 of 139 snapshots were at the worker floor.
These are still change-only observations, not an elapsed-time fraction or a
measurement of provider API concurrency. It also records the subsequent proof
deliveries and the fact that their tracked closures remained unmerged at that
snapshot.

The PR #371 disposition preserves the original two-hour workflow interval and
the temporary post-boundary hold. Under the standing owner decision recorded in
issue #26 comment 5557148036, main granted a bounded, no-reset extension from
13:57:30Z through 14:27:30Z for the already reviewed merge and guarded resume
verification only. No source growth, new feature work, or gate relaxation was
authorized.

The 14:56:42Z watch snapshot remains an observational artifact, not a provider
utilization certificate. The main-control receipt records one completion-to-next-
turn latency and a later 185.063-second control-pass overrun without rewriting
the earlier lifecycle samples. PR #372 subsequently merged through its normal
exact-head gates; the unmerged and merged closure counts therefore remain
separate observations at their respective timestamps.

The 15:31:49Z snapshot further clarifies that fresh attributable output is a
lower bound on productive activity, not a count of empty runtime slots. Occupied
native slots, fresh output, and the owner's separate provider-dashboard range of
6--8 requests remain distinct quantities; quietness alone is not vacancy
evidence. Newly published proof packets such as PRs #398 and #401 remain
unmerged observations until their ordinary CI, review, and service gates finish.

The 16:33:44Z snapshot and successor receipt preserve the same distinction at
the next service boundary. The successor list is an authorized readiness plan,
not a set of occupied slots, and `/root/astra_refill_coordinator` remains the
only demonstrated native refill operator. The accompanying meta-guidance input
records delivery to main without claiming that its requested retirement audit
was completed.

The Claim 17-2 domain report is a read-only mathematical audit, not a merged or
kernel-certified correction. It proposes a countermodel to the enlarged public
witness domain and explicitly records that no Lean instantiation, source edit,
or canonical review was performed. Main retains adjudication of that proposal;
the archive does not treat it as a verified source theorem or a completed proof
closure.

The post-merge PR #426 sample records one genuinely prevalidated successor.
The issue #422 payload was ready 751.310 seconds before the PR #365 predecessor
completed, but the new task started 63.076 seconds after completion and therefore
missed the strict 60-second target by 3.076 seconds. Its first attributable
source read followed completion by 110.070 seconds. This is a failed acceptance
sample, not a coverage or sustained-occupancy certificate; the earlier 294.078-
and 354.659-second failures remain unchanged.

The separate PR #448 routing incident preserves two independent steering
errors: a head was misidentified as the required mixed bound, and a follow-up
message reached an already occupied actor. Neither event created a new admission
or budget. The original actor scope and deadline remained in force, and no
source statement, review gate, capacity, model policy, or B8 history changed.
