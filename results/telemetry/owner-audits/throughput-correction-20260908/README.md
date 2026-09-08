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
