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
