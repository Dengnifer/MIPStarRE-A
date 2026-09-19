---
title: "Historical PR 534 CI fixture event"
date: 2026-09-18
purpose: >
  Archive the original 17 added lines of the PR 534 telemetry event without
  inserting an out-of-order entry into the current events log.
status: historical
track: qpbt
kind: event-archive
origin: "PR #534 head 7042717ee89edf398ea40da3a19fe5bd4dbcd5c2"
issue: "#515"
pr: "#534"
---

The entry below is historical, not a new CI run. It describes a failure and
its fixture-level diagnosis, not an approval. The attempted remedy is not a
fresh CI result for this preservation. The old review findings remain adverse;
the corresponding stale prose was subsequently corrected on main. This
archive does not change `results/telemetry/events.md` or renew any proof
budget. The original 17 lines follow verbatim.

## 2026-09-12T05:37Z - Issue 515 CI fixture environment

- Session `prover-515-20260912-01`, PR #534, proof commit
  `b863c71da99ee766d1d3c520a9ea5519771e216e`: the first exact-head CI passed
  the build, blueprint render, paper-gap, file-length, proof-debt, and
  proof-evasion gates, but blueprint-sync failed in one of 629 test fixtures.
  The model-policy dispatch fixture inherited `MIPSTARRE_HARDNESS_REASON`
  from the prover session and rejected its deliberately bounded job with
  "an escalation reason requires a hard job classification". The invoking,
  review, and prose model settings had already been unset. Clearing
  `MIPSTARRE_JOB_CLASS` and `MIPSTARRE_HARDNESS_REASON` as well makes the exact
  failing test pass. No workflow or fixture code is changed, and no real
  agent is launched by the dry-run fixture. The first CI log, failing fixture
  log, and manifest are preserved in
  `~/.cache/mipstarre-dev/sessions/prover-515-ci-first/`. Rerun ordinary CI
  with all five settings scrubbed; preserve this failed attempt in the record.

## End of historical excerpt
