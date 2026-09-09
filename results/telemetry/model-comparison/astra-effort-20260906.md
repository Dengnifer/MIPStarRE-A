# Astra effort: initial useful-work observations, September 6, 2026

This is an observational baseline, not an effort benchmark or a causal result.
The [dataset](astra-effort-20260906.json) contains **two terminal review attempts,
two threads, one task (PR238 review), and no included resumes**. One client
context records `xhigh`, the other `max`; **0/2 project runs have recorded
completion effort or server-effective verification**. Configured effort and the
original selection rationale are unknown for both. Client context is not a wire
capture or evidence of backend computation. No verified project-run max-versus-
xhigh quality comparison is yet possible.

## Selection and provenance

The bounded selection consists of the first two PR238 review attempts with
committed primary-checkout captures and final reports, not a sample of all Astra
work. Both are primary/`gpt-6-astra`, role `reviewer`, and concern different heads
of the same workflow PR. There are no selected implementation, proof or mathfix
tasks. Source tree: `a9122d7297bd75b5d7bf2e640601c3c9b507b87b` in the primary
checkout; some linked sources are newer than this branch's `a61ee55` base.

- `xhigh`: [capture](../sessions/reviewer-pr238-20260906-01.jsonl),
  [final report](../sessions/reviewer-pr238-20260906-01.last.md),
  [registry](../sessions.jsonl), row 712 at collection, identified by full session
  name `reviewer-pr238-20260906-01` and its thread ID in the dataset.
- `max`: [capture](../sessions/reviewer-pr238-20260906-02.jsonl),
  [final report](../sessions/reviewer-pr238-20260906-02.last.md), registry row 719,
  session `reviewer-pr238-20260906-02`.

The JSON preserves public artifact SHA-256 hashes, exact terminal-usage and
validation line numbers, and private rollout paths/hashes with the one relevant
`turn_context` timestamp/line and effort value. Only this small field extraction
is retained; no private debug log, credential or owner-session row is imported.
The committed captures do not independently expose the client effort field.

## Observed outcomes, not quality rankings

| Client context (n=1 each) | Wall seconds | Input / cached subset | Output / reasoning subset | Review artifact |
| --- | ---: | ---: | ---: | --- |
| `xhigh` | 327 | 1,623,842 / 1,537,920 | 5,151 / 2,770 | APPROVED; 0 findings |
| `max` | 951 | 1,945,108 / 1,734,784 | 18,865 / 14,149 | CHANGES_REQUESTED; 4 findings |

The first review examines initial effort normalization at `954c1bc004aae12cfff60a8a27b8eac6259f5327`.
It records 28 passing targeted workflow tests (8.337 seconds), two shell syntax
checks and whitespace validation. The second examines a broader 1,466-line
continuation/admission/shim patch at `2e6b1441f8662f4f6c716b5f5756b3cc5276950e`.
It records two passing read-only-compatible tests (0.059 seconds), four shell
syntax checks, Python parsing, whitespace checks and four concrete reproductions.
Its full regression suite was not rerun because fixtures required writes.
These difficulty descriptions are curator judgments, not calibrated scores.

These are independent reviewers' artifacts, not this curator reviewing its own
diff. Findings are outcomes, not established precision/recall: false positives
and missed defects are unknown. Zero findings do not establish completeness.
Terminal usage and review artifacts exist for 2/2 attempts; targeted Lean proof
validation samples and independently checked exact-head CI statuses are both 0.
No green CI or published review status is inferred from exit code 0. Read-only
`gh_common.py pr-view 238` observed the PR open and unmerged at 03:54:46Z, with
current head `64be227d6d95ddb625db980416bde68c45de9c67`, not either reviewed head.

Count each named canonical registry attempt once. Do not add its capture's
terminal usage again, or import duplicated owner-message probe/helper rows.
Input already includes cached input; reasoning is an output subset. Resumes and
later review heads are attempts of the same task, not independent replicates;
do not reuse cumulative same-thread totals as new attempt usage. This xhigh
curation continuation (`orc-247-20260906-02`) is excluded while terminal usage
and outcome are unavailable, even though its thread contains an earlier max turn.
Null denotes unknown, not zero. Both captures contain one model-metadata fallback
warning and no structured reconnect event; actual retry counts and retry,
compaction, service and build-lock delays are unmeasured. Cache warmth is unknown.
Patch size/difficulty, validation scope, context/cache mix, tool access and
service/build waits confound latency and quality; do not infer an effort effect.

## Six historical configuration probes, zero project-quality samples

The [sanitized probe records](../owner-messages/qpbt-meta-20260905-230133/effort-probes.json)
and [verification note](../owner-messages/qpbt-meta-20260905-230133/effort-verification.md)
record CLI 0.152.1 fresh ephemeral requests on September 5, 2026, at
23:19:44–23:22:20Z: **six probes total, three per account, one per account/effort**.
Requested/client `ultra` has completion `medium` in 2/2 probes; requested/client
`max` has completion `max` in 2/2; requested/client `xhigh` has completion `xhigh`
in 2/2. Wire transmission and backend computation remain unknown. Probes are
excluded from both the two-attempt project denominator and project-quality claims.
They neither relabel every historical Sol/Astra run nor establish equal effort
in the historical [comparison](latest.md). No new probe was run for this report.

## Selection guidance and integration boundary

The immutable [owner priority](owner-priority-20260906.md) records the
03:36:00Z research decision. Main stays max and selects max or xhigh for each
new/resumed primary Astra worker; the owner's latest "high" means xhigh.
Selection remains main's judgment by role, difficulty, observed quality and
latency, not a ranking established by these two reviews. Record the choice and
rationale at admission; append useful terminal outcomes with the same provenance,
unknowns and task/attempt distinction. Refine guidance through normal reviewed
documentation and EVOLUTION, without benchmark/filler sessions or budget resets.

The [effort/admission record](../owner-messages/qpbt-effort-admission-20260906.md)
and [relay incident](../owner-messages/qpbt-meta-20260905-230133/relay-throughput-limit-incident.json)
explain the temporary replenishment hold while preserving the eleven-worker
allocation and standing 8–11 useful-worker floor. Its six-client recovery limit
was an operational decision, not a measured server request cap. Do not attribute
that later incident's delays to these earlier reviews. The
[role correction](../owner-messages/qpbt-meta-20260905-230133/owner-meta-boundary-correction.json)
keeps meta guidance-only; all posted #26 items, including B7, await the human.

The [README](README.md) still makes the universal ultra claim in the inspected
primary snapshot. Issue237's sole author owns its narrow correction and runtime
enforcement; this report does not modify those files or historical reports.
Main must check that the correction survives integration, reconciling overlapping
main-persona/issues-prs edits **only after PR238 actually merges**. No unmerged
implementation is imported or assumed effective. The owner priority, admission
record and relay incident exist in primary but were not yet committed at
collection: their relative links need main's normal telemetry preservation and
publication, not copies or rewrites by this lane. The newer review captures and
role correction are already committed in primary. No publication, CI, new review,
merge or main installation is performed by this curation session.
