# Implementation brief - resume completed native review publication

Issue #366 repairs one workflow failure observed on PR #358. A native reviewer
may finish after the `review.sh` process that created its request has exited.
The nonce-bound response remains canonical, but the only supported entry point
currently creates a replacement request before reaching the parser.

Add `review.sh PR --resume-native-request REQUEST` for a completed native code
lane whose current diff does not touch `blueprint/`. The continuation must take
the existing per-PR lock without waiting behind a live publisher, recheck green
exact-head CI and absence of review evidence, rebuild the original prompt, and
match the request's full identity, author exclusions, model/Ultra policy, prompt
digest, clean worktree and current direct-root rollout. It then uses the existing
parser, ledger combiner, final-head check and `gh_common.py` publisher.

The resume path creates no request and invokes no model. It rejects queued or
dry-run operation, prose-lane combinations, stale or noncanonical mailbox data,
identity/policy/digest mismatches, prior publication, and live lock conflicts.
No production response is consumed until this change passes normal CI,
independent hard review, and service merge.

Evidence: `/tmp/qpbt-pr358-publication-action-status-20260908.json` and
`/tmp/qpbt-pr358-format-consumer-status-20260908.json`.
