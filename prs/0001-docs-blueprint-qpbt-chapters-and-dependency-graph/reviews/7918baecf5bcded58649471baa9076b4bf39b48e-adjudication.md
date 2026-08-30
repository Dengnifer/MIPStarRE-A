---
pr: 0001
kind: adjudication
branch: issue-0002-qpbt-blueprint
head_sha: 7918baecf5bcded58649471baa9076b4bf39b48e
verdict: ADJUDICATED
review_state: ADJUDICATED
basis: round-6 reviews at 39753e7304367b108d60e2a886fbb4349e0fc785 (code + prose)
protocol: local/protocols/review.md section 12 (round cap reached: 6 full rounds)
generated: 2026-08-30T17:00:40Z
---

# Adjudication — PR 0001 @ 7918baecf5bc

Operator adjudication under review.md §12 after six full review rounds
(finding counts 33, 26, 18, 12, 17, 15; see results/telemetry/events.md).
Dispositions of every round-6 finding:

## Findings

<!-- findings:begin -->
- [x] code-F1 (simeq vs approx on lem:ld-soundness) — fixed in 6749bd5: restored the source's two-sided consistency relations (def:consistency), vacuous-regime bound rederived.
- [x] code-F2 (def:ld-meas representative vs function outcomes) — deferred to issue #0004: encoding decision belongs to the stage-4 Lean design; the correspondence is stated precisely at def:polynomials-degree.
- [x] code-F3 (gap bib entries use repository paths) — moot: sanctioned local convention, ledgered in local/protocols/EVOLUTION.md ("Paper-gap bibliography entries cite repository paths") and noted at the entries.
- [x] code-F4 (EVOLUTION records an unimplemented amendment) — moot at this head: the round-cap amendment, review.md §12, and pr_merge.py --adjudicated are committed (main a3df2c1, merged here in 7918bae).
- [x] prose-F1 (final proof understates open dependencies) — fixed in 6749bd5: all four obligations named with their gap-note citations.
- [x] prose-F2 (transfer lemma vague quantification) — fixed in 6749bd5: restated over explicit permutation data and marked \notready.
- [x] prose-F3 (d <= q-1 claim contradicts the general theorem) — fixed in 6749bd5: scoped to the canonical parameters; general statements read through the representative convention.
- [x] prose-F4 (derived identities inside expanded-measurement definitions) — deferred to issue #0005: node-splitting restructure, tracked.
- [x] prose-F5 (missing \uses def:approx-question-indexed-operators) — fixed in 6749bd5.
- [x] prose-F6 (missing \uses def:strategy-observables) — fixed in 6749bd5.
- [x] prose-F7 (missing \uses def:povm-distance, ch15) — fixed in 6749bd5.
- [x] prose-F8 (basis-fixing definition uncited, ch16) — fixed in 6749bd5: def:binary-representation cited and used.
- [x] prose-F9 (Naimark completion not in \uses) — fixed in 6749bd5: completion described inline; remarks are not \uses targets by house rule.
- [x] prose-F10 (process language in the import proof) — fixed in 6749bd5.
- [x] prose-F11 (graph jargon in comments) — fixed in 6749bd5: three comments cleaned.
<!-- findings:end -->

## Verdict

VERDICT: ADJUDICATED
