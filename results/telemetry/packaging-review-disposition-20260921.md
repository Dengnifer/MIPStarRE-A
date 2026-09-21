# Packaging review disposition, 2026-09-21

At 11:53:09 UTC MAIN recorded the result of PR 659's fifth full independent
review, [5266220034](https://github.com/Dengnifer/MIPStarRE-A/pull/659#pullrequestreview-5266220034),
bound to `bcb03dab6152b9828d794d44ea307055b2503502`. Its verdict is
`CHANGES_REQUESTED`, with one unchecked finding. MAIN posted and read back the
adverse review status through the normal gate; no approval or merge occurred.

The reviewer independently reproduced a remaining allowance defect:
`reviewer@example.com.private-mail.net` was treated as an allowed placeholder
in normal packaging and in anonymized output containing both that address and
the configured contact. A substring test for `@example.com` does not establish
that the complete email domain is the reserved example domain. The scanner's
contract therefore is not met by the reviewed implementation.

The fifth reviewer confirmed the earlier generic contact-allowance repair,
literal and escaped identity handling, references inclusion, and the qualified
872/873/49/922 file-count evidence. Twenty focused tests passed, and independent
normal and anonymized no-PDF snapshots each contained 873 files. These checks
do not excuse the newly reproduced defect. Reviewer thread
`01a0c3c0-a32e-73d2-a0ba-4038cd02fb47` was closed after 826.519 seconds; its
actual usage and all five prior review rounds remain in `sessions.jsonl`.

## Bounded Decision

The owner's 2026-09-09 08:40/08:50 UTC instructions explicitly delegate
project-only review exceptions to MAIN, with a decision record and a report
on issue 27. Current space-3-only and single-delegate restrictions remain
unchanged. The earlier one-additional-review decision did not authorize an
automatic further round. MAIN now makes this separate decision based on the
concrete fifth-review result:

- Authorize one repair of at most 15 working minutes. Limit it to the complete
  matched-address boundary for the existing placeholder allowance, regression
  cases for normal and anonymized mixed-address output, and any count or
  provenance updates actually required after refreshing reviewed main changes.
  Preserve the current contract, references, configured-contact behavior and
  identity checks. No new filtering framework, feature, source-proof change,
  hook bypass or unrelated cleanup is authorized.
- After the concrete repaired commit has complete green canonical CI, authorize
  one fresh independent verification of at most 10 working minutes. Examine
  the repair and its consequences using the five retained full reviews as
  evidence for unchanged content. Publish actual scope and an exact-head
  verdict honestly. Count this as the sixth review observation, not a carry,
  reset, replacement for earlier costs or a fictitious fifth round.
- Every finding remains blocking until verified fixed. A changed patch cannot
  inherit approval merely from old reviews. No seventh review or additional
  repair loop is automatically authorized. MAIN must assess any further result
  separately, without weakening artifact readiness or any merge requirement.

This is task preparation, not admission. PR 663's independent reviewer
`01a0c3ce-4976-7230-a7f8-35f5ccaf53ac` is the sole current native delegate.
It started at 11:51:11.535 UTC with a 25-minute budget after MAIN rechecked the
clean published head, all nine CI contexts and the 1837-declaration blueprint
axiom audit. PR 659 repair waits for the sole slot and its fix claim.

## Comparator Follow-up

The operator also read the separate `Dengnifer/QPBT-comparator` repository.
Its dirty four-target working copy still pins the historical library commit
`a942ecb56fd25933da51286070ddc615609edc76`; GitHub reports no registered
workflow, run or open PR. The draft branch's workflow supports pull requests
and dispatch, but a draft-branch push alone is not an official verification
run. Preserve the worktree and use a coherent current-source candidate before
running comparison. The final official acceptance record remains absent.
