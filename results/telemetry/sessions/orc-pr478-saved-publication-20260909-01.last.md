Publication recovery completed on September 9, 2026.

- PR 478 GitHub head is `3bf858285397a25468fc4bcbd86d036425740b11`.
- Both ordinary graph-repair merges passed pending and committed `merge_loss_guard` checks.
- Saved repair commits and tracked obligations remain intact; no semantic edits, rebase, force push, or main push occurred.
- Canonical exact-head CI passed all nine `local-ci/*` contexts under the full-build lock. [CI manifest](/home/drx/.cache/mipstarre-dev/ci-manifests/pr478-3bf858285397a25468fc4bcbd86d036425740b11.json)
- Independent review and subsequent release were handed off through updated PR comment `5599132422`. [Handoff note](/home/drx/.cache/mipstarre-dev/prover-474-review-handoff.md)

Current `main` later advanced to `71b3bff5`, but the graph remains unambiguous with sole merge base `aa45ea71`. Release must perform its normal current-base check. B8 remains parked and the two documented obligations are unchanged.