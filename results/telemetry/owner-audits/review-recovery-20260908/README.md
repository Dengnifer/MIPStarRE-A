# Combined native-review recovery, 2026-09-08

This archive preserves the exact evidence for deploying the paired CODE/PROSE
native-review continuation in PR #476 and using it once on the two completed
PR #400 responses whose original publisher had terminated.

PR #476 passed one canonical CI run at exact head
`4c343e6c88b7714a3bbf121b3dc23839df303e3e`, with all nine contexts green,
then received independent hard review approval `5147206622`. The service gate
merged it as `81148545f0752ec09b3efe88332b49bb771312be`. A later attempted CI
launch was refused by the existing canonical lock before it started jobs or
wrote statuses; it was not a second CI run.

The service boundary parked five build rows and four session rows while holding
only the actual JSONL inode locks. It released both locks before service, then
restored the parked rows ahead of later appends with the same inodes, exact
prefixes, order, multiplicity, and valid JSON. No global writer-idle wait or
clean-tree gate relaxation was used.

After the merge, the archived command consumed the preserved PR #400 CODE and
PROSE responses through the deployed trust, parser, combiner, head, CI, lock,
and publication guards. Canonical review `5147250926` recorded two CODE and
five PROSE findings. No review was restarted, no response was edited, and the
source worktree remained unchanged. PR #400 is therefore not merge eligible.
The isolated repair commit `06583ccc58b1a9077a4cd330d3f3749e1979c081`
and its byte-preserving compressed patch are evidence for the next normal
checked-publication, CI, and fresh-review cycle; they are not recorded as
merged source. The uncompressed patch SHA-256 remains
`1a8d7b6dc97b527daf30058e980a08cf71b23aefb97cd03daedc0ce8008cacdc`.

`qpbt-pr371-single-lane-resume-predecessor-status-20260908.json` is retained as
the predecessor single-lane deployment record. It is historical context rather
than a PR #476 completion receipt.

`qpbt-review-lifecycle-all-ready-20260909.json` is the 21:54:17Z read-only
reconciliation of the 19 canonical review requests created after PR #426
merged. Its timestamps keep their original precision, including the PR #476
file-time correction; five known reviewer starts are populated and unknown
consumer or other lifecycle endpoints remain null. The earlier 21:48:35Z
snapshot is retained separately rather than overwritten. Neither file is a
selected-window occupancy or acceptance claim.

`qpbt-pr476-postmerge-telemetry-index-boundary-20260908.json` records the
short same-inode lock used to validate and stage the 855-row build and
1,045-row session prefixes. Locks were released before commit hooks or network
work; later automatic appends remain a separate suffix. The lifecycle
reconciliation update followed that boundary and did not alter either JSONL
prefix.

The project allocation, model policy, goal, proof budgets, and B8 history were
not reset. B8 remains 13 attempts and 26,509 working seconds, not tokens.
