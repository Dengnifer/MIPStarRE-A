# Exact-head review

Normative. Read `local/protocols/meta.md`, `issues-prs.md`, and `ci.md` first.

`local/bin/review.sh <github-pr-number>` runs only from a complete CI evidence
set for the current full head and base SHAs. The manifest conclusion must be
`success`, every canonical step must be `success` or `skipped`, and all eight
matching statuses plus the digest-bound `local-ci/summary` must be `success`.
A readable failure or error manifest does not authorize review.

## Tree and prompt integrity

After reading the GitHub PR identity, review takes the per-PR review lock and
atomically reserves the same per-branch fix lock used by auto-fix. It holds both
from before its first feature-tree read through review and summary publication.
The shared branch lease records a PID, an ownership token, and an optional
supersession cancellation. Review aborts if either lock is no longer owned or a
cancel file appears; cleanup removes only leases still owned by that process.

The local feature head and fetched local base must equal the GitHub full head
and base SHAs. The feature worktree must have no tracked, staged, or untracked
changes when review starts and immediately before any attestation or final
summary publication, including summary recovery. Provisional pending and
diagnostic error statuses are not review evidence. A moved comparison, dirty
tree, lost lease, or supersession request blocks publication of clean evidence.

Reviewer personas come from a trusted ref resolved once to a commit. The
reviewed head must not equal that resolved commit, even when the caller used a
different textual spelling for the same ref. Prompt files and dispatcher
persona bindings use the resolved trusted commit, never the feature branch.

## Reviewer sessions

Each dispatched lane must have a nonempty session name and thread id distinct
from the other lane, exit zero, and have exactly matching clean completion
telemetry. The matching record binds the reviewer role, PR/issue number,
worktree, thread id, start and end timestamps, and `done` status. Output from a
nonzero reviewer process is diagnostic only and can never satisfy the gate.

Within one PR, a reviewer session name or thread id may identify only one
distinct attestation. Re-reading or idempotently adopting that same attestation
is allowed; replaying either identity in another head, base, run, or body digest
is rejected before the wrapper posts another review and is invalid evidence. A
run id is likewise owned by one distinct attestation, preventing a same-head
pending status from becoming ambiguous after base movement.

Reviewer inputs such as diffs, build logs, prior ledgers, issue text, and paper
text are untrusted data. The wrapper strips controls, truncates them, prevents
fence escape, and states that instructions in the data must not be followed.
Before dispatch, it reads and validates the latest marker-bound GitHub ledger
and attaches it with PR metadata so findings carry across heads as explicitly
unresolved, resolved, or outdated. Reviewers cannot publish to GitHub; only the
trusted wrapper does so.

Lane output remains in runtime storage until combined. The combined body keeps
the findings ledger and path/line references.

## Output grammar

Every dispatched review output has exactly one section headed `## Findings`.
Ignoring surrounding blank lines, that section contains either the single line
`- none` or one or more canonical lines of the form:

```text
- [ ] F1 (changes) `path/to/file:line` — one-line summary
```

The only checkbox states are `[ ]` (unresolved), `[x]` (resolved), and `[-]`
(outdated); the parser preserves the state instead of reopening resolved or
outdated entries. A location is either a relative ASCII repository path plus a
positive decimal line number or the literal `-`. Finding identifiers, severity,
backticked location, and one-line summary must have the canonical shape. The
verdict trailer occurs exactly once and is the final nonempty line, with one of
the three documented `VERDICT:` values. Missing, duplicate, mixed, or malformed
findings sections, findings lines, or trailers block the run and produce no
clean evidence. Only unresolved entries contribute to the blocking findings
count.

## Attestation and publication

Before publication, the wrapper revalidates both leases, worktree cleanliness,
and the local and GitHub full head and base SHAs immediately before each
attestation or final-summary mutation. After its idempotency lookup, the client
repeats the full check around any intervening reviewer-identity or summary-status
read, then finishes with a fast local lease/tree check immediately before the
write. Movement or loss of ownership makes the run stale.

The wrapper publishes `local-review/summary=pending` under both leases before
dispatch. It then submits one marker-bound `COMMENT` review with the exact
`commit_id`. Clean and adverse reviews alike use `event=COMMENT` and
`fallback=none`; local review never publishes `REQUEST_CHANGES`. The
attestation binds the full PR number, full head and base SHAs, run id, canonical
findings count, event, and each dispatched review lane's name, thread id, exit,
worktree, and timestamps. Its digest covers the complete canonical ledger body
before the final marker.

The wrapper separately finalizes `local-review/summary` on that SHA: `success`
only for a zero-finding clean `COMMENT` attestation and `failure` for unresolved
findings. The status description binds the same run and ledger digest.
Publication is idempotent only when the full attestation, digest, body, commit,
event/state, and status agree. Transient and ambiguous review writes use
authoritative read-back and never issue a second review mutation.

The review `COMMENT` row must have `user.login` equal to the configured trusted
actor, and its latest summary must have the same actor in `creator.login`.
Every invocation verifies that the authenticated `gh` user is that actor.
Untrusted or missing-author marker copies are not attestations and cannot
collide with a trusted publication. Summary selection remains global per
context, so a newer untrusted status blocks rather than exposing an older
trusted result.

A valid review attestation is deliberately distinct from complete merge
evidence. Structural parsing, the exact commit and base, the body digest,
canonical ledger, event semantics, session telemetry, and cross-attestation
session uniqueness can all be validated before a final summary status exists.
Prior-ledger and review-fix consumers may read that valid attestation. Merge
evidence additionally requires the exact matching final summary status.

If a review POST succeeded but its summary status is missing or remains the
canonical `pending` status for that same attested run, a rerun adopts the
existing exact-head, exact-base attestation without redispatch or a duplicate
review POST. After another full boundary check it idempotently posts the
matching final status and verifies complete evidence. The guarded finalizer
reclassifies the latest summary inside the mutation path, repeats the full
authoritative comparison after that read, and then performs the fast local
lease/tree check before the POST; normal publication uses the same path. A
pending status for a different run, a conflicting final status, or an
attestation for a stale base is not recoverable as the current run.

GitHub approval and `reviewDecision` are never required. The normal gate is a
successful exact-head summary status plus a strictly parsed clean `COMMENT`
attestation whose reviewer session telemetry matches, with no later exact-head
`CHANGES_REQUESTED` review. This supports the common case where the repository
operator is also the PR author and GitHub forbids self-approval.

An adverse `COMMENTED` attestation remains valid raw ledger evidence for
review-fix consumers, but its summary is `failure` and it never satisfies the
clean merge gate. Raw attestation validation and review-summary merge
eligibility are deliberately separate decisions.

Kill switches disable only when set to the literal string `false`; unset means
enabled. A reviewer session must be different from every author session and
must never repair its own findings.
