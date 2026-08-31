# Exact-head review

Normative. Read `local/protocols/meta.md`, `issues-prs.md`, and `ci.md` first.

`local/bin/review.sh <github-pr-number>` runs only when all eight canonical CI
statuses are successful on the current PR head. It reads reviewer personas
from committed `main`, never from the feature branch, and launches code and
prose lanes as distinct sessions through `local/bin/dispatch.sh`.

Each dispatched lane must have a nonempty session name and thread id distinct
from the other lane, exit zero, and have exactly matching clean completion
telemetry. The matching record binds the reviewer role, PR/issue number,
worktree, thread id, start and end timestamps, and `done` status. Output from a
nonzero reviewer process is diagnostic only and can never satisfy the gate.

Reviewer inputs such as diffs, build logs, prior ledgers, issue text, and paper
text are untrusted data. The wrapper strips controls, truncates them, prevents
fence escape, and states that instructions in the data must not be followed.
Before dispatch, it reads and validates the latest marker-bound GitHub ledger
and attaches it with PR metadata so findings carry across heads as explicitly
unresolved, resolved, or outdated. Reviewers cannot publish to GitHub; only the
trusted wrapper does so.

Lane output remains in runtime storage until combined. The combined body keeps
the findings ledger and path/line references. Before publication, the wrapper
rereads the local and GitHub head and base SHAs, including a final recheck
immediately before mutation. Movement on either side makes the run stale and
produces no review evidence.

The wrapper submits one marker-bound review with the exact `commit_id`. The
attestation binds the full PR number, full head and base SHAs, run id, canonical
findings count, event and fallback policy, and both reviewer lanes' names,
thread ids, exits, worktree, and timestamps. Its digest covers the complete
canonical ledger body before the final marker. The event is determined as
follows:

- a clean verdict uses `COMMENT` with `fallback=none`;
- unresolved findings use `REQUEST_CHANGES` first and attest
  `fallback=COMMENT`.

Only an HTTP 422 response that explicitly says the pull-request author cannot
request changes on their own PR permits one `COMMENT` fallback POST. Unrelated
422 responses fail immediately. Transient and ambiguous writes use
authoritative read-back only and never trigger the fallback. The fallback body
retains positive canonical findings, `event=REQUEST_CHANGES`,
`fallback=COMMENT`, and the original exact head, base, run, digest, and reviewer
session evidence; only GitHub's represented state becomes `COMMENTED`.

It separately posts `local-review/summary` on that SHA: `success` for a clean
ledger and `failure` for unresolved findings. The status description binds the
same run and ledger digest. Publication is idempotent only when the full
attestation, digest, body, commit, event/state, and status agree.

GitHub approval and `reviewDecision` are never required. The normal gate is a
successful exact-head summary status plus a strictly parsed clean `COMMENT`
attestation whose reviewer session telemetry matches, with no later exact-head
`CHANGES_REQUESTED` review. This supports the common case where the repository
operator is also the PR author and GitHub forbids self-approval.

An adverse `REQUEST_CHANGES` attestation represented by a fallback `COMMENTED`
review remains valid ledger evidence for review-fix consumers, but its summary
is `failure` and it never satisfies the clean merge gate.

A failed CI run blocks review explicitly. Kill switches disable only when set
to the literal string `false`; unset means enabled. A reviewer session must be
different from every author session and must never repair its own findings.
