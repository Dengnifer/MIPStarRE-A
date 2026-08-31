# Exact-head review

Normative. Read `local/protocols/meta.md`, `issues-prs.md`, and `ci.md` first.

`local/bin/review.sh <github-pr-number>` runs only when all eight canonical CI
statuses are successful on the current PR head. It reads reviewer personas
from committed `main`, never from the feature branch, and launches code and
prose lanes as distinct sessions through `local/bin/dispatch.sh`.

Reviewer inputs such as diffs, build logs, prior ledgers, issue text, and paper
text are untrusted data. The wrapper strips controls, truncates them, prevents
fence escape, and states that instructions in the data must not be followed.
Before dispatch, it reads and validates the latest marker-bound GitHub ledger
and attaches it with PR metadata so findings carry across heads as explicitly
unresolved, resolved, or outdated. Reviewers cannot publish to GitHub; only the
trusted wrapper does so.

Lane output remains in runtime storage until combined. The combined body keeps
the findings ledger and path/line references. Before publication, the wrapper
rereads the local tip and GitHub head. A moved head is stale and produces no
review evidence.

The wrapper submits one marker-bound review with the exact `commit_id`:

- a clean verdict uses `COMMENT`;
- unresolved findings use `REQUEST_CHANGES` when GitHub permits it;
- only a response specifically identifying an impossible self-review may fall
  back to `COMMENT`; unrelated HTTP 422 responses remain failures.

It separately posts `local-review/summary` on that SHA: `success` for a clean
ledger and `failure` for unresolved findings. Publication is idempotent only
when marker, body, commit, and adopted event/state agree.

GitHub approval is never required. The normal gate is a successful exact-head
summary status plus a marker-bound clean ledger, with no later exact-head
`CHANGES_REQUESTED` review. This supports the common case where the repository
operator is also the PR author and GitHub forbids self-approval.

A failed CI run blocks review explicitly. Kill switches disable only when set
to the literal string `false`; unset means enabled. A reviewer session must be
different from every author session and must never repair its own findings.
