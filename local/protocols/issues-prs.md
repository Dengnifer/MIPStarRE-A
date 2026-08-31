# GitHub issue and pull-request lifecycle

Normative. Read `local/protocols/meta.md` first.

GitHub is the only authority for active issues and pull requests. The retired
local registries are immutable research data under
`results/telemetry/registry-archive/`; lifecycle commands must never read or
write them. Audit snapshots under `results/telemetry/github-snapshot/` are also
read-only telemetry, not workflow input.

## Shared access

All lifecycle commands use `local/bin/github_api.py`. It resolves `gh` from
`MIPSTARRE_GH`, then `PATH`, then `~/.local/bin/gh`; discovers the repository
from `MIPSTARRE_GITHUB_REPO` or the `github` remote; and verifies access with a
harmless API request. Mutations fail closed when GitHub cannot be reached.

The shared client supplies versioned REST headers, complete pagination,
sanitized diagnostics, and bounded retries for connection failures, timeouts,
HTTP 429, rate-limit responses, and HTTP 5xx. Permanent failures are not
retried blindly. Ambiguous mutations use stable hidden markers followed by an
authoritative read-back. A marker may be adopted only when its event, exact
commit, and complete body match.

An idempotent mutating command normally issues at most one POST or PATCH per
invocation. The sole exception is `review_once`: after GitHub definitively
rejects `REQUEST_CHANGES` with HTTP 422 and an explicit prohibition against a
pull-request author requesting changes on their own PR, it may issue one
`COMMENT` fallback carrying the same adverse attestation. Unrelated 422
responses and transient or ambiguous failures never authorize that fallback.
After an ambiguous mutation result, the command polls only the authoritative
read surface and fails ambiguous when the expected marker-bound state does not
appear. It never resolves ambiguity by repeating the same mutation.

## Issues

Create an issue with:

```bash
local/bin/issue_new.py --title "..." --body-file /path/to/body.md \
  --label formalization --parent 12
```

GitHub assigns the issue number. Requested labels are checked against all
paginated repository labels. The body contains a stable creation marker, so an
ambiguous create can adopt exactly one matching issue. A parent is linked with
GitHub's sub-issue API using the child's database id.

Creation performs no implicit keyword classification or agent dispatch. Labels
are explicit repository state, and Mathlib scouting is a separately authorized
`scout` session dispatched by the orchestrator after it has read the issue.

Close an issue with:

```bash
local/bin/issue_close.py 27 --reason completed --comment "Implemented by #31"
```

The allowed reasons are `completed` and `not-planned`, mapped to GitHub's
`state_reason`. Optional comments are marker-idempotent.

## Pull requests

`local/bin/pr_open.py` requires an explicit feature branch and base. It refuses
an empty diff, pushes only
`refs/heads/<branch>:refs/heads/<branch>` to the `github` remote, and creates or
adopts the unique open PR for that head branch. Repeated invocation validates
the adopted PR and updates its requested metadata. Issue footers use GitHub
numbers directly.

Branches normally use `issue-<github-number>-<slug>` or
`codex/issue-<github-number>-<slug>`. Brackets and Git-ref metacharacters are
forbidden. Fix commits begin exactly `[codex-auto-fix]` or
`[codex-review-fix]`; those prefixes are machine-readable gate evidence.

## Exact-head gates

`local/bin/ci.sh <pr-number>` publishes all eight `local-ci/*` statuses and one
marker-bound manifest comment for a complete run. `local/bin/review.sh
<pr-number>` publishes a commit-bound ledger review and
`local-review/summary`. Partial or moved-head runs publish no gate-satisfying
set. Runtime logs live beneath `~/.cache/mipstarre-dev/`.

`local/bin/pr_merge.py <pr-number>` accepts only an open, non-draft, mergeable
PR whose local branch and GitHub head are the same full 40- or 64-hex SHA and
whose trusted local base matches the PR's full base SHA. It holds the per-PR
review lock through the merge and reserves the branch fix lock. One fail-closed
gate evaluator runs both before merge preparation and immediately before the
merge mutation. Each evaluation binds the unchanged head and base and requires
the exact-head per-step CI statuses plus their same-run manifest, a strictly
parsed clean `COMMENT` attestation plus its same-run/digest status and matching
reviewer completion telemetry, no newer adverse exact-head review, fix-lock
quiescence, and complete within-cap fix history.

GitHub approval and `reviewDecision` are not gates. A clean independent
exact-head `COMMENT` review is sufficient with the other evidence above.

Adjudicated merges additionally require the repository adjudication label and
a current-head marker-bound `ADJUDICATION` comment with dispositions. The only
merge operation is guarded `gh pr merge --merge --match-head-commit <sha>`.
After GitHub reports success, the trusted local base may be fetched and
fast-forwarded; feature cleanup then follows the worktree safeguards.

## Snapshots and reporting

`local/bin/github-sync.sh` fetches explicit refs and creates a paginated audit
snapshot. It publishes `open-issues.json`, `open-pulls.json`, and
`metadata.json` as one generation by an atomic symlink switch; a failed
generation leaves the prior one intact. Pull objects are removed from the issue
dataset. `local/bin/housekeeping.sh standup` writes a dated report under
`results/reports/standup/` and never mutates GitHub.

Every emitted label is validated against GitHub. There is no offline mutation
mode, local sequence allocator, shadow frontmatter, or committed PR manifest.
