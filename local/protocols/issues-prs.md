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

An idempotent mutating command issues at most one POST or PATCH per invocation.
Every local review, clean or adverse, is a `COMMENT`; unresolved findings are
represented by a failing summary rather than a sticky `REQUEST_CHANGES` review.
After an ambiguous mutation result, the command polls only the authoritative
read surface and fails ambiguous when the expected marker-bound state does not
appear. It never resolves ambiguity by repeating the same mutation.

The shared parsers distinguish a valid publication from gate-complete evidence.
A complete exact-head and exact-base CI manifest with all matching step
statuses is readable when its conclusion is `success`, `failure`, or `error`.
Review and merge additionally require a successful `local-ci/summary` whose
description binds the manifest run and digest; they accept only `success` with
canonical step outcomes `success` or `skipped`.
A review attestation can likewise be structurally and session-valid before its
summary status is final, so prior-ledger and auto-fix consumers may read it.
Merge requires the exact matching final summary. Neither distinction creates a
local authority: the publications and statuses remain GitHub records, while
runtime copies are diagnostic only.

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

`local/bin/ci.sh <pr-number>` publishes `local-ci/summary=pending` before a
complete run, all eight `local-ci/*` step statuses, and one marker-bound
manifest comment. Only after authoritative manifest and status read-back may it
replace the summary with its digest-bound final state. `local/bin/review.sh
<pr-number>` publishes `local-review/summary=pending` at review start, then a
commit-bound `COMMENT` ledger and `success` for a clean attestation or `failure`
for findings. Partial or moved-head runs publish no gate-satisfying set. CI and
review require a clean committed feature worktree, including no tracked,
staged, or untracked changes, at startup and final publication boundaries.
Runtime logs live beneath `~/.cache/mipstarre-dev/`.

Review holds the per-PR review lock and the ownership-stamped branch fix lock
from before reading the feature tree through publication. It may recover a
valid exact-head and exact-base attestation whose matching summary is missing
or canonically pending by posting only the final status. It cannot recover an
unrelated pending run, a conflicting status, or a stale-base attestation, and
one review run id, reviewer session name, or thread cannot be replayed across
distinct attestations for the same PR.

`local/bin/pr_merge.py <pr-number>` accepts only an open, non-draft, mergeable
PR whose local branch and GitHub head are the same full 40- or 64-hex SHA and
whose trusted local base matches the PR's full base SHA. It reserves the
per-PR review lock, branch fix lock, and per-PR CI lock through gate publication
and the merge mutation. The feature worktree must be clean at each gate
boundary. One fail-closed evaluator runs before preparation and immediately
before merge. Each evaluation binds the unchanged head and base and requires
the success-level exact-head and exact-base CI manifest, step statuses, and
digest-bound summary; a strictly parsed clean `COMMENT` attestation plus its
exact same-run/digest summary and reviewer completion telemetry; no newer
adverse exact-head review; and complete within-cap fix history.

The evaluator reads classic protection for the PR's actual base. Required
checks must be strict and exactly `local-ci/summary` and
`local-review/summary`; administrators must be enforced; a pull-request review
rule must be present with zero required approvals, no code-owner or last-push
approval, and empty user/team/app bypass allowances; force pushes and deletions
must be disabled. Every effective branch rule is also read. Active merge queues,
nonstrict or missing summary rules, approval requirements, unavailable merge
commits, inactive referenced rulesets, or nonempty ruleset bypass actors block
the merge.

GitHub approval and `reviewDecision` are not gates. A clean independent
exact-head `COMMENT` review is sufficient with the other evidence above.

Adjudicated merges require the current `adjudicated` label and exactly one
unedited PR comment beginning `ADJUDICATION`. Its canonical JSON and final
digest marker bind the PR, head, base, and latest source review id, run, and
digest. It cites at least four ordered, distinct, session-valid review rounds
for that same head and base. Its dispositions exactly cover every unresolved
source finding: `fixed` records need nonempty reason and evidence, while
`tracked` records name an open, non-PR issue in the same repository. After a
full revalidation under all three locks, the gate publishes the exact
adjudication as `local-review/summary=success` and rereads it before merge.

The only merge mutation is one guarded
`gh pr merge --merge --match-head-commit <sha>` call, without `--admin` or
`--auto`. GitHub's strict required checks and base-freshness rule remain the
server-side last gate. A transient result triggers authoritative PR read-back,
never a second merge call; only the exact PR/head/base reported merged and
closed is accepted. After success, the trusted local base may be fetched and
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
