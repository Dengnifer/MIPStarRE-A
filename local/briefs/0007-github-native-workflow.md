# Brief: GitHub-native workflow without a local issue/PR registry

GitHub issue: `Dengnifer/MIPStarRE-A#6`

Branch: `issue-0007-github-native-workflow`

Expected PR title: `feat(local): make GitHub the workflow authority`

## Authority

This brief records the owner's 2026-08-31 directive, which supersedes the
earlier write-through/offline-fallback design archived with the old registry.
GitHub is the single source of truth for active issues and pull requests. There
must be no active `issues/` or `prs/` tree, shadow record, write-through cache,
operation journal, or offline mutation mode.

The archive-only commit `c8f1999` moved the former trees verbatim to:

- `results/telemetry/registry-archive/issues/`
- `results/telemetry/registry-archive/prs/`

Those 60 archived files are append-only research data. Do not edit, regenerate,
normalize, or use them as active workflow input.

Session, build, stage, incident, and evolution telemetry remain active and
unchanged. In particular, `dispatch.sh`, `telemetry.py`,
`results/telemetry/{sessions,builds,stages}.jsonl`, and the
`events.md` -> `EVOLUTION.md` amendment pipeline are not registry machinery.

## Shared GitHub layer

Provide one shared Python layer under `local/bin/` for repository discovery,
`gh` execution, JSON parsing, pagination, retry classification, and API
version headers. All lifecycle tools must use it.

- Resolve the CLI from `MIPSTARRE_GH`, then `PATH`, then the documented
  user-local location. Tests set `MIPSTARRE_GH` to a fake executable.
- Resolve the repository from `MIPSTARRE_GITHUB_REPO` or the `github` remote;
  the documented repository is `Dengnifer/MIPStarRE-A`.
- Probe authentication with a harmless API request. Do not trust
  `gh auth status`, because installed `gh 2.4.0` misreports the valid
  fine-grained PAT.
- Never log a token or pass one on the command line.
- Retry connection failures, timeouts, HTTP 429, and HTTP 5xx with a bounded
  exponential delay. Do not retry permanent 4xx responses blindly.
- Mutations are online-required. Exhausted or permanent failures return
  nonzero; there is no local success or pending record to fall back to.
- Make ambiguous creates and publications idempotent with stable hidden
  markers and authoritative paginated reads before another write. This is a
  remote retry defense, not a local registry.
- Use `Accept: application/vnd.github+json` and a supported explicit GitHub API
  version for REST calls.

## Issue lifecycle

Rewrite `issue_new.py` as a GitHub issue creator and `issue_close.py` as a
GitHub issue closer.

- GitHub issue numbers are the only active issue identifiers. Do not allocate
  zero-padded local ids or write Markdown records.
- `issue_new.py` uses noninteractive `gh issue create`, prints the created or
  adopted issue number and URL, and supports title, body/body-file, labels,
  assignees, and an optional GitHub parent issue number.
- A stable marker in the issue body makes retry after an ambiguous create
  recover the existing issue rather than duplicate it.
- For `--parent`, resolve the child's numeric database id and call
  `POST /repos/{owner}/{repo}/issues/{parent}/sub_issues`. GitHub's one-parent
  relation replaces all parent/children frontmatter and tracking counters.
- `issue_close.py` operates on a GitHub number. Map `completed` and
  `not-planned` to GitHub's `state_reason` values and preserve an optional
  explanatory comment.
- Labels come from the repository. Remove `local/labels.yml` as an authority;
  scripts may validate requested labels against the paginated GitHub label
  list and must report a missing label clearly.

## Pull-request lifecycle

Rewrite `pr_open.py` to publish an explicit feature ref and invoke
noninteractive `gh pr create`.

- GitHub PR numbers are the only active PR identifiers.
- Inputs are branch, base, title, body/body-file, labels, and an optional
  closing issue number. Use GitHub-number footers directly.
- Push only `refs/heads/<branch>:refs/heads/<branch>` to the `github` remote.
  Never use `git push --all` and never advance `main` outside the merge path.
- Repeated invocation adopts or updates the unique open PR for the same head
  branch. A branch with no commits ahead of base fails clearly; do not create a
  placeholder commit.
- Keep branch-name safety checks, but future names embed GitHub issue numbers.
  The current migration branch retains its historical local id and closes
  GitHub issue `#6`.

## CI publication

Rewrite `ci.sh` to accept a GitHub PR number and obtain base ref, head ref, and
head SHA from GitHub. Resolve the corresponding local worktree and require its
branch tip to equal the remote PR head before starting.

- Preserve the existing deterministic step commands and change gating.
- For every complete run, publish a status for every gate step on the exact
  starting SHA using context `local-ci/<step>`. Publish `pending` before a step
  and one of `success`, `failure`, or `error` afterward. A non-applicable step
  is a successful status whose description says it was skipped.
- Debug/partial runs must not publish a gate-satisfying status set.
- Re-read both the local branch tip and remote PR head before final
  publication. If either moved, publish no stale success and return nonzero.
- Build the existing manifest schema in runtime storage, then post the full
  JSON as an idempotent PR comment with exact PR/head/run markers. It is not
  written to an active repository registry.
- Keep build telemetry exactly as it is today.

The merge gate requires the latest status for every canonical
`local-ci/<step>` context on the current PR head to be `success`. It must not
trust GitHub's combined status alone, because unrelated contexts may be absent.

## Review publication

Rewrite `review.sh` to accept a GitHub PR number, verify the exact-head CI
statuses, and run the existing trusted-prompt code/prose review lanes.

- Reviewer output lives in runtime storage until the trusted wrapper combines
  it. Do not recreate `prs/<id>/reviews/`.
- Preserve the findings-ledger format in the submitted review body, including
  path/line references and unresolved findings.
- Re-read local and remote head SHAs after reviewers finish. A moved head makes
  the result stale and forbids publication.
- Submit one `COMMENT` review bound to `commit_id`, with a stable marker so
  retry does not duplicate an identical review. Clean and adverse verdicts
  both use `COMMENT`; the local wrapper never publishes `APPROVE` or
  `REQUEST_CHANGES` events.
- Publish a separate exact-head `local-review/summary` commit status:
  `success` for an acceptable local verdict and `failure` for unresolved
  findings. This status plus the marker-bound ledger, not a GitHub
  `APPROVED` actor, is the review gate evidence.

## Auto-fix and merge gate

Remove all reads and writes of `pr.md`, local CI manifests, and local verdict
files from `autofix.sh` and `pr_merge.py`.

- Resolve PR branch/base/head and labels from GitHub.
- Preserve the machine-local per-branch fix lock and supersession behavior.
- Derive the combined fix iteration count from PR commits whose subjects begin
  exactly `[codex-auto-fix]` or `[codex-review-fix]`; enforce the configured
  cap from that GitHub-visible history.
- Use a GitHub label for auto-fix opt-in. At the cap, remove the label and post
  a clear PR comment.
- `pr_merge.py` must enforce, in order: open/non-draft/mergeable PR; actual
  local branch tip equals GitHub head; every canonical per-step status is
  successful on that head; review state is acceptable on that same commit;
  no live fix lock; fix iteration count is within cap; and a final head recheck.
- Normal review requires a successful exact-head `local-review/summary` status
  and the matching trusted `COMMENT` ledger with no unresolved finding. An
  adverse local `COMMENT` has a failing summary and does not satisfy the gate;
  a later external exact-head `CHANGES_REQUESTED` review remains a conservative
  block.
- With `--adjudicated`, require a current-head PR comment beginning
  `ADJUDICATION`, containing the findings disposition and stable head marker,
  plus the repository's adjudication label. Missing or stale evidence blocks.
- Merge with modern `gh pr merge --merge --match-head-commit <sha>`. Probe that
  capability and fail closed on an older CLI. Do not use `--admin`, auto-merge,
  a direct push to `main`, or an unguarded merge.
- After GitHub reports the PR merged, fetch and fast-forward the trusted local
  `main` checkout to the remote merge commit; then remove the local feature
  worktree/branch under the existing cleanup safeguards.

## Snapshot and consumers

`github-sync.sh` no longer mirrors a local registry. It performs only explicit
safe ref synchronization and an atomic, paginated read-only snapshot of open
GitHub issues and PRs into:

- `results/telemetry/github-snapshot/open-issues.json`
- `results/telemetry/github-snapshot/open-pulls.json`
- `results/telemetry/github-snapshot/metadata.json`

Snapshots are audit/recovery telemetry, never lifecycle input or mutation
authority. Filter pull requests out of the issue endpoint's result.

Audit every active consumer of `issues/` and `prs/`. Rewrite or retire at least
`track.py`, `validate_tree.py`, `export_issues.py`, `agent.sh`,
`housekeeping.sh`, `autofix.sh`, the affected personas, and all normative
documentation. Historical references inside
`results/telemetry/registry-archive/` remain untouched.

Rewrite `local/protocols/issues-prs.md` around this contract. Update
`AGENTS.md`, `local/README.md`, `local/DESIGN.md`, `local/personas/main.md`,
and the affected CI/review/auto-fix/session protocol text. Append an
`EVOLUTION.md` entry with trigger "owner decision 2026-08-31, follow-on to the
re-hybridization entry". Record the interrupted write-through attempt and this
superseding decision honestly in `results/telemetry/events.md`.

Do not modify Lean, blueprint, paper sources, frozen `.github/` workflow
precedent, or any archived registry file.

## Required tests

Add a deterministic temporary-repository suite under `scripts/tests/` with a
fake `gh`; no test may contact the real repository. Cover:

1. Issue create/recovery, close reasons, label validation, and sub-issue API.
2. Explicit branch push, PR create/adoption, GitHub-number footers, and an
   empty-diff refusal.
3. Transient retries, permanent failures, missing CLI/authentication, and no
   local fallback artifacts.
4. Per-step pending/final statuses, all canonical contexts, skipped steps,
   partial-run refusal, manifest comments, and local/remote head races.
5. Exact-commit `COMMENT` reviews for clean and adverse findings, ledger bodies,
   the `local-review/summary` status, idempotency, and moved-head refusal.
6. Gate refusal for missing/failing/stale statuses, stale or adverse reviews,
   live fix locks, iteration-cap excess, and incomplete/stale adjudication.
7. An exact-head guarded `gh pr merge` invocation with no direct `main` push.
8. Paginated, atomic open-issue/open-PR snapshots and PR filtering.
9. A repository-wide assertion that active tools/docs do not create or consume
   root `issues/` or `prs/`, excluding the immutable archive and historical
   prose that explicitly names it as history.

Run focused Python/shell tests, syntax checks, `git diff --check`, and the
workflow CI lane. Do not run a full Lean build unless change gating requires it.

## Final audit repair (2026-09-01)

The final audit adds these acceptance conditions without weakening the
zero-approval `COMMENT` review contract:

- Runtime-lock acquisition never reclaims any complete record. A dead recorded
  parent may have surviving descendants, so recovery is always explicit;
  malformed, partial, ownerless, and foreign-host records remain fail-closed.
- Workspace-write `agent.sh` holds the shared branch fix lease through
  dispatch. Read-only sessions do not need it, and autofix may request
  cancellation only from a prior owner whose recorded class is `autofix `.
- Housekeeping, cache warming, and worktree warming exit 130 on `INT` and 143 on
  `TERM`, cleaning only private staging and exact owned claims.
- Status, comment, and review publication guards run after write responses and
  authoritative adoption as well as before POST. Reconciliation retries
  transient lookup failures without another mutation. Once a review POST may
  have started, an ambiguous result remains pending for idempotent adoption and
  is never overwritten by `aborted`.
- Merge preflight accepts only `draft is False`. After a topology-verified
  remote merge, local base refresh and feature cleanup are best-effort,
  warning and deferring on local dirt or failure; remote nonconformance remains
  fatal.
- Workflow change gating includes `runtime_lock.py`, `warm-worktree.sh`,
  `.github/`, and `results/telemetry/registry-archive/`. Classifiers include
  deletions and both sides of renames. Archive and frozen `.github/`
  immutability are compared with archival commit `c8f1999` and reject tracked
  dirt or untracked additions.
- Resumed sessions place worktree and sandbox options before the `resume`
  subcommand, matching the installed Codex CLI. Fresh and resumed dry-run argv
  shapes are covered by the workflow regression suite.
