# Brief: GitHub-native records with a durable local fallback

Issue: `#0007`
Target branch: `issue-0007-github-native-workflow`
Expected PR title: `feat(local): add GitHub write-through records`

## Objective

Implement the 2026-08-31 owner decision recorded in `HANDOFF.md` step 0 and
`local/protocols/EVOLUTION.md`: GitHub becomes the ordinary issue and pull
request surface for `Dengnifer/MIPStarRE-A`, while the existing committed
registry remains a complete write-through record and an offline fallback.

Local CI and review continue to execute on this server. The local same-head
manifest, verdict, and merge gate remain authoritative. The GitHub adapter
publishes those results; it must not weaken, duplicate, or replace the gate.

This is workflow work only. Do not modify Lean, blueprint, or paper-source
content.

## Sources to read first

1. `HANDOFF.md`, especially immediate step 0.
2. `local/personas/main.md`.
3. `local/README.md`, `local/DESIGN.md`, and `local/protocols/meta.md`.
4. `local/protocols/issues-prs.md`, `ci.md`, `review.md`, `sessions.md`, and
   `build-cache.md`.
5. The 2026-08-31 re-hybridization entry in `local/protocols/EVOLUTION.md`.
6. `results/telemetry/github-migration-map.md` and issue `#0007`.
7. Every script named in the scope below and the shared data layer in
   `local/bin/track.py`.

Use the GitHub REST documentation for issues, sub-issues, pull requests,
commit statuses, and pull-request reviews. The relevant fine-grained token
permissions are Issues write, Pull requests write, Commit statuses write, and
Contents write.

## Operator decisions

These points are adjudicated. Do not leave them as OPEN items.

### 1. Authority and degraded mode

- GitHub is the normal human-facing record after this change lands.
- Local issue and PR files are always written and remain sufficient to run the
  local lifecycle while GitHub is unavailable.
- A successful local mutation followed by a remote failure is not rolled back.
  Record the remote operation as pending, print an actionable warning, and
  leave enough state for deterministic reconciliation.
- Default mode is best effort so a link outage does not stop formalization.
  Provide an explicit required-online mode for operators/tests that need a
  nonzero exit when GitHub synchronization fails.
- `MIPSTARRE_GITHUB_ENABLED=false` is the literal kill switch. Unset means
  enabled, matching the existing kill-switch convention.
- Never log tokens or copy authentication material into the repository.

### 2. Identity and idempotency

- Extend issue and PR records with optional GitHub identity and synchronization
  fields. At minimum retain the GitHub number, URL, and whether synchronization
  is `synced` or `pending`; retain the numeric GitHub issue id when needed for
  the sub-issue API.
- Seed the existing mappings from
  `results/telemetry/github-migration-map.md`; never recreate those records.
- Every remotely created object carries a hidden stable marker based on the
  local id, for example `mipstarre-local-issue:0007` or
  `mipstarre-local-pr:0004`.
- Before every create attempt, and again after an ambiguous failure, search the
  authoritative REST listing for the marker. Do not rely on eventually
  consistent search indexing. Adopt a unique match; treat multiple matches as
  a conflict requiring operator attention.
- Repeated synchronization after success must be a no-op except for deliberate
  field/body/state updates.

### 3. Shared adapter and configuration

- Put GitHub API, retry, identity, and reconciliation logic in one Python
  adapter under `local/bin/`; do not duplicate ad hoc `gh` fragments across
  shell scripts.
- Invoke the REST API through `gh api`. Support an explicit executable override
  such as `MIPSTARRE_GH` so deterministic tests can supply a fake CLI.
- Resolve the repository from `MIPSTARRE_GITHUB_REPO` or the `github` remote,
  and retain `Dengnifer/MIPStarRE-A` as the documented default.
- Retry bounded transient failures with short exponential backoff. Tests must
  be able to set delays to zero.
- Validate CLI presence and `gh auth status` separately. Missing CLI,
  authentication, or connectivity is a loud pending-sync state, not silent
  success and not loss of the local record.
- Add an explicit reconciliation command that can sync one issue, one PR, or
  all pending records. Reconciliation is the recovery path after an offline or
  ambiguous operation.

### 4. Issue lifecycle

- `issue_new.py` allocates and completes the local create/classify/scout stages
  first, then ensures the GitHub issue exists with the final title, body, and
  labels.
- Apply only labels that exist in the GitHub repository and report missing
  labels; do not let one absent label abort issue creation.
- Translate local parent identity through the stored mapping. After both
  records exist, use GitHub's sub-issue endpoint to attach the child. A pending
  parent leaves an explicit pending relation for reconciliation.
- `issue_close.py` maps local `not-planned` to GitHub `not_planned` and preserves
  `completed`. It must be safe to retry even when the local issue is already
  closed.
- Remote issue bodies may expose the local id, but generated cross-reference
  footers must use mapped GitHub numbers so `#N` never points to an unrelated
  issue or pull request.

### 5. Pull-request publication and the empty-branch case

- Preserve the current operating loop in which the local PR record may be
  opened before the implementation commit exists.
- GitHub rejects a PR whose head has no commits ahead of its base. In that case
  `pr_open.py` creates the local record, marks remote creation pending, and says
  exactly why. It is not an error and must not manufacture a placeholder
  commit.
- Once the branch has a real head, reconciliation publishes the feature branch
  and creates or updates the GitHub PR. `ci.sh` may ensure this publication
  before posting its status.
- Narrow the old push rule explicitly: feature branches may be pushed as PR
  heads; GitHub `main` may advance only after the local merge gate passes.
- Translate `Addresses`/`Closes` footers from local issue ids to mapped GitHub
  issue numbers in the remote PR body.

### 6. Same-head CI status

- `ci.sh` publishes a stable context such as `MIPStarRE/local-ci` for the exact
  `HEAD_SHA` in its manifest. Publish `pending` when the run begins and the
  final `success`, `failure`, or `error` after the complete manifest is written.
- Partial/debug runs must not publish a success status.
- Before posting, ensure the commit exists in the remote repository. Never
  attach a result to a different or merely current branch head.
- An ambiguous status POST is reconciled by reading the latest status with the
  same SHA and context before retrying.
- A remote publication failure does not rewrite the local CI conclusion. It
  leaves GitHub synchronization pending and is recoverable from the manifest.

### 7. Same-head review publication

- After `review.sh` writes its local verdict files and rechecks the final head,
  publish one review summary tied explicitly to that `HEAD_SHA`.
- The GitHub account that opens these PRs cannot approve its own PR. Therefore
  publish a GitHub `COMMENT` review for every local verdict and state clearly
  that `APPROVED`, `COMMENTED`, or `CHANGES_REQUESTED` is the local gate verdict.
  Do not pretend a GitHub self-approval succeeded.
- Include the exact commit id in the review API request and verify the remote PR
  head first. A mismatch is a refused/pending publication, never a review on a
  stale or different head.
- Include a stable local-PR/head/digest marker. Repeating an identical publish
  is a no-op; a materially different rerun on the same head remains auditable.
- Preserve code/prose lane artifacts locally. The GitHub summary may combine
  them, but it must report the worst local verdict and unresolved finding count.

### 8. Merge and push ordering

- `pr_merge.py` continues to run the unchanged local gate and perform the local
  no-fast-forward merge. No remote operation may bypass `run_gate`.
- Replace `github-sync.sh`'s broad `git push --all` with a bounded,
  retry-hardened push of explicit intended refs. Feature-head publication is
  owned by the adapter; the post-merge default is `main`.
- After the local merge, push `main`; GitHub should then recognize the PR as
  merged from commit ancestry. Do not close it through the issue endpoint,
  which would record a closed-unmerged PR.
- If the post-merge push fails, keep the local merge and record remote sync as
  pending. Report that the merge already happened and direct the operator to
  reconciliation; do not invite a second merge attempt.
- Do not delete a remote feature branch until GitHub recognizes the merge. A
  local branch/worktree may be removed under the existing cleanup rules once
  recovery metadata is durable.

### 9. Protocol and telemetry consistency

- Update `AGENTS.md`, `local/README.md`, `local/DESIGN.md`,
  `local/personas/main.md`, and the affected protocols so no operative text
  still claims that GitHub operations do not exist.
- Keep `.github/` frozen as workflow precedent; do not reactivate GitHub
  Actions.
- Append an `EVOLUTION.md` implementation entry citing the owner decision and
  issue `#0007`. Amend every enforcement point affected by the changed push,
  authority, kill-switch, and gate semantics.
- Preserve local registry locks, atomic writes, primary-checkout ownership, and
  same-head merge evidence.

## Required tests

Add deterministic regression tests under `scripts/tests/`. They must run in a
temporary repository with a fake `gh` selected through configuration and must
never contact or mutate the real GitHub repository.

Cover at least:

1. Issue create, marker recovery after an ambiguous create failure, close
   reason translation, existing-label filtering, and sub-issue attachment.
2. PR create/update, the empty-diff deferred case, local-to-GitHub footer
   translation, and recovery of a previously created PR by marker.
3. Missing CLI, unauthenticated CLI, transient retry exhaustion, required-online
   failure, and best-effort pending state.
4. Pending and final same-head commit statuses, identical retry suppression,
   and no success publication for a partial CI run.
5. Review publication with `event=COMMENT`, exact `commit_id`, identical retry
   suppression, worst-verdict combination, and remote-head mismatch refusal.
6. Merge gate still refuses stale CI/review evidence; `github-sync.sh` pushes
   only explicit refs and retries bounded failures.
7. Seed mappings for GitHub issues `#1` through `#4` and PR `#5` are adopted
   without create calls.
8. `local/bin/validate_tree.py` still accepts the extended record schema.

Prefer focused unit/integration tests of the shared adapter and thin hook tests
for the shell entry points. Do not run a full Lean build for this workflow-only
change unless CI's change gating requires it.

## Deliverable and report

Commit the implementation on the issue branch with an imperative conventional
subject. The final orchestrator report must list:

- files and contracts changed;
- exact fake-`gh` tests run and results;
- local tree/CI checks run and results;
- any operation that remains pending solely because the owner has not completed
  `gh auth login`;
- a concise invariant audit covering local fallback, idempotency, same-head CI,
  same-head review, and merge-before-`main` push.
