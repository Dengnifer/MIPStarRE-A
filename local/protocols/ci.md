# Exact-head local CI

Normative. Read `local/protocols/meta.md` and `issues-prs.md` first.

Run `local/bin/ci.sh <github-pr-number>`. The command reads the PR base, head
branch, and full head and base SHAs from GitHub through `github_api.py`, resolves
the registered local worktree for that branch, and requires the local head and
trusted local base to match those remote SHAs before work starts. The feature
worktree must also be completely clean: tracked changes, staged changes, and
untracked files all make the run ineligible.

## Canonical gates

A complete run evaluates these contexts in order:

1. `local-ci/build`
2. `local-ci/blueprint-render`
3. `local-ci/paper-gaps`
4. `local-ci/blueprint-sync`
5. `local-ci/file-length`
6. `local-ci/proof-debt`
7. `local-ci/proof-evasion`
8. `local-ci/statement-origin`

The existing change classifiers and step commands are preserved. Each context
is first `pending`, then `success`, `failure`, or `error`. A non-applicable step
is `success` with a description stating that it was skipped. Context matching
is case-insensitive, because GitHub status contexts are case-insensitive.

`local-ci/summary` is the required aggregate context, not a ninth executable
step. A complete run publishes it as `pending` before any CI work. Its final
description binds the exact manifest run and canonical JSON digest.

`--only`, `--skip-build`, and `--dry-run` are diagnostic partial runs. They
write runtime logs but publish no gate-satisfying status set or manifest.

There are two evidence levels. A complete, exact-head and exact-base manifest
with matching canonical statuses is readable evidence even when its conclusion
is `failure` or `error`; auto-fix uses such evidence to classify a repair. CI
satisfies the review and merge prerequisite only when the manifest conclusion
is `success`, every canonical step outcome is `success` or `skipped`, every
matching step status is `success`, and the latest `local-ci/summary` is the
successful state for that manifest's exact run and digest. Thus a well-formed
failed run remains diagnostic evidence but is never green evidence.

## Publication

CI checks cleanliness after binding the initial comparison and again at every
final-publication boundary. Immediately before final statuses and the manifest,
it rereads the local and GitHub head and base SHAs and the complete worktree
status. The shared client repeats this full guard inside each final-status and
manifest mutation, after its idempotency lookup and immediately before the
POST. Movement, an unreadable comparison, or any dirt makes the run stale and
returns nonzero. It publishes no marker-bound manifest; after detecting a
mid-publication change it invalidates that run's contexts with `error`, so the
latest statuses cannot form a successful set. A dirty run therefore cannot
leave gate-satisfying evidence, while a clean, stable failure or error run keeps
its readable manifest for diagnosis and auto-fix.

A complete stable run posts a full JSON manifest as an immutable PR comment
with exact PR, full head, full base, and run markers. Marker adoption requires
the entire body to match. Every canonical status description names that same
run, and a consumer rejects a manifest unless the latest exact-head status for
every step names the manifest run and agrees with its result. Only after the
comment and all step statuses have been read back authoritatively does CI post
the digest-bound final `local-ci/summary`, then it rereads both the manifest and
summary. A publication failure invalidates the step and summary contexts with
`error`; a prior success can never survive as the latest summary for the failed
run.

Status creation is digest-idempotent. Each invocation issues at most one
mutation. If the POST result is ambiguous, the client polls statuses on the
exact SHA and adopts only the matching casefolded context, state, and
description digest. It fails ambiguous if read-back does not establish the
mutation and never sends a second POST.

Logs and manifests are runtime state under `~/.cache/mipstarre-dev/`. Build
events remain append-only in `results/telemetry/builds.jsonl`. No committed
issue or PR shadow record is created.

## Build lock

Single-file Lean checks do not take the machine-wide lock. A full `lake build`
uses the advisory lock and a worktree-local copy-on-write cache clone described
by `build-cache.md`. Never run `lake update`, and never write back to the hot
main cache.

The merge and review gates require the success-level evidence described above,
bound to the current full head and base SHAs. Classic branch protection also
requires only `local-ci/summary` and `local-review/summary`, with strict base
freshness. GitHub's combined status is not sufficient.
