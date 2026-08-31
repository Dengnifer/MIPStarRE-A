# Exact-head local CI

Normative. Read `local/protocols/meta.md` and `issues-prs.md` first.

Run `local/bin/ci.sh <github-pr-number>`. The command reads the PR base, head
branch, and full head and base SHAs from GitHub through `github_api.py`, resolves
the registered local worktree for that branch, and requires the local head and
trusted local base to match those remote SHAs before work starts.

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

`--only`, `--skip-build`, and `--dry-run` are diagnostic partial runs. They
write runtime logs but publish no gate-satisfying status set or manifest.

## Publication

Immediately before final publication, CI rereads the local and GitHub head and
base SHAs. Movement on either side makes the run stale and returns nonzero. A
complete stable run posts a full JSON manifest as an immutable PR comment with
exact PR, full head, full base, and run markers. Marker adoption requires the
entire body to match. Every canonical status description names that same run,
and a consumer must reject a manifest unless the latest exact-head status for
every step names the manifest run and agrees with its result.

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

The merge and review gates require the latest status for every canonical
context on the current exact head to be `success`, to name one manifest run,
and to agree with that run's exact full head and base. GitHub's combined status
is not sufficient.
