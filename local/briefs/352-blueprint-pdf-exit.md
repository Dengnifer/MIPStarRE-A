# Issue #352 - Fail closed on blueprint PDF errors

## Incident

PR #350 at `d081d5b80b3ed9ef9326be2282bd6884995029b6` exposed a
false-success path in `local/bin/ci.sh`. The PDF renderer reached an undefined
`\Exp` command and its underlying `latexmk` process returned 12, but the
`leanblueprint` wrapper returned zero while a fresh non-empty partial PDF
existed. Because the step trusted the wrapper and artifact, later successful
bbl and web commands left the exact-head manifest reporting success.

The failed log and observed PDF were copied before repair validation to
`/tmp/qpbt-ci-blueprint-render-failopen-20260908/`. Their SHA-256 values are,
respectively,
`172f76a182daf68f921651a1d292c5ba6b3064d44da7efe9c3104bb2c9d935ba`
and `bf3fc1b0c3fc1d326bd52bc5590fe4dd4dcba230d0e89647611c508f59c9e11a`.

## Repair boundary

Before rendering, remove only the generated `print.pdf`. Invoke the project's
existing `latexmk` configuration directly from `blueprint/src`, with
noninteractive, halt-on-error, and file-line diagnostic flags. Treat its
nonzero status as a blocking step failure and stop before bbl/web. After a zero
exit, retain the independent non-empty check so the invocation must have
produced a fresh artifact. Exact-head status, manifest, gating, locking, and
publication logic remain unchanged.

Blueprint source, router policy, runtime configuration, credentials, leases,
services, and model processes are out of scope. PR #350's source head is not
modified by this issue.

## Regression boundary

The isolated tests invoke the real `ci.sh` in partial mode with a temporary Git
repository, fake GitHub read, fake renderer, and a stale PDF. The actual-failure
counterfactual makes the wrapper return zero and write a fresh partial PDF while
its underlying compiler reports exit 12. The published candidate accepted that
case. The repaired driver must reject it before web rendering, alongside direct
compiler failure and zero-without-output, while genuine output remains a
successful control.
