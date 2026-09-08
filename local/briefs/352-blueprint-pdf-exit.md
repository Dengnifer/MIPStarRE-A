# Issue #352 - Fail closed on blueprint PDF errors

## Incident

PR #350 at `d081d5b80b3ed9ef9326be2282bd6884995029b6` exposed a
false-success path in `local/bin/ci.sh`. The PDF renderer reached an undefined
`\Exp` command, returned nonzero, and left an older non-empty
`blueprint/print/print.pdf`. Because the step dispatcher captures outcomes with
`errexit` disabled, the unchecked failure was replaced by later successful bbl
and web commands. The exact-head manifest therefore reported success.

The failed log and old PDF were copied before repair validation to
`/tmp/qpbt-ci-blueprint-render-failopen-20260908/`. Their SHA-256 values are,
respectively,
`172f76a182daf68f921651a1d292c5ba6b3064d44da7efe9c3104bb2c9d935ba`
and `bf3fc1b0c3fc1d326bd52bc5590fe4dd4dcba230d0e89647611c508f59c9e11a`.

## Repair boundary

Before rendering, remove only the generated `print.pdf`. Treat a nonzero
`leanblueprint pdf` status as a blocking step failure and stop before bbl/web.
After a zero exit, retain the independent non-empty check so the invocation
must have produced a fresh artifact. Exact-head status, manifest, gating,
locking, and publication logic remain unchanged.

Blueprint source, router policy, runtime configuration, credentials, leases,
services, and model processes are out of scope. PR #350's source head is not
modified by this issue.

## Regression boundary

The isolated tests invoke the real `ci.sh` in partial mode with a temporary Git
repository, fake GitHub read, fake renderer, and a stale PDF. Before the repair,
the nonzero and zero/no-output cases both incorrectly returned success; the
fresh-output control passed. After the repair, the first two must fail before
web rendering, while the control must replace the stale bytes and succeed.
