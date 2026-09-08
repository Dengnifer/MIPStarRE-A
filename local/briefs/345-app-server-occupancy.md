# Issue 345: default-home app-server occupancy

## Evidence

The owner receipt
`/home/drx/.cache/mipstarre-dev/qpbt-switch/worker-occupancy-correction-20260908.json`
defines total capacity `k` as one main root plus `k - 1` native descendants, with no
separate unrelated-use reservation. At `k = 10`, the desired lease is nine descendants,
external admission is zero, and the active-worker floor is
`ceil (0.8 * (k - 1)) = 8`.

On September 8, 2026, PID 3286270 was a same-user `codex app-server` started at
10:16:05 +0800 by the VS Code ChatGPT extension. Its effective Codex home was the
primary default `/home/drx/.codex`, and its CWD was the owner-allowlisted `/home/drx`.
The canonical router classified it as a worker, consuming the slot needed for the ninth
native descendant even though the process is unrelated application-server use.

## Change contract

- Preserve the live application-server process.
- Reuse the existing validated owner CWD allowlist.
- Exclude only an exact `app-server` command using the known primary default home in an
  allowlisted CWD, alongside the already-excluded interactive case.
- Continue counting `exec`, `e`, `review`, `mcp-server`, `exec-server`, scoped-home and
  unknown-home processes, reservations and shared native leases.
- Preserve host-visibility failure behavior and all account, credential, lease, external
  admission, CI, review and merge guards.
- Do not activate or resize the native lease from this branch. Meta owns runtime changes;
  the checkpoint switch completed independently after PID 3286270 exited.

## Verification

Add a fake-proc matrix covering command, home and CWD boundaries; run the workflow unit
suite and canonical PR CI; obtain a fresh exact-head independent Sol/Ultra native review.
Before handoff, perform one read-only actual-PID check with the branch router and make no
lease writes.

The final read-only check verified `native_process` for root PID 3351858 at the current
eight-descendant cap, observed census `[8, 0]` workers and `[1, 0]` interactives after
the exclusion, and projected replacing the existing eight-slot lease by nine as exactly
ten total slots. The lease file timestamp and SHA-256 were unchanged. PID 3286270 had
exited naturally and no replacement `app-server` was live, so the actual-PID exclusion
could not be reobserved; the fake-proc regression retains its observed command, home and
CWD shape.

After the checkpoint switch, a second read-only check verified root
PID 3846730/start187183661 with a nine-descendant lease, census `[9, 0]` workers and
`[1, 0]` interactives within capacity ten, external reservation zero, no live
`app-server`, and an unchanged lease-file timestamp and SHA-256.
