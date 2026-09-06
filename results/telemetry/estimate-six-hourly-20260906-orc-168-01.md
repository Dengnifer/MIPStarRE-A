# Six-hourly completion estimate: installed-state evidence

## Session and scope

- Session: `orc-168-20260906-01`; issue: `Dengnifer/MIPStarRE-A#168`.
- Worktree: `/home/drx/MIPStarRE-qpbt/.worktrees/issue-168-estimate-six-hourly`; unchanged base: `32a32edee16d3932525e4b1da9f84009e1fbb13b`.
- Task: change the installed completion-estimate cadence from eight to six hours,
  update the issue title and live cadence wording, and preserve unrelated jobs and reports.
- Scope authority: the explicit task in this session. The attached owner request was
  checked against the live host and issue rather than treated as installed-state evidence.
- Read current concurrency guidance and the primary checkout's
  `results/telemetry/owner-messages/qpbt-owner-access-only-20260906-0505.md`.
  This operation neither disposes B7/B8 nor changes their ledgers, budgets, accounts,
  model settings, or worker assignments. No subagents or model probes ran.
- No additional applicable `AGENTS.md` was found in the external script/cache
  ancestor directories or the worktree's telemetry subtree.

## Installed schedule and timezone

- Host/user: `GHZ` / `drx`.
- Installation began: `2026-09-06T05:23:41.167197+00:00`.
- Installation completed: `2026-09-06T13:23:41.182883+08:00`
  (`2026-09-06T05:23:41.182883+00:00`).
- Final independent verification: `2026-09-06T05:26:10.538068+00:00`
  (`2026-09-06T13:26:10.538068+08:00`).
- Timezone: `Asia/Shanghai` (CST, UTC+08:00), confirmed by `timedatectl`,
  `/etc/timezone`, and `/etc/localtime`.
- No `CRON_TZ` or `TZ` entry exists in the installed user crontab. No timezone
  override was found in the cron systemd unit, `/etc/default/cron`, systemd manager
  environment, or invoking shell. The cron service is active and running.
- Runs occur at 00:00, 06:00, 12:00, and 18:00 GHZ-local time each day.
- **Next scheduled run: 2026-09-06T18:00:00+08:00 = 2026-09-06T10:00:00+00:00.**
  This is computed from the installed schedule, not a claim that the future run succeeded.

Before:

```cron
17 * * * * /home/drx/bin/qpbt-watchdog.sh >> /home/drx/.cache/mipstarre-dev/watchdog/cron.log 2>&1
37 * * * * /home/drx/bin/astra-poll.sh >> /home/drx/.cache/mipstarre-dev/watchdog/astra-cron.log 2>&1
47 * * * * /home/drx/bin/owner-heartbeat-check.sh >> /home/drx/.cache/mipstarre-dev/watchdog/cron.log 2>&1
0 */8 * * * /home/drx/bin/estimate.sh >> /home/drx/.cache/mipstarre-dev/watchdog/cron.log 2>&1
```

Installed and independently re-read:

```cron
17 * * * * /home/drx/bin/qpbt-watchdog.sh >> /home/drx/.cache/mipstarre-dev/watchdog/cron.log 2>&1
37 * * * * /home/drx/bin/astra-poll.sh >> /home/drx/.cache/mipstarre-dev/watchdog/astra-cron.log 2>&1
47 * * * * /home/drx/bin/owner-heartbeat-check.sh >> /home/drx/.cache/mipstarre-dev/watchdog/cron.log 2>&1
0 */6 * * * /home/drx/bin/estimate.sh >> /home/drx/.cache/mipstarre-dev/watchdog/cron.log 2>&1
```

The complete before/after bytes differ only in `*/8` becoming `*/6` on the estimate
row. The three unrelated rows, their order, commands, redirections, and final newlines
are byte-identical. No environment or comment rows were added or removed.

Concurrency protection: Nonblocking advisory lock; exact action-time crontab/script byte comparison; immediate installed-state reread. No concurrent change detected. crontab has no atomic compare-and-swap interface.
The advisory lock coordinates cooperating editors only; an uncoordinated writer in
that final compare/install interval cannot be excluded by the crontab interface.

## Live script and configuration

- `/home/drx/bin/estimate.sh`: only the header's `8-hourly` became `6-hourly`.
  The complete remaining script bytes, report content, estimator formula, dates,
  account/model behavior, and executable mode `0755` are unchanged.
- `bash -n /home/drx/bin/estimate.sh` passed before and after the edit, including
  the final independent check. The estimator itself was not executed.
- The live `watchdog/estimate-issue` pointer remains exactly `168` with its original bytes.
  No additional estimate-specific live cadence configuration was found.
- `results/telemetry/owner-tools/estimate.sh` is the historical tracked copy and remains
  byte-identical to the pre-change live script; it is not the installed cron target.
  No historical reports, handoffs, or forecast values were rewritten.

## Canonical GitHub confirmation

- All GitHub reads and the single PATCH used the primary checkout's
  `/home/drx/MIPStarRE-qpbt/local/bin/gh_common.py`; no direct `gh` command was invoked by this session.
- Canonical issue: `https://github.com/Dengnifer/MIPStarRE-A/issues/168`; number `168`;
  API id `5347789246`; state remains `open`; labels remain empty.
- Previous title: `Completion estimate (8-hourly)`.
- PATCH response and independent re-reads confirm exactly: **Completion estimate (6-hourly)**.
- Issue body: only `every 8 hours` became `every 6 hours`; all remaining text is exact.
  Issue identity, labels, assignees, milestone, lock, and state metadata are unchanged.
- PATCH interval: `2026-09-06T05:24:29.835084+00:00` to `2026-09-06T05:24:31.091367+00:00`;
  canonical `updated_at`: `2026-09-06T05:24:30Z`.
- All 7 existing report comments retain their ids,
  bodies, and `updated_at` values exactly. No comment was created or edited.
- The title/body were re-read immediately before PATCH to reject an observed
  concurrent edit, and checked against the response and two subsequent GETs.

## SHA-256 evidence

| Object | Before | After |
| --- | --- | --- |
| Complete user crontab | `9c9d39b875a8cf5146abd3891bcb80dae08ffdb1d2ffa935df525eb07ece5a21` | `eaf1c4ae13a1c34434c3adc46e04c4203b7f7140a85f8f2f5664d76483fbd024` |
| Three unrelated cron rows | `28718cb3447e2c28abd3e3e56d336faafcc08429aa2a294ee239465222a5bf37` | `28718cb3447e2c28abd3e3e56d336faafcc08429aa2a294ee239465222a5bf37` |
| Installed estimate script | `96cbb2748fc62f2bb899aa220d02e80c74143681317bb8a19a62fd1cefb92099` | `cc85236a9db85fc5e2a3b348db2df2902ecd5f581b299067ea8993f7b13e5c88` |
| Estimate issue pointer | `c02efad74c4db35b2450beec922eb590d202b34c5b436bff0b6acc15059f5d21` | `c02efad74c4db35b2450beec922eb590d202b34c5b436bff0b6acc15059f5d21` |
| Issue body, UTF-8 | `35ef4ccf3623539fd4786dc217cece4b0082e6ea082dca5f7e106d06c886dd3e` | `1e5643f35def8ae39ce39fcaa4d3c00197964d04af8c79c20f1e8ae60199de8d` |

- Historical comment projection (`id`, `body`, `updated_at`), compact sorted-key
  UTF-8 JSON, before and after: `92e319795233810dc9d59664885bd2714a3428d44e4f514cc4a2c9256cf5ebb9`.
- Saved canonical PATCH response: `e3ab3b80fb066c0dd0c422af470fce3bc8794994ea89cb1f29da004bab880ffb`.
- Saved independent issue GET response: `e3ab3b80fb066c0dd0c422af470fce3bc8794994ea89cb1f29da004bab880ffb`.

## Backups and handoff

Exact prior cron and script, prepared/installed cron, original issue JSON, PATCH
payload/response, independent GET, comment snapshots, and structured verification
records remain in the private runtime directory:

`/home/drx/.cache/mipstarre-dev/watchdog/estimate-six-hourly-20260906-N1rEYk`

The originals are `crontab.before`, `estimate.sh.before`, `estimate-issue.before`,
and `issue.before.json`. Script metadata was preserved with `cp -p`; the backup
directory is private (`0700`). Runtime backups were not added to the repository.

Only this new dedicated telemetry artifact is authored in the worktree. No commit,
branch creation, primary-main modification, other-worker worktree modification,
protocol change, build, CI/review claim, merge, or unrelated GitHub mutation occurred.
The dispatcher owns the session-registry/final-message capture. Main may import this
artifact without reapplying the already-installed runtime or GitHub changes.

No access/permission failure occurred. A read-only `crontab --help` probe returned
its unsupported-option usage text; installation used the supported `crontab FILE`
interface and succeeded. Residual validation scope: the next scheduled estimator
execution and its future report have not yet occurred and were not forced.
