# Useful-cycle recovery observations, 2026-09-06

This record separates service, orchestration and mathematical outcomes. Times
are UTC unless explicitly marked otherwise. Passing fixtures, process occupancy,
publication, independent approval, merge and operational replenishment are distinct.

## Queue timeouts and publication

- `orc-257-20260906-01`: 04:55:12–05:25:12, 1800 seconds, exit124,
  no final handoff. The original capture reports577 passing tests. The owner
  independently observed only five useful workers at05:26:27. No full queue
  installation or production replacement was verified at that boundary.
- `orc-257-20260906-02`: 05:40:10–06:00:10, 1200 seconds, exit124,
  no final handoff. The consolidated staged patch remained uncommitted, with
  exactly1000 added/deleted nontelemetry lines and555 passing tests. Both attempts
  requested max and share thread01a07512-0f37-7c12-8ffe-467b44bcc5e3.
- `orc-257-20260906-03`: 06:05:21–06:17:44, 743 seconds, exit0, selected
  xhigh for publication of the already validated implementation. Normal hooks
  reran555 tests in48.417 seconds. Commit799cd3dc5919783fe4ad907a4589f5ff179d7e95
  preserves the inherited staged tree1d349b893953ab2a8a0ef670eb2de0d2e5bb0b94.
  PR269 was independently verified at06:14:37; canonical CI finished green
  at06:18:02,191 seconds after its recorded start. Neither publication nor
  this CI result establishes review, merge, deployment or operational replacement.
- The first two registry rows contain zero wrapper usage because no final usage
  event was emitted. These are unknown terminal costs, not zero-cost attempts.
  After the integration stash was restored, main verified exactly one registry
  row for each of the three attempts. The publisher observed temporary absence
  during the stash window; it was not a final loss of the failed-attempt ledger.

## Separate launcher-admission incident

At05:29–05:31 an external `npm install --global @openai/codex` temporarily
removed `/home/drx/.local/bin/codex`. The authorized shim consequently failed
before model admission with exit127 for PR262 reviewer attempts01/02. These
are not model review rounds. The installer log is
`~/.npm/_logs/2026-09-06T05_29_41_759Z-debug-0.log` and reports exit0.
The installer restored codex-cli0.153.4; main verified the unchanged authorized
shim with `--version`, and subsequent real project workers launched successfully.
Already running old-image workers and main were not restarted; unrelated owner
sessions and credentials were untouched. Main made no installation or permission
change. This incident is distinct from both queue timeouts and earlier relay
concurrency refusals. CLI version is an observational confound, not a causal
explanation of effort differences.

## Separate GitHub transport incident

Queue publication first failed before push after130196ms during HTTPS
`ls-remote`. The system resolver supplied140.82.114.3 with a SYN-SENT connection;
fresh DNS supplied20.205.243.166, which reached GitHub with normal TLS validation.
The publisher used a process-local, loopback CONNECT tunnel restricted to
github.com:443 while retaining the github.com certificate identity, the existing
gh_common credential helper and the complete checked-push gate. No global
networking, remote, credential or TLS-verification setting was changed.
The retry published PR269 normally. The tunnel ends with its detached runner.
Raw stage/PID/exit evidence and the handoff remain in
`~/.cache/mipstarre-dev/sessions/orc-257-20260906-03-events.jsonl` and
`orc-257-20260906-03-handoff.md`.

## Validated integration and preservation

PR238 merged at04:44:46 as32a32edee16d3932525e4b1da9f84009e1fbb13b.
PR262 subsequently merged asb7705e02ef143e605981839009646c509f7df2ca; its pinned
normal daemon ended successfully at06:05:14. All nine exact-head CI contexts,
independent approval, current-base ancestry and other normal gates passed.
The post-merge tail fast-forwarded local main and both aliases. The formerly
private9102b74/2bb1a67 telemetry histories are thereby visible on GitHub.

The first clean-window attempt retained stash6f367190562a2622eee0ccc333d46127b2c91ee7
and declined to start a daemon when fresh terminal telemetry appeared. A fresh
verified second attempt retained077582bdec25355fb6aa4382db609b0e35be8458 and merged
normally. The restoration evidence records74 paths and9040563 appended/created
bytes, preserving incoming prefixes and saved raw-row multiplicities without
stash pop/drop or whole-file overwrite. Both stashes, bundles and inode backups
remain in `~/.cache/mipstarre-dev/pr262-integration-20260906T055159Z/`.
The coordinating model itself timed out1200seconds at06:11:59 without final
handoff; this failed session is retained separately from the independently
verified successful daemon and restoration. Later dirty telemetry is not claimed
published merely because the earlier private history merged.

## Admissions, limits and the next operational gate

At06:07:52 main observed eight actual useful Rust worker clients: B8 attempt12,
proofs266/267, queue publication257, policy247, integration restoration252 and
the two different PR265 review roles. This was a snapshot, not uninterrupted
floor compliance; subsequent completion bursts again required replenishment.
The allocation remains eleven workers plus main, with a conservative initial
recovery admission ceiling of ten, not a measured provider limit.

At06:20 the interim PR269 waiter falsely treated a quoted historical refusal in
PR195 recovery output as a live relay failure. Main inspected every live capture:
the matching event was `item.completed/command_execution`, not `error` or
`turn.failed`; no actual current refusal was observed. Six in-memory cases then
validated the temporary waiters structured-error correction. The reviewed queue
candidate already filters structured errors and did not require a source change
for this incident. No provider probe or benchmark was run.

The recovered preauthorized waiter observed seven real workers and launched the
normal PR269 review supervisor3556100 at06:23:12, after exact green CI. This is
real vacancy-triggered admission while main was occupied, like the earlier
PR254 waiter at05:17:38, but these finite review waiters are not represented as
the completed durable useful-work queue. PR269 still requires independent
review, fresh-base integration, joint source installation, prepared useful
packets and observed completion-triggered replacements before that claim.

## Mathematical decisions and durable links

Owner05:05 explicitly withdrew the old human B7/B8 holds. Main recorded B7
operator terminal disposition5124401997 at PR195 head1dfcbd2 after checking all
seven reviewed mathematical/blueprint blobs and nine green CI contexts. This is
not a fifth model review or automatic complete-patch carry-forward. PR262s actual
merge then required a new branch refresh and exact-head re-verification.

B8 attempt11 committed6e8d67ef8ba22de69a0c166adcdf23ba6e7a33aa: the established
two-player extended-line witness is proved, with the stronger printed bound and
downstream sufficiency still open. Its dispatcher time is2335seconds, so assessed
attempt12 carries22266seconds over eleven completed attempts, retaining the
2026-09-05T19:24:00Z anchor. Main authorized at most2700 further seconds, not a
budget reset or autonomous extra attempt. Normal proof checks remain binding.

Owner cycle/meta-cadence authority is in
`owner-messages/qpbt-owner-autonomous-cycle-20260906.md`; effort evidence is in
`model-comparison/`, including the supplied API-max/official-Ultra distinction.
Issue168s separate six-hourly GHZ schedule is verified in
`estimate-six-hourly-20260906-orc-168-01.md`; its next run is18:00 Asia/Shanghai
(10:00UTC), not yet reported as executed. One combined integration boundary was
posted to issue27 as comment5557378277; this record does not duplicate it.
