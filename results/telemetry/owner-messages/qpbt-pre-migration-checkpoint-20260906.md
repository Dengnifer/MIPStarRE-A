# QPBT integration and migration checkpoint

Recorded 2026-09-07 after the owner-requested space-cap5 cycle.  No credential,
home-routing, model migration, or migration-script edit was made in this
checkpoint.

## Main and remote

- Local `main`: `e1fba87aba13615d4ca7040367326c039b32c2bf`.
- GitHub `refs/heads/main`: the same `e1fba87aba13615d4ca7040367326c039b32c2bf`.
- Primary checkout is clean.  The only pre-existing parked stashes are
  `a166dcf6d7457eafa0846bbda8de4c5d97ed20b1` (post-merge warmer row),
  `eece7e1f901c9840cf0a6d5b8224f78ef9642e24` (PR254 CI rows), and the older
  integration-preservation stashes `2b87495689367ace4146e0eeec9060da2389a646`,
  `46c5682018c2a0c3b684960ccd033f69f9b7a157`, and
  `1664884773333aa68dc08ae626baed7b5cd738e3`.  None was dropped.

## Worktree ownership

Dirty worktrees are intentionally retained under their owning lanes:

- `issue-118-combined-lines-and-restricted-averages`: modified extraction
  consistency, audit/gap note, and untracked `PolynomialImageBounds.lean`.
- `issue-168-estimate-six-hourly`: untracked estimate catch-up/report files.
- `issue-261-supported-mass-comparison`: staged QPBT/Combining/ErrorBounds,
  blueprint, audit and estimate files; this is the stale-index/transaction
  lane and remains untouched.
- `/tmp/mipstarre-18-core`: modified telemetry sessions and untracked prover
  capture/final-message files.

All other registered worktrees were clean at this audit.  Preserved transaction
markers include the PR264 CI recovery lock, PR245 CI supervisor lock, PR257/259
publication locks, PR246/247 publication locks, PR195/238 daemon failure
markers, and the issue257 abandoned-index lock.  No marker was deleted.

## Receipts and gates

- PR254/#244 refreshed at `d5f9dfe`, then `053e30d`, with exact CI success,
  carried approved review `5126051767`, and daemon-owned merge `ad5adbed43d6d933608c7824219577b0fe463a29`.
- PR290/#287 exact head `a3eb4d57` has CI success and native Ultra approved
  review `5125870231`; it remains open/stale against the current main and was
  not merged.
- B8/issue118 retains 13 attempts and `26509` cumulative working seconds;
  no attempt or budget was reset.

## Service and native runtime

- Legacy `/tmp/merge-daemon-v8.sh` PID2339019 and `/tmp/stack-watch-v3.sh`
  PID2339020 remain SIGSTOPped; their last recorded failure was the historical
  PR195 SSH reset.  They were not resumed.
- Corrected service PID1664171 runs
  `merge-service-space-cap5.py --merge --interval 300` under its lock.
  Last tick: `2026-09-06T17:32:59Z`, local/remote main `e1fba87`, primary
  clean, cap5/external0 verified, duration `36.209s`, eligibility budget
  `240s`, cadence sleep `263.791s`; all remaining eligible candidates were
  stale, so the action was HOLD and no merge was attempted.
- Native root thread `01a076bc-f4ad-7813-805b-c8b4dac71a14` is PID1064752,
  process start `172784739`, `gpt-6-astra`/literal Ultra on the scoped space
  route.  Owner allocation is total5, descendant lease4, external gate0.  The
  locked lease record is `{pid:1064752,start:172784739,slots:4,key_label:space}`;
  usage remains null and no provider-throughput claim is made.

This packet is a state handoff only.  It does not authorize migration, manual
merges, credential changes, source deletion, or bypassing CI/review gates.
