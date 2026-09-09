# Recovery v5 stale watchdog marker reconciliation

Date: 2026-09-09 (Asia/Shanghai)

Session: `orc-recovery-v5-20260909-01`

Scope: only `pr195.failed`, `pr238.failed`, `118.needs-attention`, and read-only
stack-watch runtime reconciliation. No child sessions, proof work, manual merge,
main push, account/cap/admission change, credential change, or running-script edit
was performed.

## Archived marker evidence

### `pr195.failed`

- Runtime path:
  `~/.cache/mipstarre-dev/watchdog/daemon/pr195.failed`
- Original inode: `2824660`
- Original size: `0` bytes
- Original mtime: `2026-09-06 10:16:04.728802418 +0800`
- SHA-256:
  `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`
- Complete payload: empty file.
- Live GitHub verification, through `local/bin/gh_common.py pr-view 195`:
  `state=closed`, `merged=true`, `merged_at=2026-09-06T06:52:24Z`, merge
  commit `928328ff4d45e5fdc2844b120329a2c241a3a58a`.
- Local one-shot integration evidence independently records the same merge in
  `~/.cache/mipstarre-dev/pr195-integration-20260906T064900Z/attempt-1/daemon.log`.
- Verdict: obsolete. The marker predates the verified merge and cannot describe
  an actionable open PR.

### `pr238.failed`

- Runtime path:
  `~/.cache/mipstarre-dev/watchdog/daemon/pr238.failed`
- Original inode: `2824668`
- Original size: `0` bytes
- Original mtime: `2026-09-06 07:36:44.125446476 +0800`
- SHA-256:
  `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`
- Complete payload: empty file.
- Live GitHub verification, through `local/bin/gh_common.py pr-view 238`:
  `state=closed`, `merged=true`, `merged_at=2026-09-06T04:44:46Z`, merge
  commit `32a32edee16d3932525e4b1da9f84009e1fbb13b`.
- The recovery daemon log also records PR 238 passing the gate and merging as
  that commit.
- Verdict: obsolete. The marker predates the verified merge and cannot describe
  an actionable open PR.

### `118.needs-attention`

- Runtime path:
  `~/.cache/mipstarre-dev/watchdog/lanes/118.needs-attention`
- Original inode: `159850799`
- Original size: `140` bytes
- Original mtime: `2026-09-05 10:21:51.727657394 +0800`
- SHA-256:
  `587b751d9b58b365b481c430f872f27b2d319c29cc30af785eb50636a145f489`
- Complete payload:

```text
2026-09-05T02:21:51Z merging github/main conflicted in /home/drx/MIPStarRE-qpbt/.worktrees/issue-118-combined-lines-and-restricted-averages
```

- The matching historical lane log identifies the conflict as
  `MIPStarRE/QPBT/Test/PauliBasisTest.lean` during the September 5 merge.
- Live GitHub verification, through `local/bin/gh_common.py issue-view 118`:
  issue 118 remains open, with 36 sub-issues total and 35 currently open.
  `local/bin/gh_common.py pr-for-branch
  issue-118-combined-lines-and-restricted-averages` returned no PR.
- The original worktree is preserved at branch head
  `0f4ef05370350f4017439ebd839ef0561f13130f`. It has no `MERGE_HEAD`, rebase,
  cherry-pick, revert, or unmerged index entries. No active session registry row
  or other live process owned that worktree at inspection time.
- The worktree contains later work and was not modified during this recovery:

| Path | State | SHA-256 |
| --- | --- | --- |
| `MIPStarRE/QPBT/Extraction/Consistency.lean` | modified | `06a390ac3dead7be721880eb103f7a3cdbe05706c5ed725419c51f9574ab5694` |
| `audits/2026-09-06-issue118-point-error-dependency.md` | modified | `4f5eca5d5cffd8aba5f919a0d7d147a1f627767dc98eb757c5c8eafc4a42eeac` |
| `docs/paper-gaps/qpbt_combined-lines-error-term.tex` | modified | `7d1100cdd1e4b495fe84180fbb72e23b4fc94ac0cdf77a44604fadf42ac7f167` |
| `MIPStarRE/QPBT/Combining/PolynomialImageBounds.lean` | untracked | `871109bd97b6d50354dbf89f2d828cf4c4a9c2877a88b2aa4a654f764df42762` |

- Relative to the then-current `github/main`, the preserved branch was 48
  commits ahead and 399 commits behind, with multiple merge bases. No other
  issue branch contained its head. This is a historical monolithic checkpoint,
  not a current merge repair checkout.
- Current split successors reported by `gh_common.py open-sub-issues 118`:
  `373`, `376`, `379`, `380`, `387`, `389`, `395`, `396`, `402`, `405`,
  `406`, `408`, `413`, `414`, `419`, `422`, `427`, `428`, `435`, `437`,
  `444`, `445`, `451`, `452`, `461`, `462`, `466`, `474`, `480`, `482`,
  `484`, `485`, `486`, `489`, and `494`. Each was separately confirmed open
  through `gh_common.py issue-view`. A root-118 readiness traversal found active
  ready and blocked leaves; this successor tree, not the old conflict, owns the
  continuing formalization.
- Concrete replacements for the original monolithic targets include issue 376 /
  PR 382 for the restricted mixture and average block, issue 380 / PR 386 for
  `exists_subLineWitness`, issue 389 / PR 391 for the supplied-point error
  domain, issue 395 / PR 398 for the combined-line measurement constructor,
  and issue 419 / PR 424 for the generic finite conditional-average bound. All
  five PRs were confirmed open through `gh_common.py pr-for-branch`.
- Immediate stack dependency: issue 116 / PR 213, which is still open at GitHub
  head `b04ced12caec3c76ed015f5561f9db5b195d747b`.
- Verdict: obsolete. The exact conflict recorded by the marker no longer exists,
  work continued after it, and current ownership is the split successor tree.
  Removing this marker does not declare issue 118 complete and does not modify
  its preserved worktree.

## Stack-watch runtime reconciliation

- Runtime PID: `2339020`, PPID `1`, command
  `bash /tmp/stack-watch-v3.sh`, started `2026-09-06 09:04:49 +0800`.
- Script identity at inspection: inode `37510755`, size `1553`, SHA-256
  `b54e01ba82b1f79e61f317252c9569fa6765c897e32ee9c8a032d998d4ca4f18`.
  The running script was not edited or restarted.
- Cycle evidence from distinct 300-second sleep children:
  PID `2253226` was observed at `2026-09-09 11:41:09 +0800`;
  PID `2578309`, started `11:48:29`, was observed at `11:50:38`;
  PID `2776406`, started `11:58:37`, was observed at `12:00:35`.
  PID `3124194`, started `12:08:46`, was observed at `12:09:07`.
  The parent remained PID `2339020` throughout.
- At `2026-09-09T03:28:14Z` through `03:28:15Z`, stack-watch recognized merged
  bases and launched lane tails for issues 115, 116, and 117. Its current stack
  file contains only issues 118, 156, and 224.
- The issue 116 retry exposed a live runtime mismatch. Stack-watch/lane naming
  selected the conventional path
  `.worktrees/issue-116-expanded-line-measurements`, but that path is the
  preserved branch `issue-116-expanded-line-preserved-20260907`. The open PR
  213 branch `issue-116-expanded-line-measurements` is checked out at
  `.worktrees/issue-116-expanded-line-current`. Both local refs were at
  `ebba143d7d4cfa2eed49a34a0dc15ebf6535bf1b` during final inspection, while
  GitHub PR 213 remained at `b04ced12caec3c76ed015f5561f9db5b195d747b`.
- The retry log records a merge conflict and created a fresh
  `116.needs-attention` at `2026-09-09T03:28:24Z`, then issue 116 was removed
  from the stack queue. The marker existed during inspection and was not named
  by this session's deletion command, but disappeared concurrently before the
  `2026-09-09T12:09:07+08:00` post-check. Both issue 116 worktrees were left
  untouched. No live issue 116 lane process was found. A legacy native registry
  row still says `active` for PR 213, but v5 retires native/Space ownership and
  no matching live process was established, so that row is not treated as a
  current owner.
- The running script's lane guard matches `/tmp/lane-v13.sh` through
  `/tmp/lane-v15.sh`, while its launch command uses `/tmp/lane-v17.sh`. No
  running-script edit was attempted.

## Actions and residual blockers

- After this archive file was created, the exact three scoped paths were
  removed at `2026-09-09T12:07:47+08:00`:
  `watchdog/daemon/pr195.failed`, `watchdog/daemon/pr238.failed`, and
  `watchdog/lanes/118.needs-attention`.
- A post-check at `2026-09-09T12:09:07+08:00` confirmed all three remain
  absent. No wildcard or directory-wide deletion was used.
- The primary checkout's pre-existing dirty telemetry was preserved. Main moved
  concurrently during inspection; this session did not create a main commit,
  push main, or invoke a merge command.
- Residual blocker: PR 213 needs a separately owned reconciliation of its actual
  checkout, local unpublished head, GitHub head, and the externally removed
  issue 116 marker. Stack-watch no longer has issue 116 queued, so it will not
  repair that state by itself.
- Residual risk: when issue 116 eventually becomes contained in main,
  stack-watch will dequeue issue 118 and invoke its conventional worktree. The
  preserved issue 118 checkout is intentionally dirty and split work has moved
  to child packets; a future operator must choose the successor route rather
  than treating the old monolithic branch as automatically publishable.

Removal status: complete for all three scoped obsolete markers.
