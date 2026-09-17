**Ready**

Created [lane-v20.sh](/tmp/lane-v20.sh:92), inactive and copied from v19. SHA-256:

`d0723323404b5a2adcc3fa7747a9e638a029a9de33e3c36cc767d81c6be76ac9`

Only lines 89–92 differ. The unsafe command:

```bash
flock ~/.cache/mipstarre-dev/.full-build-lock timeout 2700 lake build MIPStarRE.QPBT
```

is replaced by:

```bash
"$P/local/bin/warm-worktree.sh" "$W" \
  --build --skip-packages --lock-timeout 2700
```

This uses the current primary helper at primary HEAD `1c297a4b8fb8a74b64784ba4c8fe7e10d0ffc6ee`. `LANE_WORKTREE` handling is unchanged, and all lines outside 89–92 are identical. The helper performs a full `lake build`; compiler output goes to its runtime log, whose path is reported in the lane build log.

**Verification**

- `bash -n /tmp/lane-v20.sh`: passed.
- No v20 process or real lane/build was started.
- Fixture used fake `lake`: lock was a directory with live owner PID `1965537`, inode `38681330`.
- A contender timed out without running fake Lake or altering the lock.
- The holder released its own fixture lock after completion.
- Assigned worktree has no tracked or untracked changes.

**Runtime Findings**

The split lock domain was verified:

- At `16:50:46 +0800`, the canonical path was regular-file inode `156327558`, held by `flock` PID `1885738`.
- At `16:52:06 +0800`, the pathname was directory inode `159400186`.
- PID `1885738` still held the old regular inode with link count zero, along with inherited holders `1885740`, `1890837`, `1894134`, and `1894136`.
- Earlier unsafe tree `1773279`/`1773280`/`1773281`/`1774284` showed the same flock-based pattern.
- All those unsafe holder processes have exited.

As of `17:05:30 +0800`, the canonical directory lock was legitimately held by verified PID `2081465`, `python3 /tmp/pr454-review2-build.py`. It was not touched. Legacy v19 lane PID `1554214` remains alive in PR 399 review, already past line 92; let it finish. The other v19 lane, PID `1554215`, completed. No merge daemon was running.

**Operator Action**

After PID `1554214` and the current canonical lock owner finish, change the inactive daemon launcher at `/tmp/merge-daemon-v9-locked.sh:26` to use `/tmp/lane-v20.sh` before restarting it. Recheck that no v19 or canonical-path `flock` process remains; remove no residual lock object unless open-file and PID checks prove it inactive.