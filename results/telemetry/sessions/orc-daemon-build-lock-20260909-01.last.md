**Result**

The five-minute deadline was `2026-09-09T12:50:40+08:00`. It expired before a controlled restart was safe, so I made no edits and sent no signals.

- Original singleton: PID/SID `3517308`, `/tmp/merge-daemon-v9.sh`, log `~/.cache/mipstarre-dev/watchdog/lanes/daemon10.log`.
- Confirmed defect: v9 launches `/tmp/lane-v17.sh`, whose pre-push build has no `.full-build-lock`.
- Confirmed replacement: `/tmp/lane-v19.sh` uses `flock ~/.cache/mipstarre-dev/.full-build-lock` and supports `LANE_WORKTREE`.
- My exact diff: none. `/tmp/merge-daemon-v10.sh` remains absent; repository files were untouched.

After the deadline, concurrent owner-side activity created `/tmp/merge-daemon-v9-locked.sh`. Its exact diff from v9 is only `lane-v17.sh` → `lane-v19.sh`, retaining `PAR=4` and all merge/exact-head gates. However, it was not the active singleton at the final check.

At approximately `13:00+08:00`, runtime state was:

- PID/SID `3729228`: `/tmp/merge-daemon-v9.sh`, logging to `daemon10.log`
- PID/SID `3736298`: `/tmp/merge-daemon-v9b.sh`, also logging to `daemon10.log`
- Live refresh PID `3807197` for PR 343 remained preserved
- No active `/tmp/merge-daemon-v9-locked.sh` leader was confirmed
- `daemon11.log` was empty

Thus there was no singleton at final verification. The concurrent `v9b` also sets `PAR=1` and still selects v17, contrary to the instruction not to reinstate superseded build caps. I did not stop either service because the deadline had passed and live work was present.