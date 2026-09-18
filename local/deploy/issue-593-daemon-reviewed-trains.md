# Reviewed train daemon deployment (#593)

Deployment is **not** part of the author commit. The running daemon and scan
stay unchanged until the ordinary PR gates, fresh independent review, and owner
deployment approval are complete. Use the committed patch beside this note;
it changes only `/tmp/merge-daemon-v9k-cpa.sh`. The adapter must already be on
published `main` in the primary checkout. Do not run `pr_train.py` by hand.

## Preconditions and activation

1. In the primary checkout, confirm `main` contains this change, the current
   runtime script hashes match the issue input (daemon
   `8c613b8d2807671f548b0ed7388e96e506c2817557421befe569a82a7fcdd091`,
   scan `0736ccc34432d08e181de471048cf45d1f9641f25e75c40fc55c9070167be7f8`,
   individual merge `c7c21be52ea5ccd8305b429f5a864140ff27ef0c873518ebe197b4953339bf54`),
   and PAR=0, no refreshing lanes, no pending refresh-done queue, and no other
   publisher. A mismatch requires a new review of the actual runtime diff.
2. Stop the one daemon gracefully with its existing `$D/stop` file and wait
   for its recorded PID to exit. Do not restart another merger. Check that
   neither a prior `train-approved.running.json` nor a train process exists.
   Preserve the original script for rollback; apply the reviewed patch with
   `patch --fuzz=0 -p1 -d /tmp -i <published-main>/local/deploy/issue-593-daemon-reviewed-trains.patch`.
   Run `bash -n` on the patched copy. Confirm only the one runtime daemon
   changed. The patch installs a synchronous train call *before* the fresh-PR
   loop, retains the individual path, and skips the hourly telemetry path in
   that cycle. An interrupted or failed attempt leaves `.running.json` and
   blocks a restart until the publication record is reconciled.
3. MAIN prepares one runtime-only `train-approved.json`, **after** verifying
   PR 580 and PR 587 are still independently approved at green exact heads,
   claims free and both included as `clean` in a complete scan. Read each
   current head via the primary `local/bin/gh_common.py pr-view N` (never from
   a saved snapshot); substitute the actual 40-digit SHA values:

   ```json
   {"members":[{"number":580,"head":"<580 current SHA>"},
               {"number":587,"head":"<587 current SHA>"}]}
   ```

   Store it as `$D/train-approved.json` only when ready to admit one batch.
   No adjudicated or unreviewed member enters this batch. Leave PAR=0 and all
   model lanes disabled. Restart only the existing daemon service after the
   approved file is in place; it alone invokes the adapter and train.
4. Coordinate MAIN's required status snapshot and other primary telemetry
   appends: finish or spool them outside primary before the train begins, do
   not write/commit/push primary telemetry while the train integrates and
   checks, then resume and fold the retained records afterwards. The adapter
   commits pending telemetry at admission. When local main is ahead by
   legitimate telemetry (e.g. 62b6b04f ahead of published b6c09eb0 at the
   checkpoint), it uses `github-sync.sh main` to publish the *existing* local
   commits and its snapshot; it never resets or rebases them. Sync failure or
   nontelemetry dirt blocks the train. The daemon's ordinary pre-merge and
   hourly telemetry batching remains intact outside this train cycle.

## Observe and reconcile

Read `$D/train.log`, the daemon log, and the retained train manifest and
`publication.json` before treating a zero exit as complete. After the first
live daemon batch, MAIN verifies GitHub's merged state, exact integrated member
heads, first-parent subjects and Lean deltas, claim releases and combined CI
evidence. A selected member dropped on conflict is **not** merged merely
because another member was published. A nonzero outcome (including failure
after publication) is neither a merge confirmation nor permission to retry:
keep `.running.json`, pause the daemon, and reconcile remote main and the
train's publication evidence first. Never erase an unknown outcome or local
telemetry commit to make the gate pass. Rollback only after reconciling any
in-flight publication, using the saved pre-patch script and normal service
controls; preserve all train and daemon logs.
