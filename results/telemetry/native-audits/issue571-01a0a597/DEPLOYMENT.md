# Issue 571 Runtime Deployment
MAIN deployed the verified native proposal on 2026-09-15 at 15:28:19Z.
The old daemon, PID 3193730, exited through its stop-file protocol. The guarded
wrapper checked the exact PID/command, absence of live refresh holders, and
caps 0/0/0 before requesting the stop and again before starting the replacement.
Only its own stop token was removed. No running script was edited or signalled.
The replacement is PID 3395055, `bash /tmp/merge-daemon-v9i-cpa.sh`, parent PID 1.
MAIN verified its actual environment contains `PAR=0`, the old PID is absent,
and no stop file remains. A transient same-command child was a daemon subshell,
not a second service; it exited after the scan.
Runtime files are read-only copies, independent of worktree cleanup:
- `/tmp/daemon-scan-cpa-571-20260916.py`: SHA256
  `0736ccc34432d08e181de471048cf45d1f9641f25e75c40fc55c9070167be7f8`.
- `/tmp/merge-daemon-v9i-cpa.sh`: SHA256
  `7562614a1326b0b3d87b77c35b4b5a709d64b21bf5672da1ad5a2b664b6b7b96`.
- `/tmp/qpbt-daemon-571-restart-20260916.sh`: SHA256
  `1f086b041338ba31f23b87a545770fcf097c175bfe85161255215f35621a1118`.
The helper bytes match the reviewed proposal. Compared with the original v9h
daemon, the complete diff changes only the helper path and the default PAR from
1 to 0. Both shell files passed `bash -n`. All merge, exact-head, freshness, CI,
review and adjudication gates remain unchanged; only the daemon may merge.
No lane, key/cap change, stack-watcher restart or registry deletion occurred.
The first deployed scan reported complete coverage of 74 open PRs in eight
metadata pages, 28.889 seconds, zero candidates, and zero review queries/bodies.
The report is appended to `~/.cache/mipstarre-dev/watchdog/daemon/scan.err`.
The deployment log is
`~/.cache/mipstarre-dev/watchdog/lanes/daemon-cpa-571-20260916.log`.
Earlier scan failures remain in the logs. Fifteen fixture tests and the complete
artifact manifest were independently rerun by MAIN before deployment.
Issue 571 remains open for a bounded live scan when a review-eligible head
exists: review-body retrieval and nonempty candidate emission are fixture-tested
but have not yet been exercised live. A successful empty-candidate scan is not
evidence of a successful merge or of every network path being exercised.

## Subsequent Nonempty Scan

On 2026-09-15 at 15:44:32Z the deployed daemon emitted PR549 as an adjudicated
candidate. That scan covered all 74 PRs in 18.075 seconds, with one candidate
and zero review-body queries. The daemon then passed its unchanged gates and
merged PR549 as `40ca8cd5257649d2ef429724c308165f03925a55` at 15:45:06Z,
independently confirmed through primary gh_common.py. The registered literal-head
adjudication was accepted; no MAIN merge command was used.

An earlier read in the same cycle saw the preceding empty scan. A bounded
GraphQL comparison confirmed that the PR commit node was the actual b49709fc
head and its statuses agreed with the direct commit object. The apparent delay
was normal scan cadence, not a metadata or selector failure; no repair was made.

Nonempty adjudicated-candidate emission has therefore now been exercised live.
Clean-review body retrieval remains fixture-tested only, and issue571 stays open
for that narrower remaining transport check. Earlier evidence is retained above.

## Review-Eligible Live Coverage

The scan ending before the daemon's 2026-09-15T16:34:35Z candidate entry covered
all 73 open PRs in eight pages and 18.958 seconds. It fetched exactly one
eligible-head review batch, containing two review bodies, and emitted one clean
candidate, PR568. The daemon subsequently passed its unchanged gates and merged
PR568 as `29f0c16c737a5069a0b178d49e877416c5fa5824` at 16:35:05Z, confirmed
through primary gh_common.py. Subsequent scans covered the remaining 72 PRs.

MAIN rechecked the deployed helper/daemon hashes and live PID3395055 with PAR0.
Both runtime files still match the deployment hashes above. Empty, adjudicated,
and naturally review-eligible clean paths have now been exercised live; the
error/mismatch predicate cases remain covered by the 15 fixture tests.
The repair's stated verification is complete. Issue571 can be closed with this
evidence; this is not a claim that future network failures are impossible.
Earlier failures, narrower coverage statements and all costs remain preserved.
