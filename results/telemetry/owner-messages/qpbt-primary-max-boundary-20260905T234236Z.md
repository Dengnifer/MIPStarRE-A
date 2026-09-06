# Primary relay / Astra max owner boundary

Observation: 2026-09-05T23:42:36Z; follow-up checks through 23:44:29Z.
Publication state: pending; this file is not evidence of a GitHub comment.

The owner now requires primary relay only, 12 total concurrent uses including
main (at most 11 workers, less other use), and gpt-6-astra at literal max for
every ghz session. Sol and automatic Codex fan-out are prohibited. Secondary
credentials/history and an explicit future primary/both toggle must remain.

Main has read the latest owner brief. The main launcher requests primary/max,
but fleet enforcement is **not verified or installed**: the checked-out
router still permits both accounts and admission at capacity after timeout;
the login review export and worker shim still request xhigh. No new worker
or provider probe was launched by this main turn.

Access prevents the required safe transition: GitHub access fails with
`socket: operation not permitted`, host processes are hidden by the tool
namespace, and creation of a dispatcher-runtime lock directory fails with
`Read-only file system`. The snapshot's zero-worker count is not a host count.
No secondary worker has been declared stopped from missing namespace PIDs.
Owner-approved access is required for host verification/control, runtime
locks/configuration, GitHub, and normal gated Git writes. No bypass was used.

Local reports show PR238's previous xhigh head approved, then a daemon
main-refresh conflict in events.md (`pr238.failed`). The old Sol implementer
is recorded done. Issue113/PR195 and issue118 attempt7 have recent capture
writes but unverified host handles. Preserve their proofs and shared budget;
the owner-provided baseline is 9852 charged seconds, six completed attempts,
attempt7/10, original anchor unchanged. Do not duplicate them.

The bounded amendment brief is `local/briefs/237-relay-primary-astra-max.md`.
After access and occupancy verification, delegate it to one primary/Astra-max
worker, use normal exact-head CI/review and daemon-only merge, then resume
PR195 -> PR207 -> PR213/PR212 -> issue118/issue156. Meta remains oversight only.

## Follow-up observation: 2026-09-05T23:49:14Z

The issue113 recovery is now terminal: registry end 23:47:33 UTC, terminal
capture present, local checkpoint f1d1d3c7a1f421b255aec30c485ce593ad8e4905.
Its report records publication and nine green CI contexts but concludes
open/unmerged, mergeable=false, with exact-head review absent. Those remote
facts remain worker-reported because main still cannot reach GitHub. Preserve
the existing fourth-round review/dispositions; do not duplicate recovery or
launch an extra review. The snapshot now shows only pr238.failed, not a
verified PR195 merge. Issue118 attempt7 has no terminal event or last report.

The same access restrictions were rechecked and persist. No additional #27
comment was attempted; reuse the existing boundary marker after approval.

At 2026-09-05T23:51:06Z, the third consecutive access audit confirms the
same blocker, including a failed direct `gh_common.py pr-view 238` request.
There is still no terminal issue118 attempt7 record. The runtime caps remain
19/10/9 and profile/shim effort remains xhigh. Deployment and worker
transition require owner-approved access; no safe dispatch or publication is
possible in the present sandbox. This remains the single pending boundary
report, not a claim of a completed transition or a published GitHub comment.

Superseded after owner-approved access was restored on September 6:
`qpbt-primary-max-access-restored-20260906.md` is the current boundary body.
The existing marker was published once as #27 comment5555957194. Historical
access failures above remain evidence, not current blockers.
