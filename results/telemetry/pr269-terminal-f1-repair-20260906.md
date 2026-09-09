# PR269 missing-evidence HOLD repair

Session `orc-257-20260906-07` implements only the F1 correction authorized by
main after second normal review `5124610152`, whose reviewed head is
`523cf79c25139e6de29f62e1be43f6955d29a453`. Primary `gh_common.py` confirmed
that review, the open PR head, and actual main
`928328ff4d45e5fdc2844b120329a2c241a3a58a` before editing.

## Behavior and exact comparison

Previously, refresh discovered only files still present in the filesystem.
A saved evidence cursor was not examined after its log disappeared, so a live
launcher's reservation could coexist with an incorrectly admitted next packet.
Refresh now observes the union of saved evidence paths and newly discovered
paths. Missing evidence raises through the existing exception-to-HOLD handler
before packet admission. The observer's inode, truncation, unreadability,
partial-event and backlog checks are unchanged, as are STOP/HOLD, identity,
ticket, dispatcher, router, review and launch-environment rules.

| Path | Reviewed blob | Repaired blob |
| --- | --- | --- |
| `local/bin/useful_queue.py` | `8cd494cd275ae4c50402386e2c35cf6730333a91` | `27b73a23a64412b78e5187e4e419b239275c64a5` |
| `scripts/tests/test_useful_queue.py` | `a8262e43830f7e4a539437b356d2c4169e00b730` | `e08b46968c734022315e47d3ca0ba1d909dab8a2` |

Both modes remain `100644`. Against the reviewed head the source diff is four
additions and six deletions, and the test diff is three additions. No existing
test line is removed. Refresh uses the keyed observer result directly, removing
two redundant local-variable lines. The cumulative nontelemetry patch against
actual main is 971 additions + 29 deletions = 1000 lines, without an override.
All other nontelemetry files, including the seven incoming PR195 mathematics
and blueprint files, remain byte-identical to the reviewed head. Actual main
remains an ancestor; no further base merge was needed.

## Deterministic validation

- Before the production edit, the regression failed: `AssertionError: 1 != 0`
  at the helper's new-launch count assertion. The test observes a launch log,
  keeps its launcher alive, queues a second packet, removes the log, and
  requires held status with zero new subprocess launches.
- After the fix, all nine queue tests passed in 3.104 seconds. Separate fake
  process checks of both launch-log and session-capture disappearance after
  supervisor restart found an actual HOLD file naming the missing path, zero
  new admissions, the original ticket, the saved cursor, and no second intent.
- The existing full suite passed all 555 tests in 50.079 seconds. This count
  includes the new scenario within an existing test method. Python compilation,
  whitespace, installed hooks, and the exact scope comparison passed.

Raw reproducer, focused and suite logs are under
`~/.cache/mipstarre-dev/sessions/orc-257-20260906-07-` with suffixes
`reproducer-before.log`, `focused.log`, and `suite.log`. The session capture
also retains the two restart checks. These are deterministic author checks,
not another independent review or production admission.

## Accounting and terminal ownership

All six prior implementation/publication executions remain charged: 5858
seconds, including both earlier failures and session -05's 600-second timeout.
Primary session registry rows 792, 809, 812, 828, 839 and 842 retain those
records; zero final usage on timeouts is not zero cost. Review rows 819 and
849 retain 628 and 634 seconds separately. Both normal model-review rounds
are exhausted. This bounded 900-second correction does not reset any budget.

The previous missing-Approx.olean incident, successful private targeted build,
raw history and preservation report remain intact. No protocol, mathematical
source, proof budget or original B8 anchor is changed. Checked publication and
detached canonical CI remain required; their final head, process and logs belong
in the session handoff. Main owns terminal disposition after inspecting this
repair and its evidence. No review, adjudication, merge or deployment is claimed.
