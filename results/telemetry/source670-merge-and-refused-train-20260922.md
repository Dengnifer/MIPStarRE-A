# Runtime receipt during the comparator train

PR670 source audit: actual independent canonical COMMENT5269136643 approved
both phases at ac8343a4fe4e162821a1abd93b3506f7276403f4, zero findings.
Prose reviewer-pr670-20260922-01 ran430s; code reviewer-pr670-20260922-02 ran645s;
both exit0, Astra/ultra source-semantic rationale already recorded.
Service merge14bd77a76112e98a644bb104163e678f15cb4721 occurred16:25:15Z;
daemon completed its publication16:25:57Z. Published main709ed0cd includes it.
The audit still has13 nonterminal rows and7 unmarked nodes.

The concurrent telemetry publication raced that service merge. Its final
snapshot push failed, but f7789b03 (the approval/author-cost receipt) is verified
as an ancestor of resulting main, the primary is clean, and local/remote main
agree. No source or session data was discarded. Do not infer a stopped job
from a stale .exit file or a missing publication line while the process lives.

PR671 exacta3683e9b was gated by /tmp/meta-gate.py against actual
COMMENT5269105540 and all9 successful CI contexts. Both671 and660 are STALE
under pr_merge.head_is_fresh after the substantive650/670 merges, not merely
newly reviewed. Their local branches equal actual published heads, clean.
Parent660 is an ancestor of671. After ordinary records publication and a clean
published main, /tmp/meta-stage-train.py 660 671 staged exact heads418e0271 and
a3683e9b. The daemon consumed train-approved.running.json and started actual
daemon_train.py PID3230015 / pr_train.py PID3233634. No fresh ancestor candidate
was listed and no PR merge was run by main. Git's local merge-tree lacks the
--write-tree option; the two failed read-only prechecks changed no refs/files.
The provided precheck helper was not used because it calls gh outside gh_common;
the canonical train performs its own real merge/conflict and evidence checks.

Both freed slots were refilled with separate PR/worktree scopes:
- orc-666-20260922-01, thread01a0c4da-115f-7703-888a-18ece3785e84,
  Sol/ultra900s integration of now-merged670 into PR669. This is a new bounded
  dependency integration, not a reset of the exhausted1201s review repair.
- blueprint-667-20260922-02, thread01a0c4da-40f9-7c10-9c78-0a5ba031dc17,
  Astra/ultra source_semantic1500s, source709ed0cd. Only cross-basis-phase and
  decoding-identity claim retention and adoption evidence. Known predecessor
  audit/review2835s and all earlier gap histories stay charged. No new correction
  search, proof of a refuted statement, game change or #118 renewal is allowed.

Both routes use cpa after the authorized migration. Detailed briefs and wrappers
are /tmp/main-cpa-{integrate669,retention667}-20260922.{md,sh}. Primary telemetry
publication for this receipt is deferred until the train quiet window ends;
no completion claim or gate weakening is authorized.

Official preliminary Actions35621468975 actually completed success16:29:47Z
as observed by its model-free monitor. Sourcea3683e9b is still pre-merge; detailed
job logs are being obtained by /tmp/main-cpa-official662-evidence-20260922.sh.
Final C5 still requires service-merged main, a new coherent pin/run, and the
reviewed acceptance record in docs/comparator.md. The current run must never
be described as already satisfying that final pin requirement.

## Refused Train

Train train-ciji6fps dropped660 on a real merge conflict. The671 integration
preview passed the merge-loss guard, but fewer than two members remained, so
publication correctly refused. Both actual train processes and the daemon
exited; no source PR was published. The retained runtime directory and running
batch marker are evidence for the ordinary takeover recovery helper. Do not
re-stage this same ancestor/descendant pair. The approved671 replacement needs
a separate normal refresh;660's history must remain preserved until its content
is actually integrated. Do not manufacture another member or waive the gate.

Official-job metadata readback succeeded. The first log download was refused
by gh because its output contains terminal escape sequences, not by GitHub
permissions. The retry uses the documented --allow-escape-sequences option
while redirecting captured output to a file, never executing log content.
