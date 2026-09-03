# Owner log — interventions by the owner's session (Claude Fable 5.1)

Chronological record of what the owner-side session did to the project, why,
and where the evidence is. Complements `events.md` (incidents, written by
whoever hits them), `EVOLUTION.md` (protocol amendments) and `owner-audits/`
(the audit data). Owner-side scripts are archived under `owner-tools/`; the
directives sent to the operator session under `owner-messages/`. The live
copies run outside the repository on purpose (`~/bin`, `/tmp`, cron).

Repository: `Dengnifer/MIPStarRE-A`. Operator: the codex (gpt-5.6-sol) session
"qpbt-main" in tmux `qpbt` on ghz. Times UTC.

## 2026-09-01 — Overbuild contained; lean GitHub-native workflow rebuilt

- **Found:** the operator had spent 17 h / 21 commits / +14.6k lines on
  workflow scaffolding (bespoke API client, lock manager, 5.6k-line test suite
  in the hooks) with zero Lean progress; verbal corrections had not stuck.
- **Did:** paused it; archived the work as `telemetry/issue-0007-overbuilt`;
  rebuilt the layer lean (net +464 lines: `gh_common.py`, exact-SHA merge
  gate, marker-idempotent statuses/reviews) with an opus agent fleet plus
  adversarial verification; PR #7 merged as `e3349ea` after four review
  rounds and a §12 adjudication; follow-ups #8–#15.
- **Guard added:** pre-commit refuses >400 changed workflow-layer lines
  unless the owner sets `MIPSTARRE_INFRA_OVERRIDE=1`; persona "Scope control"
  section; standing briefing `~/.codex/prompts/goal.md` (pasted at launch —
  codex's built-in `/goal` shadows custom prompts).
- **Launched** the first gpt-5.6-sol operator session.

## 2026-09-02 — Fix-cap stall; operator behaviour bounded; channels to the owner

- **Found:** PR #5 (QPBT skeleton) green but blocked by merge gate 6 (six
  `[codex-review-fix]` commits > cap 5); the operator escalated to the owner
  because gate text said "human attention" and the briefing forbade weakening
  gates. Audit (six read-only lanes, three refuters; `owner-audits/audit-full.json`)
  found the cap carried no safety property.
- **Did:** issue #20 / PR #21 retired the cap and enumerated the single
  owner-gated control; two reviewer rounds (13, 14 findings, seven of them
  re-raises) → owner adjudication at `4a0d5ec`, merged `2bb76f7`; issues #22–#24
  for the pre-existing residue. Retired the first operator session (its work
  committed as `f94fe3c`), amended the briefing, launched a fresh session with
  `owner-messages/qpbt-main-handoff.md`.
- **Measured the reviewer lane** (14 agents; `owner-audits/reviewer-assessment.json`):
  1h50m and 34M tokens for a 188-line PR, 84 % of reads outside the diff, a
  finding quota (~17) regardless of size, no memory across rounds → issue #25
  (landed by the operator as PR #28).
- **Channels:** pinned issues #26 "Owner inbox" (one BLOCKER per comment, plain
  language, only what truly needs the owner) and #27 "Progress log"
  (`owner-messages/qpbt-inbox-directive.md`, `qpbt-inbox-addendum.md`).
- **Also:** clean retirement pattern for background waits (detached
  `setsid nohup` scripts + marker files + one wake-up) to save owner-session
  quota.

## 2026-09-03 — Disk migration; eight-hour stall; watchdog

- **Found (disk):** root filesystem 97 % full; the project was 87 GB, 58 GB of
  it eight identical 7.3 GB copies of `.lake/packages` (ext4, no reflink).
- **Did:** shared read-only package store `~/.cache/mipstarre-dev/packages/<key>`
  (`key = sha256(lake-manifest.json ‖ lean-toolchain)[:16]`, `chmod -R a-w`);
  live migration by same-filesystem `mv` + `ln -s` on every checkout
  (`owner-tools/migrate-packages.sh`), verified with `lake build`
  (8,984 jobs) against the store. Project 87 → 28 GB; disk 185 → 237 GB free.
  Code/protocol change: issue #50 / PR #51.
- **Found (stall):** no merge to `main` for 8 h. Causes: (1) the operator
  serialized on PR #51 through three reviewer rounds, grew it 107 → 400 lines
  and opened five hardening issues (#54–#58); (2) two PRs (#39, #44) green on
  their exact heads for hours, unmerged; (3) codex's automatic approval review
  timed out on escalated commands and rejected them ("Automatic approval
  review timed out"), so some merges never executed.
- **Did:** reset PR #51 to its original head plus a ten-line fix (`6286280`),
  adjudicated it after its fourth round; closed #54–#58 as not planned; one
  hygiene follow-up #59; directive `owner-messages/qpbt-stall-directive.md`
  (merge green PRs first at every iteration; ≤2 review rounds then adjudicate;
  never grow a PR to satisfy findings; findings asking for mechanisms are out
  of scope).
- **Guards added:** hourly owner-side watchdog `owner-tools/qpbt-watchdog.sh`
  (installed at `~/bin`, cron `17 * * * *`, state in
  `~/.cache/mipstarre-dev/watchdog/`): trips on stale main ≥4 h, a green PR
  unmerged ≥1 h, a PR past 2 review rounds, or a paused pane; nudges the
  session and posts a plain report to #26 (first live report 16:32Z).
  Operator relaunched with `approval_policy=never`, `workspace-write`,
  network on, telemetry cache writable (`owner-tools/relaunch_qpbt_noescalation.sh`)
  so no command waits on the approval reviewer; to be baked into
  `main-session.sh` (PR #41).
- **Lessons recorded** in `events.md` (2026-09-03 entries): "merge what is
  green" is the first step of every loop; a stall guard must live outside the
  thing it guards; a shared dependency tree is safe when writes fail loudly.

## Owner-side artifacts (live locations on ghz)

| Artifact | Live location | Archived copy |
|---|---|---|
| Watchdog | `~/bin/qpbt-watchdog.sh`, crontab `17 * * * *` | `owner-tools/qpbt-watchdog.sh` |
| Package-store migration | `/tmp/migrate-packages.sh` | `owner-tools/migrate-packages.sh` |
| Operator launch / relaunch | `/tmp/launch_qpbt_main.sh`, `/tmp/relaunch_qpbt_noescalation.sh` | `owner-tools/` |
| Standing briefing | `~/.codex/prompts/goal.md` | (operator-owned) |
| Directives to the operator | tmux pastes | `owner-messages/` |
| Audit data | — | `owner-audits/` |

## 2026-09-03 — Owner session takes the operator role (2026-09-03T23:21:32Z)

- **Why:** after the stall and reviewer-churn episode the owner asked the
  Claude session to run the operator loop itself for one to two days, with
  codex worker sessions on ghz unchanged.
- **How:** codex main session posted its handover state to #27 and quit;
  telemetry `stages.jsonl` event=takeover; astra availability polled hourly
  by `owner-tools/astra-poll.sh` (cron :37); the stall watchdog keeps running
  and now nudges the owner session through #26 rather than a tmux pane.
- **Hand-back:** on the owner's word; recorded as event=handback with the
  state at that moment.
