OWNER MESSAGE — wrap this session up now; a fresh session will continue.

1. Do not start new work and do not touch PR #5 or any worktree.
2. In the primary checkout, append this bullet to the existing `## 2026-09-02 — PR #5 review-fix cap` entry in results/telemetry/events.md: `- **Owner disposition (2026-09-02):** the merge-time cap is retired by amendment (issue #20 / PR #21, EVOLUTION.md 2026-09-02); PR #5 merges after a fresh-base merge of main — no cap override.`
3. Commit every pending edit in the primary checkout (the four 42-* briefs, the untracked local/briefs/0016-orchestrator-task.md and 0017-orchestrator-task.md, and the telemetry files) as one commit with a conventional subject such as `docs(briefs): stage 4.2 adjudications; telemetry`. Commit only — do NOT push and do NOT run github-sync.sh; the owner syncs main after PR #21 merges.
4. Run `python3 /tmp/amend_goal.py` (it prints "amended ..."). Do not edit anything else.
5. Reply with the commit SHA and a two-line summary of where stage 4.2 stands, then exit codex with /quit (or Ctrl-C twice).
