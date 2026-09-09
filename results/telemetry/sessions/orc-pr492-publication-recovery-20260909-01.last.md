Publication recovery completed.

- Published SHA: `854f237403dd32d6797bdddb09514cd60fcf27c7`
- Root cause: three merge bases caused pre-push `git diff --merge-base` failure.
- Repaired with an ordinary merge of saved head `271a688e` and then-current main `8d33601f`; merge-loss guards passed.
- Checked push passed all preflight checks.
- All nine `local-ci/*` statuses are green on the exact published SHA.
- GitHub reports PR #492 mergeable and clean.
- Worktree is clean; no associated failure marker existed.
- Autofix budget remains unchanged at 2/5.
- No semantic proof work or review launch was performed.

Current main subsequently advanced to `1c297a4b`; the graph retains a unique merge base and GitHub reports no conflict. Independent exact-head review remains for the main session.