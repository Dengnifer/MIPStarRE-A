# Lane repair task — merge mode (conflicted merge of `github/main`)

## Task

Resolve the merge conflict in this worktree (branch `{{BRANCH}}`, pull request
#{{PR}} of {{REPO}}).  The worktree is `{{WORKTREE}}` and it belongs to lane
{{LANE}}.

The worktree is in the middle of a merge of `github/main` (git status shows
unmerged paths; if it is not mid-merge, run: `git merge --no-edit github/main`).
Resolve every conflict so that the pull request's definitions, theorems and
proofs are kept and main's newer definitions are respected.

Never drop a theorem or a proof; no sorry, no admit, no new axiom.  Check every
touched Lean file with: `lake env lean <file>`; if a module was renamed or
removed on main, follow main (`git log --diff-filter=R -- <path>` or `rg` for the
moved declarations).  Do not push (the lane pushes).  Finish with a short list of
the files you changed and anything you could not repair.

Then commit the merge with the message: `merge github/main into {{BRANCH}}`.

## Why these constraints are load-bearing

- A repair that deletes paths `main` carries still fails the lane's post-merge
  missing-path check (issue #222) and `local/bin/merge_loss_guard.py`.  Both
  guards are untouched by the repair path: resolving a conflict by deleting
  main's file does not get the pull request merged, it parks the lane again.
- The lane — not this session — publishes.  A push from here bypasses
  `local/bin/pr_open.py` and `local/bin/checked-push.sh`, which is the one gate
  that catches statement drift before it reaches GitHub.
- `sorry`, `admit` and new axioms are proof-integrity failures, not repairs: CI
  (`local-ci/proof-debt`, `local-ci/proof-evasion`) rejects them on the exact
  head and the lane parks again with a worse marker.

## Report

End with:

1. the files you changed, one per line;
2. anything you could not repair, and why (name the conflicting declarations);
3. the exact `lake env lean` invocations you ran and their outcome.

Do not report success unless every touched Lean file type-checks.

---

Provenance: this file is the committed task text for the `merge` mode of
`results/telemetry/owner-tools/fix-lane.sh`.  The renderer substitutes the
pull-request number, the lane number, the branch, the worktree path and the
repository slug before dispatch, and refuses to dispatch if any placeholder token
is left unresolved — the task an orc receives is this text, never a shell string
literal.  The constraints above are the verbatim constraints the 2026-09-12
operator tool used; do not weaken them.
