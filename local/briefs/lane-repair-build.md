# Lane repair task — build mode (`lake build` fails after the merge of `github/main`)

## Task

Repair the build of this worktree (branch `{{BRANCH}}`, pull request #{{PR}} of
{{REPO}}).  The worktree is `{{WORKTREE}}` and it belongs to lane {{LANE}}.

`github/main` is already merged and committed, but `lake build MIPStarRE.QPBT`
fails (see the first errors with: `lake build MIPStarRE.QPBT 2>&1 | grep -m5
error`).  Typical causes: modules renamed or removed on main (bad import),
declarations renamed, signatures changed.  Repair the pull request's files so the
build passes.

Never drop a theorem or a proof; no sorry, no admit, no new axiom.  Check every
touched Lean file with: `lake env lean <file>`; if a module was renamed or
removed on main, follow main (`git log --diff-filter=R -- <path>` or `rg` for the
moved declarations).  Do not push (the lane pushes).  Finish with a short list of
the files you changed and anything you could not repair.

Then commit with the message: `fix build after merging github/main`.

## Why these constraints are load-bearing

- A repair that deletes paths `main` carries still fails the lane's post-merge
  missing-path check (issue #222) and `local/bin/merge_loss_guard.py`.  Deleting
  a module that no longer compiles is not a build fix: it parks the lane again.
- The lane — not this session — publishes.  A push from here bypasses
  `local/bin/pr_open.py` and `local/bin/checked-push.sh`.
- `sorry`, `admit` and new axioms are proof-integrity failures, not repairs.  A
  build that only passes because a proof became `sorry` fails
  `local-ci/proof-debt` / `local-ci/proof-evasion` on the exact head.
- Do not edit `MIPStarRE/QPBT.lean` or another re-export file to route around a
  broken import: the operator serializes re-exports.  Name the re-export you
  need in the report instead.

## Report

End with:

1. the files you changed, one per line;
2. anything you could not repair, and why (name the failing modules and the first
   error of each);
3. the exact `lake env lean` invocations you ran and their outcome.

Do not report success unless every touched Lean file type-checks.

---

Provenance: this file is the committed task text for the `build` mode of
`results/telemetry/owner-tools/fix-lane.sh`.  The renderer substitutes the
pull-request number, the lane number, the branch, the worktree path and the
repository slug before dispatch, and refuses to dispatch if any placeholder token
is left unresolved — the task an orc receives is this text, never a shell string
literal.  The constraints above are the verbatim constraints the 2026-09-12
operator tool used; do not weaken them.
