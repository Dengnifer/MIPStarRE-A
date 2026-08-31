# Auto-fix loop

Normative. Read `local/protocols/meta.md`, `issues-prs.md`, `ci.md`, and
`review.md` first.

`local/bin/autofix.sh <github-pr-number> --mode
{ci,blueprint,review,auto}` operates only on GitHub state and runtime artifacts.
The PR must carry the `auto-fix-codex` opt-in label. Setting
`LOCAL_AUTO_FIX_ENABLED=false` disables the loop; unset means enabled.

## Evidence and order

The command resolves the exact PR branch, base, and head from GitHub. It reads
only a marker-bound exact-head CI manifest and review ledger. Fix categories
are serialized `ci` then `blueprint` then `review`; audit and synchronization
failures are never guessed into an automatic repair.

Each fix session is dispatched through `local/bin/dispatch.sh` using a trusted
persona and a fenced, sanitized evidence block. The session cannot publish or
merge. A successful repair is committed with the exact prefix
`[codex-auto-fix]` or `[codex-review-fix]`, pushed only to the explicit feature
ref, and followed by fresh exact-head CI and review as appropriate.

## Lock and cap

A machine-local per-branch lock under `~/.cache/mipstarre-dev/locks/` prevents
concurrent fixers. The lock records the head it owns; a moved head supersedes
the run. No lock file is committed.

The combined iteration count is derived from the complete GitHub-visible PR
commit history. Only subjects beginning exactly with the two fix prefixes
count. GitHub's PR-commits endpoint exposes at most 250 commits, so a history
that cannot be proven complete is a hard failure. At the configured cap, the
wrapper removes the opt-in label, posts one marker-bound terminal comment, and
runs the required final review. It does not reset the count locally.

All mutations are online-required and exact-head. There is no committed fix
counter, PR frontmatter, local verdict authority, or offline success path.
