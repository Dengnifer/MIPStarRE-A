# Auto-fix loop

Normative. Read `local/protocols/meta.md`, `issues-prs.md`, `ci.md`, and
`review.md` first.

`local/bin/autofix.sh <github-pr-number> --mode
{ci,blueprint,review,auto}` operates only on GitHub state and runtime artifacts.
The PR must carry the `auto-fix-codex` opt-in label. Setting
`LOCAL_AUTO_FIX_ENABLED=false` disables the loop; unset means enabled.

## Evidence and order

The command initially resolves the PR branch plus the full head and base SHAs
from GitHub. After taking the branch fix lock, it binds them again together with
the fetched local base ref and the initial local feature tip. It then reads only
a marker-bound CI manifest or valid review attestation for that exact full head
and base. A failed or error CI manifest remains readable; only designated
`failure` outcomes authorize a fix, while infrastructure `error` outcomes do
not. Fix categories are serialized `ci` then `blueprint` then `review`; audit
and synchronization failures are never guessed into an automatic repair.
Review-fix authorization uses the attestation parser's canonical unresolved
count, never checkbox-like text elsewhere in the review body. The count and
body come from one parsed attestation snapshot.

The manifest comment, review `COMMENT`, and their status rows must be published
by the configured trusted GitHub actor. Copied markers from another account are
not auto-fix authorization, and a newer untrusted status blocks selection under
GitHub's global latest-context semantics.

Each fix session is dispatched through `local/bin/dispatch.sh` using a trusted
persona and a fenced, sanitized evidence block. The session cannot publish or
merge. A successful repair is committed with the exact prefix
`[codex-auto-fix]` or `[codex-review-fix]`, pushed only to the explicit feature
ref, and followed by fresh exact-head CI and review as appropriate.
The trusted prompt ref is resolved once to a commit, must differ from the
original evidence head, and supplies both the prompt files and dispatcher
persona binding.

Before local advancement, the fixer revalidates its ownership token, absence of
a supersession cancel, the unchanged GitHub branch/base refs, the original
remote head and base SHAs, and the fetched local base immediately after locking,
before every dispatch, after every dispatch, and immediately before every
commit. The final pre-dispatch cancellation check is the phase-start
linearization point. A canonical cancellation bound to that exact claim and
written after this point may let the active phase finish one wrapper commit and
the leased push; it prevents every later phase. The remaining boundaries still
require exact ownership and the unchanged full comparison. Lost ownership or a
malformed, unbound, or changed cancellation record fails closed. Same-head base
movement therefore stops the run before dispatch, commit, or push.

Auto-fix is the one workflow allowed to advance the local feature tip before
publication. It tracks that expected local tip after each prefixed commit while
continuing to require the original remote head and base comparison. The final
push names the new local commit explicitly and uses a lease against the
original remote feature head; only a successful push establishes a new remote
comparison for later CI.

## Lock and cap

A machine-local per-branch lock under `~/.cache/mipstarre-dev/locks/` prevents
concurrent fixers, reviews, merges, and human write sessions on the same feature
tree. A workspace-write `agent.sh` invocation reserves that lock before
dispatch and holds it through dispatch completion; a read-only invocation need
not reserve it. The ownership-stamped layout is shared with review and merge:
PID, random UUID token, directory identity, and a digest of complete structured
owner metadata. A newer fixer receives the current complete claim from the
serialized acquisition attempt, then revalidates both that exact claim and an
`autofix ` owner prefix under the persistent sibling mutex before writing a
claim-bound cancellation record. A human-agent, review, or merge owner is never
cancelled. If the directory or owner changed in between, the replacement is
not cancelled. Loss of ownership or a malformed owner/cancellation record stops
the holder at a boundary.
Cancellation before local advancement stops it cleanly; cancellation after a
wrapper-owned commit starts no new phase. Any phase already running completes
at most its one wrapper commit, after which only ownership/comparison checks and
the original-head leased push remain, so no committed tip is stranded. Shell
command failures remain nonzero even inside phase-status handling; interrupt
and termination signals release only the owned lease and retain their signal
exit status. Cap-time release and signal cleanup use the same exact claim and
never remove another process's lease. Complete dead-parent records remain held
until explicit recovery because descendants may survive. Ownerless, malformed,
partial, and foreign-host locks also remain for explicit operator recovery. No
lock file is committed.

The combined iteration count is derived from the complete GitHub-visible PR
commit history. Only subjects beginning exactly with the two fix prefixes
count. GitHub's PR-commits endpoint exposes at most 250 commits, so a history
that cannot be proven complete is a hard failure. At the configured cap, the
wrapper removes the opt-in label, posts one marker-bound terminal comment, and
runs the required final review. It does not reset the count locally.

All mutations are online-required and exact-head. There is no committed fix
counter, PR frontmatter, local verdict authority, or offline success path.
