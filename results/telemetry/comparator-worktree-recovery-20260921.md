# Comparator worktree recovery, 2026-09-21

MAIN incident observation at 2026-09-21T10:43:07Z. Recovery remains in progress;
this record does not certify complete recovery or comparator acceptance.

## Failure and cause

The old-pin diagnostic comparison completed with a headline-statement mismatch
for `MIPStarRE.QPBT.pauli_soundness`, as expected from comparing the repaired
direct-effect challenge to library pin `a942ecb5`. Both exports are retained;
this run provides no acceptance evidence for the current library.

At 10:37:15 UTC the sole native author connected a temporary package directory
to the live issue-662 author worktree using a symlink named MIPStarRE, then ran
`lake build Solution` in the external comparator checkout. Lake reported:

```
info: MIPStarRE: URL has changed; deleting
  '/home/drx/QPBT-comparator/.lake/packages/MIPStarRE' and cloning again
error: inappropriate type (error code: 20, not a directory)
```

The dependency link targeted
`/home/drx/MIPStarRE-qpbt/.worktrees/issue-662-comparator-acceptance-20260920`.
Lake's replacement removed that worktree's contents, including its .git pointer
and private .lake directory. The primary repository's Git worktree metadata and
index survived. The first setup command at 10:37:02 had been rejected by the
automatic tool review for its rm-style deletion; it did not execute. The
subsequent fresh-directory/symlink setup executed and caused this loss through
Lake's dependency management.

## Recovery observed so far

The author restored the external packages link to its prior cache directory,
recreated the author worktree's .git pointer, restored tracked files from its
surviving index with checkout-index, and warmed only its private build through
the canonical worktree-setup helper. Committed HEAD `d9a380b8`, the pending
PR 660 merge, and staged changes survive.

Index recovery is insufficient to establish full recovery. MAIN's 10:32:11
census recorded an unstaged change to the newly staged
scripts/comparator/challenge_config.py (`AM`) and the untracked predecessor
ProofProbe.lean. After restoration the configuration is only staged (`A`) and
the scratch file is absent. Both need recovery from retained patches/rollouts
or an explicit account of missing content.

At 10:40:26 MAIN interrupted the same author task for a bounded five-minute
incident checkpoint, with no further comparator runs or expanded edits until
the cause and missing-file accounting are settled. The existing 10:56:55.140
deadline and all earlier costs remain; there is no new budget or parallel
writer. The author is told to retain checks already run and every recovered
change, and to write /tmp/main-comparator-space3-continuation-20260921.md.

## Required continuation

Recover the unstaged configuration edit from the current native rollout and
the scratch file from the preserved predecessor rollout. Verify the recovered
source and focused tests before claiming a stable candidate. Future diagnostic
runs must consume a disposable independent Git checkout at a coherent source
pin. A live author worktree must never be exposed as a managed Git dependency
through a package symlink: Lake may replace that dependency while reconciling
its URL or revision. No credential, account, gate or completion criterion was
changed to address this incident.

Evidence: native author 01a0c373-664c-7123-bde2-1786665a2da3, tool calls and
outputs from 10:37:02 through 10:38:55; prior author
01a0c25b-c0be-7e52-b34b-b93341ae2f81 retains the original scratch-file history.

## Recovery verified and task closed

The author completed exact recovery before its final response at
10:45:02.754 UTC. The unstaged configuration support was restored from the
predecessor's recorded patch (rollout zero-based ordinal 501). MAIN compared
the recovered file's diff from published PR 660 with that patch: the split
and common_opens schema documentation, accepted keys, fields, validation and
constructor arguments match. This supersedes the earlier reconstruction-only
observation above.

ProofProbe.lean was restored untracked by replaying the predecessor's three
recorded patches. MAIN independently preserved the same final text under
/tmp/issue662-ProofProbe-recovered-20260921.lean. Both files have SHA-256
`2f9526a36207a4568b9314909df01a1a6151e4e477c2f441686daa3af1a22e8f`.
The probe was not rerun or adopted as library proof content. No missing
pre-incident untracked/unstaged file remains identified.

The author thread is closed. Actual runtime was 1987.614 seconds from
10:11:55.140 through 10:45:02.754, including incident recovery and all
continuations. No commit or PR publication occurred. The recovered staged
tree at the start of MAIN's subsequent validation is
`9e681b196dd70bef743de35de5f402237d2a2f72`, with HEAD `d9a380b8` and pending
MERGE_HEAD `418e0271`. LDT drift, compilation against freshly rebuilt metadata,
ordinary publication, CI, independent review and current-source comparator
acceptance remain work to do.

At 10:48:04 UTC MAIN started the canonical warm-worktree --build command on
the frozen recovered tree under the machine-wide lock. Its log is
/home/drx/.cache/mipstarre-dev/logs/worktree-build-20260921T104804Z-682081.log.
This is a build of the stated working tree, not a PR CI status for its old
published head. The sole native slot moved to fresh independent PR 659
reviewer 01a0c393-90ef-76b1-9a6e-a2959eb4d978 at 10:47:03.220 UTC, with its own
20-minute limit ending 11:07:03.220 UTC. The comparator continuation keeps all
predecessor and incident costs; those costs do not transfer to the review.
