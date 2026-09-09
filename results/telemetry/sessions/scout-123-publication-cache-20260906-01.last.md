<!-- scout: scout-123-publication-cache-20260906-01 2026-09-06 -->
## Mathlib scouting report — 2026-09-06

**Finding:** the repeated failures come from a successfully built but outdated shared snapshot, combined with a publication gate that refreshes changed modules without necessarily refreshing the root’s transitive import closure. **One canonical warmer refresh should remove this shared backlog for subsequent fresh worktrees.** It will not update already-populated worktrees or eliminate future branch-specific compilation.

### Mathematical source

This is an operational investigation, not a proof-scoping task. Issue #123’s mathematical references remain unchanged.

I read its locally saved issue record in `results/telemetry/github-snapshot/open-issues.json:1`, generated September 6 at 10:15:57 UTC+08. No GitHub request was made, respecting the local-only restriction. Existing local #123 scout reports concern mathematical topics, not this cache diagnosis; live issue-comment deduplication remains operator-owned.

### Relevant Mathlib definitions

Not applicable. No replacement mathematical definitions are needed.

### Relevant Mathlib lemmas and theorems

Not applicable. This failure is not evidence of a missing lemma or a proof defect.

### Relevant MIPStarRE declarations

- `main` — `scripts/Checkdecls.lean:39` — the declaration checker **dynamically imports `MIPStarRE`** and looks up blueprint declarations. Its only static import is `Lean`; building the checker executable does not establish freshness of the dynamically imported project root.
- Root import chain — `MIPStarRE.lean:3`, `MIPStarRE/QPBT.lean:25`, `MIPStarRE/QPBT/Games/Sandwich.lean:1` — current source already exposes the missing pasting modules. No added imports or theorem changes are warranted.

### Diagnosis and evidence

**1. Cache generation and source generation differ.**

`/home/drx/.cache/mipstarre-dev/hot-main/current/STAMP:1` identifies:

- Snapshot: `snap-20260905T194526Z-dadd6fc4ba46`
- Source SHA: `dadd6fc4ba46049f59de69dbd97af4c3122ad118`
- Published: **September 6, 2026, 03:45:30 UTC+08**
- Status: `complete`; recorded build duration: **219 seconds**
- Key: `ce2a00c4ed264b375191755c0044ef2d07f11c728408560ec2424e49bb328e18`

The physical snapshot is under `/data/users/drx/mipstarre-cache/hot-main/snapshots/`. Its build log ends with successful builds of both aggregate roots and all 9,130 jobs. Thus, **“complete” is valid for that older commit**, not for current main.

The five pasting source modules were absent at that SHA. Their integration through PR #205 occurred at `223f01a10241e8006db04166fcfdd6acdff02663`, **07:14:39 UTC+08**, after publication of the snapshot.

**2. This is not a toolchain-key mismatch.**

The primary checkout, hot checkout, and all four packet worktrees have the same key above and share package store `/data/users/drx/mipstarre-cache/packages/185353eebe93a5ab`.

Actual configuration is **Lean/Mathlib v4.32.0**, not the v4.31.0 stated in AGENTS.md. Mathlib’s checked-out revision matches the manifest: `81a5d257c8e410db227a6665ed08f64fea08e997`.

**3. The compiled import closure is demonstrably older.**

The snapshot lacks the five `.olean` files for `Assembly`, `SchmidtMirror`, `CodewordConsistency`, `CrossMove`, and `PinchedReduction`.

Its `Sandwich.trace` records imports of only `Quantitative` and `ErrorFunctions`; packet #242’s rebuilt trace additionally records `Pasting.Assembly` and `Pasting.SchmidtMirror`:

- `/home/drx/.cache/mipstarre-dev/hot-main/current/build/lib/lean/MIPStarRE/QPBT/Games/Sandwich.trace:1`
- `.worktrees/issue-242-controlled-unitary-algebra/.lake/build/lib/lean/MIPStarRE/QPBT/Games/Sandwich.trace:1`

The current `Sandwich.lean` source blob is identical across main and all four packets: `1f13431133d795fb5dd3064bd72c93e400a001a5`. This establishes the shared source/artifact discrepancy independently of elapsed times or file timestamps.

**4. Setup and publication explain the repetition.**

- `clone_build_tier` — `local/bin/warm-worktree.sh:440` — preserves populated build trees.
- Consumer selection — `local/bin/warm-worktree.sh:618` — gates on the configuration key, **not source-SHA equality**; its warm path builds only when requested.
- Setup — `local/bin/worktree-setup.sh:198` — invokes the canonical adjacent consumer.
- Checked publication — `local/bin/checked-push.sh:124` — invokes the normal hook.
- Hook — `.githooks/pre-push:188` — builds changed Lean modules, then runs the dynamic declaration checker. Those module builds need not rebuild unrelated aggregate importers.
- CI — `local/bin/ci.sh:799` — subsequently runs a full project build, but initial publication can fail before reaching CI.

**5. All four private repairs are now recorded as successful.**

| Packet | Build seconds, excluding lock wait | Completion, UTC+08 | Evidence |
|---|---:|---|---|
| #239 | 654 | 11:19:48 | `results/telemetry/builds.jsonl:649` |
| #242 | 670 | 11:35:27 | `results/telemetry/builds.jsonl:653` |
| #245 | 669 | 12:16:52 | `results/telemetry/builds.jsonl:660` |
| #246 | 714 | 12:30:09 | `results/telemetry/builds.jsonl:663` |

Packet #242’s preserved before/after evidence is particularly clear: **57 missing declarations → all 1,387 resolved** after the completed rebuild, without source/import changes:

- `/home/drx/.cache/mipstarre-dev/sessions/orc-242-20260906-01-publication/checkdecls-initial.log:1`
- `/home/drx/.cache/mipstarre-dev/sessions/orc-242-20260906-01-publication/checkdecls-refreshed.log:1`

### Suggested approach

**Minimal recommendation: refresh the canonical cache once; change no scripts or Lean files initially.**

1. **Coordinate with existing supervisors first.** Do not restart their repairs, warm their worktrees, or cancel builds. At the final observation, **12:35:58 UTC+08**, the full-build lock directory was absent; that is an observation, not a reservation or scheduling guarantee.
2. From the primary checkout, the operator can schedule the existing warmer against a freshly resolved, fixed main SHA:
   ```bash
   local/bin/cache-warmer.sh --sha "$(git rev-parse main)" --lock-timeout 14400
   ```
   **Not executed here.** Let it acquire its own writer lease and the same `/home/drx/.cache/mipstarre-dev/.full-build-lock` used by CI. Do not wrap it in another acquisition of that lock. The existing shared package symlink permits the warmer to skip package fetching.
3. Accept the refresh only after normal completion: new atomic `current` target, exact intended SHA, matching key, `status=complete`, successful root build, and the five pasting artifacts present. The warmer publishes failed builds as `partial`, so merely observing a new snapshot is insufficient.
4. Let subsequent fresh consumers inherit it and run their normal declaration/publication/CI gates. **Do not force-reclone active or already-repaired worktrees.** Their existing private artifacts remain theirs.

Final observed main was `9102b74d823cab6d3a9ee17cd9405c29be61ef97`; its change from initial main `a9122d7` is telemetry-only for the inspected build inputs. If main’s build inputs advance during warming, finish that warmer and reassess before admitting another batch.

### Gaps to fill

- **Missing operational evidence:** why no newer generation was published after the later merges. `spawn_cache_warmer` and `post_merge` at `local/bin/pr_merge.py:403` and `local/bin/pr_merge.py:465` show automatic warming can be skipped after failed synchronization or explicitly disabled. I found no evidence establishing which happened here; assigning a specific cause would be speculation.
- A refresh removes this common inherited backlog, **not the general dynamic-import dependency gap**. Future branch changes introducing new import edges can still require root-closure rebuilding before declaration checking.
- No mathematical gap, proof-budget change, or immediate script patch follows from these findings.

### Searched

Inspected canonical warmer/setup/consumer/checked-push/CI/checker code, lock protocol, snapshot stamp and traces, package identities, Git history and import differences, all four warm markers, original failure logs, completed rebuild logs, telemetry, API documentation, and relevant prior audit/report records.

**Session accounting:** read-only inspection ended at **474 seconds**. Local rollout verifies configured `gpt-6-astra` / `xhigh`; server-side effort is unverified. Last available usage snapshot, at 12:34:47 UTC+08: **1,340,475 input tokens, 1,255,680 cached input, 8,953 output**; final accounting remains dispatcher-owned. No files, builds, probes, sessions, publications, reviews, merges, or B7/B8 budgets were changed.