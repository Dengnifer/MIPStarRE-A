# Build cache protocol — the hot main cache

Normative. This document specifies the local replacement for the parent
workflow's GitHub Actions build cache, and the rules every worktree must obey to
avoid duplicate compilation. It is the protocol behind three executables:

| script | role |
|---|---|
| `local/bin/cache-warmer.sh` | the **single writer**: builds `main`, publishes read-only snapshots |
| `local/bin/warm-worktree.sh` | the **consumer**: keyhash-gated copy-on-write clone into a worktree |
| `local/bin/worktree-setup.sh` | fresh-worktree bootstrap (replaces `.codex/setup.sh`) |

Governing invariants: `local/DESIGN.md` #1 (single cache writer) and #7 (one full
`lake build` machine-wide). Where this document and `DESIGN.md` disagree,
`DESIGN.md` wins.

---

## 1. What is being replaced, and why it was built that way

The parent repository's caching design is the residue of a specific, documented
failure. The load-bearing citations:

| parent mechanism | citation | what it encodes |
|---|---|---|
| Split restore/save, save only on `main` | `.github/workflows/pr-ci.yml:137-167` | *"The cache is saved only from main and restored everywhere."* |
| `lean-action`'s own cache disabled | `.github/workflows/pr-ci.yml:138-142` | The post-mortem: a ~2.6 GB entry saved **per PR run** cycled through the 10 GB repository cache budget and evicted the main-branch entry, *"so no run ever restored usable MIPStarRE oleans and every run rebuilt the whole library."* |
| Same policy restated in the weekly job | `.github/workflows/docgen.yml:75-77` | *"See pr-ci.yml: per-run lake caches evict the main build cache from the repository cache budget."* |
| Main runs exempt from cancellation | `.github/workflows/pr-ci.yml:50` | *"Do not cancel main-branch runs: they seed the build cache."* |
| Save runs `if: always()` on main | `.github/workflows/pr-ci.yml:161-162` | *"Save even when the build failed: a partial cache still spares the next run the modules that did compile."* |
| ProofWidgets prune workaround | `.github/workflows/docgen.yml:56-69` | A fresh-tree upstream bug that aborts the entire Mathlib cache fetch |
| `elan` install isolated from the cache lifecycle | `.github/workflows/docgen.yml:44-54` | Avoids *"a partial cache save or restore-then-overwrite that could negate the ProofWidgets workaround"* |
| Independent cache for the doc subproject | `.github/workflows/docgen.yml:135-140` | `docbuild/` is its own Lake project with its own key |
| Mathlib bumps are manual only | `.github/workflows/update.yml:3-5` | A bump *"triggers a full library rebuild and possibly an auto-fix cascade"* |
| Lean setup removed from a PR job | `.github/workflows/pr-ci.yml:314` | A job was demoted to a notice *"after repeated runner disk exhaustion"* |

The single sentence to carry forward: **many writers destroyed the one valuable
cache entry.** Every rule below exists to make that impossible locally, where the
same failure mode reappears as parallel agent worktrees writing into a shared
build tree.

---

## 2. The two-tier split

`.lake/` holds two caches with different provenance, different lifetimes, and
different sharing rules. Conflating them is the primary way to reintroduce the
parent's failure.

**Tier 1 — `.lake/build`** — this project's own compiled artifacts (`.olean`,
`.ilean`, `.c`, `.trace` for `MIPStarRE` modules). This is *exactly* what the
parent cached, and only from `main`. Locally it is produced by the warmer and
distributed as copy-on-write clones. Each worktree owns a **private, writable**
copy.

**Tier 2 — `.lake/packages`** — Mathlib and its transitive dependencies. The
parent never put these in the GitHub cache; they come from Mathlib's own cloud
cache via `lake exe cache get` inside `lean-action`. Locally the same holds:
**every worktree runs its own `lake exe cache get`.**

> **Tier 2 is never symlinked into a worktree.** A shared `.lake/packages` looks
> attractive (it saves the download), but it is read-only only by convention, and
> a single consumer running `lake update` mutates the tree for every other
> worktree simultaneously. The download is cheap; a corrupted shared dependency
> tree during a multi-agent session is not. `warm-worktree.sh` therefore fetches
> per worktree, and `worktree-setup.sh` refuses to run `lake update` at all.

Consequence for `lake update`: it is not part of any automated path here. It
rewrites `lake-manifest.json`, which moves the cache key (§3) out from under
every published snapshot, and it mutates vendored package checkouts. Mathlib
bumps stay human-invoked, exactly as `update.yml:3-5` argues.

---

## 3. The cache key

```
keyhash := sha256( bytes(lean-toolchain) ‖ bytes(lake-manifest.json) ‖ bytes(lakefile.toml) )
```

concatenated in that fixed order, `‖` being byte concatenation. This is the local
analog of `hashFiles('lean-toolchain', 'lake-manifest.json', 'lakefile.toml')` in
`pr-ci.yml:143-149`. The definition is duplicated verbatim in `cache-warmer.sh`
and `warm-worktree.sh` (function `compute_keyhash`); the two copies **must stay
byte-identical**, or every consumer silently and permanently takes the cold path.
A missing input file is a hard error, never a default.

Two properties matter, and they are not symmetric:

1. **A snapshot may be older than the consumer's base commit.** The parent's
   `restore-keys` deliberately drop the SHA suffix and prefix-match the newest
   entry under the same hash. This is safe because Lake's staleness test is
   trace-hash based, not mtime based: a cloned artifact whose inputs still hash
   equal is reused, and everything else is rebuilt. Cloned files therefore do not
   need their timestamps preserved.
2. **A snapshot must never cross a keyhash boundary.** A `lean-toolchain` bump,
   a Mathlib revision change, or a `lakefile.toml` edit is *total* invalidation.
   `warm-worktree.sh` compares its own keyhash against the snapshot `STAMP`
   before copying anything, and on mismatch refuses the clone, warns, and falls
   back to the cold path. It never partially reuses.

---

## 4. On-disk layout

All runtime state lives under `MIPSTARRE_CACHE_ROOT`, default
`~/.cache/mipstarre-dev/`. Nothing in this tree is ever committed.

```
~/.cache/mipstarre-dev/
├── .full-build-lock/            # machine-wide: one full `lake build` at a time
│   └── info                     # pid, host, started, started_epoch, purpose
├── .telemetry-lock/             # short-lived; serializes JSONL appends
├── logs/                        # captured build logs (warm-*.log, worktree-build-*.log)
└── hot-main/
    ├── .writer-lease/           # only the warmer holds this
    │   └── info
    ├── repo/                    # the always-warm detached checkout of main
    ├── snapshots/
    │   ├── snap-<utc>-<sha12>/
    │   │   ├── STAMP
    │   │   └── build/           # a byte copy of repo/.lake/build
    │   └── snap-<utc>-<sha12>/
    └── current -> snapshots/snap-<utc>-<sha12>   # absolute symlink
```

Snapshot names are `snap-<YYYYmmddTHHMMSSZ>-<sha12>` so that reverse
lexicographic order *is* reverse chronological order — the GC needs no `stat`
calls and no name parsing.

### `STAMP` schema

A flat `key=value` file, one pair per line. It is **data, not code**: both scripts
parse it with a whitelist and validate each value (`keyhash` must be 64 lowercase
hex characters, `status ∈ {complete, partial}`, `sha` hex). Nothing in it is ever
`eval`ed or `source`d.

```
sha=<full 40-char commit sha of the build>
keyhash=<64 hex chars, §3>
timestamp=<ISO 8601 with offset>
timestamp_epoch=<unix seconds>
status=complete|partial
build_seconds=<integer>
toolchain=<contents of lean-toolchain>
snapshot=<snapshot directory name>
warmer_version=1
```

---

## 5. The warmer — `cache-warmer.sh`

```
local/bin/cache-warmer.sh [--ref main | --sha <sha>] [--force] [--keep N]
                          [--targets "<lake targets>"] [--lock-timeout S]
                          [--lease-ttl S] [--gc-only] [--status]
```

### 5.1 Writer lease

Acquired by `mkdir hot-main/.writer-lease` — `mkdir(2)` is the atomic
test-and-set. The lease directory holds an `info` file with `pid`, `host`,
`started`, `started_epoch`, `purpose`.

Staleness is decided in this order:

* **Same host**: the holder's liveness is authoritative (`kill -0 pid`). A dead
  pid means stale immediately; a live pid means *not* stale regardless of age.
* **Different host, or no pid**: fall back to age > TTL (default 43200 s).

The TTL is deliberately much larger than the study map's suggested 3 h: this
repository's own cold full build took **25052 s** (`results/telemetry/builds.jsonl`,
2026-08-30). An age-only rule with a short TTL would break a live warmer's lease
mid-build and produce exactly the concurrent-writer situation the lease exists to
prevent.

**Breaking a stale lock is done by renaming, not deleting.** Two processes that
both judge a lock stale will both attempt `mv lockdir lockdir.stale.<pid>.<epoch>`;
`rename(2)` is atomic, so exactly one succeeds and proceeds to delete and
re-acquire, while the loser loops and finds the lock freshly held. A
`rm -rf && mkdir` sequence has no such guarantee.

### 5.2 Build

1. Clone or fetch `hot-main/repo` from the primary checkout; resolve `origin/<ref>`
   first, then `<ref>` (`DESIGN.md` #8). Check out **detached** and forced.
   `.lake/` is gitignored, so the checkout never touches the build tree, and
   `git clean` is deliberately not run (it would descend into vendored packages).
2. Apply the fresh-state workaround (§8.2).
3. Acquire the machine-wide full-build lock (§7) — **waiting, never aborting.**
   This is the local reading of `pr-ci.yml:50`: a main build seeds the cache and
   is never cancelled in favour of a newer commit. If main moves during a build,
   finish, then warm again.
4. `lake exe cache get` (failure is a warning, not fatal — the build simply
   compiles more from source), then `lake build`, then any `--targets`.
   **No `lake update`.**
5. Everything is logged to `~/.cache/mipstarre-dev/logs/warm-<utc>-<sha12>.log`.
   Telemetry records the log *path*, never log *content* — build output is
   untrusted text (`DESIGN.md` #6) and does not belong in a data file that agent
   prompts may later read.

### 5.3 Atomic publish

The publish sequence, and the reason each step is in this order:

1. Copy `repo/.lake/build` into `snapshots/<name>.tmp/build` with
   `cp -c -R` (APFS copy-on-write; falls back to `cp -R` with a warning if the
   source and destination are not on the same APFS volume).
2. Write `snapshots/<name>.tmp/STAMP`.
3. `mv snapshots/<name>.tmp snapshots/<name>` — a same-directory `rename(2)`.
   A snapshot directory therefore becomes visible only when it is already
   complete and stamped. **A reader can never observe a torn snapshot.**
4. Re-point `current` by creating a sibling symlink and `os.replace`-ing it over
   the old one (`rename(2)` again, which does not follow symlinks).

> Step 4 is done through `python3`, not `mv`. BSD `mv` `stat()`s its destination,
> follows the existing `current` symlink to the directory it names, and would
> move the new link *inside* the snapshot instead of replacing it. This is a real
> trap, not a hypothetical one.

Consumers exploit exactly this: they `readlink current` **once**, and hold the
resolved concrete path for the rest of the run.

### 5.4 Partial snapshots are intentional

If `lake build` fails, the warmer still publishes, with `status=partial`, and
exits non-zero. This is `pr-ci.yml:161-162` ported directly: a broken `main`
commit must not stall every consumer at zero cache, and the modules that did
compile are still worth distributing. Consumers accept partial snapshots and say
so loudly.

A non-zero exit from the warmer therefore means *"main did not build cleanly"* —
not *"nothing was published."* A cron wrapper should treat it as an alert, not a
reason to retry.

### 5.5 Retention

Keep the newest `--keep` snapshots (default 2), the local analog of the parent's
10 GB repository cache budget. **The snapshot `current` points to is never
collected**, even when it falls outside the keep window: a consumer that has
resolved `current` must find a live directory. Abandoned `*.tmp` staging
directories older than an hour are swept.

---

## 6. The consumer — `warm-worktree.sh`

```
local/bin/warm-worktree.sh [<worktree>] [--force] [--build] [--no-build]
                           [--force-cold] [--skip-packages] [--status]
```

The consumer is **read-only with respect to the cache**. It refuses outright to
operate on any path inside `hot-main/repo` or `hot-main/snapshots`.

Decision procedure:

1. Compute the worktree's own keyhash (§3).
2. Resolve `current` **once**; require `build/` and `STAMP` to exist.
3. Read and validate the `STAMP`. A malformed stamp is treated as *no snapshot*.
4. **Keyhash gate.** Mismatch → warn with both hashes, name the likely cause
   (toolchain / manifest / lakefile change), point at the warmer, and take the
   cold path. Never a partial reuse, never a silent skip.
5. **Warm path**: `cp -c -R <snapshot>/build → <worktree>/.lake/build.incoming.$$`,
   then `rename` into place. Write the idempotency marker
   `<worktree>/.lake/.mipstarre-warm-stamp` recording the snapshot name, keyhash,
   snapshot status and time. Then fetch tier 2 with `lake exe cache get`.
   No full build unless `--build` is given — the point of the warm path is that
   the agent's next incremental `lake build` compiles only its own delta.
6. **Cold path**: `lake exe cache get`, then a full `lake build` under the
   machine-wide lock (§7), unless `--no-build`.

### 6.1 Idempotency and the do-not-clobber rule

Re-running on an already-warmed worktree is a no-op for tier 1. Specifically:

* marker snapshot **and** keyhash both match the resolved snapshot → skip the
  clone;
* `.lake/build` is populated but was **not** warmed from this snapshot → leave it
  alone and warn. It may hold hours of an agent's incremental work; replacing it
  with a main snapshot is destructive and is only done under `--force`.

### 6.2 Why copy-on-write, and why not a symlink

On APFS, `cp -c -R` clones extents rather than bytes: the operation is near
instantaneous and initially consumes no additional space, with divergence paid
for only as the worktree's own build writes new blocks. This is what makes a
*private writable copy per worktree* affordable — and a private writable copy is
precisely what preserves the single-writer invariant. A writable symlink or
bind-style share of `.lake/build` across two concurrent `lake build` invocations
is the local restatement of the parent's eviction bug and is never acceptable.

---

## 7. Concurrency: two locks, deliberately separate

| lock | path | held by | protects |
|---|---|---|---|
| writer lease | `hot-main/.writer-lease` | the warmer only | the snapshot store and `hot-main/repo` |
| full-build lock | `.full-build-lock` | warmer **and** consumers | RAM/CPU: one full `lake build` machine-wide |

They are separate so that a consumer's own full build can proceed while the
warmer sits idle between commits, and so that a warmer holding the writer lease
does not block a consumer that only wants to *read* a published snapshot.

`DESIGN.md` #7: **single-file `lake env lean <file>` checks take no lock.** They
are read-only over existing oleans, which is exactly why the `.githooks/pre-push`
gate uses them per changed file rather than a whole-library build. Do not add
locking there.

The parent's equivalent constraint was runner disk exhaustion, severe enough that
a CI job dropped Lean setup entirely and now only emits a notice
(`pr-ci.yml:314`). Locally the binding resource is RAM during a Mathlib-scale
build; the lock is the analog of a concurrency group.

Both locks use the same mkdir/rename-to-break protocol described in §5.1, with
the same liveness-first staleness rule, so a consumer and the warmer agree on
what a stale lock is.

### 7.1 Interoperating with `local/bin/ci.sh`

`ci.sh` takes the same machine-wide full-build lock around its build step. Two
compatibility hazards follow, and both are handled here:

* **Path.** All four takers — `cache-warmer.sh`, `warm-worktree.sh`, `ci.sh`,
  and `housekeeping.sh`'s linter sweep — default the lock to
  **`$CACHE_ROOT/.full-build-lock`** and honour the override
  **`MIPSTARRE_FULL_BUILD_LOCK`**. One path, one mutex. (Historical note: the
  first draft had `ci.sh` on `$CACHE_ROOT/hot-main/.full-build-lock` and the
  sweep on a third flock — *two different paths are two independent mutexes,
  and the invariant is silently void*; unified 2026-08-30, see
  `local/protocols/EVOLUTION.md`.)
* **Metadata layout.** `ci.sh` records its holder in `<lock>/owner` (pid, ISO
  time, tag — one per line); these scripts record `<lock>/info` as `key=value`.
  A script that cannot read the other's holder would conclude "no pid, therefore
  stale" and break a *live* lock mid-build. Therefore: every acquisition here
  writes **both** files, and staleness detection reads `info` first, then
  `owner`, and falls back to the lock directory's mtime for age. An absent `host`
  field is read as "this host", which keeps pid liveness authoritative.

---

## 8. Fresh-worktree bootstrap — `worktree-setup.sh`

Replaces `.codex/setup.sh` (the Codex cloud environment hook) per `DESIGN.md`'s
GitHub→local mapping. Order of operations:

1. **Assert `elan`** — never install it by piping a URL into a shell. This is a
   developer machine, not a disposable runner. Missing `elan` is a hard, actionable
   error.
2. **PATH**: `$HOME/.elan/bin` is exported for this process. The shell rc file is
   modified **only** under `--persist-path`; otherwise the line to add is printed.
3. **Toolchain guard**: `elan toolchain install $(cat lean-toolchain)`, once, only
   if the pin is not already installed.
4. **No `lake update`** — stated in the log, not silently omitted (§2).
5. **`origin/main` check** (`DESIGN.md` #8): a warning, because the hooks and every
   diff-based audit silently self-disable without it. Silent self-disabling is the
   documented failure this check exists to surface.
6. **Fresh-state workaround** (§8.2).
7. **`warm-worktree.sh`** — invoked from the copy *next to this script*, not the
   copy inside the worktree being bootstrapped. A worktree may hold an unreviewed
   branch; the bootstrap must not execute code from the tree it is bootstrapping.
   This is the local analog of `DESIGN.md` #5 (trusted prompts come from `main`).
   If the consumer script is missing, this is a **hard error**: without it the
   worktree would start cold, silently, which is the outcome the whole protocol
   exists to prevent.
8. **`scripts/install_git_hooks.sh`**, then `--check`. `docs/ci-automation.md`
   calls out `--check` specifically for *"each fresh worktree used for a PR."*

`--check` is report-only and mutates nothing (`DESIGN.md` #10). It exits non-zero
if anything is missing.

### 8.1 Git environment hygiene

Every invocation of `lake` or of `git` inside a vendored package is wrapped in
`run_outside_git_env`, ported from `.githooks/pre-push:19-25`: it unsets every
variable named by `git rev-parse --local-env-vars` in a subshell. Without it, a
script invoked from inside a git hook leaks `GIT_DIR` / `GIT_INDEX_FILE` into
Lake's package checkouts, and nested git operations resolve the wrong repository.

### 8.2 The ProofWidgets fresh-state workaround

Kept verbatim in intent from `docgen.yml:56-69`, in all three scripts, because a
pristine agent worktree is exactly the fresh state that triggers it.

*Upstream form.* `lake exe cache get` runs `lake update`, whose mathlib
post-update hook prunes `.lake/packages/proofwidgets/.lake/build/lib` before
fetching a cloud release. On a tree that has never built, the directory does not
exist, and the uncaught exception aborts the **entire** cache fetch. Fix: create
the directory, but only if `proofwidgets` was actually checked out.

*Local form.* The same fetch also aborts when a vendored package tree is
**dirty**: build byproducts (`widget/js/lake.trace`) block the revision checkout.
Recorded in `results/telemetry/builds.jsonl`, 2026-08-30 — a failed build followed
by a successful retry after `git reset --hard` in the package. The scripts
therefore reset any vendored package tree with **tracked** modifications before
fetching.

`git clean` is deliberately **not** run inside a vendored package: it would delete
downloaded build output at a cost of hours. If an untracked byproduct still blocks
a checkout, the fetch fails loudly and the caller falls back to compiling from
source.

---

## 9. Telemetry

Every full build and every cache event appends one JSON line to
`results/telemetry/builds.jsonl`, per `DESIGN.md`'s telemetry contract.

```jsonc
{"ts": "<ISO 8601 with offset>",
 "kind": "warm" | "rebuild" | "cache-get",
 "trigger": "<who asked for this>",
 "outcome": "success" | "failed",
 "seconds": <int>,
 "sha": "<commit, when known>",
 "note": "<sanitized, ≤400 chars>"}
```

* `warm` — a warmer build and publish.
* `rebuild` — a consumer's full `lake build` (cold path, or `--build`).
* `cache-get` — a per-worktree tier-2 fetch.

Three properties are load-bearing:

* **The primary checkout owns the file.** Even when invoked from a linked
  worktree, the scripts resolve `git rev-parse --git-common-dir` back to the
  primary repository, so an append-only JSONL does not fork per worktree and
  produce merge conflicts. Override with `MIPSTARRE_TELEMETRY_DIR`.
* **Appends are serialized** by a short-lived `mkdir` lock, and give up after 5 s
  rather than delaying a build. Telemetry never blocks or fails a build; every
  failure path degrades to a warning.
* **`note` is sanitized** — non-printable characters stripped, truncated to 400
  characters — because notes may quote build output, and compiler output is
  untrusted text regardless of where it was produced (`DESIGN.md` #6).

---

## 10. Operating procedures

```bash
# Seed or refresh the hot main cache (do this after every merge to main).
local/bin/cache-warmer.sh --ref main

# What is published right now?
local/bin/cache-warmer.sh --status

# Bootstrap a brand-new agent worktree end to end.
local/bin/worktree-setup.sh /path/to/.worktrees/issue-0042-qpbt-basis

# Verify an existing worktree without touching it.
local/bin/worktree-setup.sh /path/to/worktree --check

# Re-warm a worktree after the warmer published a newer snapshot.
local/bin/warm-worktree.sh /path/to/worktree --force

# What would this worktree do, warm or cold?
local/bin/warm-worktree.sh /path/to/worktree --status
```

After a toolchain or Mathlib bump lands on `main`, the ordering is fixed: **warm
first, adopt second.** The bump changes the keyhash, so every existing snapshot
is invalid and every worktree cold-paths until a fresh snapshot exists. Run
`cache-warmer.sh --ref main` before dispatching agents, or pay for a full build in
each worktree serialized behind one lock.

---

## 11. Failure modes and how each degrades

| condition | behaviour |
|---|---|
| No snapshot published yet | Warn, name the warmer command, take the cold path. |
| Keyhash mismatch | Warn with both hashes, take the cold path. Never a partial reuse. |
| Malformed / unreadable `STAMP` | Treated as *no snapshot*; cold path. |
| Snapshot is `partial` | Used, with a warning naming the SHA that failed. |
| `cp -c` unsupported (non-APFS, cross-volume) | Warn, fall back to `cp -R`. Correct, just slower and larger. |
| `lake exe cache get` fails | Warn; tier 2 gets compiled from source. Non-fatal. |
| Full-build lock held | Wait; the warmer waits indefinitely by default, consumers time out per `--lock-timeout`. |
| Stale lock (dead pid, or age > TTL) | Broken by atomic rename, with a warning naming the dead holder. |
| Primary repo has no commits on `main` | Hard error naming the cause. Never a silent no-op. |
| `warm-worktree.sh` missing during bootstrap | Hard error. `--skip-warm` is the explicit opt-out. |
| `origin/main` does not resolve | Warning, non-zero exit from `--check`, because hooks self-disable silently. |
| `python3` absent | Warmer: hard error (needed for the atomic publish). Consumer: warning, telemetry skipped. |

---

## 12. Deliberately not ported here

* **Change gating by path filter** (`dorny/paths-filter`) belongs to the local PR
  CI driver, not to the cache layer. See `local/protocols/ci.md`. Note the parent's
  documented failure: path filters were patched twice after checks silently never
  ran, so the driver's globs must stay in lockstep with the audit scripts' scan
  trees.
* **The site/badges/docs component store** (`blueprint.yml`, `badges.yml`,
  `docgen.yml`, `deploy-pages.yml`, `scripts/fetch-latest-artifact.sh`) is a
  separate concern; `local/bin/site.sh` owns it per `DESIGN.md`.
* **The `docbuild/` cache** (`docgen.yml:135-140`) is a second, independent Lake
  project with its own key. Locally the persistent directory *is* the cache: keep
  `docbuild/.lake/build` in the hot-main checkout and wipe it only when
  `docbuild/lean-toolchain` or `docbuild/lake-manifest.json` changes, comparing a
  stored hash exactly as the CI key does. Not implemented by these three scripts.
* **`create-release.yml`** (toolchain-matched tags) exists purely for the external
  Lake/Reservoir ecosystem. A local-only setup has no downstream consumers;
  skipped with that reason.
* **`update.yml` → a local `mathlib-bump.sh`.** Not built here. When it is, it must
  end by asking the warmer to build the new toolchain into a fresh snapshot before
  any agent worktree adopts the bump (§10).

---

## 13. Invariant checklist

A change to any of these scripts must preserve all of the following:

1. Only `cache-warmer.sh` writes into `hot-main/`. Consumers refuse to run there.
2. `compute_keyhash` is byte-identical across both scripts.
3. A snapshot becomes visible only via `rename(2)`, fully built and stamped.
4. `current` is re-pointed only via `rename(2)` over the symlink — never `mv`.
5. Consumers resolve `current` exactly once per run.
6. Keyhash mismatch → cold path. Never a partial or best-effort reuse.
7. Failed builds still publish, flagged `partial`.
8. GC never removes the snapshot `current` names.
9. At most one full `lake build` machine-wide; `lake env lean` takes no lock.
10. `.lake/packages` is per-worktree and never symlinked; no automated `lake update`.
11. The ProofWidgets fresh-state workaround runs before any `lake exe cache get`.
12. Every `lake` / vendored-`git` invocation goes through `run_outside_git_env`.
13. `STAMP` is parsed by whitelist and validated; never `eval`ed or `source`d.
14. Telemetry is best-effort, serialized, sanitized, and lands in the primary checkout.
15. Every degradation is a loud warning or a hard error. Never a silent no-op.
