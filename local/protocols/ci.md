# Protocol — local PR CI

Normative protocol for `local/bin/ci.sh`, the local replacement for
`.github/workflows/pr-ci.yml` (frozen under `.github/`, never executed here).
Read `meta.md` first; `build-cache.md` owns the hot-main cache this protocol
consumes but never writes.

`ci.sh <pr-id>` is the **only** thing allowed to set `ci_status` in a PR
record. Everything downstream — `review.sh` (invariant 2: review only after
green CI on the same head SHA), `autofix.sh` (invariant 3: sync/audit failures
are never auto-fixed), and the merge gate in `pr_merge.py` — reads the manifest
this script writes and nothing else.

## 1. What it is

The parent repository consolidated seven workflows into one so that a pull
request produces exactly **one** CI completion event, which the auto-fix
dispatcher keys off (`pr-ci.yml:3-8`). The local port keeps that property: one
invocation, one manifest, one exit code.

```
local/bin/ci.sh <pr-id> [--worktree PATH] [--base REF] [--only STEP]
                        [--force-all] [--skip-build] [--dry-run]
```

`<pr-id>` is `7`, `0007`, or `0007-slug`; the script resolves it to a single
directory under `prs/`, reads `branch` and `base` from `pr.md` frontmatter,
finds the branch's worktree (via `git worktree list`, falling back to
`.worktrees/<branch with / → ->`), and runs everything **inside that
worktree**. Nothing is run in the primary checkout.

Exit status: `0` all gating steps passed or were legitimately skipped; `1` at
least one gating step failed or could not run; `2` the run could not start
(unknown PR id, missing worktree, unresolvable base).

### Preconditions that are hard errors, never silent skips

| Precondition | Why it is fatal |
|---|---|
| `prs/<id>/pr.md` exists with a `branch` key | there is no branch to test |
| a worktree for that branch exists | CI must not test the primary checkout |
| `origin/<base>` or `<base>` resolves | invariant 8 — the diff-based audits and the change gating self-disable without a base, which is exactly the "checks silently stopped running" failure the parent repo patched twice |
| a merge base exists | the change set is undefined without one |
| `python3` on `PATH` | every audit job and the manifest writer need it |

There is deliberately **no `LOCAL_CI_ENABLED` kill switch**. `LOCAL_REVIEW_ENABLED`
and `LOCAL_AUTO_FIX_ENABLED` exist because a disabled reviewer or fixer merely
stops work from happening; a disabled CI would hand the merge gate a green
light it never earned. If CI must not run, do not run it — the record keeps its
previous `ci_status`.

## 2. Job table

Eight steps, in this order, named exactly after the parent workflow's job ids
so the auto-fix dispatcher's mapping (build → ci-fix, blueprint-render →
blueprint-fix, everything else → never auto-fixed) ports without translation.

| Step | Parent job | What it runs (in the worktree) | Gate |
|---|---|---|---|
| `build` | `build` (`pr-ci.yml:115-168`) | warm `.lake/build`, `lake exe cache get`, `lake build`, `lake build MIPStarRE.LDT.Test.AxiomAudit` (`:155-156`), `scripts/comparator/check_challenge_drift.py` (`:158-159`) | `lean ∨ comparator ∨ workflow` |
| `blueprint-render` | `blueprint-render` (`:173-243`) | `leanblueprint pdf` + non-empty `blueprint/print/print.pdf` (`:210-218`), `texra-blueprint bbl` (`:222-223`), `texra-blueprint web` with `grep '^ERROR:'` (`:225-243`) | `blueprint_src ∨ workflow` |
| `paper-gaps` | `paper-gaps` (`:248-271`) | `texra-blueprint --root . paper-gaps check` | `paper_gaps ∨ workflow` |
| `blueprint-sync` | `blueprint-sync` (`:273-317`) | `python3 -m unittest discover -s scripts/tests`, `blueprint_lean_sync.py --update-lean-decls`, `blueprint_lean_sync.py --ci`, `blueprint_axiom_audit_needed.py --base-ref` | `lean ∨ blueprint ∨ scripts ∨ workflow` |
| `file-length` | `file-length` (`:319-340`) | `check_oversized_lean_files.py --root .` (>1000 lines) | `mip_lean ∨ scripts ∨ workflow` |
| `proof-debt` | `proof-debt` (`:342-386`) | `unittest test_audit_paper_facing_proof_debt.py`, `audit_paper_facing_proof_debt.py --ci` | `mip_lean ∨ tex_chapter ∨ scripts ∨ workflow` |
| `proof-evasion` | `proof-evasion` (`:388-445`) | four regression tests, then `audit_lean_axiom_declarations.py --ci`, `audit_conclusion_shaped_hypotheses.py --ci`, `audit_unfaithful_markers.py --ci`, and `check_duplicate_private_helpers.py --ci` (advisory) | `mip_lean ∨ scripts ∨ workflow` |
| `statement-origin` | `statement-origin` (`:447-487`) | `check_statement_paper_origin.py --root .` | `ldt_lean ∨ scripts ∨ workflow` |

Every step is blocking. The single advisory sub-check is
`check_duplicate_private_helpers.py`: exit 1 means "candidates reported" and is
downgraded to a warning, any other nonzero status is a real failure — the same
`set +e` dance as `pr-ci.yml:432-445`.

Two GitHub-only behaviours are dropped on purpose: `GITHUB_STEP_SUMMARY`
blocks and `::error` / `::notice` / `::warning` annotations are inert outside
Actions, so the step's stdout+stderr log **is** the summary. `--github-annotations`
is not passed to `check_duplicate_private_helpers.py`. Exit-code semantics are
preserved exactly: `::warning` never failed a job, and the `^ERROR:` grep
always did.

### Steps that did not run

A step whose area did not change is recorded `skipped` with the reason — never
omitted. A skipped step is green for the merge gate, exactly as a skipped
GitHub job is. This is why the gating globs are load-bearing (§3): a glob that
under-matches turns a real gate into a permanent, invisible `skipped`.

## 3. Gating globs — keep in lockstep

`git diff --name-only --no-renames <merge-base> <head>` replaces
`dorny/paths-filter@v3`. `--no-renames` is deliberate: reporting both the old
and the new path means a rename *out of* a gated tree still trips that tree's
filter, and deletions count. `*` in these patterns spans `/`, matching
minimatch's `**`.

| Area | Globs | Parent |
|---|---|---|
| `lean` | `*.lean`, `lakefile.*`, `lean-toolchain`, `lake-manifest.json` | `pr-ci.yml:84-88` |
| `mip_lean` | `MIPStarRE/*.lean` | `:89-90` |
| `ldt_lean` | `MIPStarRE/LDT/*.lean` | `:91-92` |
| `blueprint` | `blueprint/*` | `:93-94` |
| `blueprint_src` | `blueprint/src/*` | `:95-96` |
| `tex_chapter` | `blueprint/src/chapter/*.tex` | `:97-98` |
| `paper_gaps` | `docs/paper-gaps/*`, `texra-blueprint.toml`, `MIPStarRE/*.lean`, `blueprint/src/*`, `docs/*.md` | `:99-107` |
| `scripts` | `scripts/*` | `:108-109` |
| `comparator` | `scripts/comparator/*` | `:110-111` |
| `workflow` | `.github/workflows/pr-ci.yml`, `local/bin/ci.sh`, `local/protocols/ci.md` | `:112-113`, extended |

> **Lockstep warning.** These globs must move together with the trees the audit
> scripts actually scan. The parent repo patched the `paper_gaps` filter twice
> after checks silently never ran — the note at `pr-ci.yml:102-104` is the scar.
> The failure mode is asymmetric: an over-broad glob costs CPU, an under-broad
> glob costs a merged regression that no check ever looked at. When you widen
> a scan tree in `scripts/*.py`, widen the matching glob in `ci.sh` in the same
> commit, per `meta.md` §5.

The `workflow` area is the one deliberate extension. On GitHub it meant "the
workflow file changed, so re-run everything"; locally the CI definition lives
in three files — the frozen reference, this driver, and this protocol — and any
of them changing forces a full run.

## 4. Manifest schema

Written atomically (same-directory tempfile + `os.replace`) to

```
prs/<pr-dir>/ci/<head_sha>.json          complete run  (committed)
prs/<pr-dir>/ci/<head_sha>.partial.json  --only / --skip-build run
```

Step logs live outside the repository, under
`~/.cache/mipstarre-dev/ci-logs/<pr-id>/<head_sha>/<step>.log`.

```jsonc
{
  "schema": 1,
  "generator": "local/bin/ci.sh",
  "replaces": ".github/workflows/pr-ci.yml",
  "pr": "0007",                  // 4-digit id
  "pr_dir": "0007-qpbt-basis",   // directory under prs/
  "branch": "issue-7-qpbt-basis",
  "base": "main",                // from pr.md frontmatter
  "base_ref": "origin/main",     // what actually resolved
  "merge_base": "<sha>",
  "head_sha": "<sha>",           // the SHA every step ran against
  "worktree": "/abs/path",
  "started": "2026-08-30T09:23:07+0800",   // ISO-8601 with offset
  "finished": "2026-08-30T09:41:52+0800",
  "seconds": 1125,               // whole run, integer
  "conclusion": "success",       // success | failure | error
  "partial": false,              // true ⇒ not a merge-gate verdict
  "areas": { "lean": true, "blueprint_src": false, ... },
  "changed_files": ["MIPStarRE/Quantum/PauliBasis.lean", ...],
  "warnings": ["texra-blueprint not installed; skipped ...", ...],
  "steps": [
    {
      "step": "build",           // one of the eight job ids, always all eight
      "outcome": "success",      // success | failure | error | skipped
      "seconds": 883,
      "log_path": "/Users/…/.cache/mipstarre-dev/ci-logs/0007/<sha>/build.log",
      "blocking": true,
      "note": ""                 // skip reason, exit code, or degradation cause
    }
  ]
}
```

Outcome vocabulary — the distinction is what routes the auto-fix loop:

| `outcome` | Meaning | Auto-fix |
|---|---|---|
| `success` | the step ran and passed | — |
| `failure` | the step ran and the code is wrong | `build` → ci-fix, `blueprint-render` → blueprint-fix, everything else → **never** |
| `error` | the step could not run (missing tool, unbootstrapped worktree, build lock unavailable) | never — this is an operator problem, not a code problem |
| `skipped` | gated out, or excluded by `--only` / `--skip-build` | — |

`conclusion` is `failure` if any step failed, else `error` if any step errored,
else `success`. The run's exit status is `0` iff `conclusion == "success"`.

## 5. PR record updates

`ci.sh` rewrites two frontmatter keys of `prs/<pr-dir>/pr.md` atomically:

```
head_sha:  <the SHA CI actually tested>
ci_status: pending → running → success | failure | error
```

`running` is written **before the first step**. A crashed, killed, or
power-cut run therefore leaves `running`, never a stale `success`: the review
gate's "green CI on the same head SHA" check (invariant 2) fails closed.

`head_sha` and `ci_status` are written together, because a status without the
SHA it belongs to is unusable to the gate.

A **partial** run (`--only`, `--skip-build`) does not touch `pr.md` at all and
writes `<sha>.partial.json`. Partial runs are a debugging aid; they must not be
able to produce a merge-gate verdict, and they must not clobber a complete
manifest for the same SHA.

## 6. Concurrency and locks

Two advisory `mkdir`-based lease directories, both under
`~/.cache/mipstarre-dev/` (`MIPSTARRE_CACHE_ROOT` overrides the root). Each
holds an `owner` file: pid, ISO timestamp, tag. A lock is broken only when its
owner pid is dead or its stamp is older than `MIPSTARRE_FULL_BUILD_LOCK_STALE_S`
(default 3 h).

| Lock | Scope | On contention |
|---|---|---|
| `locks/ci-<pr-id>.lock` | one `ci.sh` per PR | **refuse immediately** (exit 2) |
| `hot-main/.full-build-lock` | one full `lake build` machine-wide (invariant 7) | wait up to `MIPSTARRE_CI_BUILD_LOCK_WAIT_S` (default 4 h), then record `build` as `error` and continue with the Python steps |

Only the `build` step takes the full-build lock. The audits are pure Python and
take nothing; single-file `lake env lean` checks are read-only over oleans and
take nothing either — which is precisely why `.githooks/pre-push` can use them
per-file without serializing.

`ci.sh` never cancels a running build. GitHub cancels in-progress PR runs
(`pr-ci.yml:48-51`) because its runners are disposable and main-branch runs —
the ones that seed the cache — are exempt. Locally there is nothing disposable:
killing a build mid-flight leaves a half-written `.lake/build` and a held lease.
So a second run for the same PR is refused, and a foreign live build lease is
waited on, never stolen. Do not `kill -9` a running `ci.sh`; if you must, remove
the lease directories by hand.

## 7. Build step and the two-tier cache

`build` is the only step that touches the cache, and it only ever **reads** the
shared tree. This is the local translation of the parent's main-only cache save
policy, whose rationale is documented at `pr-ci.yml:137-142`: per-PR saves of
~2.6 GB cycled through the 10 GB repository budget and evicted the main entry,
so no run ever restored usable oleans. The local failure mode is identical if a
worktree writes into the shared snapshot, so it does not.

1. If `.lake/build` is absent, run `local/bin/warm-worktree.sh <worktree>`,
   which resolves the hot-main snapshot and clones it copy-on-write. Contract:
   idempotent, exit 0 when it populated or deliberately declined, nonzero on a
   hard error.
   - warmer missing → loud warning, cold build (still correct, just slow);
     set `MIPSTARRE_CI_REQUIRE_WARMER=1` to make it an `error` instead.
2. `.lake/build` (this project's oleans, per-worktree, writable) and
   `.lake/packages` (Mathlib and friends) are **different tiers** and are never
   conflated. If `.lake/packages` is a symlink it points at the shared hot-main
   dependency tree and is read-only: `lake exe cache get` is **skipped**,
   because it writes there. If it is a real directory, `lake exe cache get`
   runs, mirroring what `lean-action` does inside the parent job. Never run
   `lake update` in a consumer worktree.
3. `.lake/packages` absent entirely → `error`, pointing at
   `local/bin/worktree-setup.sh`. That bootstrap path is where the ProofWidgets
   prune workaround lives, and a package-free tree is exactly the state that
   triggers it. `MIPSTARRE_CI_ALLOW_COLD_FETCH=1` overrides for a tree you know
   is clean.
4. `lake build`, then `lake build MIPStarRE.LDT.Test.AxiomAudit`, then the
   comparator drift check.

Every `lake` and `python3` invocation goes through a subshell that unsets
`git rev-parse --local-env-vars` first. Inherited `GIT_DIR`/`GIT_INDEX_FILE`
make Lake resolve nested package repositories against the wrong repository;
`.githooks/pre-push:19-24` does the same thing for the same reason, and any
orchestrator that invokes `ci.sh` from inside a git hook inherits the problem.

Lake's staleness is trace-hash-based, not mtime-based, so a restored snapshot
older than the merge base is safe — but only within one
`hash(lean-toolchain, lake-manifest.json, lakefile.toml)` class. Crossing that
boundary is `build-cache.md`'s problem, not this protocol's: `ci.sh` delegates
the check to `warm-worktree.sh` and simply builds whatever it is handed.

## 8. The axiom audit is reported, not run

`blueprint-sync` deliberately has no Lean setup. On GitHub that was forced by
repeated runner disk exhaustion, and the job degraded to a `::notice` telling a
human to run the audit locally (`pr-ci.yml:303-317`). Locally the constraint is
different but the conclusion is the same: the machine has a single full-build
budget, already spent by `build`. So `blueprint_axiom_audit_needed.py` runs, and
when it answers `true` the run records a warning:

> run `python3 scripts/blueprint_leanok_axioms.py --ci` in a Lean environment

De-automation of this kind is a legitimate evolution step (`meta.md` §4), and
this one is inherited rather than invented.

## 9. Telemetry

When `build` actually ran (any outcome but `skipped`), one line is appended to
`results/telemetry/builds.jsonl`:

```json
{"ts":"…","kind":"ci-build","trigger":"ci.sh pr=0007","seconds":883,
 "outcome":"success","sha":"…","note":"branch issue-7-qpbt-basis"}
```

This satisfies the `meta.md` duty that every full build be accounted for, and
makes "how much wall time did CI cost this PR" answerable by a script. The
per-step seconds in the manifest are the finer-grained record.

## 10. Trust boundary

Two things about `ci.sh` are worth stating plainly.

**It executes branch-authored code.** The audit scripts, the test suite, and
`lakefile.toml` all come from the worktree under test, because that is what CI
means and what the parent workflow did. Never run `ci.sh` on a branch you would
not run a shell script from.

**Its logs are untrusted data.** Compiler diagnostics, plasTeX output and test
failures can contain arbitrary text, including text shaped like instructions.
`ci.sh` stores logs verbatim and makes no attempt to clean them. Any consumer
that feeds a log into an agent prompt — `autofix.sh` above all — owes the
sanitization required by invariant 6: strip control characters, break fences,
truncate, and frame the payload as data that must not be followed. The manifest
gives consumers `log_path` rather than log content precisely so this stays the
consumer's explicit, visible responsibility.

## 11. Deliberate deviations from the parent workflow

| Parent | Local | Reason |
|---|---|---|
| `GITHUB_STEP_SUMMARY`, `::error`/`::notice`/`::warning` | per-step log file + `warnings` array | inert outside Actions; exit codes carry all gating meaning |
| `cancel-in-progress` for PR runs | second run refused, running builds never killed | local build state is not disposable |
| cache `restore`/`save` actions | hot-main snapshot read via `warm-worktree.sh`; `ci.sh` never writes the shared cache | invariant 1 — the eviction failure documented at `pr-ci.yml:137-142` |
| `workflow` filter = the YAML file | also `local/bin/ci.sh`, `local/protocols/ci.md` | the CI definition is now three files |
| `--github-annotations` on the duplicate-helper audit | dropped | annotation-only flag |
| `push`-to-main and docs-only `pull_request` triggers | none | the docs-only paths existed solely to emit the completion event that started PR Review (`pr-ci.yml:31-33`); locally the lifecycle script calls `review.sh` directly |
| implicit "PR event" job conditions | every run is a PR run | `ci.sh` is only ever invoked on a PR record |

## 12. Amendments

Changing a gating glob, a step's command set, the manifest schema, the
`ci_status` vocabulary, or a lock's name or semantics is a protocol amendment:
record the trigger in `results/telemetry/events.md`, edit this file and
`ci.sh` together, append to `EVOLUTION.md`, and grep `local/` for every other
enforcement point (`meta.md` §5). The manifest schema in particular is a
contract with `review.sh`, `autofix.sh` and `pr_merge.py`; bump `schema` when
it changes incompatibly.
