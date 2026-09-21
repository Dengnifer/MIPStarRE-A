# Artifact packet C1 — clean-clone build evidence (2026-09-21)

Auditor: Opus helper `opus-audit-clean-clone-20260921-01` (nonce 9f58d960), acting
for the meta session. Read-only with respect to the repository: no commit, no push,
no PR, no file in the repository tree was created or modified (`git status` was
empty in the clone at every checkpoint, and the primary checkout was never written
to).

## Verdict

**A sceptical reviewer who clones this repository and builds it succeeds.**
`lake build MIPStarRE.QPBT` (plus the two named test modules) completed from a
fresh clone with an empty `.lake/build` in **803 s (13 m 23 s)**, exit code 0,
zero errors. The axiom audit, the blueprint `\leanok` audit and the `sorry`
check all pass. Eleven discrepancies between the README and what was measured are
listed in section 6; none of them affects the soundness claims, and the two that
matter for a reviewer are (a) the measured build excludes the Mathlib download,
and (b) `lake build MIPStarRE.QPBT` alone is not enough to run the repository's
own blueprint axiom gate — `lake build MIPStarRE` is.

## 1. What was built, and from where

| item | value |
|---|---|
| commit (github/main at the time of the clone) | `05df4b74fea7d291050909102c737e6b03d85ba6` (2026-09-20 03:57:39 +0900) |
| clone | `git clone --no-local --branch main --single-branch /home/drx/MIPStarRE-qpbt`, then `git checkout --detach 05df4b74…` |
| clone location | `/home/drx/.cache/mipstarre-dev/clean-clone-20260921/repo` |
| working tree after checkout | clean (0 lines of `git status --porcelain`) |
| toolchain | `leanprover/lean4:v4.32.0`; `lean 4.32.0` (commit `8c9756b2`), `Lake 5.0.0-src+8c9756b` |
| Mathlib | rev `81a5d257c8e410db227a6665ed08f64fea08e997` (`inputRev v4.32.0`), manifest version 1.2.0 |
| other deps | batteries `023ce7d6`, aesop `a7dbf0c6`, Qq `38d591e7`, proofwidgets `6e311e2a`, importGraph `7e9612bf`, LeanSearchClient `c5d5b8fe`, plausible `e12c1910`, Cli `88679d08` |
| host | 128-core Intel Xeon Platinum 8358P @ 2.60 GHz, 503 GiB RAM (the same machine as every row in `results/telemetry/builds.jsonl`) |

`--no-local` was used deliberately, so the clone owns its objects and shares no
hardlinks with the primary checkout.

## 2. Dependencies: reused, never re-fetched, never rebuilt

Tier 2 (`.lake/packages`) was linked to the project's shared read-only store
exactly as `local/bin/warm-worktree.sh` does for worktrees:

```
key  = sha256(lake-manifest.json ‖ lean-toolchain)[:16] = 185353eebe93a5ab
link = <clone>/.lake/packages -> /home/drx/.cache/mipstarre-dev/packages/185353eebe93a5ab
```

Checks performed before building:

* the store exists for this manifest+toolchain pair, and the key computed from the
  clone's own files matches the existing store directory;
* the store is genuinely read-only — `touch .lake/packages/__probe` returned
  `Permission denied`, so nothing in this run could have mutated Mathlib for other
  worktrees;
* `lake env printenv LEAN_PATH` resolved the whole dependency graph with exit code
  0 and **no** `lake update`, no clone, no download, and left `git status` empty;
* `lake exe cache get` was **not** run, and no network access occurred;
* **tier 1 was empty**: `.lake/build` did not exist before the build. The
  project's own oleans were all compiled in this run (659 `.olean` files, 3.6 GB,
  were produced).

## 3. The build

Command (the README's QPBT target, plus the two test modules the packet names;
`MIPStarRE.QPBT.Test.NonVacuity` is already inside the target's closure,
`MIPStarRE.QPBT.Test.AxiomAudit` is not):

```
nice -n 10 env LEAN_NUM_THREADS=16 \
  lake build MIPStarRE.QPBT MIPStarRE.QPBT.Test.AxiomAudit MIPStarRE.QPBT.Test.NonVacuity
```

It ran detached while this auditor held the machine-wide full-build lock
`~/.cache/mipstarre-dev/.full-build-lock` (acquired with `mkdir`, `purpose=opus-clean-clone-build-20260921`,
released on exit) — the same lock `warm-worktree.sh` and `ci.sh` use, so no other
full build could overlap.

| measurement | value |
|---|---|
| start / end (UTC, taken on ghz) | 2026-09-21T01:43:49Z / 2026-09-21T01:57:12Z |
| **wall time** | **803 s (13 m 23 s)** |
| exit code | 0 — `Build completed successfully (9313 jobs)` |
| jobs | 9313 total; **602 modules actually compiled** (the rest were Mathlib oleans served from the store and checked by trace hash) |
| CPU | 5528 s user + 960 s system, 808 % average CPU |
| peak RSS, single process | 5.10 GB |
| peak RSS, summed over all `lean`/`lake` processes (20 s sampling) | 84.3 GB |
| peak concurrent `lean` processes | 21 |
| errors | 0 |
| warnings | 136 lines, all style/linter, none from `MIPStarRE.QPBT`'s own soundness path |
| output size | `.lake/build` 3.6 GB, 659 `.olean` |
| tree after the build | `git status --porcelain` empty |

Warning breakdown (136): `linter.style.show` 42, `linter.unusedDecidableInType` 33,
`linter.style.maxHeartbeats` 27, `linter.unusedFintypeInType` 16,
`linter.style.openClassical` 10, `linter.flexible` 5, `linter.style.whitespace` 1,
`linter.style.emptyLine` 1.

Note on thread capping: Lake 5.0.0 has **no** `-j` / `--jobs` option (`lake build -j 16`
fails with `unknown short option '-j'`). `LEAN_NUM_THREADS=16` caps the threads
inside each `lean` process but not Lake's process-level scheduling, which reached
21 concurrent `lean` processes. The run was `nice -n 10`, so it yielded to
everything else on the machine.

A second build of the README's "build everything" target from that state added
only 12 modules and took **26 s** (`lake build MIPStarRE`, exit 0, 9325 jobs).

## 4. Checks run from that clone

**4.1 Axiom audit — PASS.** `MIPStarRE.QPBT.Test.AxiomAudit` is part of the build
and is a compile-time regression test (it throws at elaboration if an unexpected
axiom appears). It reported all thirteen QPBT headline declarations as depending on
exactly `[propext, Classical.choice, Quot.sound]`:

`pauli_soundness`, `pauli_soundness_qubit`, `exists_ld_soundness`,
`exists_spcc_value_one`, `honestStrategy_isSPCC`, `exists_combinedLinesWitness`,
`exists_extendedLinesWitness_established`, `exists_globalPairWitness`,
`exists_actual_rounded_global_pair_error_bound`,
`exists_projective_setting_isometry_bounds`,
`exists_arbitrary_strategy_isometry_bounds`,
`pauli_soundness_deltaQld_ofExtractionWitness`,
`exists_symmetric_projective_strategy_approx`.

The README's own manual recipe was re-run independently in the clone and agrees:

```
$ printf 'import MIPStarRE.QPBT.Test.Soundness\n#print axioms MIPStarRE.QPBT.pauli_soundness\n' > AxiomCheck.lean
$ lake env lean AxiomCheck.lean
'MIPStarRE.QPBT.pauli_soundness' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`sorryAx` appears nowhere.

**4.2 `scripts/blueprint_leanok_axioms.py --ci` — PASS, but only after
`lake build MIPStarRE`.**

* After the QPBT build alone: **exit 1**, `PASS: 1835, FAIL: 2`. Both failures are
  `MIPStarRE.LDT.Pasting.hAConsistency_submeas_of_context` and
  `MIPStarRE.LDT.Pasting.fromHToG_of_context`, and neither is an axiom failure: the
  script could not run `#print axioms` because
  `MIPStarRE/LDT/Pasting/Defs/Context.olean` does not exist — that module is
  outside the `MIPStarRE.QPBT` closure. The script's on-demand fallback
  (`ensure_module_olean`, `scripts/blueprint_leanok_axioms.py:262`) invokes
  `lake env lean <file> -o <olean> -i <ilean>`, which does **not** build the
  module's own dependencies, so it cannot recover from a partially built tree.
* After `lake build MIPStarRE` (26 s): **exit 0**, `PASS: 1837 decls, FAIL: 0`,
  `\leanok` placements 306 statement-only / 1531 proof-level, and
  "No proof-level `\leanok`-tagged declarations depend on `sorryAx`."

**4.3 Zero `sorry` under `MIPStarRE/` — PASS.** `git grep -E '(^|[^A-Za-z_.])sorry([^A-Za-z_]|$)' -- 'MIPStarRE/*.lean'`
returns three lines, all prose inside docstrings, none of them Lean syntax:

```
MIPStarRE/LDT/Test/AxiomAudit.lean:81:   … no direct `sorry`; it calls the internal simultaneous
MIPStarRE/QPBT/Combining/Apply.lean:57:  … whose proof was an open `sorry`; the printed sentence …
MIPStarRE/QPBT/Test/AxiomAudit.lean:27:  … not a report: if a `sorry` …
```

Also zero under `MIPStarRE/`: `admit`, `native_decide`, `unsafe` declarations, and
project-introduced `axiom` declarations (the one `^\s*axiom` hit,
`MIPStarRE/QPBT/Test/QubitForm.lean:16`, is the word "axiom" starting a line of a
doc comment).

## 5. Reproducibility caveat a reviewer must be told

The 803 s figure is a cold build of **this project's own 602 modules only**.
Mathlib's oleans came from the machine's shared store rather than from
`lake exe cache get`, because the packet forbade downloading or rebuilding
Mathlib. A reviewer starting from nothing additionally pays the
`lake exe cache get` download and unpack of the pinned Mathlib build
(~7.3 GB in this project's store). The measurement is therefore a faithful
lower bound with a named, single missing component, not an end-to-end
wall-clock for a machine with no cache.

## 6. README vs. measurement — discrepancies

The README was **not** edited (the meta will dispatch a docs fix). Each item below
is a statement in `README.md` at commit `05df4b74` that the clean-clone run
contradicts or updates.

| # | README says | Measured | Severity |
|---|---|---|---|
| 1 | "**A clean-clone build of `MIPStarRE.QPBT` has not yet been timed and recorded.**" | It now has: 803 s wall, 602 modules, 0 errors, on the documented machine (Mathlib served from the local store). | fix — this is exactly the sentence a reviewer looks for |
| 2 | "There is no dedicated Pauli-test axiom-audit module yet — the existing `MIPStarRE/LDT/Test/AxiomAudit.lean` covers the classical low-degree track only — so the check is made by asking Lean directly" | `MIPStarRE/QPBT/Test/AxiomAudit.lean` exists, is built by `lake build MIPStarRE.QPBT.Test.AxiomAudit`, and machine-checks all 13 QPBT headline declarations. Its own docstring says it was written precisely so a reader need not run a throwaway metaprogram. | fix — the README understates the artifact |
| 3 | "In the `.lean` files of the whole tree the word `sorry` occurs exactly four times: twice in prose inside docstrings (`LDT/Test/AxiomAudit.lean:81`, `QPBT/Combining/Apply.lean:57`), once in prose in `scripts/comparator/challenge_header.lean:14`, and once as real syntax in `scripts/comparator/challenge_footer.lean:44`" | Eight times. The four named ones, plus `MIPStarRE/QPBT/Test/AxiomAudit.lean:27` (prose), `scripts/comparator/challenge_qpbt_header.lean:15` (prose) and `scripts/comparator/challenge_qpbt_footer.lean:31,59` (real syntax, the statement-only QPBT challenge template). | fix — a reviewer who runs the grep gets a different number than the README promises; the substantive claim (none under `MIPStarRE/`) still holds |
| 4 | names only `scripts/comparator/expected/Challenge.lean.expected` (prose at :14, `sorry` at :802) among the extensionless Lean-shaped files | `scripts/comparator/expected/ChallengeQPBT.lean.expected` also exists, with prose at :15 and `sorry` at :2624 and :2652. | fix |
| 5 | "There is no comparator challenge for `pauli_soundness` yet." | The repository now carries the QPBT challenge template: `scripts/comparator/challenge_qpbt_header.lean`, `challenge_qpbt_footer.lean` and the checked-in `expected/ChallengeQPBT.lean.expected`. Whether the external `Dengnifer/QPBT-comparator` repository is still a placeholder was **not** checked (no network in this audit), so only the in-repo half of the sentence is contradicted. | fix, with the external half re-checked first |
| 6 | Build-time table: "Timings below are … from `results/telemetry/builds.jsonl` (1,608 rows)" | The file has 1,630 rows at this commit; the two row-count columns (1,248 and 172) are stale by the same drift. | minor |
| 7 | The table's two kinds of build are "incremental" (median 37 s) and "fresh worktree seeded from a warm local cache" (median 75 s) | Neither describes a clean clone. A third row is now available: *clean clone, Mathlib from a local store, project oleans from scratch — 803 s*. | fix (add the row) |
| 8 | "expect the `lake exe cache get` download of Mathlib to dominate the first build" | Consistent with, but not demonstrated by, this run: the download was deliberately bypassed. Worth stating as still-unmeasured rather than as an expectation. | minor |
| 9 | Build recipe lists `lake exe cache get` then `lake build MIPStarRE.QPBT` and says `lake build MIPStarRE` "build everything" | Correct as written, but the README nowhere says that the repository's own blueprint gate (`scripts/blueprint_leanok_axioms.py --ci`, which the pre-push hook runs) **requires** `lake build MIPStarRE`; after `lake build MIPStarRE.QPBT` alone it exits 1 with two spurious failures (section 4.2). A reviewer following the README's QPBT-only path and then running the documented gate sees a red result on a green repository. | fix — highest practical risk to a sceptical reviewer |
| 10 | Machine requirements paragraph gives cores and RAM but no memory figure for the build | Peak was 5.10 GB in a single `lean` process and ~84 GB summed across 21 concurrent processes; on a small machine the concurrency, not any single module, is the memory constraint, and Lake 5.0.0 offers no `-j` to cap it. | minor (useful addition) |
| 11 | "23 files raise `maxHeartbeats` and 17 raise `synthInstance.maxSize`" | Confirmed exactly: 23 and 17. Listed here as *checked and correct*, not a discrepancy. | none |

Also checked and correct: the paper-gap register count — `docs/paper-gaps/` holds 49
`.tex` files, of which 4 (`command.tex`, `template.tex`, `policy.tex`,
`proof-gap-protocol.tex`) are not notes, leaving exactly the 45 the README claims.

## 7. Disk and disposition

The clone was left in place, as instructed:

```
/home/drx/.cache/mipstarre-dev/clean-clone-20260921   5.7 GB total
  repo/.lake/build   3.7 GB   (this project's own oleans, built in this run)
  repo/.git          318 MB
  repo (sources)     ~1.7 GB
```

`.lake/packages` is a symlink into the existing shared store and adds nothing.
Free space on `/` afterwards: 1.8 TB of 5.0 TB. The meta decides on cleanup;
deleting the directory reclaims 5.7 GB and loses only the warm build.

## 8. Timing of this audit

Start 2026-09-21T01:35:42Z, end 2026-09-21T02:07:12Z (both from `date -u +%FT%TZ`
on ghz), well inside the 200-minute budget. Artifacts left on ghz for inspection:
`/tmp/opus-9f58d960-build.out` (QPBT build log), `/tmp/opus-9f58d960-build2.out`
(full-library build log), `/tmp/opus-9f58d960-leanok.out` and
`/tmp/opus-9f58d960-leanok2.out` (blueprint gate, before and after the full build),
`/tmp/opus-9f58d960-mem.txt` (memory samples).
