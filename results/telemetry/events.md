# Incident and observation log

Dated bullets, one incident each: symptom → diagnosis → fix → lesson.
This file is the raw feed for `local/protocols/EVOLUTION.md`.

## 2026-08-30

- **Stale seed clone.** Symptom: files copied from the sibling `../MIPStarRE`
  checkout were dated Jul 5 while upstream main was Aug 25. Diagnosis: the
  local clone's fetched refs were two months old; `git status` against a stale
  `origin/main` looked clean. Fix: `git fetch`, then `git archive origin/main`
  overlay plus replay of upstream deletions. Lesson: verify snapshot freshness
  against the remote SHA (`gh api .../branches/main`) before seeding, not
  against local tracking refs.
- **Warm-cache invalidation by toolchain bump.** The upstream snapshot moved
  to Lean v4.32.0 while the copied `.lake` was built on v4.31.0; the planned
  zero-cost cache seed became a full rebuild (25,052 s, see `builds.jsonl`).
  Lesson: the hot-cache keyhash (lean-toolchain + lake-manifest.json +
  lakefile.toml) is the first thing to check when estimating seed cost.
- **Dirty vendored package blocks `lake exe cache get`.** Symptom: cache
  fetch aborted with "Your local changes ... would be overwritten by
  checkout" for `.lake/packages/proofwidgets/widget/js/lake.trace`.
  Diagnosis: past builds mutate files inside the vendored package's git tree;
  a CoW-copied `.lake` carries that dirt. Fix: `git reset --hard` inside the
  package. Lesson: worktree bootstrap must reset vendored package trees
  before cache fetch (ported into `worktree-setup.sh`).
- **Mathlib cache partial miss.** 20 of ~9k cache files failed to download;
  `lake build` compiled those modules locally. No action needed; noted as a
  normal degraded mode of `lake exe cache get`.
- **Workflow critic stalled on oversized prompt.** Symptom: the study
  workflow's final critic agent made no progress for 6×180 s and the run
  failed after its 7 readers had finished. Diagnosis: the critic prompt
  embedded the full 180 KB merged JSON of all reader results. Fix: harvested
  reader results from the journal; the main session performed the critique
  itself over a rendered digest. Lesson: pass large fan-in data to agents by
  file path, not inline; cap inline context in synthesis prompts.
- **Verification pass caught four live defects in the drafted layer.** The
  7-builder Opus draft passed syntax/smoke on the data layer, but the Fable
  verifier live-demonstrated: (1) the merge gate could never accept a reviewed
  PR (verdict-file glob mismatch); (2) the cap-time forced review was a
  guaranteed no-op (review refused under the fix lock its own caller held);
  (3) three uncoordinated machine-wide build locks; (4) `printf '%04d'` octal
  crash on ids 0008/0009. All fixed same day (`EVOLUTION.md` entry); post-fix
  smoke rerun: issue → PR → green CI fixture → review verdict → merge gate
  PASS → full no-ff merge with bookkeeping. Lesson: multi-agent drafts need an
  adversarial cross-cutting verifier; per-builder self-tests missed every
  cross-script contract break.
- **First warmer run headed for a duplicate 7-hour compile.** Symptom: on its
  first invocation `cache-warmer.sh` cloned the primary repo into
  `hot-main/repo` with an empty `.lake` and would have compiled the whole
  library from source, duplicating the seed build finished the same morning.
  Diagnosis: the drafted warmer had no first-run seeding path — the parent CI
  never needed one because its first cache save came from an ordinary main
  run. Fix: killed the run, added `seed_hot_repo_lake` (copy-on-write clone
  of the primary checkout's `.lake` under a matching keyhash), reran.
  Lesson: every "restore" mechanism needs an answer for the empty-store case;
  cold paths that silently recompute for hours are duplicate-compilation bugs
  even when they terminate correctly.
- **Silent CRLF normalization defeated the split verifier.** Symptom: the
  paper-mirror splitter reported byte-identity, but `cmp` against the arXiv
  source showed every line differing. Diagnosis: the source ships CRLF line
  endings; Python's `read_text` silently normalizes them, so the in-script
  string comparison saw two normalized copies while the emitted files (LF)
  differed from the original (CRLF) by one byte per line. Fix: read bytes,
  normalize CRLF→LF deliberately, verify at byte level modulo exactly that
  normalization, record it in the mirror README. Lesson: verification must
  compare at the representation level of the claim — a byte-level claim needs
  a byte-level check; text-mode I/O is not neutral.
- **Machine slept mid-fleet (stage 3 extraction).** Three readers died with
  "Your computer went to sleep mid-response"; a fourth stalled on retries. The
  two survivors (sec8, sec14a) returned complete inventories. Fix: hold a
  `caffeinate -is` assertion for long agent runs; re-run failed readers via
  workflow resume (cached successes reused) with FILE-based output — large
  inline structured returns remain fragile (second occurrence; the rule from
  the study-fleet incident now also covers agent outputs, not just inputs).
- **First codex review caught three real process defects (PR #0002).** On a
  one-file deletion, the reviewer verified the deletion mathematically (git
  blob identity, alias config, retained note vs paper source) and flagged:
  unfilled Motivation/Description/Testing template in `pr.md`, unfilled bug
  template in the issue, and an `Addresses`/`Closes` divergence between
  the PR record and the commit that would have left the completed issue
  open after merge. All three fixed; verdict machinery
  (CHANGES_REQUESTED → ledger → merge-gate block) worked as specified.
  Lesson: the commit message is not the record — the PR/issue files are
  authoritative for merge bookkeeping, and the reviewer reads them.
- **Registry fork recurred via a stale worktree script copy.** After the
  registry-root fix landed on main, a CI+review chain invoked from inside
  the blueprint worktree ran the branch's pre-fix copies of the scripts and
  forked the registry again. Fix: artifacts relocated; operational rule
  added to `local/README.md` — always invoke workflow tools via the primary
  checkout's path. Lesson: a protocol fix in versioned tooling is not
  deployed until every live branch carries it; invocation discipline (or a
  merge into open branches) bridges the gap.
- **Review-fix loop reached the faithfulness layer (stage 3).** Rounds:
  33 → 26 → 18 findings. Round 1 was mostly writer errors; round 2 mostly
  boundary domains plus register violations introduced by round-1 fixers;
  round 3 exposed two genuine source obstructions (the classical-test
  instantiation at dimension 2m+2 vs the m | q admissibility, and
  supremum attainment in the symmetrization lemma), which per the
  faithfulness policy became the first QPBT paper-gap notes rather than
  silent statement conditioning. The codex reviewer independently enforced
  the parent project's statement-drift discipline.
- **Review loop non-convergent at the tail (PR #0001).** Finding counts by
  round: 33, 26, 18, 12, 17. Rounds 1-2 removed real defects; by round 5 the
  reviewer audited proof sketches of imported theorems at formalization
  depth, invented obligations for heuristic repair sketches in gap notes,
  and relitigated a policy sanctioned in a ledger it cannot see from the
  branch. Diagnosis: a fresh reviewer per round has no memory of prior
  adjudications and unbounded depth on new text; iteration alone does not
  terminate. Fix: review.md gains a round-cap/operator-adjudication rule
  (see EVOLUTION.md) mirroring the parent's bot-fix iteration-cap
  philosophy.
- **`elan show` errors on this machine.** `~/.elan/toolchains/stable` is a
  stale non-symlink directory (Jan 2025); pinned-toolchain resolution is
  unaffected. Left untouched; scripts must not depend on `elan show`.
- **Fable 5 usage limit hit (2026-08-31).** All four 4.2 brief-drafter agents failed at dispatch with the account limit message; the main session continued. Mitigation: subagent fleets fall back to Opus (the standing model policy makes this the default for non-frontier reasoning anyway); codex sessions unaffected. Lesson for the paper: multi-model quotas are a real scheduling constraint — parallelism plans need a per-model budget column.
- **Invalid UTF-8 argv broke every review dispatch of PR #0003.** Symptom: codex exited 2 in ~1 s with "invalid UTF-8 was detected in one or more arguments"; the pre-model retry failed identically. Diagnosis: `dispatch.sh` truncates untrusted attachments with `head -c`, which cuts at a byte boundary; the QPBT Lean diff is dense with mathematical Unicode, and the cut split a multibyte character — stage-3 TeX diffs were ASCII-heavy, so the latent defect never fired. Fix: UTF-8-safe truncation (decode with errors=ignore after the byte cap). Lesson: byte-capped truncation of UTF-8 text must always be followed by a decode-boundary repair; and a failing dispatch should be reproduced with the REAL payload, not a toy probe (the toy probe passed and misdirected the first diagnosis to transience).
