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
- **GitHub CLI discovery and API authentication were separate prerequisites.**
  Symptom: `gh` was not on the main session's `PATH`, Ubuntu reported no
  installed package, and a system install attempt could not obtain `sudo`;
  inspection then found an existing binary at `~/.local/bin/gh`. Diagnosis:
  the handoff's required user-local path was absent from this shell, while
  `gh auth status` independently reported no authenticated GitHub host; the
  repository deploy key authenticates Git transport, not GitHub API calls.
  Fix: use the explicit user-local binary for preflight and leave API writes
  pending until the owner completes `gh auth login` with the scoped PAT.
  Lesson: migration preflight must check user-local binary discovery, API
  authentication, and SSH Git access separately before attempting installation.
- **The main-session sandbox initially denied the workflow lock root.**
  Symptom: the first `issue_new.py` invocation failed before allocation with
  `EROFS` for `~/.cache/mipstarre-dev/locks/issues-seq.lock`. Diagnosis: the
  workspace sandbox admitted repository writes but not the shared runtime
  cache required by the lifecycle's concurrency protocol. Fix: rerun the same
  sanctioned command with explicit access to the cache root; issue `#0007`
  was then allocated once. Lesson: authorize the runtime lock root for main
  lifecycle commands and never bypass the locks merely because the repository
  itself is writable.
- **Old `gh auth status` falsely rejected a valid fine-grained PAT.**
  Symptom: after `gh 2.4.0` accepted the token, `gh auth status` reported that
  it was no longer valid, prompting an attempted client upgrade over a link
  transferring only about 10 KiB/s. Diagnosis: this client predates
  fine-grained PATs; a direct read-only `gh api user --jq .login` call
  authenticated successfully as `Dengnifer`. Fix: stopped the unnecessary
  release download and adopted a functional API capability probe for issue
  `#0007` instead of treating `auth status` as authoritative. Lesson:
  authenticate by exercising the required API surface; a legacy client's
  credential-format diagnostic can be a false negative.

## 2026-08-31

- Write-through adapter superseded during implementation. Symptom: the first issue-0007 orchestrator had begun adding a durable local GitHub-operation journal when the owner rejected retaining any local issue/PR fallback. Diagnosis: the earlier step-0 brief preserved registry machinery that no longer matched the owner's desired GitHub-only authority. Fix: stopped the session before commit, reverted its partial edit, verified and moved all 60 issue/PR files byte-identically into results/telemetry/registry-archive in the isolated c8f1999 commit, and re-scoped issue 0007 to read live GitHub gate evidence. Lesson: when eliminating an operational registry, archive research evidence before rewriting consumers, and treat an explicit owner authority decision as a protocol amendment rather than extending the superseded design.
- Codex resume dispatch rejected the worktree option. Symptom: dispatch.sh allocated orc-0007-20260831-02, but codex exec resume exited 2 with 'unexpected argument -C' before producing an event. Diagnosis: the dispatcher assembles fresh and resumed codex invocations in the same option order even though this CLI requires global worktree options before the resume subcommand. Fix: retained the zero-usage failed session record and started orc-0007-20260831-03 as a fresh sanctioned session with the committed brief. Lesson: dispatch.sh needs an explicit resume-mode argv test; telemetry-complete failure handling does not imply the resume command itself is compatible.

## 2026-09-01

- Post-audit merge evidence admitted incomplete bindings. Symptom: reviewer
  output could survive a nonzero lane exit, review evidence did not bind the
  base, run, canonical body digest, and dispatcher completion record as one
  object, and the merge gate did not reserve both workflow locks through a
  repeated final evaluation. Ambiguous mutation retries could also send a
  second POST or PATCH. Diagnosis: independently reasonable idempotence and
  exact-head checks were composed without a single strict evidence contract.
  Fix: issue 0007 now uses full-SHA run/digest attestations, exact reviewer
  telemetry, one-mutation read-back, and the same fail-closed evaluator before
  and immediately before guarded merge. Lesson: exact-head evidence is useful
  only when every producer, parser, status, session, and final consumer agrees
  on the same immutable run identity.
- Post-hardening audit found evidence could outlive its committed comparison.
  Symptom: CI and review could begin or publish from a dirty feature worktree;
  review accepted failed CI and permissively normalized malformed reviewer
  output; incomplete review publication could not be recovered without another
  review; and auto-fix did not bind the fetched base through dispatch, commit,
  and push. Reviewer identities and trusted refs also admitted replay or
  unlike-string equality gaps. Diagnosis: full-SHA markers protected remote
  objects, but the producer-side tree, lock lease, parser grammar, evidence
  completion state, and base comparison were not one contract. Fix: require a
  clean committed tree at producer boundaries, ownership-stamped shared fix
  leases, success-only CI review gating, strict state-preserving findings
  parsing, attestation-only consumers plus exact summary recovery, resolved
  trusted commits, cross-attestation identity uniqueness, and full head/base
  checks throughout auto-fix. The final implementation audit also found that a
  cancel arriving after a wrapper commit could strand the unpublished local
  tip; the fix stops further dispatches but permits its ownership-checked,
  original-head leased publication handoff. A second final audit found boundary
  tail, idempotency-lookup, replay preflight, run-id, and summary
  reclassification races; in-process mutation guards, pre-POST identity
  validation, unique attestation run ids, structured findings consumption, and
  one guarded finalizer close them. The closing shell audit additionally found
  that review-fix read its count and body in separate snapshots, a late cancel
  could strand a wrapper commit, phase failures could be masked by Bash's
  conditional `errexit` semantics, and signal traps could report success. It
  also exposed findings/trailer prefix lookalikes and arbitrary backticked text
  passing as canonical locations. Fix: consume one parsed attestation snapshot,
  make cancellation ownership-only for every boundary after local advancement,
  test fallible phase commands explicitly, preserve signal exit status during
  owned-lock cleanup, and require prefix-safe section/trailer sentinels plus
  relative path-and-line locations.
  Lesson: exact-head evidence is trustworthy only when the local committed
  state and every transition to publication are bound as rigorously as the
  remote marker.
- Final merge-integrity audit found that client evidence and server enforcement
  were still separate contracts. Symptom: CI had no digest-bound required
  summary, adverse local reviews could attempt sticky `REQUEST_CHANGES`, merge
  did not validate the actual base's protection and effective rules, and the
  free-form adjudication path did not prove its review rounds or dispositions.
  The merge mutation also needed an explicit no-retry ambiguity path and a CI
  lease alongside the review/fix leases. Diagnosis: exact-head client checks
  alone do not close the final interval in which GitHub evaluates required
  checks, base freshness, and merge policy. Fix: publish pending then
  read-back-bound CI/review summaries; use `COMMENT` for every local review;
  validate zero-approval strict protection and nonweakening effective rules;
  require four exact-comparison adjudication rounds with exhaustive fixed or
  open-issue dispositions; and issue one match-head merge under all three
  leases, reconciling a transient result by read-back only. Lesson: the last
  merge checkpoint must make producer evidence, operator adjudication, local
  serialization, and GitHub's server gate one auditable contract.
