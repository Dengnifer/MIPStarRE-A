# Main-session handoff — state as of 2026-08-31

Written by the outgoing Claude main session at migration to ghz. The
incoming codex main session (persona: `local/personas/main.md`, launcher:
`local/bin/main-session.sh`) continues from exactly here.

## Project

Formalize the quantum Pauli basis test (QPBT) of MIP\*=RE (arXiv:2001.04383,
§7 + the "Analysis of the Pauli basis test" appendix; secondary
arXiv:1904.05870) in Lean 4, using the fully local agent workflow in
`local/` (the localized continuation of LionSR/MIPStarRE's GitHub workflow),
recording telemetry throughout as data for a research paper on
self-evolving formalization workflows.

## Stage status

| Stage | Status |
|---|---|
| 1 — workflow skeleton (`local/`, registry, telemetry, hot cache) | DONE |
| 2 — per-section paper mirrors (`references/qpbt-paper`, `neexp-paper`) | DONE |
| 3 — blueprint ch11–ch16, ~250 nodes, 3 paper-gap notes | DONE (PR #0001, §12-adjudicated after 6 review rounds) |
| 4.1 — minimal Lean skeleton (`MIPStarRE/QPBT/`, thm:pauli + 39-node closure, 167 decls, 16 proof-position sorries, build green) | IMPLEMENTED on branch `issue-0006-qpbt-minimal-skeleton` (commit `db4327a`), PR #0003 — **review pending** (see Immediate next steps) |
| 4.2 — full skeleton of all blueprint nodes (sorry proofs) | Briefs DRAFTED (`issues/briefs/42-*.md`), OPEN items need adjudication |
| 4.3 — proofs | Not started; parallelization plan below |

## Immediate next steps (in order)

1. **PR #0003**: review round 1 is DONE at head `db4327a` —
   CHANGES_REQUESTED with 17 findings in
   `prs/0003-*/reviews/db4327a...-code.md` (no prose lane: the diff has no
   blueprint files). Adjudicate each finding against the blueprint/source
   before fixing (reviewers can be wrong — see events.md); dispatch a
   repair session (`dispatch.sh --role prover` or an orc), commit, re-run
   `ci.sh 0003` + `review.sh 0003`; round cap 4, then §12 adjudication.
   Merge; close #0006; telemetry.
2. **Adjudicate the 4.2 brief OPEN items** (all four briefs in
   `issues/briefs/42-*.md`; the fleet's cross-brief notes are summarized in
   each). The consequential ones:
   - polyFunc subtype has NO Fintype instance in the repo — decide the
     coefficient-box equivalence route (ch15 brief OPEN-3) once, wave-wide.
   - Ownership of `def:consistency`, `def:symmetric-game`,
     `def:projective-strategy-general`, `def:line-point-dist` — the ch14
     brief claims all four (its OPEN-1); confirm to avoid double
     definitions with the residual brief.
   - Reconcile briefs against the MERGED 4.1 names (each brief's
     RECONCILE list; e.g. `tauObservable` export, `ProjectiveSetting` vs
     `ExpandedSetting` naming, top-level `deltaLine ε` convention,
     `deltaQld_mono` append to `Test/Soundness.lean`).
   - The divisibility-guard split (ch15 OPEN-7) and the double error-form
     of `lem:qld-4-13` (OPEN-4) — match the blueprint's adjudicated state.
3. **Stage 4.2 wave A** (parallel): issues + orchestrators for (a) ch14
   skeleton, (b) residual ch11–13 nodes. Wave B after wave A merges:
   ch15 ∥ ch16. One worktree per orchestrator; `dispatch.sh` serializes
   writers per worktree by lock.
4. **Stage 4.3**: build `local/bin/frontier.py` (blueprint `\uses` DAG +
   sorry list → ready set), keep 4–6 prover lanes saturated; per-module
   batch PRs; the two mathematical critical-path items are the paper-gap
   obligations: `gap:qpbt_ld-dimension-divisibility` (recommended
   direct-index-sampling route WITH the game-level strategy transport) and
   the `lem:ld-soundness` import interface (tensor-code correspondence +
   the K ≥ 12m(d+1) bound cases). Also pending from stage 3:
   issues #0004, #0005; blueprint `\uses` sync gaps listed in the 4.1
   orchestrator report (`results/telemetry/sessions/orc-0006-20260831-01.last.md`).

## Hard-won operational lessons (do not relearn these)

- Fill issue/PR record bodies — the reviewer audits them (twice flagged).
- Review loop: cap at 4 rounds, then §12 adjudication; reviewers have no
  memory across rounds and unbounded depth on new text.
- Byte-capped truncation of UTF-8 must repair the decode boundary
  (dispatch.sh does now); reproduce failures with the REAL payload.
- Machine-wide full-build mutex: `$CACHE_ROOT/.full-build-lock`; a live
  owner is never broken. Single-file `lake env lean` needs no lock.
- Hot cache: only `cache-warmer.sh` writes snapshots; worktrees consume
  via `worktree-setup.sh`; never `lake update`.
- Pass large agent inputs by file path; never inline huge JSON.
- events.md → EVOLUTION.md is the amendment pipeline; cite triggers.

## Environment on ghz

Lean v4.32.0 via elan; codex CLI ≥0.151 (auth in `~/.codex`); blueprint
stack via pip --user (`leanblueprint`, `plastex`, `texra-blueprint` 0.3.8;
`tomllib` shim for Python 3.10 at
`~/.local/lib/python3.10/site-packages/tomllib.py`); TeX native; 128 cores
(full `lake build` is fast — still honor the mutex). `PATH` needs
`$HOME/.elan/bin` and `$HOME/.local/bin`. Git hooks: run
`scripts/install_git_hooks.sh` in every fresh worktree. GitHub mirror via
`local/bin/github-sync.sh` (deploy key `~/.ssh/id_ed25519_mipstarre_qpbt`).

## Telemetry so far (for the paper)

Stages 1–4.1 logs in `results/telemetry/` are complete: stage timings,
~14M Claude-agent tokens + ~25 codex sessions, 15+ ledgered incidents,
12 protocol amendments. Keep the same discipline; the model-family switch
(Claude main → GPT main) is itself a recorded event and a datum.
