# Task: implement the stage-4.1 minimal Lean skeleton (issue #0006, PR #0003)

You are the orchestrator for issue #0006. Implement the minimal Lean 4
skeleton for the quantum Pauli basis test in this worktree
(branch `issue-0006-qpbt-minimal-skeleton`).

## Authority and inputs, in order

1. `issues/briefs/0006-minimal-skeleton-brief.md` — the design brief: the
   39-node closure, the 13-file tree under `MIPStarRE/QPBT/`, the
   node→declaration mapping with REUSE/NEW decisions and signature
   sketches. Follow it; signature sketches may be adjusted where Lean
   forces it, with a `--` comment noting the deviation.
2. `blueprint/src/chapter/ch11_qpbt_algebra.tex`, `ch12_qpbt_games.tex`,
   `ch13_qpbt_test.tex` — the statements being encoded. Statement
   fidelity to these (and through them to `references/qpbt-paper/`)
   outranks convenience. Every statement-like declaration carries a
   docstring citing its blueprint label AND the paper mirror
   file:line-range (AGENTS.md paper-origin rule).
3. `AGENTS.md` — conventions (naming, file structure, module docstrings,
   line limits, import style).

## Orchestrator adjudications of the brief's OPEN items (binding)

- OPEN-1/OPEN-6: carry `def:subfield-trace` and `def:binary-representation`
  in the skeleton. `pauli_soundness` is stated over the FIXED self-dual
  normal-basis identification exactly as the paper fixes it (no
  quantification over arbitrary field models). The missing blueprint
  `\uses` edges are a known blueprint gap — do NOT edit the blueprint in
  this PR; note them in your final report.
- OPEN-2: keep `lem:pauli-observable-expansion` as a sorry'd lemma, as
  the brief has it.
- OPEN-3: inline the typed-CL construction per the brief; note the
  blueprint gap in the report.
- OPEN-4: keep `Game.value` as the csSup form for fidelity.
- OPEN-5: the basis-free pivot characterization is approved; the
  RREF-equivalence lemma is out of scope (stage 4.3).

## Working rules

- All proofs are `sorry`. No axioms. No `native_decide`. Definitions must
  be real (no placeholder `def foo := 0`-style scaffolding that cannot
  support later proofs — AGENTS.md "castle-in-the-air" rule).
- Iterate with `lake env lean MIPStarRE/QPBT/<File>.lean` per file (the
  worktree's cache is warm; single-file checks take seconds). Run
  `lake build` once at the end.
- `rg -n "sorry" MIPStarRE/QPBT` at the end: every hit must be a proof
  placeholder, never a definition body.
- Wire the imports: `MIPStarRE/QPBT.lean` re-exports the modules;
  `MIPStarRE.lean` gains `import MIPStarRE.QPBT`.
- You may dispatch helper codex sessions with
  `local/bin/dispatch.sh --role prover --issue 0006 --worktree <this worktree> -- "<subtask>"`
  for parallelizable file groups, but for a skeleton of this size doing
  it yourself file-by-file in dependency order is acceptable.
- Commit on this branch as you complete coherent units (PR title
  conventions from AGENTS.md; subject `feat(QPBT): ...`; body cites
  issue #0006). Do NOT touch `issues/`, `prs/`, `results/`, the
  blueprint, or any file outside `MIPStarRE/` + `MIPStarRE.lean`.

## Definition of done

`lake build` succeeds; `pauli_soundness` states thm:pauli faithfully per
ch13 (statement-integrity check: paper assumptions vs Lean assumptions,
paper conclusion vs Lean conclusion — include this audit in your final
report); every closure node from the brief exists with its docstring and
citation; all sorries are proof-level. Finish with a report: files
created, declaration count, sorry count, deviations from the brief,
blueprint gaps to sync later.
