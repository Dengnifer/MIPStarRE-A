---
title: "PR535 source-fidelity review repair"
date: 2026-09-14
purpose: >
  Record the source-domain correction for the global polynomial-pair theorem
  and the accompanying blueprint and provenance repairs.
issue: "#513"
pull_request: "#535"
review: "5199515994"
status: complete
start_head: 4c90749080524e1bd3b14b8e259cc31f5e9a78af
---

# Scope

The repair addresses the nine findings in canonical review `5199515994` while
preserving the completed construction of `exists_globalPairWitness`. The
mathematical sources are the strategy assumptions at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:160-172` and
`lem:qld-4-7` with its proof at lines 1267--1404.

# Finding Dispositions

1. The public hypothesis `0 < epsilon` was removed from
   `exists_globalPairWitness`. Its only use was to prove `0 <= epsilon`; the
   proof now uses `ProjectiveSetting.eps_nonneg`, which derives this fact from
   the strategy value and success hypothesis already contained in the setting.
2. The blueprint now gives separate existential statements for
   `exists_rounded_polynomial_wrong_variable_mass` and
   `exists_rounded_polynomial_separated_mass`. It no longer identifies their
   independently chosen rounded measurements.
3. The polynomial-fiber statement now selects a nonzero coefficient of a
   nonconstant monomial, rather than asserting that the coefficient polynomial
   is itself nonconstant.
4. The direct passing-error statement retains the unit cap
   `min {1, 3 (sqrt (...) + y)}`.
5. The duplicated pair-completion entries were consolidated. Definitions now
   introduce the restriction, transport, and completion constructions, while
   theorem environments state injectivity, effect, range, readout, and
   projectivity properties.
6. The public scalar lemmas `rpow_quarter_nonneg` and
   `sqrt_deficit_bound_le` are linked from the formalization-only blueprint
   theorem `thm:qld-quarter-power-deficit-bound`.
7. Direct blueprint dependencies now record the conditioned polynomial bound,
   the three inputs used by the established line construction, the rounded
   separated-mass theorem used by pair completion, and the direct-line overlap
   used in `lem:qld-4-13-established`.
8. Boolean implementation descriptions were replaced by the mathematical
   orders `XZ`, `ZX`, `x | z`, and `z | x`.
9. PR, commit, and proof-recovery history was removed from mathematical
   docstrings and blueprint prose. The history remains in this audit and the
   earlier issue-513 audits.

# Preserved Provenance

The relevant immutable sources remain recorded as follows:

- PR535 pair completion: `1744bd9533055b9b43af9a8d46906cbafb69afdd`, with
  earlier restriction and completion work through `cb6d86d8`.
- PR545 scalar passing bound: `2f8f5cc4631db2db23f76513a2f7f56dffc8fa4f`.
- PR549 established line construction:
  `aeaca3aee589ff666c5ab6feb2681e2cb06e8b1d`, including the construction
  chain at `6e8d67ef8ba22de69a0c166adcdf23ba6e7a33aa`.
- PR296 polynomial-image estimates:
  `2c8f147643d151d8616864cf49817dc6422a9a86`.

Further mathematical and branch history is in
`audits/2026-09-14_issue-513_actual-error-absorption.md`,
`audits/2026-09-14_issue-513_retained-pair-completion.md`, and
`audits/2026-09-14_issue-513_pr535-branch-reconciliation.md`.

# Statement Integrity

Paper assumptions: an admissible tuple and a projective strategy succeeding
with probability at least `1 - epsilon`. The source does not separately assume
strict positivity of `epsilon`.

Lean assumptions: `P : AdmissibleParams`, `epsilon : Real`, and
`S : ProjectiveSetting P epsilon`. Nonnegativity of `epsilon` follows internally
from `S.eps_nonneg`; no error-domain premise is exposed to the caller.

Paper conclusion: universal constants `a > 1` and `0 < b < 1`, followed by
projective global polynomial-pair measurements on both local spaces satisfying
the `X`- and `Z`-point consistency conclusions for both players.

Lean conclusion: universal constants with the same inequalities, followed by
`Nonempty (GlobalPairWitness S (deltaQld ...))`. The witness contains both
projective pair measurements and all four universally quantified consistency
fields. The quantifier order is constants, parameters, error, and strategy.

Verdict: faithful boundary hypotheses. `AdmissibleParams` and
`ProjectiveSetting` package the paper's domain, and no additional public
mathematical assumption remains.

# Validation

- Every changed Lean file passed `lake env lean` directly.
- The explicit current-source signature query confirmed the absence of
  `0 < epsilon`.
- The full `GlobalPairWitness` field expansion and exact target signature were
  printed from the current source. Axiom queries for the target and thirteen
  supporting declarations returned exactly `propext`, `Classical.choice`, and
  `Quot.sound`.
- `leanblueprint web` and `leanblueprint pdf` passed.
- Blueprint synchronization passed after regenerating `blueprint/lean_decls`.
- `lake exe checkdecls blueprint/lean_decls` resolved all 1534 declarations.
- `scripts/install_git_hooks.sh` and `scripts/install_git_hooks.sh --check`
  passed, with `core.hooksPath=.githooks`.
- `git diff --check`, the added-token scan, the changed-file provenance scan,
  and the 100-column scan passed.

A focused Lake target was attempted only to refresh the cached `Apply.olean`.
It could not remove read-only cached IR artifacts in the copy-on-write cache, so
the exact signature and axiom queries were instead checked in the same direct
Lean elaboration as the current `Apply.lean` source. This cache limitation is
not a Lean diagnostic and no cache permission or runtime setting was changed.

No full project build, canonical CI, independent review, publication, or push
was performed.

# Existing Open Obligations

This repair introduces no proof hole. `Apply.lean` retains three pre-existing
open auxiliaries:

- `exists_extendedLinesWitness_ofPointsWitness`, whose supplied-point domain
  must be realigned to include the actual point error; see issue #509 and
  `docs/paper-gaps/qpbt_combined-lines-error-term.tex`.
- `exists_extendedLinesWitness`, which requires a different estimate for the
  printed error expression; see issue #510 and the same paper-gap note.
- `exists_extendedLinesWitness_established_ofPointsWitness`, which requires a
  supplied-point construction with the correct dependence on its point error,
  or removal after factoring through the proved existential construction; see
  `docs/paper-gaps/qpbt_combined-lines-error-term.tex`.

None of these declarations occurs in the axiom closure of
`exists_globalPairWitness`.
