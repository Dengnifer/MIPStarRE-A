# MIPStarRE-dev

Formalization project for mathematics around $\mathrm{MIP}^*=\mathrm{RE}$ —
the **local-only continuation** of
[LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE). All workflow
operations (CI, review, issues, PRs, site) run locally; see
[`local/README.md`](local/README.md) and [`local/DESIGN.md`](local/DESIGN.md).
Badges and the published site are replaced by `local/bin/site.sh` output
served from the local component store.

## Active paper track

- **Active (QPBT)**: the quantum Pauli basis test —
  arXiv:2001.04383, *MIP\*=RE* (§7 "Classical and Quantum Low-degree Tests"
  and appendix "Analysis of the Pauli basis test"), with arXiv:1904.05870,
  *NEEXP in MIP\** as secondary source. Per-section paper mirrors:
  `references/qpbt-paper/`, `references/neexp-paper/` (see their READMEs for
  the file/line manifests; split by `scripts/split_reference_paper.py`).
- **Inherited (LDT)**: arXiv:2009.12982, *Quantum soundness of the classical
  low individual degree test*; mirror at `references/ldt-paper/`.

## Source-of-truth order (LDT)

When working on the active track, consult these locations in this order:

1. **`references/ldt-paper/`** — in-repo TeX source mirror for the paper. This is the mathematical ground truth.
2. **`blueprint/src/chapter/`** — active, dependency-tracked LaTeX blueprint with Lean cross-references (`\lean{}`, `\leanok`).
3. **`MIPStarRE/`** — Lean scaffold that matches the blueprint. Declarations in `MIPStarRE.LDT.*` are cross-referenced from the blueprint.

Supporting notes:

- `audits/2026-03-20_ldt-source-map.md` — source-file / theorem-ownership map
- `audits/2026-03-20_ldt-blueprint-dependency-review.md` — dated dependency-review snapshot (context, not canonical)

The blueprint is organized by **theorem ownership and proof dependency**, not by raw TeX input order.

## Repository layout

```
MIPStarRE/
├── Quantum/               # Reusable matrix / measurement infrastructure
│   ├── FiniteHilbert.lean
│   ├── FiniteMatrix.lean
│   ├── Measurement.lean
│   └── ProjectorONB.lean
└── LDT/                   # Low individual degree test (12 submodules)
    ├── Basic/             # Parameters, operators, distributions, submeasurements
    ├── Test/              # Test definitions & main theorem
    ├── Preliminaries/
    ├── MakingMeasurementsProjective/
    ├── MainInductionStep/
    ├── ExpansionHypercubeGraph/
    ├── GlobalVariance/
    ├── SelfImprovement/
    ├── CommutativityPoints/
    ├── Commutativity/
    ├── Pasting/
    └── Tactic/            # Project-local tactics & simp sets
```

Each LDT submodule typically contains `Defs.lean` and `Theorems.lean` (larger
submodules split these across subdirectories). The root module `MIPStarRE.lean`
re-exports `MIPStarRE.Quantum` and `MIPStarRE.LDT`.

Top-level directories:

- `MIPStarRE/` — Lean source (see above)
- `blueprint/src/` — active blueprint (chapters under `blueprint/src/chapter/`)
- `references/` — in-repo TeX mirrors of the source papers
- `docs/` — contributor guides, style, naming, proof integrity, CI notes
- `audits/` — dated chapter-by-chapter dependency-scouting reports
- `local/` — the local workflow layer (protocols, personas, executables)
- `issues/`, `prs/` — local issue tree and PR registry
- `results/telemetry/` — session/build/stage telemetry (research data)

## Recommended proof-filling order

The source-file order is not the proof-dependency order. The recommended implementation order is:

1. Sections 3–4: test setup and preliminaries
2. Section 5: making measurements projective
3. Sections 7–8: expansion and global variance
4. Section 9: self-improvement
5. Sections 10–11: commutativity
6. Section 12: pasting
7. Section 6: main induction wrapper

## Build

**Toolchain**: See `lean-toolchain` and `lakefile.toml` for the pinned Lean and Mathlib versions.

From the repo root:

```bash
# First-time setup: fetch the Mathlib cache, then build
lake exe cache get
lake build

# Type-check a single file (fastest iteration loop)
lake env lean MIPStarRE/LDT/SelfImprovement/Defs.lean

# Check declarations referenced from the blueprint
lake exe checkdecls blueprint/lean_decls
```

Blueprint commands (from the repo root, with `leanblueprint` on your `PATH`):

```bash
leanblueprint pdf    # PDF output
leanblueprint web    # HTML output
```

## Contributing

Start with [`docs/CONTRIBUTING.md`](docs/CONTRIBUTING.md) for PR/issue conventions and the review checklist. Key references:

Shared Mathlib-style conventions (style, naming, documentation, PR review,
proof integrity, prose) live in the `lean-conventions` skill of
[texra-ai/texra-lean-skills](https://github.com/texra-ai/texra-lean-skills),
auto-installed for Claude Code via `.claude/settings.json` (other agents:
clone the repository and symlink the skill directories into the agent's
skill location, as described in its README).

MIPStarRE-local references:

| File | Purpose |
|------|---------|
| `docs/CONTRIBUTING.md` | PR format, issue templates, label taxonomy, review checklist |
| `docs/project_conventions.md` | MIPStarRE-local addenda to the shared conventions (linter warnings, source-faithfulness review, proof integrity) |
| `docs/mathematical_language.md` | Project-local mathematical language rules for Lean names and documentation |
| `docs/blueprint_style_guide.md` | Blueprint notation and section conventions |
| `docs/ci-automation.md` | GitHub-era CI/CD reference (mechanisms now live in `local/`) |
| `local/README.md` | Local workflow: lifecycle, commands, ground rules |
| `audits/` | Chapter-by-chapter Mathlib dependency scouting reports |

When adding or completing a declaration, update the corresponding blueprint entry in `blueprint/src/chapter/`: add `\lean{DeclName}` and `\leanok` for new results, or `\leanok` on `\begin{proof}` for newly proven results.
