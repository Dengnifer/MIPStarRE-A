# Issue 295 current PolynomialImageBounds validation

Observed: `2026-09-19T06:33:19Z`. Scope: bounded read-only supplement. Worktree head:
`cafe0b5727f50714a2842acf5628f367c2b3a949`.

## Result

- The target module is byte-identical to published main
  `04f79c5071d020fc4578b9ae11808eff2daa575b`.
- Exact source SHA256: `8fd7d1ef781ba368020ff0dae922b601d10065491a9d47706630cef4bc146dd1`.
  Exact Git blob OID on both revisions: `febd9025a72f1d0c60f6af7304c557a2eac9d84b`.
- The imported compiled artifact SHA256 is
  `7cf764259a66d1a2bab076b589c44ec1637c23119785ad34c7b1fc22249d7d6d`.
- Fresh environment enumeration found one and only one qualified-name suffix match for
  each of the 21 targets: **11 public, 10 private, 0 missing**.
- `Lean.collectAxioms` reports exactly `[propext, Classical.choice, Quot.sound]`
  for every actual compiled constant, including all ten generated private names.
- All 21 declaration type headers match the exact retained issue118 source and the
  retained PR296 public checkpoint after normalization of whitespace and removal of
  the visibility keyword. This is stronger than a names-only comparison.
- The complete texts of `orderedIndicator` and `diagonalIndicator`, including their
  defining bodies, also match all three retained/current sources after whitespace
  normalization.

## Fresh Axiom Probe

Probe: `/tmp/qpbt-295-current-axiom-probe.lean` (SHA256 `e3ae8a7bf248a7d0245e55cb97a580b2080ca10d690cf04f5ec6ffeb92b7c88c`).

Log: `/tmp/qpbt-295-current-axiom-probe.log` (SHA256 `85ee1aa52f5870c4e80481dd70263fa086a21b22d79cbef0b76f5ffba52471f1`).

| # | Receipt target | Current visibility | Actual compiled constant | Axiom closure | Signature mapped |
|---:|---|---|---|---|---|
| 1 | `orderedIndicator` | public | `MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator` | exact standard 3 | yes |
| 2 | `diagonalIndicator` | public | `MIPStarRE.QPBT.PolynomialImageBounds.diagonalIndicator` | exact standard 3 | yes |
| 3 | `orderedIndicator_gram_of_ne_zero` | private | `_private.MIPStarRE.QPBT.Combining.PolynomialImageBounds.0.MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator_gram_of_ne_zero` | exact standard 3 | yes |
| 4 | `orderedIndicator_norm_sq_of_ne_zero` | private | `_private.MIPStarRE.QPBT.Combining.PolynomialImageBounds.0.MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator_norm_sq_of_ne_zero` | exact standard 3 | yes |
| 5 | `diagonalIndicator_bounds` | private | `_private.MIPStarRE.QPBT.Combining.PolynomialImageBounds.0.MIPStarRE.QPBT.PolynomialImageBounds.diagonalIndicator_bounds` | exact standard 3 | yes |
| 6 | `orderedIndicator_zero` | private | `_private.MIPStarRE.QPBT.Combining.PolynomialImageBounds.0.MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator_zero` | exact standard 3 | yes |
| 7 | `orderedIndicator_gram_le_one` | public | `MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator_gram_le_one` | exact standard 3 | yes |
| 8 | `abs_orderedIndicator_norm_sq_sub_diagonal_le` | public | `MIPStarRE.QPBT.PolynomialImageBounds.abs_orderedIndicator_norm_sq_sub_diagonal_le` | exact standard 3 | yes |
| 9 | `avg_abs_orderedIndicator_norm_sq_sub_diagonal_le` | public | `MIPStarRE.QPBT.PolynomialImageBounds.avg_abs_orderedIndicator_norm_sq_sub_diagonal_le` | exact standard 3 | yes |
| 10 | `avg_sum_abs_orderedIndicator_norm_sq_sub_diagonal_le` | public | `MIPStarRE.QPBT.PolynomialImageBounds.avg_sum_abs_orderedIndicator_norm_sq_sub_diagonal_le` | exact standard 3 | yes |
| 11 | `sum_projective_state_norm_sq` | public | `MIPStarRE.QPBT.PolynomialImageBounds.sum_projective_state_norm_sq` | exact standard 3 | yes |
| 12 | `avg_sum_abs_projective_orderedIndicator_le` | public | `MIPStarRE.QPBT.PolynomialImageBounds.avg_sum_abs_projective_orderedIndicator_le` | exact standard 3 | yes |
| 13 | `avg_uniform_sum_abs_projective_orderedIndicator_le` | public | `MIPStarRE.QPBT.PolynomialImageBounds.avg_uniform_sum_abs_projective_orderedIndicator_le` | exact standard 3 | yes |
| 14 | `orderedIndicator_reverse` | public | `MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator_reverse` | exact standard 3 | yes |
| 15 | `exists_nonzero_nonlinear_coeff` | private | `_private.MIPStarRE.QPBT.Combining.PolynomialImageBounds.0.MIPStarRE.QPBT.PolynomialImageBounds.exists_nonzero_nonlinear_coeff` | exact standard 3 | yes |
| 16 | `specialization_ne_linear_of_coeff` | private | `_private.MIPStarRE.QPBT.Combining.PolynomialImageBounds.0.MIPStarRE.QPBT.PolynomialImageBounds.specialization_ne_linear_of_coeff` | exact standard 3 | yes |
| 17 | `avg_specialization_eq_linear_le_of_coeff` | private | `_private.MIPStarRE.QPBT.Combining.PolynomialImageBounds.0.MIPStarRE.QPBT.PolynomialImageBounds.avg_specialization_eq_linear_le_of_coeff` | exact standard 3 | yes |
| 18 | `avg_diagonalIndicator_le_of_not_linear` | private | `_private.MIPStarRE.QPBT.Combining.PolynomialImageBounds.0.MIPStarRE.QPBT.PolynomialImageBounds.avg_diagonalIndicator_le_of_not_linear` | exact standard 3 | yes |
| 19 | `avg_orderedIndicator_norm_sq_le_of_not_linear` | private | `_private.MIPStarRE.QPBT.Combining.PolynomialImageBounds.0.MIPStarRE.QPBT.PolynomialImageBounds.avg_orderedIndicator_norm_sq_le_of_not_linear` | exact standard 3 | yes |
| 20 | `avg_sum_orderedIndicator_norm_sq_le_of_not_linear` | private | `_private.MIPStarRE.QPBT.Combining.PolynomialImageBounds.0.MIPStarRE.QPBT.PolynomialImageBounds.avg_sum_orderedIndicator_norm_sq_le_of_not_linear` | exact standard 3 | yes |
| 21 | `nonlinear_mass_le_ordered_error` | public | `MIPStarRE.QPBT.PolynomialImageBounds.nonlinear_mass_le_ordered_error` | exact standard 3 | yes |

The ten private generated names are:

- `orderedIndicator_gram_of_ne_zero` -> `_private.MIPStarRE.QPBT.Combining.PolynomialImageBounds.0.MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator_gram_of_ne_zero`
- `orderedIndicator_norm_sq_of_ne_zero` -> `_private.MIPStarRE.QPBT.Combining.PolynomialImageBounds.0.MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator_norm_sq_of_ne_zero`
- `diagonalIndicator_bounds` -> `_private.MIPStarRE.QPBT.Combining.PolynomialImageBounds.0.MIPStarRE.QPBT.PolynomialImageBounds.diagonalIndicator_bounds`
- `orderedIndicator_zero` -> `_private.MIPStarRE.QPBT.Combining.PolynomialImageBounds.0.MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator_zero`
- `exists_nonzero_nonlinear_coeff` -> `_private.MIPStarRE.QPBT.Combining.PolynomialImageBounds.0.MIPStarRE.QPBT.PolynomialImageBounds.exists_nonzero_nonlinear_coeff`
- `specialization_ne_linear_of_coeff` -> `_private.MIPStarRE.QPBT.Combining.PolynomialImageBounds.0.MIPStarRE.QPBT.PolynomialImageBounds.specialization_ne_linear_of_coeff`
- `avg_specialization_eq_linear_le_of_coeff` -> `_private.MIPStarRE.QPBT.Combining.PolynomialImageBounds.0.MIPStarRE.QPBT.PolynomialImageBounds.avg_specialization_eq_linear_le_of_coeff`
- `avg_diagonalIndicator_le_of_not_linear` -> `_private.MIPStarRE.QPBT.Combining.PolynomialImageBounds.0.MIPStarRE.QPBT.PolynomialImageBounds.avg_diagonalIndicator_le_of_not_linear`
- `avg_orderedIndicator_norm_sq_le_of_not_linear` -> `_private.MIPStarRE.QPBT.Combining.PolynomialImageBounds.0.MIPStarRE.QPBT.PolynomialImageBounds.avg_orderedIndicator_norm_sq_le_of_not_linear`
- `avg_sum_orderedIndicator_norm_sq_le_of_not_linear` -> `_private.MIPStarRE.QPBT.Combining.PolynomialImageBounds.0.MIPStarRE.QPBT.PolynomialImageBounds.avg_sum_orderedIndicator_norm_sq_le_of_not_linear`

No unsealing, visibility change, surrogate declaration, module edit, rebuild, or clean
operation was used. The probe imported the current compiled module and enumerated its
environment constants before applying `Lean.collectAxioms` to the unique suffix match.

## Statement Mapping

The exact original source is still present at
`/home/drx/MIPStarRE-qpbt/.worktrees/issue-118-combined-lines-and-restricted-averages/MIPStarRE/QPBT/Combining/PolynomialImageBounds.lean`
and re-verifies to the issue-pinned SHA256
`871109bd97b6d50354dbf89f2d828cf4c4a9c2877a88b2aa4a654f764df42762`.
The retained PR296 checkpoint at
`2c8f147643d151d8616864cf49817dc6422a9a86` has module SHA256
`e976b6e8319dd0af06b64a56d5e644c208cea73ed7d80ab84c0b9485c8041434`.
The comparison artifact is `/tmp/qpbt-295-signature-comparison.json` (SHA256 `cc19474ca362374d796cb7ea29a6e017686dfbaf514cd2c306d9af8c2779b3c9`).

For every target, the complete source declaration header through `:=` is equal across
original source, PR296, and current source after whitespace normalization and deleting
only `private`. Thus the hypotheses, binder order, and conclusion text were retained;
the current change is visibility for ten targets, not a mathematical signature change.
The two definitions' complete declaration texts, including their bodies, also match.

Limits:

- Historical original/PR296 compiled environments were not rebuilt or re-probed. The
  historical comparison uses the exact retained source files, not old `.olean` files.
- The attempt13 receipt (SHA256
  `1c4c69600ff7268aa218d07f4c7624dfb5b43475aec8dc7d3f3226767591872a`)
  records names and axiom closures, not full signatures; it cannot by itself prove
  statement preservation.
- Theorem proof bodies were not compared. Current pretty-type hashes are
  formatting-sensitive, not canonical kernel fingerprints.
- This validates preservation of these auxiliary declarations only. It does not claim
  paper-theorem faithfulness, close a source gap, or complete unrestricted
  `lem:qld-4-7`.

## Criterion Recommendation

An operational API-criterion clarification is justified. The authoritative issue body
still literally requires "the same 21 public declarations," so that literal criterion
is not met: ten are private. At the same time, all 21 signatures and axiom closures are
preserved, and the prior consumer audit found that exactly the 11 public targets have
outside-module consumers while none of the ten private targets does.

Recommended interpretation: require all 21 preserved declarations with unchanged
signatures and standard-only axiom closures; require public visibility exactly for the
outside-consumed subset; state `11 public / 10 private / 0 missing` explicitly. This is
a bookkeeping/API clarification, not a mathematical completion claim. No issue was
mutated.

## Preservation

B8 remains at 13 attempts and 26509 working seconds. No new construction or proof was
attempted. Issues 524, 598, 527, and 118 were untouched. No repository source edit,
full build, CI, review, cache mutation, publication, or source-gap completion claim was
made. The worktree remained clean at the requested head.
