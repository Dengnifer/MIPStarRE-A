# PR 386: distribution API review repair

## Scope and size

This assessment addresses F1 and F2 of
[review 5151088100](https://github.com/Dengnifer/MIPStarRE-A/pull/386#pullrequestreview-5151088100),
bound to `9c77af050fc5ced90ff683dcc51b3b6bc4c7efd8`.

The comparison base is the review's fixed merge base,
`de4a87cbb440c1a6be8c3db512ac8c61a9be8ae5`.
For Lean files only, the PR changes from 18 files, +4864/-20 lines, to
18 files, +4753/-27 lines. The repair relative to the reviewed head is
13 Lean files, +931/-1049 lines. This report is additional documentation,
excluded from those counts. No commits were discarded or rewritten.

## F1: shared distribution laws

Thirty existing theorems move, with their statements, proofs, names, and
declaration docstrings unchanged, into the two existing shared API files.
There are no new definitions, wrappers, simp attributes, or proof abstractions.
The three all-generic modules `SubLineBind`, `SubLineProduct`, and
`SubLineShuffle` are removed after relocating every declaration.
The remaining five feature modules retain all their domain-specific results.

The destination `MIPStarRE/QPBT/Games/DistributionAux.lean` has 793 lines.
It receives the following twelve names from `RestrictedMixture`,
`SubLineBind`, and `RestrictedAverage`:

- `Distribution.sum_filter_weight_eq_avgOver`
- `Distribution.bind_map`
- `Distribution.bind_uniform_restrict_eq`
- `Distribution.bind_map_left`
- `Distribution.bind_congr_support`
- `Distribution.bind_const`
- `Distribution.bind_bind`
- `Distribution.prod_bind_left`
- `Distribution.bind_uniform_fin_two`
- `avgOver_bind`
- `avgOver_mix`
- `avgOver_bind_uniform_component_le`

The destination `MIPStarRE/QPBT/Games/DistributionMarginals.lean` has 624 lines.
It receives the following eighteen names from `SubLineProduct`,
`SubLineShuffle`, `SubLineBlocks`, `SubLineSeed`, and `SubLineSupport`:

- `Distribution.support_nonempty_of_isProbability`
- `Distribution.prod_map_left`
- `Distribution.prod_map_fst`
- `Distribution.prod_map_of_fst`
- `Distribution.prod_map_eq_bind`
- `Distribution.prod_support`
- `Distribution.prod_weight`
- `Distribution.map_bijective_eq`
- `Distribution.prod_map_right`
- `uniformDistribution_prod`
- `uniformDistribution_snd_event_mass`
- `Distribution.restrict_congr`
- `Distribution.restrict_prod_snd`
- `restrict_uniform_prod_snd`
- `Distribution.restrict_prod_fst`
- `uniformDistribution_fst_event_mass`
- `restrict_uniform_prod_fst`
- `Distribution.restrict_map`

### Import dependencies

`DistributionAux` now imports `MIPStarRE.LDT.Basic.DistributionAvg` instead
of `MIPStarRE.LDT.Basic.Distribution`. The former transitively imports the
latter and supplies `avgOver_nonneg`, used by the existing component estimate.
The first placement attempt omitted this dependency, failed a focused Lean
check, and was reverted before the corrected relocation.

`DistributionMarginals` retains its two imports:
`MIPStarRE.LDT.Basic.PMFAverages` and `MIPStarRE.QPBT.Games.DistributionAux`.
Neither shared file imports a QPBT feature module.

`SubLineSeed` replaces its import of `SubLineBind` by the latter's former
import, `SubLinePrefix`. `SubLineConstruct` drops `SubLineProduct`;
`SubLineSource` drops `SubLineShuffle`. The shared API is already available
through `Combining.Defs -> Test.LowDegreeGameTheorems -> Games.DistributionMarginals`.
All other feature imports remain unchanged. No import-only compatibility
modules remain.

## F2: one seed-marginal proof

The original private `map_uniformDistribution_seed` in
`MIPStarRE/QPBT/Test/LowDegreeGameTheorems.lean` is exported under the
already-public name `uniformDistribution_map_ldSeed`. Its proof is unchanged,
and its two existing local callers use the public name. The duplicate
declaration in `RestrictedMixture` is removed; its caller retains the same name.
No public theorem name is lost and no alias is introduced.
The original map `LdSpace.seed` and the duplicate's
`fun z : LdSpace L => z.seed` are definitionally equal.
Neither file acquires a new import for this reuse.

## Statement integrity

The paper source is
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:243-272`
for the seed marginal, and
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1038-1116`
for restricted laws and sub-lines. The corresponding blueprint labels are
`lem:alnf`, `lem:dlnf`, `def:ith-restricted-line`,
`lem:restricted-line-mixture-bounds`, and `lem:qld-sublines`.

- Seed marginal: the paper samples a uniform ambient tuple; Lean samples
  `uniformDistribution (LdSpace L)` for `L : LdParams`. Both conclude that
  the retained scalar seed is uniform. Verdict: faithful finite encoding.
- Mixture and error bounds: the paper assumes its low-degree parameter domain
  and a nonnegative average bound; Lean retains `LdParams` or
  `AdmissibleParams`, nonnegativity, and the average-bound hypotheses.
  The conclusions retain the uniform mixtures and factors `2m` and `4m^2`.
  The consistency instance retains the point and line witnesses representing
  the preceding results and the universal constant outside all parameters.
  Verdict: no change to the existing source-aligned statements.
- Sub-lines: the paper concludes existence for its seed-indexed extended
  line-point distribution. Lean retains `Nonempty (SubLineWitness P)` on the
  directly indexed carrier for `P : AdmissibleParams`, with the same separate
  X and Z marginal properties. Verdict: unchanged auxiliary scope, not a proof
  of transport to the paper's extended seed-indexed carrier.

`Combining/Lines.lean`, `Combining/Defs.lean`, and the chapter 15 blueprint
are byte-identical to the reviewed head. The thirty relocated declaration
blocks were compared verbatim before and after the move. No hypothesis,
conclusion, quantifier order, definition, or proof-debt marker was changed.

## Validation and remaining obligations

Focused `lake env lean` checks passed for both shared files,
`LowDegreeGameTheorems`, `RestrictedMixture`, `RestrictedAverage`,
`SubLineSupport`, `SubLineBlocks`, `SubLineSeed`, `SubLineConstruct`,
`SubLineSource`, and `Combining/Lines.lean`.
The `sorry|axiom` scans found no holes in the relocated API. The existing
`exists_ld_soundness` hole and both combined-line construction holes remain.
`leanblueprint web` from `blueprint/` and `git diff --check` passed.
An axiom audit of all thirty relocated theorems, the reused seed marginal,
and the seven completed packet declarations reports only `propext`,
`Classical.choice`, and `Quot.sound`.

Canonical exact-head CI and guarded publication are recorded separately by
the workflow and the session handoff. This repair does not adjudicate the
review or launch another full review. The source-dimensional sub-line
transport and the existing measurement-construction obligations remain
outside this simplifier pass.
