# PR365 / issue364 current-main assessment

Prepared read-only on 2026-09-19. No repository, worktree, cache, GitHub, CI,
status, or metadata mutation was performed.

## Disposition

**(b) Narrow preservation packet. PR365 is not fully superseded.**

Published `main` has the soundness and downstream rounded/pair construction,
but no public declaration has PR365's statement: ordinary `PolyMeas` witnesses
on the original expanded spaces with all three scalar consistency defects at
the unchanged direct-soundness `deltaLd` bound. The current downstream theorem
changes both the witnesses and conclusions, and weakens the exposed point
bound through projective rounding. Matching downstream purpose is therefore
not statement supersession.

## Exact heads and records

- Published `main`: `b5f52bcae19a350de0ff9c29d695df8fe82fd420`.
- PR365/worktree: `e6ff96075f48b084e5377f76d5eeb50337a45fc6`;
  sole Lean commit `c39d7f2551f6c53f6fb50406dd3f9c8cdd3bab59`.
- Pending daemon train, not published main:
  `04f79c5071d020fc4578b9ae11808eff2daa575b`; its PR623 merge
  `ec549bdc50248057fc32ee32a9efaf3ecc9f14db` contributes the PR363 public
  point-readout identity.
- GitHub reads through `local/bin/gh_common.py`: issue364 and PR365 remain open;
  PR365 head is unchanged and dirty/conflicting; latest review is
  `5195354732` at the exact head.
- Reused prior inventory: `/tmp/opus-report-pr365-20260917.md`, SHA-256
  `f6ef4a42a8c7c950f0dcd0054f425abb4dbdb69fc07a14cba2abad1f00e51ea8`.
- Proof provenance to retain: `c39d7f25` was authored by Dengnifer on
  2026-09-08; blueprint commit `e6ff9607` records Claude Opus 5 as co-author.
  The issue364 brief records no numeric time/token cost, so none is invented;
  the commits, brief, prior report, and any external telemetry should remain
  attached when MAIN preserves the packet.

## Source and scope

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1289`
states `lem:qld-4-7`: projective measurements of separated polynomial pairs,
with point consistency. Its first proof paragraph invokes low-degree soundness
to obtain a polynomial POVM consistent with the combined scalar point family.

PR365 is only a supplied-witness, directly indexed consequence of that first
paragraph. It assumes `CombinedPointsWitness` and `ExtendedLinesWitness`,
returns nonprojective ordinary scalar-polynomial POVMs, and proves neither
polynomial separation nor the paired projective measurement. It must remain a
separate formalization-support node, not `\leanok` for source `lem:qld-4-7`.
Issue527's source correspondence remains qualified: the direct carrier avoids,
but does not discharge, the printed tensor-code correspondence and
`2m+2` seed-indexed obligations. The supplied line witness also does not close
source gap #598. Source gap #524 is unrelated.

## Statement correspondence

PR365's theorem
`ExtendedLineGame.exists_native_scalar_polynomial_measurements_of_supplied_witnesses`
has three exact `deltaLd` conclusions after taking the unique `Fin 1`
polynomial coordinate:

1. supplied Alice scalar point measurement versus Bob polynomial evaluation;
2. Alice polynomial evaluation versus supplied Bob scalar point measurement;
3. mutual consistency of the two ordinary polynomial POVMs.

Published replacements cover only components:

- `exists_direct_ld_soundness_of_k_eq_one_any_strategy`
  (`AnyStrategySoundness.lean:114`) gives the same three bounds for
  `DirectPolyMeasTuple` against the strategy's total point readout.
- `strategy_value_ge_directPassingErrorEnvelope`
  (`PassingValue.lean:89`) supplies the required passing premise with the named
  envelope.
- `exists_rounded_polynomial_ordered_estimates`
  (`RoundedPolynomialEstimates.lean:170`) internally scalar-postprocesses the
  tuple comparisons, but publicly returns projective tuple measurements and
  ordered errors bounded by `4 * eta + 8 * deltaQ`; it does not expose any of
  PR365's three exact scalar bounds.
- `exists_pairWitness_of_points_lines` returns paired projective measurements
  (`PairPointConsistency.lean:226`) at a still later, larger error and likewise
  is not statement-equivalent.

The later pipeline therefore does not imply PR365 through an existing public
API. In particular, the third exact scalar mutual-consistency conclusion is
not exported anywhere on published main.

## Proof-content accounting

Already preserved on published main:

- arbitrary-strategy Naimark soundness and all three tuple bounds;
- the concrete passing-error proof and named `directPassingErrorEnvelope`;
- the point-readout calculation as private
  `point_scalar_measurement` (`RoundedPolynomialEstimates.lean:89-111`);
- question-dependent scalar postprocessing in the rounded proof
  (`RoundedPolynomialEstimates.lean:219-254`).

Still unique to PR365:

- the public ordinary-`PolyMeas` existence statement at the unchanged error;
- extraction by `directPolyMeasTupleMarginal` and the evaluation identity
  `directPolyMeasTuple_evaluation_marginal`;
- postprocessing of the tuple/tuple defect to the ordinary-polynomial mutual
  defect without the rounding loss.

## Narrow preservation packet

After train `04f79c50` is actually published, preserve four tightly scoped
files/items:

1. Rename the module to a mathematical name such as
   `ExtendedLineGame/SuppliedScalarPolynomialConsistency.lean` and rename the
   theorem to
   `exists_scalar_polynomial_measurements_of_supplied_witnesses`. Preserve its
   statement, replacing the inline `3 * (sqrt ... + ...)` by
   `directPassingErrorEnvelope`; add no premise, projectivity claim, or weaker
   target.
2. Replace the stale call to the absent
   `exists_direct_polynomial_measurements_of_supplied_witnesses` by direct use
   of `exists_direct_ld_soundness_of_k_eq_one_any_strategy`,
   `strategy_value_ge_directPassingErrorEnvelope`, and positivity of the named
   envelope. Retain the existing coordinate-marginal proof.
3. Imports should be the current APIs:
   `DirectLowDegree.AnyStrategySoundness`, `ExtendedLineGame.PassingValue`, and
   the public `ExtendedLineGame.NativePointConsistency` supplied only by
   pending PR623; add the renamed module to `MIPStarRE/QPBT.lean`.
4. Add one separate ch15 formalization-support blueprint node matching only
   the scalar theorem. Use current node
   `thm:qld-direct-soundness-any-strategy`, the separate supplied-point node
   from PR623, and `fact:data-processing`. Do not restore the branch's combined
   three-declaration node or its shared-constant/marginal assertions. Update
   `local/briefs/364-native-scalar-consistency.md` to retain authorship,
   proof provenance, and cumulative cost while recording the refreshed APIs.

Drop the PR365 ch13 node: published main already documents the same soundness
theorem at `thm:qld-direct-soundness-any-strategy` (`ch15:4264-4288`). Do not
resurrect the obsolete supplied-direct-soundness wrapper.

## Review findings that remain applicable

From review `5195354732`, carry forward only F4, F7, F8, F10, and the PR365
portion of F9:

- split the blueprint entry so `\leanok` matches one public signature;
- include `fact:data-processing` in `\uses`;
- remove implementation word `Native` from module/theorem naming;
- replace `Lean-only` by `formalization-only`;
- replace tactic prose such as "after unfolding" by mathematical prose.

The other findings target ancestors or files already handled independently on
main and are not part of this preservation packet.

## Limitation

The packet cannot compile against published `b5f52bca` as-is because the public
`point_values_measurement_eq_suppliedQ` declaration is not there. An equivalent
proof exists only as a private theorem on published main; the reusable public
declaration is present only in pending train `04f79c50`. This assessment does
not assume that train has published and makes no completion claim for #598,
#524, or #527.
