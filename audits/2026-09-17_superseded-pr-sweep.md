---
title: "Superseded-PR sweep over the open pull requests"
date: 2026-09-17
purpose: >
  Model-free sweep of every open pull request for declarations the PR
  adds against its merge base that the published main branch already
  contains, by name or by normalised statement.
issue: "#576"
pr: ""
---

# Superseded-PR sweep over the open pull requests

## Headline

- Open pull requests examined: **69**
- With at least one new declaration `github/main` already contains: **38** — #253, #289, #296, #299, #342, #363, #365, #397, #398, #399, #400, #409, #411, #415, #420, #430, #433, #441, #442, #443, #449, #456, #457, #467, #469, #470, #472, #481, #483, #488, #491, #533, #534, #536, #539, #543, #545, #547
- Of those, matched by **fully qualified name** (the strongest signal): **34** — #253, #296, #342, #363, #365, #397, #398, #399, #400, #409, #411, #415, #420, #430, #433, #442, #443, #449, #456, #457, #467, #469, #470, #472, #483, #488, #491, #533, #534, #536, #539, #543, #545, #547

## Method

Generated 2026-09-17T14:29:44Z by `local/bin/dup_check.py sweep` against `github/main` (6546 guarded declarations indexed).
For each open pull request the sweep parses only the Lean files the PR
touches, at the PR head and at its merge base, and calls a declaration
*new* when the head has a fully qualified name the merge base lacks.
Each new declaration is matched against the reference three ways:

| match | meaning |
|---|---|
| `fqn` | the same fully qualified name is already declared on the reference |
| `statement` | a different name whose statement normalises to the same string (comments stripped, proof cut at the top-level `:=`/`by`/`where`, binder names renamed positionally, whitespace collapsed) |
| `short` | the same last name component elsewhere inside the `MIPStarRE` namespace |

No model was called and no proof was checked.

## Limitations

- The comparison is textual. A `statement` or `short` match is a prompt
  to read both declarations, never by itself a verdict about the
  mathematics; a `fqn` match is a genuine name collision on merge.
- A stacked pull request whose base branch has since merged into the
  reference shows its parent's declarations as new against its own merge
  base, so part of its count is stack staleness rather than a second
  proof of the same result. Read the per-PR detail before acting.
- Only the reference is searched. An overlap between two *open* pull
  requests is invisible here; the declaration-claims registry
  (`local/registry/declaration-claims.jsonl`) is what covers that case.
- A head branch missing from the local object store is reported as
  skipped, not as clean: the sweep never fetches on its own.

## Per pull request

| PR | new declarations | already on the reference | fqn | statement | short |
|---:|---:|---:|---:|---:|---:|
| #398 | 200 | 222 | 199 | 20 | 3 |
| #469 | 183 | 205 | 180 | 22 | 3 |
| #449 | 126 | 127 | 124 | 1 | 2 |
| #534 | 51 | 47 | 46 | 1 | 0 |
| #539 | 37 | 37 | 37 | 0 | 0 |
| #543 | 30 | 30 | 30 | 0 | 0 |
| #491 | 29 | 28 | 27 | 0 | 1 |
| #533 | 27 | 27 | 27 | 0 | 0 |
| #400 | 7 | 26 | 4 | 22 | 0 |
| #299 | 151 | 20 | 0 | 20 | 0 |
| #472 | 18 | 16 | 16 | 0 | 0 |
| #457 | 16 | 14 | 14 | 0 | 0 |
| #342 | 12 | 12 | 12 | 0 | 0 |
| #399 | 12 | 12 | 11 | 1 | 0 |
| #430 | 13 | 11 | 11 | 0 | 0 |
| #296 | 21 | 8 | 6 | 2 | 0 |
| #420 | 10 | 8 | 8 | 0 | 0 |
| #488 | 8 | 8 | 7 | 1 | 0 |
| #470 | 7 | 7 | 7 | 0 | 0 |
| #253 | 26 | 5 | 5 | 0 | 0 |
| #442 | 9 | 4 | 4 | 0 | 0 |
| #443 | 3 | 3 | 3 | 0 | 0 |
| #456 | 3 | 3 | 2 | 1 | 0 |
| #409 | 4 | 2 | 2 | 0 | 0 |
| #411 | 2 | 2 | 2 | 0 | 0 |
| #415 | 2 | 2 | 2 | 0 | 0 |
| #433 | 2 | 2 | 2 | 0 | 0 |
| #467 | 3 | 2 | 2 | 0 | 0 |
| #481 | 5 | 2 | 0 | 2 | 0 |
| #483 | 3 | 2 | 2 | 0 | 0 |
| #545 | 2 | 2 | 2 | 0 | 0 |
| #547 | 16 | 2 | 2 | 0 | 0 |
| #289 | 15 | 1 | 0 | 1 | 0 |
| #363 | 3 | 1 | 1 | 0 | 0 |
| #365 | 4 | 1 | 1 | 0 | 0 |
| #397 | 1 | 1 | 1 | 0 | 0 |
| #441 | 1 | 1 | 0 | 1 | 0 |
| #536 | 11 | 1 | 1 | 0 | 0 |
| #212 | 2 | 0 | 0 | 0 | 0 |
| #213 | 0 | 0 | 0 | 0 | 0 |
| #260 | 0 | 0 | 0 | 0 | 0 |
| #265 | 0 | 0 | 0 | 0 | 0 |
| #271 | 8 | 0 | 0 | 0 | 0 |
| #272 | 0 | 0 | 0 | 0 | 0 |
| #274 | 10 | 0 | 0 | 0 | 0 |
| #288 | 5 | 0 | 0 | 0 | 0 |
| #294 | 0 | 0 | 0 | 0 | 0 |
| #349 | 0 | 0 | 0 | 0 | 0 |
| #350 | 0 | 0 | 0 | 0 | 0 |
| #383 | 0 | 0 | 0 | 0 | 0 |
| #417 | 0 | 0 | 0 | 0 | 0 |
| #454 | 0 | 0 | 0 | 0 | 0 |
| #465 | 0 | 0 | 0 | 0 | 0 |
| #479 | 2 | 0 | 0 | 0 | 0 |
| #487 | 8 | 0 | 0 | 0 | 0 |
| #493 | 1 | 0 | 0 | 0 | 0 |
| #503 | 0 | 0 | 0 | 0 | 0 |
| #507 | 0 | 0 | 0 | 0 | 0 |
| #538 | 2 | 0 | 0 | 0 | 0 |
| #540 | 0 | 0 | 0 | 0 | 0 |
| #542 | 3 | 0 | 0 | 0 | 0 |
| #546 | 6 | 0 | 0 | 0 | 0 |
| #552 | 0 | 0 | 0 | 0 | 0 |
| #554 | 0 | 0 | 0 | 0 | 0 |
| #556 | 0 | 0 | 0 | 0 | 0 |
| #561 | 0 | 0 | 0 | 0 | 0 |
| #573 | 2 | 0 | 0 | 0 | 0 |
| #577 | 0 | 0 | 0 | 0 | 0 |
| #578 | 0 | 0 | 0 | 0 | 0 |

## Matches in detail


### PR #398 — Recover the combined line measurement constructor

https://github.com/Dengnifer/MIPStarRE-A/pull/398

- **fqn** `MIPStarRE.QPBT.DistanceCalculus.effect_mul_postprocess_effect_self` already at `MIPStarRE/QPBT/Observables/LineMeasurement/BipartiteTransport.lean:44`
- **fqn** `MIPStarRE.QPBT.DistanceCalculus.leftPlaced_sum_adjoint_mul_le_one` already at `MIPStarRE/QPBT/Observables/LineMeasurement/SquareRootError.lean:39`
- **fqn** `MIPStarRE.QPBT.DistanceCalculus.measurement_sum_adjoint_mul_le_one` already at `MIPStarRE/QPBT/Observables/LineMeasurement/SquareRootError.lean:32`
- **short** `MIPStarRE.QPBT.measurement_sum_adjoint_mul_le_one` already at `MIPStarRE/QPBT/Games/DistanceTheorems.lean:368`
- **fqn** `MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_left_refine_le` already at `MIPStarRE/QPBT/Observables/LineMeasurement/BipartiteTransport.lean:81`
- **fqn** `MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_placed_le_four` already at `MIPStarRE/QPBT/Observables/LineMeasurement/SquareRootError.lean:98`
- **fqn** `MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_placed_le_two_mul_one_sub_overlap` already at `MIPStarRE/QPBT/Observables/LineMeasurement/BipartiteTransport.lean:54`
- **fqn** `MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_right_refine_le` already at `MIPStarRE/QPBT/Observables/LineMeasurement/BipartiteTransport.lean:119`
- **fqn** `MIPStarRE.QPBT.DistanceCalculus.rightPlaced_sum_adjoint_mul_le_one` already at `MIPStarRE/QPBT/Observables/LineMeasurement/SquareRootError.lean:49`
- **fqn** `MIPStarRE.QPBT.DistanceCalculus.stateQForm_zero` already at `MIPStarRE/QPBT/Observables/LineMeasurement/LinePointOverlap.lean:43`
- **fqn** `MIPStarRE.QPBT.DistanceCalculus.sum_norm_sub_apply_sq_le_four` already at `MIPStarRE/QPBT/Observables/LineMeasurement/SquareRootError.lean:60`
- **fqn** `MIPStarRE.QPBT.EvaluatesTo.add` already at `MIPStarRE/QPBT/Observables/LineMeasurement/Evaluation.lean:51`
- … and 210 more (re-run the sweep with `--json`)

### PR #469 — Prove the subline X marginal mixture law

https://github.com/Dengnifer/MIPStarRE-A/pull/469

- **fqn** `MIPStarRE.QPBT.CombinedLinesWitness.one_sub_Z_overlap_le` already at `MIPStarRE/QPBT/Combining/ZEvalDeficit.lean:452`
- **fqn** `MIPStarRE.QPBT.CombinedLinesWitness.one_sub_Z_overlap_le_at` already at `MIPStarRE/QPBT/Combining/ZEvalDeficit.lean:341`
- **fqn** `MIPStarRE.QPBT.CombinedLinesWitness.one_sub_Z_overlap_restricted_le` already at `MIPStarRE/QPBT/Combining/ZEvalDeficit.lean:603`
- **fqn** `MIPStarRE.QPBT.CombinedLinesWitness.one_sub_Z_overlap_restricted_le_at` already at `MIPStarRE/QPBT/Combining/ZEvalDeficit.lean:549`
- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.orderedZX_dist_le` already at `MIPStarRE/QPBT/Combining/OrderedPoints.lean:43`
- **fqn** `MIPStarRE.QPBT.DistanceCalculus.effect_mul_postprocess_effect_self` already at `MIPStarRE/QPBT/Observables/LineMeasurement/BipartiteTransport.lean:44`
- **fqn** `MIPStarRE.QPBT.DistanceCalculus.leftPlaced_sum_adjoint_mul_le_one` already at `MIPStarRE/QPBT/Observables/LineMeasurement/SquareRootError.lean:39`
- **fqn** `MIPStarRE.QPBT.DistanceCalculus.measurement_sum_adjoint_mul_le_one` already at `MIPStarRE/QPBT/Observables/LineMeasurement/SquareRootError.lean:32`
- **short** `MIPStarRE.QPBT.measurement_sum_adjoint_mul_le_one` already at `MIPStarRE/QPBT/Games/DistanceTheorems.lean:368`
- **fqn** `MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_left_refine_le` already at `MIPStarRE/QPBT/Observables/LineMeasurement/BipartiteTransport.lean:81`
- **fqn** `MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_placed_le_four` already at `MIPStarRE/QPBT/Observables/LineMeasurement/SquareRootError.lean:98`
- **fqn** `MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_placed_le_two_mul_one_sub_overlap` already at `MIPStarRE/QPBT/Observables/LineMeasurement/BipartiteTransport.lean:54`
- … and 193 more (re-run the sweep with `--json`)

### PR #449 — feat(QPBT/Combining): add point-line marginal distances

https://github.com/Dengnifer/MIPStarRE-A/pull/449

- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.marginal_X_distance_le` already at `MIPStarRE/QPBT/Combining/Points/WitnessMarginals.lean:37`
- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.marginal_X_linePoint_distance_le` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:97`
- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.marginal_X_option_linePoint_distance_le` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:165`
- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.marginal_Z_distance_le` already at `MIPStarRE/QPBT/Combining/Points/WitnessMarginals.lean:77`
- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.marginal_Z_linePoint_distance_le` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:119`
- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.marginal_Z_option_linePoint_distance_le` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:184`
- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.postprocess_fst_effect` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:67`
- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.postprocess_snd_effect` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:83`
- **fqn** `MIPStarRE.QPBT.DistanceCalculus.effect_mul_postprocess_effect_self` already at `MIPStarRE/QPBT/Observables/LineMeasurement/BipartiteTransport.lean:44`
- **fqn** `MIPStarRE.QPBT.DistanceCalculus.leftPlaced_sum_adjoint_mul_le_one` already at `MIPStarRE/QPBT/Observables/LineMeasurement/SquareRootError.lean:39`
- **fqn** `MIPStarRE.QPBT.DistanceCalculus.measurement_sum_adjoint_mul_le_one` already at `MIPStarRE/QPBT/Observables/LineMeasurement/SquareRootError.lean:32`
- **short** `MIPStarRE.QPBT.measurement_sum_adjoint_mul_le_one` already at `MIPStarRE/QPBT/Games/DistanceTheorems.lean:368`
- … and 115 more (re-run the sweep with `--json`)

### PR #534 — feat(QPBT/Combining): discharge combined_line_measurement_consistency

https://github.com/Dengnifer/MIPStarRE-A/pull/534

- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.marginal_X_distance_le` already at `MIPStarRE/QPBT/Combining/Points/WitnessMarginals.lean:37`
- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.marginal_X_linePoint_distance_le` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:97`
- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.marginal_X_option_linePoint_distance_le` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:165`
- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.marginal_Z_distance_le` already at `MIPStarRE/QPBT/Combining/Points/WitnessMarginals.lean:77`
- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.marginal_Z_linePoint_distance_le` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:119`
- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.marginal_Z_option_linePoint_distance_le` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:184`
- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.postprocess_fst_effect` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:67`
- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.postprocess_snd_effect` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:83`
- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.combinedLineMeasurement_consistency_le_conditioned` already at `MIPStarRE/QPBT/Combining/Lines/Conditioning.lean:174`
- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.combinedLineMeasurement_evaluated_eq_pasted` already at `MIPStarRE/QPBT/Combining/Lines/Construction.lean:173`
- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.consistencyDefect_bipartition` already at `MIPStarRE/QPBT/Combining/Lines/Construction.lean:98`
- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.exists_opposite_bipartition` already at `MIPStarRE/QPBT/Combining/Lines/Construction.lean:53`
- … and 35 more (re-run the sweep with `--json`)

### PR #539 — feat(QPBT/Extraction): discharge tildeM_consistent_pointMeas'

https://github.com/Dengnifer/MIPStarRE-A/pull/539

- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.consistencyDefect_pairState_eq_AA'_BA''` already at `MIPStarRE/QPBT/Combining/Lines/PairStateConsistencyTransport.lean:30`
- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.consistencyDefect_pairState_eq_AB''_BB'` already at `MIPStarRE/QPBT/Combining/Lines/PairStateConsistencyTransport.lean:69`
- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.encodingPauli_point_consistency_eq` already at `MIPStarRE/QPBT/Extraction/NonencodingSupport.lean:117`
- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.expanded_point_consistency_eq` already at `MIPStarRE/QPBT/Extraction/NonencodingSupport.lean:140`
- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.placePlayer_alice_mul_placeSide_bob_tensor` already at `MIPStarRE/QPBT/Extraction/PointConsistency.lean:44`
- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.placeSide_alice_finset_sum` already at `MIPStarRE/QPBT/Extraction/PointConsistencyPrime.lean:55`
- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.placeSide_alice_tensor_mul_placePlayer_bob` already at `MIPStarRE/QPBT/Extraction/PointConsistencyPrime.lean:42`
- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.placeSide_alice_tensor_one` already at `MIPStarRE/QPBT/Extraction/PointConsistencyPrime.lean:32`
- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.placeSide_bob_finset_sum` already at `MIPStarRE/QPBT/Extraction/PointConsistency.lean:57`
- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.placeSide_bob_tensor_one` already at `MIPStarRE/QPBT/Extraction/PointConsistency.lean:34`
- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.pointMeasExp_effect_eq_sum_sub` already at `MIPStarRE/QPBT/Extraction/PointConsistency.lean:70`
- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.point_encodingPauli_consistency_eq` already at `MIPStarRE/QPBT/Extraction/NonencodingSupport.lean:96`
- … and 25 more (re-run the sweep with `--json`)

### PR #543 — feat(QPBT/Extraction): prove nonencoding marginal mass bound

https://github.com/Dengnifer/MIPStarRE-A/pull/543

- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.consistencyDefect_pairState_eq_AA'_BA''` already at `MIPStarRE/QPBT/Combining/Lines/PairStateConsistencyTransport.lean:30`
- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.consistencyDefect_pairState_eq_AB''_BB'` already at `MIPStarRE/QPBT/Combining/Lines/PairStateConsistencyTransport.lean:69`
- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.encodingPauliMeas` already at `MIPStarRE/QPBT/Extraction/EncodingSupport.lean:55`
- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.encodingPauliMeas_effect` already at `MIPStarRE/QPBT/Extraction/EncodingSupport.lean:63`
- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.encodingPauliMeas_effect_eq_zero_of_not_isEncoding` already at `MIPStarRE/QPBT/Extraction/EncodingSupport.lean:87`
- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.encodingPauliMeas_effect_nonneg` already at `MIPStarRE/QPBT/Extraction/EncodingSupport.lean:74`
- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.encodingPauliMeas_eval_effect_eq_convolution` already at `MIPStarRE/QPBT/Extraction/EncodingSupport.lean:121`
- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.encodingPauliMeas_postprocess_eval` already at `MIPStarRE/QPBT/Extraction/EncodingSupport.lean:101`
- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.encodingPauli_point_consistency_eq` already at `MIPStarRE/QPBT/Extraction/NonencodingSupport.lean:117`
- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.expanded_point_consistency_eq` already at `MIPStarRE/QPBT/Extraction/NonencodingSupport.lean:140`
- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.point_encodingPauli_consistency_eq` already at `MIPStarRE/QPBT/Extraction/NonencodingSupport.lean:96`
- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.sum_encodingPauliMeas_effect_eq_one` already at `MIPStarRE/QPBT/Extraction/EncodingSupport.lean:80`
- … and 18 more (re-run the sweep with `--json`)

### PR #491 — feat(QPBT/Combining): restore nondegenerate pasting consistency

https://github.com/Dengnifer/MIPStarRE-A/pull/491

- **fqn** `MIPStarRE.QPBT.Distribution.bind_map` already at `MIPStarRE/QPBT/Games/DistributionAux.lean:447`
- **fqn** `MIPStarRE.QPBT.Distribution.bind_uniform_restrict_eq` already at `MIPStarRE/QPBT/Games/DistributionAux.lean:490`
- **fqn** `MIPStarRE.QPBT.Distribution.sum_filter_weight_eq_avgOver` already at `MIPStarRE/QPBT/Games/DistributionAux.lean:435`
- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.place_AA'_mul_place_BA''_nonneg` already at `MIPStarRE/QPBT/Combining/Lines/ConsistencyPositivity.lean:60`
- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.place_AB''_mul_place_BB'_nonneg` already at `MIPStarRE/QPBT/Combining/Lines/ConsistencyPositivity.lean:69`
- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.place_mul_place_nonneg` already at `MIPStarRE/QPBT/Combining/Lines/ConsistencyPositivity.lean:48`
- **fqn** `MIPStarRE.QPBT.aLinePointDist_eq_bind_restricted` already at `MIPStarRE/QPBT/Combining/Lines/RestrictedMixture.lean:96`
- **fqn** `MIPStarRE.QPBT.aLinePointDist_zero_direction_mass` already at `MIPStarRE/QPBT/Combining/Lines/ZeroDirectionMass.lean:24`
- **fqn** `MIPStarRE.QPBT.avgOver_bind` already at `MIPStarRE/QPBT/Games/DistributionAux.lean:720`
- **fqn** `MIPStarRE.QPBT.avgOver_bind_uniform_component_le` already at `MIPStarRE/QPBT/Games/DistributionAux.lean:777`
- **fqn** `MIPStarRE.QPBT.avgOver_le_restrict_add_discarded_mass` already at `MIPStarRE/QPBT/Games/RestrictedAverage.lean:60`
- **fqn** `MIPStarRE.QPBT.avgOver_mix` already at `MIPStarRE/QPBT/Games/DistributionAux.lean:747`
- … and 16 more (re-run the sweep with `--json`)

### PR #533 — feat(QPBT/Extraction): complete Alice point consistency

https://github.com/Dengnifer/MIPStarRE-A/pull/533

- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.consistencyDefect_pairState_eq_AA'_BA''` already at `MIPStarRE/QPBT/Combining/Lines/PairStateConsistencyTransport.lean:30`
- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.consistencyDefect_pairState_eq_AB''_BB'` already at `MIPStarRE/QPBT/Combining/Lines/PairStateConsistencyTransport.lean:69`
- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.encodingPauli_point_consistency_eq` already at `MIPStarRE/QPBT/Extraction/NonencodingSupport.lean:117`
- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.expanded_point_consistency_eq` already at `MIPStarRE/QPBT/Extraction/NonencodingSupport.lean:140`
- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.placePlayer_alice_mul_placeSide_bob_tensor` already at `MIPStarRE/QPBT/Extraction/PointConsistency.lean:44`
- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.placeSide_bob_finset_sum` already at `MIPStarRE/QPBT/Extraction/PointConsistency.lean:57`
- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.placeSide_bob_tensor_one` already at `MIPStarRE/QPBT/Extraction/PointConsistency.lean:34`
- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.pointMeasExp_effect_eq_sum_sub` already at `MIPStarRE/QPBT/Extraction/PointConsistency.lean:70`
- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.point_encodingPauli_consistency_eq` already at `MIPStarRE/QPBT/Extraction/NonencodingSupport.lean:96`
- **fqn** `MIPStarRE.QPBT.avg_mass_outside_support_le_consistency_defect` already at `MIPStarRE/QPBT/Games/SupportMass.lean:86`
- **fqn** `MIPStarRE.QPBT.consistencyDefect_comm_of_commute` already at `MIPStarRE/QPBT/Extraction/NonencodingSupport.lean:37`
- **fqn** `MIPStarRE.QPBT.consistencyDefect_convolution_eq_of_perfect` already at `MIPStarRE/QPBT/Games/DistanceTheorems/TensorConsistency.lean:153`
- … and 15 more (re-run the sweep with `--json`)

### PR #400 — fix(QPBT/Combining): recover subline Z-term claim

https://github.com/Dengnifer/MIPStarRE-A/pull/400

- **fqn** `MIPStarRE.QPBT.SubLineSamplingData` already at `MIPStarRE/QPBT/Combining/Lines/SubLineConstruct.lean:52`
- **statement** `MIPStarRE.QPBT.Poly` already at `MIPStarRE/QPBT/Combining/Defs.lean:35`
- **statement** `MIPStarRE.QPBT.PolyPair` already at `MIPStarRE/QPBT/Combining/Defs.lean:40`
- **statement** `MIPStarRE.QPBT.SubLinePointDir` already at `MIPStarRE/QPBT/Combining/Lines/SubLineConstruct.lean:44`
- **statement** `MIPStarRE.QPBT.ExtendedPointQuestion` already at `MIPStarRE/QPBT/Combining/Points.lean:32`
- **statement** `MIPStarRE.QPBT.PointPair` already at `MIPStarRE/QPBT/Combining/Points/Commutation.lean:52`
- **statement** `MIPStarRE.QPBT.SubLineTriple` already at `MIPStarRE/QPBT/Combining/Witnesses.lean:136`
- **statement** `MIPStarRE.QPBT.SubLinePointSample` already at `MIPStarRE/QPBT/Combining/Witnesses.lean:141`
- **statement** `MIPStarRE.QPBT.SubLineComponent` already at `MIPStarRE/QPBT/Combining/Witnesses.lean:147`
- **statement** `MIPStarRE.QPBT.LinePointPairSample` already at `MIPStarRE/QPBT/Combining/ZEvalDeficit.lean:326`
- **statement** `MIPStarRE.QPBT.PauliTuple` already at `MIPStarRE/QPBT/Observables/Anticommuting.lean:27`
- **statement** `MIPStarRE.QPBT.WinImplications.PauliLdRemainder` already at `MIPStarRE/QPBT/Observables/WinImplications/LowDegree.lean:28`
- … and 14 more (re-run the sweep with `--json`)

### PR #299 — feat(QPBT/Test): construct the honest Pauli-basis-test strategy (exists_spcc_value_one)

https://github.com/Dengnifer/MIPStarRE-A/pull/299

- **statement** `MIPStarRE.QPBT.Poly` already at `MIPStarRE/QPBT/Combining/Defs.lean:35`
- **statement** `MIPStarRE.QPBT.PolyPair` already at `MIPStarRE/QPBT/Combining/Defs.lean:40`
- **statement** `MIPStarRE.QPBT.SubLinePointDir` already at `MIPStarRE/QPBT/Combining/Lines/SubLineConstruct.lean:44`
- **statement** `MIPStarRE.QPBT.SubLineSamplingData` already at `MIPStarRE/QPBT/Combining/Lines/SubLineConstruct.lean:52`
- **statement** `MIPStarRE.QPBT.ExtendedPointQuestion` already at `MIPStarRE/QPBT/Combining/Points.lean:32`
- **statement** `MIPStarRE.QPBT.PointPair` already at `MIPStarRE/QPBT/Combining/Points/Commutation.lean:52`
- **statement** `MIPStarRE.QPBT.SubLineTriple` already at `MIPStarRE/QPBT/Combining/Witnesses.lean:136`
- **statement** `MIPStarRE.QPBT.SubLinePointSample` already at `MIPStarRE/QPBT/Combining/Witnesses.lean:141`
- **statement** `MIPStarRE.QPBT.SubLineComponent` already at `MIPStarRE/QPBT/Combining/Witnesses.lean:147`
- **statement** `MIPStarRE.QPBT.LinePointPairSample` already at `MIPStarRE/QPBT/Combining/ZEvalDeficit.lean:326`
- **statement** `MIPStarRE.QPBT.PauliTuple` already at `MIPStarRE/QPBT/Observables/Anticommuting.lean:27`
- **statement** `MIPStarRE.QPBT.WinImplications.PauliLdRemainder` already at `MIPStarRE/QPBT/Observables/WinImplications/LowDegree.lean:28`
- … and 8 more (re-run the sweep with `--json`)

### PR #472 — Transfer point-line marginals to the conditioned pasting law

https://github.com/Dengnifer/MIPStarRE-A/pull/472

- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.marginal_X_distance_le` already at `MIPStarRE/QPBT/Combining/Points/WitnessMarginals.lean:37`
- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.marginal_X_linePoint_distance_le` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:97`
- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.marginal_X_option_linePoint_distance_le` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:165`
- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.marginal_Z_distance_le` already at `MIPStarRE/QPBT/Combining/Points/WitnessMarginals.lean:77`
- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.marginal_Z_linePoint_distance_le` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:119`
- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.marginal_Z_option_linePoint_distance_le` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:184`
- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.postprocess_fst_effect` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:67`
- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.postprocess_snd_effect` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:83`
- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.opFamilyDistSq_postprocess_some` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:141`
- **fqn** `MIPStarRE.QPBT.avgOver_linePointDist_point` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:35`
- **fqn** `MIPStarRE.QPBT.avgOver_prod_linePointDist_points` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:49`
- **fqn** `MIPStarRE.QPBT.consistencyDefect_nondegenerateLinePastingDist_le` already at `MIPStarRE/QPBT/Combining/Lines/Conditioning.lean:35`
- … and 4 more (re-run the sweep with `--json`)

### PR #457 — Prove combined point line marginal defect bounds

https://github.com/Dengnifer/MIPStarRE-A/pull/457

- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.marginal_X_distance_le` already at `MIPStarRE/QPBT/Combining/Points/WitnessMarginals.lean:37`
- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.marginal_X_linePoint_distance_le` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:97`
- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.marginal_X_option_linePoint_distance_le` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:165`
- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.marginal_Z_distance_le` already at `MIPStarRE/QPBT/Combining/Points/WitnessMarginals.lean:77`
- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.marginal_Z_linePoint_distance_le` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:119`
- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.marginal_Z_option_linePoint_distance_le` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:184`
- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.postprocess_fst_effect` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:67`
- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.postprocess_snd_effect` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:83`
- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.opFamilyDistSq_postprocess_some` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:141`
- **fqn** `MIPStarRE.QPBT.avgOver_linePointDist_point` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:35`
- **fqn** `MIPStarRE.QPBT.avgOver_prod_linePointDist_points` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:49`
- **fqn** `MIPStarRE.QPBT.exists_combinedPoints_line_marginal_defect_le` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:344`
- … and 2 more (re-run the sweep with `--json`)

### PR #342 — Bound the extended direct coefficient loss

https://github.com/Dengnifer/MIPStarRE-A/pull/342

- **fqn** `MIPStarRE.QPBT.avgOver_directALinePointDist_coefficientEvaluation` already at `MIPStarRE/QPBT/Combining/DirectLowDegree/ResampledCoefficientConsistency.lean:94`
- **fqn** `MIPStarRE.QPBT.avgOver_directALinePointDist_resample` already at `MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/LineResampling.lean:180`
- **fqn** `MIPStarRE.QPBT.avgOver_directDLinePointDist_coefficientEvaluation` already at `MIPStarRE/QPBT/Combining/DirectLowDegree/ResampledCoefficientConsistency.lean:119`
- **fqn** `MIPStarRE.QPBT.avgOver_directDLinePointDist_resample` already at `MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/LineResampling.lean:204`
- **fqn** `MIPStarRE.QPBT.consistencyDefect_directALine_coefficients_evaluated_eq_joint` already at `MIPStarRE/QPBT/Combining/DirectLowDegree/ResampledCoefficientConsistency.lean:143`
- **fqn** `MIPStarRE.QPBT.consistencyDefect_directALine_coefficients_le_joint_add` already at `MIPStarRE/QPBT/Combining/DirectLowDegree/ResampledCoefficientConsistency.lean:192`
- **fqn** `MIPStarRE.QPBT.consistencyDefect_directCoefficients_le_evaluated_add` already at `MIPStarRE/QPBT/Combining/DirectLowDegree/CoefficientConsistency.lean:34`
- **fqn** `MIPStarRE.QPBT.consistencyDefect_directDLine_coefficients_evaluated_eq_joint` already at `MIPStarRE/QPBT/Combining/DirectLowDegree/ResampledCoefficientConsistency.lean:168`
- **fqn** `MIPStarRE.QPBT.consistencyDefect_directDLine_coefficients_le_joint_add` already at `MIPStarRE/QPBT/Combining/DirectLowDegree/ResampledCoefficientConsistency.lean:215`
- **fqn** `MIPStarRE.QPBT.directCoefficientEvaluationDefect` already at `MIPStarRE/QPBT/Combining/DirectLowDegree/ResampledCoefficientConsistency.lean:30`
- **fqn** `MIPStarRE.QPBT.directJointCoefficientEvaluationDefect` already at `MIPStarRE/QPBT/Combining/DirectLowDegree/ResampledCoefficientConsistency.lean:50`
- **fqn** `MIPStarRE.QPBT.extendedDirectLd_coefficientCollisionLoss_le_five_mul` already at `MIPStarRE/QPBT/Combining/DirectLowDegree/ExtendedCoefficientLoss.lean:23`

### PR #399 — Prove extraction marginal complement absorption

https://github.com/Dengnifer/MIPStarRE-A/pull/399

- **fqn** `MIPStarRE.QPBT.Distribution.bind_bind` already at `MIPStarRE/QPBT/Games/DistributionAux.lean:620`
- **fqn** `MIPStarRE.QPBT.Distribution.bind_congr_support` already at `MIPStarRE/QPBT/Games/DistributionAux.lean:575`
- **fqn** `MIPStarRE.QPBT.Distribution.bind_const` already at `MIPStarRE/QPBT/Games/DistributionAux.lean:589`
- **fqn** `MIPStarRE.QPBT.Distribution.bind_map_left` already at `MIPStarRE/QPBT/Games/DistributionAux.lean:545`
- **fqn** `MIPStarRE.QPBT.Distribution.bind_uniform_fin_two` already at `MIPStarRE/QPBT/Games/DistributionAux.lean:689`
- **fqn** `MIPStarRE.QPBT.Distribution.prod_bind_left` already at `MIPStarRE/QPBT/Games/DistributionAux.lean:661`
- **fqn** `MIPStarRE.QPBT.Distribution.prod_map_eq_bind` already at `MIPStarRE/QPBT/Games/DistributionMarginals.lean:190`
- **fqn** `MIPStarRE.QPBT.Distribution.prod_map_fst` already at `MIPStarRE/QPBT/Games/DistributionMarginals.lean:138`
- **fqn** `MIPStarRE.QPBT.Distribution.prod_map_left` already at `MIPStarRE/QPBT/Games/DistributionMarginals.lean:91`
- **fqn** `MIPStarRE.QPBT.Distribution.prod_map_of_fst` already at `MIPStarRE/QPBT/Games/DistributionMarginals.lean:177`
- **fqn** `MIPStarRE.QPBT.Distribution.support_nonempty_of_isProbability` already at `MIPStarRE/QPBT/Games/DistributionMarginals.lean:74`
- **statement** `MIPStarRE.QPBT.uniformDistribution_map_ldSeed` already at `MIPStarRE/QPBT/Test/LowDegreeGameTheorems.lean:86`

### PR #430 — Add completed point line-point marginal transport

https://github.com/Dengnifer/MIPStarRE-A/pull/430

- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.marginal_X_distance_le` already at `MIPStarRE/QPBT/Combining/Points/WitnessMarginals.lean:37`
- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.marginal_X_linePoint_distance_le` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:97`
- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.marginal_X_option_linePoint_distance_le` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:165`
- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.marginal_Z_distance_le` already at `MIPStarRE/QPBT/Combining/Points/WitnessMarginals.lean:77`
- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.marginal_Z_linePoint_distance_le` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:119`
- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.marginal_Z_option_linePoint_distance_le` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:184`
- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.postprocess_fst_effect` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:67`
- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.postprocess_snd_effect` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:83`
- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.opFamilyDistSq_postprocess_some` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:141`
- **fqn** `MIPStarRE.QPBT.avgOver_linePointDist_point` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:35`
- **fqn** `MIPStarRE.QPBT.avgOver_prod_linePointDist_points` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:49`

### PR #296 — Recover ordered polynomial-image bounds through public APIs

https://github.com/Dengnifer/MIPStarRE-A/pull/296

- **fqn** `MIPStarRE.QPBT.PolynomialImageBounds.abs_orderedIndicator_norm_sq_sub_diagonal_le` already at `MIPStarRE/QPBT/Combining/PolynomialImageBounds.lean:153`
- **fqn** `MIPStarRE.QPBT.PolynomialImageBounds.diagonalIndicator` already at `MIPStarRE/QPBT/Combining/PolynomialImageBounds.lean:49`
- **statement** `MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator` already at `MIPStarRE/QPBT/Combining/PolynomialImageBounds.lean:45`
- **fqn** `MIPStarRE.QPBT.PolynomialImageBounds.nonlinear_mass_le_ordered_error` already at `MIPStarRE/QPBT/Combining/PolynomialImageBounds.lean:433`
- **fqn** `MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator` already at `MIPStarRE/QPBT/Combining/PolynomialImageBounds.lean:45`
- **statement** `MIPStarRE.QPBT.PolynomialImageBounds.diagonalIndicator` already at `MIPStarRE/QPBT/Combining/PolynomialImageBounds.lean:49`
- **fqn** `MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator_gram_le_one` already at `MIPStarRE/QPBT/Combining/PolynomialImageBounds.lean:140`
- **fqn** `MIPStarRE.QPBT.PolynomialImageBounds.sum_projective_state_norm_sq` already at `MIPStarRE/QPBT/Combining/PolynomialImageBounds.lean:176`

### PR #420 — Add combined point line-point marginal transport

https://github.com/Dengnifer/MIPStarRE-A/pull/420

- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.marginal_X_distance_le` already at `MIPStarRE/QPBT/Combining/Points/WitnessMarginals.lean:37`
- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.marginal_X_linePoint_distance_le` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:97`
- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.marginal_Z_distance_le` already at `MIPStarRE/QPBT/Combining/Points/WitnessMarginals.lean:77`
- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.marginal_Z_linePoint_distance_le` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:119`
- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.postprocess_fst_effect` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:67`
- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.postprocess_snd_effect` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:83`
- **fqn** `MIPStarRE.QPBT.avgOver_linePointDist_point` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:35`
- **fqn** `MIPStarRE.QPBT.avgOver_prod_linePointDist_points` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:49`

### PR #488 — Lift weighted line collision to product samples

https://github.com/Dengnifer/MIPStarRE-A/pull/488

- **fqn** `MIPStarRE.QPBT.avgOver_aLinePointDist_resample_parameter` already at `MIPStarRE/QPBT/Combining/Lines/AxisLineResampling.lean:28`
- **fqn** `MIPStarRE.QPBT.avgOver_linePointDist_resample_parameter` already at `MIPStarRE/QPBT/Combining/Lines/MixedResampling.lean:28`
- **statement** `MIPStarRE.QPBT.avgOver_uniform_lineRepMap_resample_parameter` already at `MIPStarRE/QPBT/Combining/Lines/SubLineUniform.lean:137`
- **fqn** `MIPStarRE.QPBT.evalOpt_affine_parameter_of_direction_ne_zero` already at `MIPStarRE/QPBT/Combining/Lines/AffineEvaluation.lean:23`
- **fqn** `MIPStarRE.QPBT.evalOpt_uniform_parameter_collision_le` already at `MIPStarRE/QPBT/Combining/Lines/UniformAffineCollision.lean:25`
- **fqn** `MIPStarRE.QPBT.linePointDist_nondegenerate_weighted_collision_le` already at `MIPStarRE/QPBT/Combining/Lines/WeightedCollision.lean:28`
- **fqn** `MIPStarRE.QPBT.polynomial_ofFn_eval_eq_evalCoefficient` already at `MIPStarRE/QPBT/Algebra/Coefficients.lean:36`
- **fqn** `MIPStarRE.QPBT.prod_linePointDist_nondegenerate_weighted_collision_le` already at `MIPStarRE/QPBT/Combining/Lines/ProductWeightedCollision.lean:29`

### PR #470 — Prove weighted nondegenerate line collision bound

https://github.com/Dengnifer/MIPStarRE-A/pull/470

- **fqn** `MIPStarRE.QPBT.avgOver_aLinePointDist_resample_parameter` already at `MIPStarRE/QPBT/Combining/Lines/AxisLineResampling.lean:28`
- **fqn** `MIPStarRE.QPBT.avgOver_linePointDist_resample_parameter` already at `MIPStarRE/QPBT/Combining/Lines/MixedResampling.lean:28`
- **fqn** `MIPStarRE.QPBT.evalCoefficient_collision_card_le` already at `MIPStarRE/QPBT/Algebra/Coefficients.lean:88`
- **fqn** `MIPStarRE.QPBT.evalOpt_affine_parameter_of_direction_ne_zero` already at `MIPStarRE/QPBT/Combining/Lines/AffineEvaluation.lean:23`
- **fqn** `MIPStarRE.QPBT.evalOpt_uniform_parameter_collision_le` already at `MIPStarRE/QPBT/Combining/Lines/UniformAffineCollision.lean:25`
- **fqn** `MIPStarRE.QPBT.linePointDist_nondegenerate_weighted_collision_le` already at `MIPStarRE/QPBT/Combining/Lines/WeightedCollision.lean:28`
- **fqn** `MIPStarRE.QPBT.polynomial_ofFn_eval_eq_evalCoefficient` already at `MIPStarRE/QPBT/Algebra/Coefficients.lean:36`

### PR #253 — feat(QPBT/Extraction): prove the extraction register transport

https://github.com/Dengnifer/MIPStarRE-A/pull/253

- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.extractionAuxReference` already at `MIPStarRE/QPBT/Extraction/EPRState.lean:99`
- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.extractionAuxReference_norm` already at `MIPStarRE/QPBT/Extraction/EPRState.lean:104`
- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.idealExpState_norm` already at `MIPStarRE/QPBT/Extraction/EPRState.lean:91`
- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.reindexState_idealExpState` already at `MIPStarRE/QPBT/Extraction/EPRState.lean:78`
- **fqn** `MIPStarRE.QPBT.extractionEprFirstEquiv` already at `MIPStarRE/QPBT/Extraction/EPRState.lean:28`

### PR #442 — Prove same-placement line point distance bound

https://github.com/Dengnifer/MIPStarRE-A/pull/442

- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.opFamilyDistSq_postprocess_some` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:141`
- **fqn** `MIPStarRE.QPBT.avgOver_linePointDist_point` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:35`
- **fqn** `MIPStarRE.QPBT.avgOver_prod_linePointDist_points` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:49`
- **fqn** `MIPStarRE.QPBT.exists_expLine_point_same_placement_distance_le` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:205`

### PR #443 — Bound uniform affine-parameter collisions

https://github.com/Dengnifer/MIPStarRE-A/pull/443

- **fqn** `MIPStarRE.QPBT.evalOpt_affine_parameter_of_direction_ne_zero` already at `MIPStarRE/QPBT/Combining/Lines/AffineEvaluation.lean:23`
- **fqn** `MIPStarRE.QPBT.evalOpt_uniform_parameter_collision_le` already at `MIPStarRE/QPBT/Combining/Lines/UniformAffineCollision.lean:25`
- **fqn** `MIPStarRE.QPBT.polynomial_ofFn_eval_eq_evalCoefficient` already at `MIPStarRE/QPBT/Algebra/Coefficients.lean:36`

### PR #456 — Prove mixed line-point parameter resampling

https://github.com/Dengnifer/MIPStarRE-A/pull/456

- **fqn** `MIPStarRE.QPBT.avgOver_aLinePointDist_resample_parameter` already at `MIPStarRE/QPBT/Combining/Lines/AxisLineResampling.lean:28`
- **fqn** `MIPStarRE.QPBT.avgOver_linePointDist_resample_parameter` already at `MIPStarRE/QPBT/Combining/Lines/MixedResampling.lean:28`
- **statement** `MIPStarRE.QPBT.avgOver_uniform_lineRepMap_resample_parameter` already at `MIPStarRE/QPBT/Combining/Lines/SubLineUniform.lean:137`

### PR #409 — feat(QPBT/Combining): add point self-consistency transport

https://github.com/Dengnifer/MIPStarRE-A/pull/409

- **fqn** `MIPStarRE.QPBT.avgOver_linePointDist_point` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:35`
- **fqn** `MIPStarRE.QPBT.avgOver_prod_linePointDist_points` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:49`

### PR #411 — Add combined point postprocess marginal identities

https://github.com/Dengnifer/MIPStarRE-A/pull/411

- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.postprocess_fst_effect` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:67`
- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.postprocess_snd_effect` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:83`

### PR #415 — Preserve placed distance under option completion

https://github.com/Dengnifer/MIPStarRE-A/pull/415

- **fqn** `MIPStarRE.QPBT.DistanceCalculus.stateQForm_conjTranspose_mul_mul` already at `MIPStarRE/QPBT/Games/DistanceTheorems/Support.lean:323`
- **fqn** `MIPStarRE.QPBT.ProjectiveSetting.opFamilyDistSq_postprocess_some` already at `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:141`

### PR #433 — feat(QPBT/Games): restore restricted-average mass split

https://github.com/Dengnifer/MIPStarRE-A/pull/433

- **fqn** `MIPStarRE.QPBT.avgOver_le_restrict_add_discarded_mass` already at `MIPStarRE/QPBT/Games/RestrictedAverage.lean:60`
- **fqn** `MIPStarRE.QPBT.avgOver_restrict_mul_mass` already at `MIPStarRE/QPBT/Games/RestrictedAverage.lean:25`

### PR #467 — feat(QPBT/Combining): restore consistency under restriction

https://github.com/Dengnifer/MIPStarRE-A/pull/467

- **fqn** `MIPStarRE.QPBT.avgOver_le_restrict_add_discarded_mass` already at `MIPStarRE/QPBT/Games/RestrictedAverage.lean:60`
- **fqn** `MIPStarRE.QPBT.avgOver_restrict_mul_mass` already at `MIPStarRE/QPBT/Games/RestrictedAverage.lean:25`

### PR #481 — Prove concrete Claim 17-2 closure

https://github.com/Dengnifer/MIPStarRE-A/pull/481

- **statement** `MIPStarRE.QPBT.subline_Z_term_near_one_re_direct` already at `MIPStarRE/QPBT/Combining/Claims.lean:348`
- **statement** `MIPStarRE.QPBT.subline_replace_by_ordered_product_re_direct` already at `MIPStarRE/QPBT/Combining/Claims.lean:79`

### PR #483 — Prove nondegenerate line fiber collision bound

https://github.com/Dengnifer/MIPStarRE-A/pull/483

- **fqn** `MIPStarRE.QPBT.avgOver_uniform_lineRepMap_resample_parameter` already at `MIPStarRE/QPBT/Combining/Lines/SubLineUniform.lean:137`
- **fqn** `MIPStarRE.QPBT.polynomial_ofFn_eval_eq_evalCoefficient` already at `MIPStarRE/QPBT/Algebra/Coefficients.lean:36`

### PR #545 — feat(QPBT/Combining): absorb both direct-game errors

https://github.com/Dengnifer/MIPStarRE-A/pull/545

- **fqn** `MIPStarRE.QPBT.exists_direct_global_pair_error_bound` already at `MIPStarRE/QPBT/Combining/DirectPassingErrorBounds.lean:187`
- **fqn** `MIPStarRE.QPBT.exists_direct_passing_polynomial_bound` already at `MIPStarRE/QPBT/Combining/DirectPassingErrorBounds.lean:27`

### PR #547 — feat(QPBT/Combining): prove finite quadratic POVM obstruction

https://github.com/Dengnifer/MIPStarRE-A/pull/547

- **fqn** `MIPStarRE.QPBT.CombinedPointsWitness.exists_error_of_projective` already at `MIPStarRE/QPBT/Combining/PointErrorObstruction.lean:30`
- **fqn** `MIPStarRE.QPBT.linear_quadratic_agreement_le` already at `MIPStarRE/QPBT/Combining/PointErrorObstruction.lean:67`

### PR #289 — feat(QPBT/Combining): reconstruct separated polynomial pairs

https://github.com/Dengnifer/MIPStarRE-A/pull/289

- **statement** `MIPStarRE.QPBT.TotalDegreePoly` already at `MIPStarRE/QPBT/Observables/LineDefs.lean:113`

### PR #363 — Expose supplied scalar point measurements after direct soundness

https://github.com/Dengnifer/MIPStarRE-A/pull/363

- **fqn** `MIPStarRE.QPBT.exists_direct_ld_soundness_of_k_eq_one_any_strategy` already at `MIPStarRE/QPBT/Combining/DirectLowDegree/AnyStrategySoundness.lean:114`

### PR #365 — Derive native scalar polynomial consistency from supplied soundness

https://github.com/Dengnifer/MIPStarRE-A/pull/365

- **fqn** `MIPStarRE.QPBT.exists_direct_ld_soundness_of_k_eq_one_any_strategy` already at `MIPStarRE/QPBT/Combining/DirectLowDegree/AnyStrategySoundness.lean:114`

### PR #397 — Recover opposite-placement consistency symmetry

https://github.com/Dengnifer/MIPStarRE-A/pull/397

- **fqn** `MIPStarRE.QPBT.consistencyDefect_opposite_symm` already at `MIPStarRE/QPBT/Combining/Lines/Construction.lean:362`

### PR #441 — feat(QPBT/Combining): resample canonical line parameter

https://github.com/Dengnifer/MIPStarRE-A/pull/441

- **statement** `MIPStarRE.QPBT.avgOver_uniform_lineRepMap_resample_parameter` already at `MIPStarRE/QPBT/Combining/Lines/SubLineUniform.lean:137`

### PR #536 — feat(QPBT/Test): prove soundness transfer estimates

https://github.com/Dengnifer/MIPStarRE-A/pull/536

- **fqn** `MIPStarRE.QPBT.sqrt_deltaQld_le` already at `MIPStarRE/QPBT/Combining/RootErrorBounds.lean:23`
