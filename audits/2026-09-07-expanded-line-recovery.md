# Recovery of the Full Expanded-Line Packet

## Mathematical Scope

This recovery retains the complete packet #116 / PR213. Its source is
`lem:qld-comm-line-cons` in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:523-678`.
The targets are the degree bound, positivity, completeness, projectivity,
vanishing outside the axis degree bound, and all three expanded-line
consistency conclusions, followed by the existential error-function theorem.
No smaller collection of auxiliary results is substituted for that scope.

The measurement is the convolution of the strategy line measurement with the
Pauli-register measurement whose labels are restricted low-degree encodings.
The saved proof first establishes an exact overlap identity for the completed
evaluation classes, including the `none` class for a non-evaluating line
answer. Bipartite transport gives the evaluation-class bound; projective
refinement then gives the line-versus-point bound. This reverses the order of
the second and third estimates in the paper without changing their final
statements. All four directed opposite-placement pairs are handled directly.

The public result uses `deltaLine epsilon = sqrt epsilon`. The saved estimates
are first proved with a linear error and a uniform bound by four, then combined
to obtain the common square-root error. Constants precede all parameter and
strategy quantifiers and are independent of the register dimensions.

## Preserved Histories

- Existing PR213 remote head, confirmed by the API and `git ls-remote`:
  `35fa3c10c1baf206d409adbd205f261545916002`.
- Original local branch/worktree `issue-116-expanded-line-measurements`:
  `f1dc470395734138ab5e8c4ff1fc485d1edce79a`, clean, with no Git transaction or
  matching live writer observed before recovery.
- The remote head is an ancestor of the saved local head. Both histories remain
  reachable and unchanged; the local source includes the later cleanup and
  dependency work, not merely the remote snapshot.
- PR213 has old exact-head green CI at its remote head and no independent
  review. That evidence is not current-head recovery acceptance.
- Frozen current-main base:
  `c830b4893539eeee0ab2c56c6afee662f6d5a433`.
- New recovery lane: `.worktrees/issue-116-expanded-line-current`, initialized
  from that main base through canonical worktree setup.
- Stack prerequisite PR298 / #297:
  `956e10fa93df81f4d44bdc2eaa6615caf0d7a5dc`.
- Stack prerequisite PR207 / #115, after its helper-reuse repair:
  `6e2edbbd1c3e12190a5dbc07f7abe598c49335b8`.
- Both stack merges passed the normal merge-loss guard; their combined base is
  `581f7c6b05db21e12baf7a9457b741f4cbebfdc4`.

Neither stack prerequisite is represented here as merged. Their review/CI and
merge gates remain separate. The recovery does not import the honest strategy
from PR299 to obtain shared lemmas.

The new recovery base does not yet contain the original local issue116 head as
an ancestor. Updating PR213 therefore still requires normal history
reconciliation after proof-content validation. No force push, reset, branch
replacement, or suppression of a merge-loss finding is authorized by this
manifest. The original source is preserved throughout that later decision.

## Source Manifest

The saved facade and ten modules contain 4,812 lines. All are retained in the
recovery. Paths below are relative to `MIPStarRE/QPBT/Observables/` and identify
the saved source at `f1dc470`:

| Path | Saved Blob |
| --- | --- |
| `LineMeasurement.lean` | `dcc11472c6413efc61ba8c85b644cfbc6a0fa3f3` |
| `LineMeasurement/BipartiteTransport.lean` | `4a4f5e00d86c0650f71e8c00fde9a657f486d4e4` |
| `LineMeasurement/EvalClassConsistency.lean` | `293e5abfe7c2e907670df4c7347db1834b231cd2` |
| `LineMeasurement/Evaluation.lean` | `c497f0d0ca7daf5ee9816f25c5e451d47b940a91` |
| `LineMeasurement/Expanded.lean` | `9c38f5188253a8c1a97f84b4aa45972c14d7fb1c` |
| `LineMeasurement/LinePointConsistency.lean` | `54a477637a56ad6a0b5a6db826a77f4cad90da91` |
| `LineMeasurement/LinePointOverlap.lean` | `42f4d9c5cb4bbaa7b5b3c3c31267e1bd980834b2` |
| `LineMeasurement/Projector.lean` | `d14c2b4da2edfc38168d1e4a5719a141f41d0b19` |
| `LineMeasurement/Restriction.lean` | `f2c47922720e30f68ea103ec7b6aebc44a4d4743` |
| `LineMeasurement/SelfConsistency.lean` | `50bcbdba4c12701fbf9af93ad77fab87c6816896` |
| `LineMeasurement/SquareRootError.lean` | `89de284cd8957b35b6500136f823352029ca03b5` |

The published #297 `Restriction` module is retained byte for byte instead of
restoring the older copy: its current blob is
`c4134cdb75758af27c0f63b22d4abb06d10fef1b`. It contains the same degree and
evaluation proof content on the current public interface. Because that module
no longer imports the old `Evaluation` module, `LinePointOverlap` imports
`Evaluation` explicitly where its additivity and partial-evaluation lemmas are
used. This is the sole initial layout adaptation; no duplicate restriction
definitions are introduced.

## Statement Integrity

The repository's public-header parser compared all 21 pre-existing public
declarations in the current-main facade with the saved definitions and theorems
across the full module layout. Every header matches, including all eight packet
targets, `ExpandedLineConclusions`, and `exists_deltaLine`.

- Paper assumptions: a projective strategy satisfying the test's winning
  premise, admissible parameters, a Pauli basis, and the sampled line-point
  distribution. The source includes the symmetric register placements.
- Lean assumptions: the existing `ProjectiveSetting P epsilon` and the same
  admissible parameters, canonical line descriptions, and opposite placements.
  No additional construction, residual, bridge, or consistency input is added.
- Paper conclusions: existence of projective expanded line measurements and
  the self-consistency and two point-consistency bounds with polynomial error.
- Lean conclusions: the same concrete convolution measurements and all three
  bounds on all four directed opposite-placement pairs, with a universal
  constant and the common square-root error, packaged by `exists_deltaLine`.
- Encoding qualification: the completed evaluation classes and zero effect for
  a non-evaluating answer are the current blueprint's explicit zero-direction
  convention, not a new restriction on the line distribution or theorem domain.

The body of `ExpandedLineConclusions`, not only its `Prop`-valued header, was
also compared byte for byte with frozen main and is unchanged. All previous
worktrees and mathematical budgets are retained; B8/#118 remains at 13 attempts
and 26,509 working seconds with no new attempt.

## Current API Adaptation

The restored proofs needed only local interface repairs and reuse of existing
proofs; no public packet statement, quantifier order, or error function changed.

- The saved private Pauli completeness lemma collided with the now-public
  `sum_pauliProj_eq_one`. The duplicate completeness and positivity proofs are
  replaced by the public `sum_pauliProj_eq_one` and `posSemidef_pauliProj`.
- Line-measurement projectivity uses the existing public
  `SandwichProduct.postprocess_isProjective`.
- The square-summability helpers retain their statements and apply the existing
  public measurement bound, including its left and right placed measurements.
- Projective fiber absorption uses
  `SandwichProduct.effect_mul_postprocess_effect`.
- Self-consistency uses the current public `consistencyDefect_congr` and
  `reindexState_norm_eq` in place of the obsolete names.
- The public facade invokes the current `win_low_degree`, whose statement
  matches the saved winning-implication proof entry.

These replacements leave the archived source proofs available at `f1dc470` and
reuse their already-public mathematical counterparts, rather than introducing
assumptions or copying old private WinImplications aliases.

## Fresh Validation

Every recovered implementation module and the public `LineMeasurement` facade
passes a direct source check on this recovery stack. Scoped Lake builds through
the complete facade pass, and `lake env lean MIPStarRE/QPBT.lean` passes.

The fresh harness `/tmp/qpbt-116-complete-axioms-20260907.lean` imports the
compiled facade and checks all eight packet targets plus `exists_deltaLine`.
All nine axiom closures contain only `propext`, `Classical.choice`, and
`Quot.sound`; the original existential statement is checked explicitly.
The earlier construction harness also verifies twelve standard-only closures
covering the degree bound, projectors, measurement construction, axis-zero
property, and square-root conversion. No recovered module contains a new
proof hole or prohibited bypass, and no linter is disabled.

Only after these checks is the proof-level blueprint marker for
`lem:qld-comm-line-cons` added, with a description of the alternative order of
the formalized estimates. Historical ancestry reconciliation, canonical CI,
independent review, and service-owned integration remain separate pending gates.

## Historical Reconciliation

The validated recovery was committed as
`b59b328c532aa3354e22a5437c1731ee8c5b2a06` before the ordinary merge of the saved
`f1dc470` history. That merge exposed twelve final conflicts; all other paths
were identical to the validated recovery. The eight owned Lean conflicts retain
the validated recovery content, including the exact published #297 Restriction
module. No source theorem or construction hypothesis is changed by resolution.

The only unrelated Lean conflict is
`Combining/DirectLowDegree/Transport/SeedFiber.lean`. Its incoming version adds
thirty lines declaring `reindexState_norm_eq` and `vecTensor_norm_eq` in the
root QPBT namespace. Those names, statements, and proofs are already present
in the imported `State.lean`. Retaining the current SeedFiber version avoids
duplicate declarations; both archived proof versions remain in the saved
history. This is duplicate avoidance, not deletion of a mathematical result.

The incoming chapter14 snapshot also predates several current-main and PR207
proof nodes. Resolution retains those nodes and the #297 restriction auxiliary,
and incorporates the valid additional #116 measurement/evaluation links and
the cross-reference identifying its direct treatment of all four placements.

One incoming prose assertion needs correction: the alternative proof displayed
an overlap equality for each fixed outcome `a`. The proved identity is instead
summed over the completed outcome set, as stated by
`sum_stateQForm_evalClass_AA'_BA''_eq`. The ancillary Pauli label shifts the two
answer labels together. This preserves their total agreement probability, but
not the probability assigned to a fixed label: if the original answers are
both zero, averaging a common uniform field shift spreads that agreement mass
over the field labels. Thus a fixed-label overlap need not equal its original
value. The recovery retains the correct summed-overlap/inconsistency argument;
the old prose remains preserved in `f1dc470` for provenance.

The designated telemetry coordinator separately resolves `events.md` and
`owner-sessions.jsonl`. The latter retains all 247 current raw rows exactly;
the older incoming completion of owner session #210 is already represented by
the later clock-reanchored current record. Its historical rows and all three
merge stages are archived, and an explicit supersession note records why
reintroducing the older clock row would duplicate accounting. The author does
not normalize, discard, or independently rewrite these telemetry records.

The normal merge-loss guard and post-resolution source checks remain required
before the two-parent history merge is committed. Original worktrees, refs,
and raw inputs remain preserved throughout; no abort, reset, or force operation
is used.
