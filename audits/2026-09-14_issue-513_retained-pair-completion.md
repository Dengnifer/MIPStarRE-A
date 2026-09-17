---
title: "Retained point overlap and completion of the actual polynomial-pair measurements"
date: 2026-09-14
purpose: >
  Record both retained mismatch estimates, the faithful completion of the
  actual rounded measurements, all four point-consistency bounds, full
  signature and axiom evidence, and the remaining source-level composition.
issue: "#513"
status: partial
start_head: a5e16b79c2128ade384dee8b72a9d13354d6ae34
---

# Scope

The concrete retained-overlap and completion goal is complete. The new
`ExtendedLineGame.exists_pairWitness_of_points_lines` constructs a
`GlobalPairWitness` with all four point-consistency conclusions from the
actual point and directly indexed extended-line witnesses. Its explicit
error retains the line contribution and eighth-root rounding loss.

The source theorem `exists_globalPairWitness` is unchanged and remains open,
which accounts for this audit's partial status. The source blueprint entry
`lem:qld-4-7` remains `notready`; completed auxiliary entries state their
actual inputs and numerical conclusions explicitly.

The new modules, relative to `MIPStarRE/QPBT/Combining/`, are
`RetainedPointBounds.lean`, `PairCompletion.lean`, and
`ExtendedLineGame/{PairMeasurement,RetainedPointMass,PairPointConsistency}.lean`.
Two existing helper proofs are exposed for reuse, without changing their
statements or proof bodies. The QPBT aggregate import is synchronized.

# Source of Truth

The paper passage was read before tactics:
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1360-1404`,
especially `eq:qld-s-good-and-bad` through `eq:qld-sgg-mhat-sandwich`.
The ordered, scalar-nonlinear, and wrong-variable audits dated 2026-09-14
were read first. No concentration estimate was reproved.

PR535's complete `PairCompletion.lean` was read at immutable commit
`1744bd9533055b9b43af9a8d46906cbafb69afdd`. Only its algebraic dependency
chain is recovered: polynomial-pair recovery and embedding, restriction,
missing operator, completion labels and effects, and projectivity. The two
unused heterogeneous consistency corollaries are omitted. The original
provenance through `cb6d86d8`, `3de03d0a`, and `aaa5cb48` is retained in the
module documentation. These recovered proofs earn no new-proof attribution.

PR549's complete `Apply.lean` was read at immutable commit
`aeaca3aee589ff666c5ab6feb2681e2cb06e8b1d`, including its imports,
namespace, section context, theorem signature, and full established-line
construction proof. It is inspected read-only and is not imported into this
worktree. No saved branch, PR552 merge index, or other worktree was changed.

# Findings

## Incorrect Outer Projection

Let X and Z be complete projective measurements with outcomes in a finite
field F, let r,t be field elements, and let v be an arbitrary vector. Put

$$
 T_{\alpha,\beta}
 =\sum_{\alpha b+\beta c=\alpha r+\beta t}X_bZ_c.
$$

For beta nonzero, orthogonality gives the exact Gram identity

$$
 ((I-X_r)T_{\alpha,\beta})^*((I-X_r)T_{\alpha,\beta})
 =\sum_{\substack{\alpha b+\beta c=\alpha r+\beta t\\b\ne r}}
 Z_cX_bZ_c.
$$

Every selected pair differs from (r,t), so its scalar collision probability
is exactly 1/|F|. The sandwich weights are nonnegative and sum to the actual
mass of v. The zero-beta exception costs at most the same amount by
contraction. Consequently

$$
 \mathbb E_{\alpha,\beta}\|(I-X_r)T_{\alpha,\beta}v\|^2
 \leq\frac{2}{|F|}\|v\|^2.
$$

The squared triangle inequality applied after the wrong projection proves

$$
 \|(I-X_r)v\|^2\leq
 2\mathbb E_{\alpha,\beta}\|v-T_{\alpha,\beta}v\|^2
 +\frac{4}{|F|}\|v\|^2.
$$

This verifies the suggested constants; it does not assume them. Neither
normalization of v nor commutation of X with Z is imposed. The X marginal
uses order XZ, and the Z marginal uses ZX, so the incorrect projection is
always the outer factor of the ordered product.

## Faithful Image And Retained Sums

The singleton and canonical field map define an actual equivalence e between
the direct outcome carrier and bounded extended polynomials over the Pauli
field. Both degree certificates follow from support inclusion. Composing
the saved bounded embedding j with the inverse of e gives the injective
actual outcome map `directCombinedEmbedding`. Its range predicate is proved
equivalent to formal equality with `combinePoly` after field transport, and
its actual direct readout is the affine combination of the two evaluations.

For every opposite placement p1,p2, the vectors used are exactly
`v_g = placed(R_{j(g)}) psiHat`. They are never normalized individually.
The joint coordinate equivalence and opposite-placement commutation identify
their residual with the full existing ordered-error sum. Injectivity bounds
the retained sums by that full sum; completeness and projectivity give total
squared mass one. No outcome cardinality or omitted-label term appears.

Writing G for the actual excluded mass, H_W for retained diagonal overlap,
and K_W for retained point mismatch, the checked results are

$$
 K_W=1-G-H_W,\qquad
 K_X\leq2E^{XZ}+4/q,\qquad K_Z\leq2E^{ZX}+4/q.
$$

Thus both retained overlaps are at least `1-G-2E^W-4/q`. The theorems cover
every opposite placement, including the heterogeneous pairs AA'|BA'' and
BB'|AB'', with no symmetry or equal-space hypothesis.

## Completed Measurements And Four Bounds

Relabel R through e and apply the saved completion, assigning every excluded
outcome to the fixed pair of zero polynomials. That pair is only the location
of the missing operator; the measurement contains all actual retained effects
and is not a default witness. Projectivity follows from the saved construction.

The added positive operator commutes with each opposite point effect, so
completion increases retained agreement. Its defect is at most G+K_W.
For the same two measurements supplied by the existing rounded constructor,
set

$$
 \delta=\delta_{\rm ld}\left(a,b,
   3\left(\sqrt{\delta_Q+\delta_L}+md/q\right),q,2m+2,d,1\right),
 \quad\eta=\delta+\sqrt{220\delta^{1/4}}+2\sqrt{2\delta},
 \quad E=4\eta+8\delta_Q.
$$

The preceding concentration bound is B=6E+(12md+4d+10)/q. Therefore each
completed defect is at most

$$
 D=B+2E+4/q=8E+(12md+4d+14)/q.
$$

| Global measurement | Opposite point measurement | Bound |
| --- | --- | --- |
| Alice on AA', X evaluation | Bob X on BA'' | D |
| Alice on AA', Z evaluation | Bob Z on BA'' | D |
| Bob on BB', X evaluation | Alice X on AB'' | D |
| Bob on BB', Z evaluation | Alice Z on AB'' | D |

The full elaborated signature quantifies universal a,b before P, epsilon,
deltaQ, deltaL, S, points, and lines. The only witness inputs are
`CombinedPointsWitness S deltaQ` and `ExtendedLinesWitness S points deltaL`.
There is no retained-overlap input, concentration producer, supplied global
witness, extra section parameter, or additional typeclass premise.

# Required Action

Compose with PR549's proved `exists_extendedLinesWitness_established`, whose
full inspected signature supplies both witnesses, with
`deltaQ = pointError epsilon` and
`deltaL = C*m*combinedError epsilon (md/q)` for polynomially bounded functions.
Its proof constructs the points, lines, subline law, and actual extended
measurement before proving its two consistency fields. It does not assume
an extended-line or global-pair constructor and has no extra section inputs.
Recover its required proof dependencies, preserving provenance, when carrying
out this composition in the authorized branch.

The new constructor consumes precisely that directly indexed completed-answer
line witness. Neither its signature nor the public `GlobalPairWitness`
conclusion mentions the source's seed-bearing auxiliary game. Accordingly,
source-domain identification is not an additional premise required by this
alternative route to the public global theorem. The source-labelled auxiliary
routes still require their own unresolved identifications and must remain
`notready`. Their discrepancies are documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` and
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`.

The remaining numerical proof must bound `min(1,D)` by a universal `deltaQld`
after that actual substitution, including the square root of deltaQ+deltaL
and the eighth-root rounding term. A suitable next target is
`exists_actual_rounded_global_pair_error_bound`. The existing
`exists_global_pair_error_bound` controls a different expression and is not
a proof of this bound. No new unfinished Lean declaration is introduced.

All five existing holes in `Apply.lean` remain exactly where they were:
`exists_extendedLinesWitness_ofPointsWitness`, `exists_extendedLinesWitness`,
`exists_extendedLinesWitness_established_ofPointsWitness`,
`exists_extendedLinesWitness_established`, and `exists_globalPairWitness`.
The established constructor is proved in the immutable PR549 tree, but its
proof has not been transplanted here. The other auxiliary obligations are
not silently discharged by the new result.

# Validation

Focused Lean checks pass for the five new modules, the two reused-helper
modules, and both aggregate imports. Only necessary worktree-local objects are
emitted. The private `.lake/Issue513PairAxioms.lean` prints the complete witness
fields and full constructor signatures; its output is retained in
`.lake/Issue513PairAxioms.log`. All twelve inspected new closure roots list
exactly `propext`, `Classical.choice`, and `Quot.sound`, including
`exists_pairWitness_of_points_lines`. The unchanged public source theorem
still lists `sorryAx`.

The new Lean modules contain no proof holes, axioms, unsafe bypasses,
placeholder tactics, or debug commands. Whitespace and 100-column scans pass.
`leanblueprint web` succeeds with existing bibliography warnings. The
declaration inventory is regenerated after the web build. Auxiliary blueprint
entries expose their full mathematical scope; no source `notready` is removed.
Blueprint synchronization passes, and the declaration checker resolves all
1523 inventory entries. The source-header guard reports no changed
source-labelled public headers. Audit YAML and all eight required sections
are checked. Changed-declaration coverage is checked against the normal
commit before the terminal handoff.
Normal installed hooks are checked and used for the ordinary commit. Full
build, CI, review, publication, push, PR mutation, descendants, and runtime
changes are excluded by the owner's scope and are not run.

# Statement Integrity

Paper assumptions of `lem:qld-4-7`: admissible parameters, positive test
error, and a projective strategy passing the Pauli test. Public Lean
assumptions: unchanged admissible parameters, positive error, and
`ProjectiveSetting`. Paper conclusion: universal constants and projective
polynomial-pair measurements satisfying all four point-consistency bounds.
Public Lean conclusion: unchanged `GlobalPairWitness` at `deltaQld`, with
unchanged quantifiers. Verdict: the faithful boundary encoding is preserved;
the source proof remains incomplete.

For the new auxiliary, the explicit point and direct-domain line inputs
produce the actual rounded measurements internally. Its conclusion constructs
the full witness at D, not the final universal source error. Verdict: exact
quantitative construction under the displayed auxiliary inputs. The source
theorem acquires no hypothesis, weakened conclusion, or proof-level completion
marker over an unresolved dependency.

# Review Use

Check the wrong-projection Gram identity and scalar-collision sum first.
Then inspect the injective outcome transport and the retained sum's inclusion
in the full ordered error. Finally check the exact mass-overlap identity and
the four fields of the completed witness. Distinguish the recovered algebraic
completion from the new retained estimates and heterogeneous placement proof.

# History And Costs

The owner-specified start is 2026-09-14T11:23:01Z and the original deadline
is 11:48:01Z. The first local clock was 11:23:17.770225149Z. The native task
has a 25-minute elapsed limit including checks, audit, and normal commit,
with three minutes reserved for finalization. MAIN records the authoritative
terminal native span and usage. This audit does not invent a terminal duration
or add an intermediate checkpoint to that span.

Preserve these prior spans separately: 9760 seconds, 1311.339 seconds,
1262.781 seconds, 827.06 seconds, and 1367.512 seconds. No prior history is
reset or folded into the current continuation. Native token snapshots remain
cumulative and nonadditive; current native token usage is unavailable here.
The separate issue278/B8 history remains separate.

All writes are confined to the owner-specified third-attempt worktree.
PR552's frozen exact staged merge and every other worktree, runtime control,
live account, and session controller remain untouched.
