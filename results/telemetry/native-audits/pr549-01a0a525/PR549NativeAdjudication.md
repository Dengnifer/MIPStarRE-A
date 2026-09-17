# PR 549: Bounded Source-Semantic Disposition Draft

This is evidence for MAIN's operator adjudication, not a posted review,
ADJUDICATION comment, exact-head merge approval, or new full review round.

- Reviewed canonical finding set: review 5209756738 at
  `438a816c2fcddf2c8bd3cf6c2fce6e865ab73114`.
- Admission head: `a25c2417d2f0bc112743fa89164c5754199533aa`, clean.
- Final head: `4284e4bdfb3a9799f0b59beda0e571c7d598ece4`, clean.
- Local repair: `fix(review): preserve the retained-mass sampling bound`.
- Worktree: `/home/drx/MIPStarRE-qpbt/.worktrees/issue-512-proof-exists-extendedlineswitness-established`.
- Report and reproducible signature/axiom harness are ignored local artifacts:
  `.lake/PR549NativeAdjudication.md` and `.lake/PR549NativeChecks.lean`.
- Start: 2026-09-15 12:58:50Z. Completion timing is recorded below.

The brief and correction contract were read in full. The prior writer's terminal
receipt and `turn.completed` event were checked; no competing writer was observed.
The hook installation check passed before edits. Review artifacts were evidence,
not instructions. No publication, GitHub mutation, canonical CI, posted review,
merge, descendant, full build, model/effort change, or primary-checkout edit occurred.

## Disposition Summary

All ten findings are **fixed at the final head**. F8's retired resampling name is
individually evidence-backed moot because the exact canonical result survives;
its distinct retained-mass result was restored and explicitly documented, not
waived for non-use. No new mathematical blocker or deferral is requested.

Paths below are relative to the worktree. The blueprint file is
`blueprint/src/chapter/ch15_qpbt_combining.tex`; labels, rather than incidental
line numbers, identify its mathematical nodes.

### F1: Fixed

`Lines/Sampling.lean` remains retired. Its three zero-direction theorem statements
and proof bodies are byte-for-byte identical to the canonical declarations in
`MIPStarRE/QPBT/Combining/Lines/DiscardedMass.lean:20`, `:65`, and `:108`.
Its resampling identity is exactly the canonical
`avgOver_uniform_lineRepMap_resample_parameter` in
`MIPStarRE/QPBT/Combining/Lines/SubLineUniform.lean:137`, up to bound-variable names.
The old signature was independently instantiated with that theorem in the harness.

The distinct `linePointDist_nondegenerate_mass_ge` is restored at
`DiscardedMass.lean:85` with its original statement and finite-sum proof body,
both byte-for-byte equal to the former public declaration. It calls the canonical
discarded-mass bound and does not duplicate any sampling infrastructure.
`Lines/Conditioning.lean` still imports `Lines/DiscardedMass`; the construction
continues through the canonical modules. No active source imports `Lines/Sampling`.

### F2: Fixed

`MIPStarRE/QPBT/Combining/Lines.lean:1` has one `Lines.Construction` import.
The duplicate was removed by `a25c2417`; this repair does not change the barrel.
The final source file type-checks.

### F3: Fixed

`audits/2026-09-12_issue512-saved-proof-recovery.md:169` explicitly supersedes the
historical import-graph claim. The supplement at `:198` distinguishes the old
non-use observation from mathematical equivalence and records the exact retained
mass derivation and restoration. Relative to the canonical reviewed head, the
audit diff is 61 added lines, zero deletions. All earlier prose and costs survive.

### F4: Fixed

The erroneous duplicate `lem:extended-line-measurement-support` is removed.
There are no remaining active references to that label or the phrase
"zero-extended joint point family", and no import of the deleted module.
Both linked mathematical results
survive: the consistency comparison at `lem:qld-extended-line-overlap-comparison`
(blueprint `:2207`) and axis degree at `lem:qld-combined-polynomial-axis-degree`
(blueprint `:2160`). The established proof still cites both nodes.

The surviving comparison now explicitly uses the single alphabet
`F_q union {bottom}`, represented by `Option (PauliScalar P)`. Its point
postprocessing is `(a,b) -> some (alpha*a + beta*b)`, with zero effect at `none`.
The line side is completed evaluation followed by `extendedDirectScalarEquiv`.
It is not the pair alphabet `Option F_q x Option F_q`.
This matches `MIPStarRE/QPBT/Combining/ExtendedLines/Overlap.lean:348`, especially
`:358`, and the combined-value definition in paper `lem:qld-4-12`, lines 1012-1017.
The RHS remains `1 - avgOver sublines.D (pairedSublineOverlap ...)` for every
directed opposite placement. No witness, quantifier, law, error, or Lean proof
was changed by consolidation or by the explicit alphabet clarification.

### F5: Fixed

The source `lem:qld-4-13` node (blueprint `:1428`) depends on `lem:qld-4-12`
at `:1432` and remains `notready` at `:1431`. Paper lines 1020-1034 use the
combined scalar family; line 1126 expressly attributes it to Lemma 4.12.
Lemma 4.10 remains the appropriate prerequisite for the underlying joint pair,
not its replacement in the source Lemma 4.13 dependency.

### F6: Fixed

The proof of `lem:combined-line-measurement-consistency` includes
`lem:qld-opposite-bipartition-transport` and
`lem:consistency-defect-integrand-le-one` (blueprint `:1304` and `:1305`).
These match the calls to `consistencyDefect_opposite_symm` and
`consistencyDefect_integrand_le_one` at
`MIPStarRE/QPBT/Combining/Lines/Construction.lean:428` and `:458`.
The reversed placement and unit cap are genuine steps, not decorative dependencies.

### F7: Fixed

`lem:direct-subline-law-construction` (blueprint `:1901`) links all ten concrete
declarations below. `lem:direct-subline-witness-exists` cites it in its proof.
The description explicitly records admissible parameters, positive seed-index
conditioning fibers, support restrictions, incidence for points on the extended
line, field identifications, zero diagonal directions, and separate one-point
marginals using an independent uniform parameter. It does not assert a stronger
joint conditional law or equality with the source's seed-indexed extended law.

### F8: Fixed

The old public name `avgOver_lineRepMap_resample_parameter` has no consumers and
is retired in favor of the exact canonical theorem at `SubLineUniform.lean:137`.
The missing-entry complaint for this duplicate name is evidence-backed moot;
no different domain or lost zero-direction case is hidden by its retirement.
The distinct `linePointDist_nondegenerate_mass_ge` is public again, through the
canonical module, and has its own truthful support node
`lem:qld-nondegenerate-line-mass` (blueprint `:1124`) with statement and proof
`leanok` tags and the discarded-mass dependency. Final reverse coverage passes.

### F9: Fixed

At blueprint `:2830`, the established proof now says that no outcome above
degree `d` occurs on an axis-parallel extended line. This matches the zero-effect
conclusion of `SubLineWitness.extendedMeasurement_axis_degree` at
`ExtendedLines/Measurement.lean:464` and `ExtendedLinesWitness.axis_degree` at
`Combining/Witnesses.lean:257`. Axis here is the stored test kind `.axis`.
The process-language phrase "support field" has been removed from that proof.

### F10: Fixed

`MIPStarRE/QPBT/Combining/Apply.lean:117` opens with conditional existence of
extended-line measurements and states the first-route numerical estimate.
The later `Unfaithful` paragraph at `:130`, issue #511 reference, false
arbitrary-point-error domain, and elimination plan are unchanged.

## Sampling Equivalence and Preservation

Put `q = Fintype.card (ScalarQ L)` and let `mu = linePointDist L`.
All three bounds quantify over exactly `L : LdParams`; this record carries
positive `m,d,k`, admissible field size, and `m | q`. No new nondegeneracy or
extended-dimension-divisibility premise is introduced.

| Former public result | Preserved result and exact content |
| --- | --- |
| `dLinePointDist_zero_direction_mass_le` | Same name; diagonal zero-direction mass at most `1/q`. |
| `linePointDist_zero_direction_mass_le` | Same name; mixed-law zero-direction mass at most `1/(2q)`. |
| `prod_linePointDist_zero_X_direction_mass_le` | Same name; first-line zero-direction mass under the independent product law at most `1/(2q)`. |
| `avgOver_lineRepMap_resample_parameter` | `avgOver_uniform_lineRepMap_resample_parameter`; arbitrary `K : Type*` with `Field`, `Fintype`, `DecidableEq`, arbitrary natural dimension, arbitrary direction including zero, arbitrary real-valued function of representative and point. |
| `linePointDist_nondegenerate_mass_ge` | Same name restored in `DiscardedMass`; nonzero-direction support mass at least `3/4`. |

For the fifth result, write `p = E_mu[1_{direction=0}]` and
`r = sum_{sample in support(mu), direction != 0} mu(sample)`.
The support partition and probability normalization give `r+p=1`.
The preserved bound gives `p <= 1/(2q)`; a field has `q>=2`, so
`p<=1/4` and `r>=3/4`. This is the original finite-sum proof, using
`Finset.sum_filter_add_sum_filter_not`, `linePointDist_isProbability`,
the canonical zero-direction theorem, and `Fintype.one_lt_card`.

The previously cited `nondegenerateLinePastingMass_bounds` provides only
`1/2 <= retained product mass <= 1`; positivity alone is weaker still.
Non-use was therefore not accepted as equivalence. Although the stronger result
is derivable from preserved canonical estimates, its public theorem and proof
have been retained explicitly to satisfy the preservation contract.

The resampling check keeps the representative jointly with the point. For
direction `v`, both sides average an arbitrary `value (lineRepMap v point) ...`;
the second point is `lineRepMap v point + t*v` with independent uniform `t`.
No positive-dimensional or nonzero-direction restriction is added.

## Ten Construction Declarations

The common domain is `P : AdmissibleParams`: admissible field size, `m | q`,
and `d>=1`, with `m>=1` derived internally. There is no hypothesis
`2*m+2 | q`. The carrier is `SubLineTriple P`, with directly indexed extended
lines and source `LineDesc P.toLdParams` lines. Scalar models are related by
the fixed field equivalence. The harness prints every full signature and checks
all ten axiom closures.

| Declaration | Definition/signature evidence and actual hypotheses |
| --- | --- |
| `subLineDist` | `Lines/SubLineConstruct.lean:150`: uniform `Fin 2` mixture of axis and diagonal pushforwards of `subLineRawDist`. |
| `subLineDist_isProbability` | `SubLineConstruct.lean:450`: probability normalization for every `P`, with no supplied probability premise. |
| `subLineDist_map_fst` | `SubLineConstruct.lean:534`: exact equality to the marginal of `directLinePointDist P.extendedDirectLd`. |
| `subLineDist_map_subLineXProjection` | `Lines/SubLineMixture.lean:172`: the X one-point marginal equals the bind of `subLineComponentDist` with `subLineXComponentDist`. |
| `subLineDist_map_subLineZProjection` | `SubLineMixture.lean:187`: the corresponding Z identity with the same component law. |
| `subLineDist_source_mixture` | `SubLineMixture.lean:202`: one existential normalized component distribution and both separate marginal equalities. |
| `exists_raw_of_mem_subLineDist_support` | `SubLineConstruct.lean:211`: requires support membership and recovers kind, extended coordinate, auxiliary sample, both seed-index equations, and equality to the constructed triple. |
| `subLineTripleOf_incidence` | `SubLineConstruct.lean:367`: requires both seed-index equations and membership of the point in the extended line; concludes both projected incidences. |
| `subLineTripleOf_compatibility` | `SubLineConstruct.lean:385`: requires both seed-index equations; constructs eight affine scalars satisfying `IsCombineLineCompatible`. |
| `subLineTripleOf_axis_closure` | `SubLineConstruct.lean:433`: requires extended kind `.axis`; concludes both source kinds `.axis`. No seed-index hypothesis is needed here. |

The normalized source seed laws at `SubLineConstruct.lean:60` restrict uniform
field elements to the two prescribed index fibers. Positivity is proved from
the parameter domain, not assumed of the witness. The index pair is the
pushforward of a uniform extended coordinate by `subLineXIndex/subLineZIndex`;
outside its own block each index is the first source coordinate. This is the
concrete auxiliary construction, not a claim to reproduce every random choice
in the printed construction. Its required separate mixture conclusions are proved.

`Combining/Lines.lean:310` constructs `exists_subLineWitness` by selecting this
law and discharging all fields. In particular, its calls at `:320` onward
recover the seed-index equations from support before applying incidence or
compatibility. No missing support or conditioning hypothesis is silently dropped.

## Statement Integrity

### Printed Lemma 4.13 Versus the Established Auxiliary

Paper assumptions: the standing admissible Pauli-test parameters and a projective
strategy passing with error `epsilon`; the preceding point construction supplies
the joint measurements and their combined scalar family from Lemma 4.12.
Paper passages inspected include 931-963, 970-1019, 1020-1034, 1038-1116,
1118-1246 (including line 1126) of
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`, and the source
line-point definition at `08_classical_and_quantum_low_degree_tests.tex:274-287`.

Lean assumptions: `P : AdmissibleParams`, `epsilon : Real`, and
`S : ProjectiveSetting P epsilon`. The latter contains an actual strategy,
projectivity, and `1-epsilon <= value`; nonnegative error is derived, not a
new premise. The established theorem does not assume a point witness, a bridge,
or an arbitrary point-error scalar. Its exact quantifier order is:

```text
exists deltaQ, IsPolyErr deltaQ and
  exists C > 0,
    exists deltaCombine, IsPolyErr2 deltaCombine and
      forall P epsilon S,
        exists points : CombinedPointsWitness S (deltaQ epsilon),
          Nonempty (ExtendedLinesWitness S points
            (C * m * deltaCombine epsilon (m*d/q))).
```

The universal functions and constant precede `P`, the error, and the strategy;
the point witness is existential for that strategy and is shared by the line
construction. In the proof the outer constant is chosen to be one, without
changing the public existential statement.

Paper conclusion: POVMs on both expanded local spaces, general line degree at
most `m*d+1`, axis degree at most `d`, both displayed opposite-placement
consistency comparisons with the combined scalar point family, source
line-point sampling over `F_q^(2m+2)`, field-valued answer sum, and error
`poly(m^2*epsilon,m*d/q)`.

Lean conclusion: the same numerical degree bounds and both opposite placements,
but directly indexed line descriptions and direct law, the completed single
answer alphabet `Option F_q`, and `C*m*poly(epsilon,m*d/q)`. Polynomial errors
use the documented additive power bound with positive exponents, not the
literal product shorthand. No claim is made that completed line evaluation
always returns a field value, including on zero-direction singleton lines.

Verdict: **exact match to the explicitly restricted auxiliary blueprint node,
not equivalence to the printed source theorem**. Relative to the source, the
quantitative conclusion is weaker and the carrier/law/alphabet comparisons remain
separate documented obligations. Boundary hypotheses such as `d>=1` and the fixed
finite-field model predate this repair. No Lean theorem statement was weakened,
strengthened, or supplied with new hypotheses here. `lem:qld-4-13` stays
`notready`; `lem:qld-4-13-established` alone retains its auxiliary `leanok`.

The stored source-error obligation `exists_extendedLinesWitness` remains open
under #510. The arbitrary-deltaQ helper
`exists_extendedLinesWitness_established_ofPointsWitness` remains explicitly
`Unfaithful` under #511; its point error cannot simply be omitted from the line
bound. The #509 supplied-point companion and its proof hole are unchanged.
Source carrier/law transport and completed-answer-to-field-sum comparison remain
in `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` and
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`. These pre-existing obligations
are not deferrals of F1-F10. The complex Claim 17-2 obligation is not modified.

`exists_globalPairWitness` is unchanged and standard-axiom clean. Its universal
strategy-error domain still includes zero; no `epsilon>0` premise was introduced.
This bounded task does not re-adjudicate the independent global-pair proof.

### Overlap, Sub-Line, and Retained-Mass Statements

The overlap auxiliary assumes genuine previously constructed point, paired-line,
and sub-line witnesses and a directed opposite placement. It concludes the
completed combined-scalar defect bound above, on the same law and with the same
unit-minus-overlap RHS. The corrected node is exact on that declared auxiliary
domain; it does not claim the source field-answer conclusion.

The sub-line auxiliary assumes only `AdmissibleParams` and constructs the
normalized direct law, its extended marginal, affine/incidence properties, the
two separate mixture marginals, and axis closure. Its blueprint now makes the
pointwise support and conditioning boundaries explicit. It remains auxiliary,
not the source-labelled seed-indexed sub-line lemma.

The retained-mass theorem is not printed as a separate source result. Its paper
input is the unchanged equal-mixture line-point law. Its Lean assumptions and
`3/4` finite-sum conclusion are exactly those of the removed theorem. Its proof
uses the canonical `1/(2q)` estimate and probability complement calculation.
Verdict: **exact restoration of a proved formalization-only quantitative
consequence**, neither a new source hypothesis nor source-status inflation.

## Checks and Limitations

Passed checks:

1. `scripts/install_git_hooks.sh --check` before edits.
2. `lake env lean MIPStarRE/QPBT/Combining/Lines/DiscardedMass.lean`.
   Its branch-private `.olean` was refreshed with a focused `lean -o` invocation.
3. `lake env lean MIPStarRE/QPBT/Combining/Lines.lean`.
4. `lake env lean MIPStarRE/QPBT/Combining/Apply.lean`, with only the three
   pre-existing `sorry` warnings at declarations starting on lines 73, 107, 149.
5. `lake env lean .lake/PR549NativeChecks.lean`: five exact former signature
   checks; printed full signatures for the ten construction declarations and
   the overlap/established statements; 21 enforced axiom-closure checks.
   Every checked closure was exactly `propext`, `Classical.choice`, `Quot.sound`.
6. Byte comparisons of the three duplicate bounds and restored retained-mass
   declaration against the old `Sampling.lean`: identical statements and proofs.
7. `leanblueprint web`: exit 0.
8. `python3 scripts/blueprint_lean_sync.py --root . --update-lean-decls --ci`
   after web generation: exit 0. The declaration list is ignored generated output.
9. Exact-head reverse coverage with `blueprint_lean_sync.py --ci
   --warn-missing-blueprint --fail-on-missing-blueprint --diff-base a25c2417...
   --diff-head HEAD --changed-files MIPStarRE/QPBT/Combining/Lines/DiscardedMass.lean`:
   exit 0, no missing changed-declaration entries. Twelve pre-existing
   statement-header/proof-tag warnings outside this change remain warnings.
10. `check_blueprint_latex.py`, blueprint label resolution, and `git diff --check`.
11. Normal pre-commit hooks: all passed, with no new proof-obligation metadata,
    conclusion-shaped premise, proof-debt header, or explicit axiom findings.
12. Target proof/witness/extended-line files are unchanged relative to admission.
    The only restored Lean declaration is in `DiscardedMass.lean`.

Transient validation failures were resolved, not treated as passes: the first
scratch harness used Boolean `!=` where the historical statement uses propositional
inequality; it was corrected to `Not (=)` without changing repository mathematics.
The initial generated declaration list had 236 stale entries and lacked the new
restored link. One coverage invocation also omitted required `--diff-base`.
The web generator reintroduced stale generated entries while it was running;
regeneration after its completion, followed by the correctly parameterized
exact-head check, passed. No tracked declaration-list churn was introduced.

No full build, standalone `lake exe checkdecls`, full-project blueprint axiom
sweep, or canonical CI was run. The 21 targeted Lean axiom checks and source
checks use the branch-private dependency artifacts; MAIN still owns fresh
exact-head deterministic gates and any operator adjudication/publication.

## Changed Paths and Costs

This delegate changed only:

- `MIPStarRE/QPBT/Combining/Lines/DiscardedMass.lean`
- `audits/2026-09-12_issue512-saved-proof-recovery.md`
- `blueprint/src/chapter/ch15_qpbt_combining.tex`

The local harness/report and regenerated blueprint/build outputs are ignored.
No primary source, telemetry ledger, prior commit, or archived evidence was edited.
Historical thirteen attempts, 26,383 recorded seconds, the earlier approximately
805 verification seconds (approximately 27,188 before recovery), recovery and
correction sessions, all five review rounds, queue costs, the 419-second outage,
and the 1973-second publication continuation remain unchanged. This session is
additional bounded adjudication/repair cost, not a new proof-attempt reset.

Final clean-worktree and hook recheck at 2026-09-15 13:17:27Z: head
`4284e4bdfb3a9799f0b59beda0e571c7d598ece4`; no tracked or untracked worktree
changes reported. Elapsed time to that check was 18 minutes 37 seconds from
the first recorded timestamp. Report completion and final handoff remain within
the 20-minute budget and before the 13:20Z hard stop.
